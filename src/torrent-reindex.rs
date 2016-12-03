#![feature(conservative_impl_trait)]
#![feature(inclusive_range_syntax)]

extern crate bdecode;
extern crate walkdir;
extern crate multimap;
extern crate crypto;
#[macro_use] extern crate clap;
extern crate rayon;
#[macro_use] extern crate itertools;

use itertools::Itertools;
use std::fmt::Display;
use std::error::Error;
use std::env;
use std::path::{Path, PathBuf};
use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, SeekFrom};
use bdecode::{DictIter, Kind, Node, decode};
use walkdir::WalkDir;
use multimap::MultiMap;
use crypto::digest::Digest;
use crypto::sha1::Sha1;
use clap::{Arg, App, SubCommand, ArgGroup};
use rayon::par_iter::*;


/*

strategy:

- cull uninteresting files based on size
- cull large files with interior pieces or with padding by probing a piece contained in the file
- TODO: cull small without internal pieces if they have sha1 in the metadata
- TODO: better iteration order for the scan window
- try all combinations at piece boundaries
- (optional) full scan of the remaining large files since we only probed 1 piece in the first step


TODO: optimize large file operations. open a file once and then scan for multiple torrents at once


*/

macro_rules! println_err(
    ($($arg:tt)*) => { {
        let r = writeln!(&mut ::std::io::stderr(), $($arg)*);
        r.expect("failed printing to stderr");
    } }
);

struct Torrent {
	name: String,
	metadata_path: Option<PathBuf>,
	files: Vec<TFile>,
	piece_size: u64,
	hashes: Vec<u8>
}

#[derive(Debug)]
enum TorrentError {
	Encoding(bdecode::Error),
	Io(std::io::Error),
	Invalid(String)
}

impl std::fmt::Display for TorrentError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.description())
	}
}

impl std::error::Error for TorrentError {
	fn description(&self) -> &str {
		""
	}

	fn cause(&self) -> Option<&std::error::Error> {
		match *self {
			TorrentError::Encoding(ref err) => Some(err),
			TorrentError::Io(ref err) => Some(err),
			TorrentError::Invalid(_) => None
		}
	}
}

impl From<std::io::Error> for TorrentError {
	fn from(err: std::io::Error) -> TorrentError {
		TorrentError::Io(err)
	}
}

impl From<bdecode::Error> for TorrentError {
	fn from(err: bdecode::Error) -> TorrentError {
		TorrentError::Encoding(err)
	}
}

impl Torrent {

	fn from_file(p: &Path) -> Result<Torrent, TorrentError> {

		let mut torrent_file: File = File::open(p)?;

		let read_buf = &mut Vec::with_capacity(torrent_file.metadata().unwrap().len() as usize);

		torrent_file.read_to_end(read_buf);

		let mut decode_options : bdecode::Options = Default::default();
		// a few TB-sized torrents are very very large...
		decode_options.set_token_limit(1_000_000);
		// bdecode::Options{depth_limit: 20, token_limit: 200_000}

		let mut info = bdecode::decode_with_opts(read_buf, &decode_options)?.as_dict().and_then(|mut d| d.find_key(b"info")).and_then(|n| n.as_dict()).ok_or(TorrentError::Invalid("missing info dictionary".to_owned()))?;

		let mut multi : Option<Vec<_>> = info.find_key(b"files").map(|e| e.as_list().unwrap().scan(0, |offset, f| {
			let mut file_dict = f.as_dict().unwrap();
			let len = file_dict.find_key(b"length").and_then(|n| n.as_int()).unwrap_or(0);
			let path = file_dict.find_key(b"path").and_then(|n| n.as_list()).unwrap().fold(PathBuf::new(), |mut p, x| {
				p.push(x.as_str().unwrap_or(&offset.to_string()));
				p
			});
			let file = TFile { offset: *offset, length: len, path: path, tail_read: TailReadMode::Span };
			*offset = *offset + len;

			Some(file)
		}).collect());

		let single = info.find_key(b"length").map(|e| vec!(TFile{ offset: 0, length: e.as_int().unwrap(), path: PathBuf::new(), tail_read: TailReadMode::Truncate}));
		let tname = info.find_key(b"name").and_then(|n| n.as_str()).unwrap_or("no name");
		let plen = info.find_key(b"piece length").and_then(|n| n.as_int()).unwrap();
		let pieces = info.find_key(b"pieces").and_then(|n| n.as_bytes()).unwrap();

		let mut files = single.or(multi).unwrap();

		if let Some(mut last) = files.last_mut() {
			last.tail_read = TailReadMode::Truncate;
		}

		return Ok(Torrent { metadata_path: Some(p.to_owned()), name: tname.to_owned(), files: files, hashes: pieces.to_owned(), piece_size: plen });
	}

	fn num_pieces(&self) -> u64 {
		return ceil_div(self.files.last().unwrap().end(), self.piece_size);
	}

}

#[derive(Hash, Eq, PartialEq, Clone, Copy, Debug)]
enum TailReadMode {
	Truncate,
	ZeroPad,
	Span
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
struct TFile {
	offset: u64,
	length: u64,
	path: PathBuf,
	tail_read: TailReadMode
}

fn ceil_div(x : u64, y : u64) -> u64 {
	1 + ((x - 1) / y)
}

impl TFile {

	fn aligned(&self, piece_size : u64) -> bool {
		self.offset % piece_size == 0
	}

	fn full_piece_offset(&self, piece_size : u64) -> Option<u64> {
		let offset = if self.aligned(piece_size) {
			self.offset
		} else {
			self.offset + piece_size - self.offset % piece_size
		};

		if offset + piece_size > self.end()  {
			return None;
		}

		Some(offset)
	}

	fn piece_numbers(&self, piece_size: u64, internal_only: bool) -> impl Iterator<Item=u64> {
		let offset = self.offset;
		let start = self.offset / piece_size;
		let fend = self.end();
		let tail_mode = self.tail_read;

		return (start..).take_while(move |i| {
			i * piece_size < fend
		}).filter(move |i| {
			let pstart = i * piece_size;
			let pend = pstart + piece_size;
			if internal_only {
				return pstart >= offset && (tail_mode != TailReadMode::Span || pend <= fend)
			}
			return true
		});
	}

	fn has_interior_pieces(&self, piece_size : u64) -> bool {
		self.piece_numbers(piece_size, true).next().is_some()
	}

	fn num_pieces(&self, piece_size : u64) -> usize {
		let piece_start = self.offset - self.offset % piece_size;
		let span = self.end() - piece_start;
		return ceil_div(span, piece_size) as usize;
	}

	fn first_piece(&self, piece_size : u64) -> u64 {
		self.offset / piece_size
	}


	fn end(&self) -> u64 {
		return self.offset + self.length;
	}

}

struct MappedTorrent {
	torrent: Torrent,
	candidates: Vec<Vec<CandidateFile>>
}

#[repr(u8)]
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum PieceState {
	NotScanned,
	Match,
	Fail
}

#[derive(Debug, Eq, PartialEq, Clone)]
struct CandidateFile {
	path: PathBuf,
    duplicates: Vec<PathBuf>,
	pieces: Vec<PieceState>
}

impl CandidateFile {
	fn build(num_pieces: usize, path: PathBuf) -> CandidateFile {
		CandidateFile {pieces: vec![PieceState::NotScanned; num_pieces], path: path, duplicates: vec![]}
	}

	fn set_piece_state(&mut self, idx: usize, val: PieceState) {
		self.pieces[idx] = val
	}

	fn piece_state(&self, idx: usize) -> PieceState {
		self.pieces[idx]
	}
}


#[derive(Debug)]
enum MatchState {
	Skipped,
	Matched,
	NoMatches
}

impl MappedTorrent {
	fn cull_file(&mut self, i: usize, fast_scan: bool) -> bool {

		let ps = self.torrent.piece_size;
		let it;

		{
			let ref tf = self.torrent.files[i];
			let limit = if fast_scan {1} else {usize::max_value()};
			it = tf.piece_numbers(ps, true).take(limit);
		}

		self.scan_pieces(it)
	}

	fn match_any(&mut self) -> MatchState {
		if self.candidates.iter().all(|c| c.is_empty()) {
			return MatchState::NoMatches;
		}

		let mut files : Vec<_> = self.torrent.files.iter().enumerate().map(|(i,tf)| (i, tf.length)).collect();
		files.sort_by_key(|e| e.1);

		let mut something = false;

		for &(i, _) in files.iter().rev() {
			let scanned = self.cull_file(i, true);
			if scanned {
				something = true;
				break;
			}

		}

		if something {
			let any = self.candidates.iter().flat_map(|ref e| e.iter()).any(|cf| cf.pieces.iter().any(|p| *p == PieceState::Match));
			return if any {MatchState::Matched} else {MatchState::NoMatches};
		}


		MatchState::Skipped
	}

	fn scan_pieces<T : Iterator<Item = u64>>(&mut self, to_scan : T) -> bool {

		let torrent = &self.torrent;
		let p_size = torrent.piece_size;
		let ref mut candidates = self.candidates;
		let mut scanned = false;


		let mut first_file = 0;

		//println!("{:?}", candidates);

		for piece_idx in to_scan {
			let hash_offset : u64 = piece_idx * 20;
			let piece_space_offset = piece_idx * p_size;
			let pend = piece_space_offset + p_size;

			//println!("{} {} {}", piece_idx, piece_space_offset, first_file);

			while piece_space_offset >= torrent.files[first_file].end() {
				first_file += 1;
			}



			let mut last_file = first_file;
			let hash = &torrent.hashes[hash_offset as usize..(hash_offset + 20) as usize];

			while torrent.files[last_file].tail_read == TailReadMode::Span && pend > torrent.files[last_file].end() {
				last_file += 1;
			}


			//println!("next it {} {} {}", piece_idx, first_file, last_file);


			let window = &mut candidates[first_file...last_file];

			// can't scan a piece if we have 0 candidates
			// TODO: eliminate 0-length files earlier
			if window.iter().enumerate().any(|(i,v)| torrent.files[first_file + i].length > 0 && v.is_empty()) {
				first_file = last_file;
				continue;
			}

			if window.iter().enumerate().flat_map(|(i, cset)| {
				let ref tf = torrent.files[i + first_file];
				let idx = (piece_idx - tf.offset / p_size) as usize;

				cset.iter().map(move |cf| cf.piece_state(idx))

			}).filter(|p| *p == PieceState::NotScanned).count() == 0 {
				first_file = last_file;
				continue;
			}

			//let cnt = window.iter().map(|cset| format!("{}", cset.len())).join(",");
			//println_err!("comb {}", cnt);

			let cnt = window.iter().map(|cset| cset.len()).fold(1, |acc, v| if acc < 10000  {acc * v} else {acc});

			//println!("comb {}", cnt);

			if cnt >= 5000 {
				println_err!("warning: combinatorial explosion at piece {}; potentially unbounded processing time", piece_idx);
				/*
				for (i, cset) in window.iter().enumerate() {
					println!("{} -> {}",torrent.files[first_file + i].path.display(), cset.iter().map(|cf| cf.path.to_string_lossy()).join(", "))
				}*/
			}


			let mut counters = vec![0 ; window.len()];

			//println!("{:?}", window);

			let mut buf = vec![0 as u8; p_size as usize];
			let mut sha = Sha1::new();

			let first_file_piece_offset = (piece_idx - torrent.files[first_file].offset / p_size) as usize;

			'window: loop {
				let mut read = 0;

				for (i, &j) in counters.iter().enumerate() {
					let ref tf = torrent.files[i + first_file];
					if tf.length == 0 {
						continue;
					}

					let ref cf = window[i][j];
					// TODO cache file handles
					let mut f = File::open(&cf.path).unwrap();
					let seek = std::cmp::max(tf.offset, piece_space_offset) - tf.offset;
					if seek > 0 {
						f.seek(SeekFrom::Start(seek)).unwrap();
					}

					//let remaining = p_size - buf.len() as u64;
					loop {
						let bytes = f.read(&mut buf[read..]).unwrap();
						read += bytes;
						if bytes == 0 || read == p_size as usize {
							break;
						}
					}
				}

				sha.input(&buf[..read]);
				let digest = &mut [0; 20];
				sha.result(digest);

				sha.reset();

				scanned = true;

				if digest == hash {
					for (i, &j) in counters.iter().enumerate() {
						let ref tf = torrent.files[i + first_file];
						let idx = (piece_idx - tf.offset / p_size) as usize;
						if tf.length == 0 {
							continue;
						}
						let ref mut cf = window[i][j];

						cf.set_piece_state(idx, PieceState::Match);
					}
					// iterating over all possible combinations is slow
					// bail instead and fix up based on the matches we have
					break 'window;
				}



				//println!("p:{} st{:?} h:{} read:{}", piece_idx, stack, digest == hash, buf.len());


				for i in 0..counters.len() {
					if window[i].len() == 0 {
						continue;
					}

					counters[i] = counters[i] + 1;
					if counters[i] >= window[i].len() {
						counters[i] = 0;
					}
					if i == counters.len() - 1 && counters[i] == 0 {
						break 'window;
					}
					if counters[i] != 0 {
						break;
					}
				}
			}

			for (i, cset) in window.iter_mut().enumerate().filter(|&(_,ref cset)| cset.len() > 1) {

				let idx = if i == 0 {first_file_piece_offset} else {0};
				if let Some(match_idx) = cset.iter().position(|cf| cf.piece_state(idx) == PieceState::Match) {
					let mut f = File::open(&cset[match_idx].path).unwrap();
					let ref tf = torrent.files[i + first_file];

					let chunk_start = std::cmp::max(tf.offset, piece_space_offset);
					let chunk_end =  std::cmp::min(tf.end(), pend);

					let read_limit = chunk_end - chunk_start;

					let mut reference = vec![0 ; read_limit as usize];
					let mut probe = vec![0 ; read_limit as usize];

					let seek = chunk_start - tf.offset;
					f.seek(SeekFrom::Start(seek)).unwrap();
					f.read_exact(&mut reference[..]).unwrap();

					for cidx in (0..cset.len()).filter(|j| *j != match_idx) {
						let ref mut cf = cset[cidx];
						let mut f2 = File::open(&cf.path).unwrap();
						f2.seek(SeekFrom::Start(seek)).unwrap();
						f2.read_exact(&mut probe[..]).unwrap();

						let old_val = cf.piece_state(idx);
						let new_state = if probe == reference {PieceState::Match} else {PieceState::Fail};
						assert!(old_val == PieceState::NotScanned || old_val == new_state);
						cf.set_piece_state(idx, new_state);
					}

				}
			}

			for (i, vec) in window.iter_mut().enumerate() {
				let ref tf = torrent.files[first_file + i];
				let idx = (piece_idx - tf.offset / p_size) as usize;

				for ref mut cf in vec.into_iter() {
					//let matched = hash_matches.contains(&cf.path);
					//println!("pi:{} idx:{} i:{} ff:{} {:?} {:?}", piece_idx,idx, i, first_file, cf, tf);
					let state = cf.piece_state(idx);
					if state == PieceState::NotScanned {
						cf.set_piece_state(idx, PieceState::Fail);
					}
					//cf.set_piece_state(idx,if matched {PieceState::Match} else {PieceState::Fail});
				}

				// TODO: make pruning configurable to allow partial scans
				vec.retain(|cf| cf.piece_state(idx) == PieceState::Match);

			}

			first_file = last_file;
		}

		return scanned;
	}
}

struct FileSearch {
	torrents: Vec<MappedTorrent>
}

impl FileSearch {
	fn new() -> FileSearch {
		return FileSearch {torrents:vec![] };
	}

	fn add_torrents<'a, T: Iterator<Item=&'a Path> + 'a>(&mut self, paths : T) {
		for p in paths.flat_map(|p| WalkDir::new(p)) {
			match p {
				Ok(f) => {
					let len = match f.metadata() {
						Ok(meta) => meta.len(),
						Err(msg) => {
							println_err!("error: could not stat torrent file {:?} ", msg);
							continue;
						}
					};

					if len == 0 || !f.file_type().is_file() {
						continue;
					}
				 	match Torrent::from_file(f.path()) {
						Ok(t) => self.add_torrent(t),
						Err(msg) => println_err!("could not parse torrent file {} {:?}", f.path().display(), msg)
					}
				},
				Err(msg) => println_err!("skipping torrent file {:?}", msg)
			}

		}
	}

	fn add_torrent(&mut self, torrent : Torrent) {
		let num_files = torrent.files.len();
		self.torrents.push(MappedTorrent {torrent: torrent, candidates: vec![vec![]; num_files]})
	}

	fn add_dirs(&mut self, dir : Vec<String>) {

		let file_index_by_size: MultiMap<u64, (usize, usize)> = self.torrents.iter().enumerate().flat_map(|(i,ref t)| t.torrent.files.iter().enumerate().map(move |(j,tf)| (tf.length, (i,j)))).collect();

		// select files with size of interest
		'walker: for file in dir.into_iter().flat_map(|d| WalkDir::new(d)) {
			match file {
				Ok(f) => {
					let len = f.metadata().unwrap().len();
					if len == 0 || !f.file_type().is_file() {
						continue;
					}

					if let Some(offsets) = file_index_by_size.get_vec(&len) {
						for &(i, j) in offsets {
							let ref mut mapping = self.torrents[i];
							let piece_count = mapping.torrent.files[j].num_pieces(mapping.torrent.piece_size);
							let cf = CandidateFile::build(piece_count, f.path().to_owned());
							mapping.candidates[j].push(cf);
						}
					}
				},
				Err(msg) => {println_err!("skipping file: {}", msg);}
			}
		}
	}

	fn cull_large_files(&mut self, fast_scan: bool) {
		// eliminate non-matching files with internal pieces
		(&mut self.torrents).par_iter_mut().for_each(|mapped| {
			for i in 0..mapped.torrent.files.len() {
				mapped.cull_file(i, fast_scan);
			}
		})
	}

	fn sort_candidates(&mut self) {
		for mapped in &mut self.torrents {
			for i in 0..mapped.torrent.files.len() {
				let name : &str = mapped.torrent.name.as_str();
				let ref tf = mapped.torrent.files[i];
				let ref mut cset = mapped.candidates[i];

				cset.sort_by_key(|cf| {
					let mut points = 0 as i32;
					if tf.path.extension() == cf.path.extension() {
						points += 1;
					}

					let torrent_path = tf.path.components().rev().map(|cmp| cmp.as_os_str().to_string_lossy()).chain(Some(std::borrow::Cow::Borrowed(name)));
					let file_path = cf.path.components().rev().map(|cmp| cmp.as_os_str().to_string_lossy());

					points += torrent_path.zip(file_path).filter(|&(ref a, ref b)| a.to_lowercase() == b.to_lowercase()).count() as i32;

					-points
				});
			}
		}
	}

    fn fold_small_files(&mut self) {
        for ref mut mapped in &mut self.torrents {
            for i in 0..mapped.torrent.files.len() {
                let ref tf = mapped.torrent.files[i];

                if mapped.candidates[i].len() < 2 || tf.has_interior_pieces(mapped.torrent.piece_size) {
                    continue;
                }

                let mut cset = vec![];

                std::mem::swap(&mut cset, &mut mapped.candidates[i]);

                mapped.candidates[i] = cset.into_iter().map(|cf| (hash_file(&cf.path), cf)).group_by(|pair| pair.0).into_iter().map(|group| {

                    let (hash, mut dups) = group;

                    let mut first = dups.next().unwrap().1;
                    first.duplicates = dups.map(|pair| pair.1.path).collect();

                    first
                }).collect();



            }
        }

    }

	fn iter<'a>(&'a self) -> impl Iterator<Item=(&'a Torrent,&'a TFile,&'a Vec<CandidateFile>)> + 'a {
		return self.torrents.iter().flat_map(move |mapping| mapping.candidates.iter().enumerate().map(move |(i, paths)| {
			(&mapping.torrent, &mapping.torrent.files[i], paths)
		}));
	}

	fn cull_spans(&mut self, fast: bool) {

		(&mut self.torrents).par_iter_mut().for_each(|mapping| {
			let ps = mapping.torrent.piece_size;

			for i in 0..mapping.torrent.files.len() {
				//let needs_scan = mapping.candidates[i].into_iter().all(|cf| cf.pieces.iter().all(|p| *p == PieceState::NotScanned));

				let limit = if fast {1} else {usize::max_value()};
				let pieces = mapping.torrent.files[i].piece_numbers(ps,false).take(limit);

				mapping.scan_pieces(pieces);
			}

		})
	}

}

fn hash_file(p : &Path) -> Option<[u8 ; 20]> {

    if let Ok(mut file) = File::open(p) {
        let mut hash = Sha1::new();
        let mut digest = [0 ; 20];
        let mut read_buffer = [0 ; 16*1024];

        loop {
            let read = file.read(&mut read_buffer).unwrap();
            if read == 0 {
                break;
            }

            hash.input(&read_buffer[..read]);
        }

        hash.result(&mut digest);

        return Some(digest)
    }

    None
}


fn find(torrents: Vec<String>, dirs: Vec<String>, fast: bool) -> Result<FileSearch, std::io::Error> {

	//println!("{}", name);

	let mut search = FileSearch::new();

	//println!("loading torrents");
	search.add_torrents(torrents.iter().map(|d| Path::new(d)));
    //println!("indexing directories");
	search.add_dirs(dirs);
    //println!("eliminating large files");
	search.cull_large_files(true);
    //println!("sorting likely candidates by filename");
	search.sort_candidates();
    //println!("folding identical small files");
    search.fold_small_files();
    //println!("scanning boundary pieces");
	search.cull_spans(fast);
	if !fast {
		search.cull_large_files(false);
	}

	return Ok(search);
}


fn print(search : &FileSearch) {
	for mapping in search.torrents.iter() {
		println!("torrent: {}", mapping.torrent.name);
		for (i, tf) in mapping.torrent.files.iter().enumerate() {
			print!("{}:{} -> ", i, tf.path.display());
			let ref cands = mapping.candidates[i];
			if cands.is_empty() {
				print!("no matches")
			} else {
                let file_desc = cands.iter().map(|cf| {
                    let path = cf.path.to_string_lossy();
                    let skipped = cf.pieces.iter().filter(|p| **p == PieceState::NotScanned).count();
                    let hashed = cf.pieces.iter().filter(|p| **p == PieceState::Match).count();
                    let num = tf.num_pieces(mapping.torrent.piece_size);
                    let dups = cf.duplicates.iter().map(|p| p.to_string_lossy()).join(" ");

                    let mut result : String = format!("{} ({}/{} skipped:{})",path,hashed,num, skipped);

                    if dups.len() > 0 {
                        result.push_str(&format!(" [dups: {}]", dups));
                    }

                    result
                }).join("\t");
				print!("found: {}", file_desc);
			}

			println!("");
		}

	}
}

fn check_presence(torrents: Vec<String>, dirs: Vec<String>) {

	let mut search = FileSearch::new();

	search.add_torrents(torrents.iter().map(|d| Path::new(d)));
	search.add_dirs(dirs);

	for mut torrent in search.torrents {
		let result = torrent.match_any();
		let p = match torrent.torrent.metadata_path {
			Some(p) => p.to_string_lossy().into_owned(),
			None => "".to_owned()
		};
		println!("torrent {:?}\t{}\t{}", result, p, torrent.torrent.name)
	}

}


fn main() {


	let args = App::new("torrent-reindex")
		.about("find files matching those described by .torrents")
		.arg(Arg::with_name("none").short("n").help("print torrents for which no matching files were found"))
		.arg(Arg::with_name("jobs")
			.short("j").help("number of parallel reads. 1 likely provides best throughput on spinning rust")
			.takes_value(true).default_value("1"))
		.arg(Arg::with_name("single-torrent")
			.value_name("TORRENT")
			.help("path containing torrent file(s)")
			.required(true)
			.multiple(true)
			.takes_value(true))
		.arg(Arg::with_name("multi-torrent")
			.short("t")
			.help("multple torrents")
			.value_name("TORRENT")
			.takes_value(true)
			.multiple(true))
		.group(ArgGroup::with_name("torrents").arg("single-torrent").arg("multi-torrent"))
		.arg(Arg::with_name("dirs")
			.help("directories to scan")
			.short("d")
			.default_value(".")
			.takes_value(true)
			.multiple(true))
		.arg(Arg::with_name("fast")
			.long("fast")
			.help("only probe 1 piece per file."))
		.arg(Arg::with_name("presence")
			.long("presence")
			.short("p")
			.help("bail out as soon as some data is found. use for a quick (and inaccurate) check which torrents may or may not have data"))
		/*
		.arg(Arg::with_name("v")
			.short("v")
			.multiple(true)
			.help("Sets the level of verbosity"))
		*/
		.get_matches();


	
	let torrents = args.values_of("torrents").unwrap().map(|s| s.to_owned()).collect();
	let dirs = args.values_of("dirs").unwrap().map(|s| s.to_owned()).collect();
	let fast = args.is_present("fast");
	let presence = args.is_present("presence");
	let threads = value_t!(args.value_of("jobs"), usize).unwrap();

	let thread_conf = rayon::Configuration::new().set_num_threads(threads);

	rayon::initialize(thread_conf).unwrap();

	if presence {
		check_presence(torrents, dirs);
		std::process::exit(0);
	}

	match find(torrents, dirs, fast) {
		Ok(found) => print(&found),
		Err(cause) => println_err!("{:?}", cause)
	}
}

#[cfg(test)]
mod tests {
	use super::find;
	use std::path::{Path, PathBuf};

    #[test]
    fn it_works() {
        println!("foo");
		let vals = vec!["test/mismatches", "test/files"].into_iter().map(|s| s.into()).collect();

		let result = find(vec!["test/test.torrent".to_owned()], vals, false).unwrap();

		println!("{:?}", result.torrents[0].candidates);
		let expect : Vec<PathBuf> = ["test/files/a", "test/files/b", "test/files/c", "test/files/d", "test/files/e"].into_iter().map(|e| Path::new(e).to_owned()).collect();

		let actual_it  = result.iter().flat_map(|(torrent, tf, paths)| paths.into_iter());

		for (a, b) in actual_it.zip(expect) {
			assert!(*a.path == b)
		}

		//assert!(actual_it.eq(expect.into_iter()));
		assert!(false);
    }
}
