# torrent-reindex

A simple CLI tool to recursively find any files that match a list of .torrent files.

## requirements

* rust nightly (1.15 at the time of writing)
* cargo

## build

    git clone https://github.com/the8472/torrent-reindex.git .
    cargo build --release

## run

    torrent-reindex -t dir/containing/torrents -d /dir/containing/data  # look for matching files; scan all pieces
    torrent-reindex --fast -t file.torrent -d /dir/to/scan              # look for matching files; scan 1 piece per file
    torrent-reindex --presence --fast -t file.torrent -d /dir/to/scan   # look for 1 piece per torrent
