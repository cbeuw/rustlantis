#!/bin/sh

echo "$1"

TMPDIR="${TMPDIR:-/tmp}"

SOURCE="$TMPDIR/$1.rs"

target/release/generate $1 > $SOURCE || { echo "$1 panicked" 1>&2; exit 1; }
if target/release/difftest $SOURCE; then
    rm $SOURCE
else
    SOURCE_DEBUG="$TMPDIR/$1-debug.rs"
    target/release/generate --debug $1 > $SOURCE_DEBUG

    REPRO_DIR="${REPRO_DIR:-repros/}"
    mkdir -p $REPRO_DIR

    if target/release/difftest $SOURCE_DEBUG 2> /dev/null; then
        mv $SOURCE $REPRO_DIR
    else
        rm $SOURCE
        mv $SOURCE_DEBUG $REPRO_DIR
    fi
    exit 1
fi
