#!/bin/bash

echo "$1"

SOURCE="$TMPDIR/$1.rs"

target/release/fuzz $1 > $SOURCE || { echo "$1 panicked" 1>&2; exit 1; }
target/release/difftest $SOURCE
rm $SOURCE
