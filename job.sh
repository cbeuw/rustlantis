#!/bin/bash

set -eu

while true
do
    seed=$(python3 -c "print(int.from_bytes(open('/dev/urandom', 'rb').read(8), 'little'))")
    code=$(target/release/generate $seed)
    if ! target/release/difftest - <<< $code
    then
        mkdir -p out
        printf "%s" "$code" > out/$seed.rs
    fi
done
