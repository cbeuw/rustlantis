#!/bin/bash
set -eu

cargo build --release
export MIRI_SYSROOT=$(cargo +nightly miri setup --print-sysroot)
export RUSTLANTIS_MIRI_PATH="$(rustup run nightly miri --print sysroot)/bin/miri"
export RUSTLANTIS_RUSTC_PATH="$(rustup run nightly rustc --print sysroot)/bin/rustc"

function cleanup {
    kill $(jobs -p)
}
trap cleanup EXIT

proc=$(nproc)
for job in $(seq 0 $((proc-1))); do
    nice -n 19 ./job.sh &> $job.out &
done

wait
