#!/bin/bash
mkdir -p out
for seed in {0..10}; do
    target/release/fuzz $seed > out/$seed.rs
    target/release/difftest out/$seed.rs
done