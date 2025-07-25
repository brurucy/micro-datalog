#!/bin/bash

for i in {1..25}; do
    echo "Running benchmark iteration: $i"
    
    cargo run --release -- --use-all-data --tc-linear \
    --micro-magic --ascent --fb --query-source 1136 --query-target 1144 \
    --batch-size 5000
done

for i in {1..25}; do
    echo "Running benchmark iteration: $i"
    
    cargo run --release -- --use-all-data --tc-linear \
    --micro-magic --ascent --fb --query-source 0 --batch-size 5000
done

for i in {1..25}; do
    echo "Running benchmark iteration: $i"
    
    cargo run --release -- --use-all-data --tc-linear \
    --micro-magic --ascent --fb --batch-size 5000
done

echo "All benchmarks completed!" 