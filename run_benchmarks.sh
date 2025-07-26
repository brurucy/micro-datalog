#!/bin/bash

for i in {1..25}; do
    echo "Running benchmark iteration: $i"
    
    cargo run --release -- --use-all-data --rdf \
    --micro-tabling --ascent --micro-magic --micro-streaming \
    --query-source 223 --query-middle 118 --query-target 151 
done

for i in {1..25}; do
    echo "Running benchmark iteration: $i"
    
    cargo run --release -- --use-all-data --rdf \
    --micro-magic --micro-tabling --ascent --micro-streaming --query-target 34
done

for i in {1..25}; do
    echo "Running benchmark iteration: $i"
    
    cargo run --release -- --use-all-data --rdf \
    --micro-tabling --ascent --micro-streaming --micro-magic
done

echo "All benchmarks completed!" 