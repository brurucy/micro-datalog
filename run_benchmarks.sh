#!/bin/bash

# Run benchmarks 25 times
for i in {1..25}; do
    echo "Running benchmark iteration: $i"
    
    cargo run --release -- --use-all-data --university \
    --micro-magic --ascent --micro-streaming \
    --query-predicate subOrganizationOf \
    --query-source-str ResearchGroup0 --arity 2
done

echo "All benchmarks completed!" 