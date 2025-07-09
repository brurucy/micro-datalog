#!/bin/bash

# Array of query source values to test
QUERY_SOURCES=(318 3843 1874 3937 217 3983 1748 3059 3890 443)


# Run benchmarks for each query source
for source in "${QUERY_SOURCES[@]}"; do
    echo "Running benchmarks for query source: $source"
    
    # Run the benchmark with current query source
        #--edges 14000 \
       # --ascent
    cargo run --release -- \
        --query-source $source \
       --edges 13000 \
       --ascent
done

echo "All benchmarks completed!" 