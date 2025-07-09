#!/bin/bash

# Array of nodes to test
NODES=(1)

# Create results directory if it doesn't exist
mkdir -p results

# Create results file
RESULTS_FILE="results/tuple_counts.txt"
echo "Node,Tuples" > $RESULTS_FILE

# Process each node
for node in "${NODES[@]}"; do
    echo "Testing node: $node"
    
    # Run micro-magic benchmark
    MAGIC_OUTPUT=$(cargo run --release -- \
        --query-source $node \
        --use-all-data \
        --batch-size 88234 \
        --micro-magic \
        --skip-visualization 2>&1)
    
    # Extract tuple count
    TUPLES=$(echo "$MAGIC_OUTPUT" | grep "Inferred tuples:" | awk '{print $3}')
    
    # Save to results file
    echo "$node,$TUPLES" >> $RESULTS_FILE
    echo "Node $node: $TUPLES tuples"
done

echo "Results saved to $RESULTS_FILE" 