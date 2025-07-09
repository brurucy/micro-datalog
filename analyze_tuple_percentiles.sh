#!/bin/bash

# Create results directory if it doesn't exist
mkdir -p results

# Temporary file to store all tuple counts
TEMP_FILE="results/tuple_counts_temp.txt"
echo "Node,Tuples" > $TEMP_FILE

# Get all unique nodes from the graph file
echo "Extracting unique nodes from graph..."
NODES=$(cat data/facebook_combined.txt | tr ' ' '\n' | sort -n | uniq)

# Counter for progress
TOTAL_NODES=$(echo "$NODES" | wc -l)
CURRENT=0

# Process each node
for node in $NODES; do
    CURRENT=$((CURRENT + 1))
    echo -ne "Processing node $node ($CURRENT/$TOTAL_NODES)\r"
    
    # Run micro-magic benchmark
    MAGIC_OUTPUT=$(cargo run --release -- \
        --query-source $node \
        --micro-magic \
        --use-all-data \
        --batch-size 88234 \
        --skip-visualization 2>&1)
    
    # Extract tuple count
    TUPLES=$(echo "$MAGIC_OUTPUT" | grep "Inferred tuples:" | awk '{print $3}')
    
    # Save to temp file
    echo "$node,$TUPLES" >> $TEMP_FILE
done

echo -e "\nCalculating percentiles..."

# Sort by tuple count and calculate percentiles
sort -t',' -k2 -n $TEMP_FILE > results/sorted_tuple_counts.txt

# Calculate total number of nodes
TOTAL=$(wc -l < results/sorted_tuple_counts.txt)
TOTAL=$((TOTAL - 1))  # Subtract header line

# Function to get percentile value
get_percentile() {
    local percentile=$1
    local position=$((TOTAL * percentile / 100))
    local value=$(tail -n +2 results/sorted_tuple_counts.txt | head -n $position | tail -n 1 | cut -d',' -f2)
    echo "$value"
}

# Calculate and display percentiles
echo "Tuple Count Percentiles:"
echo "10th percentile: $(get_percentile 10)"
echo "30th percentile: $(get_percentile 30)"
echo "50th percentile: $(get_percentile 50)"
echo "70th percentile: $(get_percentile 70)"
echo "90th percentile: $(get_percentile 90)"
echo "99th percentile: $(get_percentile 99)"

# Save percentiles to file
echo "Percentile,Value" > results/tuple_percentiles.txt
echo "10,$(get_percentile 10)" >> results/tuple_percentiles.txt
echo "30,$(get_percentile 30)" >> results/tuple_percentiles.txt
echo "50,$(get_percentile 50)" >> results/tuple_percentiles.txt
echo "70,$(get_percentile 70)" >> results/tuple_percentiles.txt
echo "90,$(get_percentile 90)" >> results/tuple_percentiles.txt
echo "99,$(get_percentile 99)" >> results/tuple_percentiles.txt

# Clean up temporary file
rm $TEMP_FILE

echo "Results saved to results/tuple_percentiles.txt"
echo "Sorted tuple counts saved to results/sorted_tuple_counts.txt" 