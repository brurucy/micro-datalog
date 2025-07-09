import random

def process_edges(input_file, output_file, batch_size=100):
    selected_edges = []
    current_batch = []
    
    # Read the input file and process edges in batches
    with open(input_file, 'r') as f:
        for line in f:
            edge = line.strip()
            if edge:  # Skip empty lines
                current_batch.append(edge)
                
                # When we have a full batch, select a random edge
                if len(current_batch) == batch_size:
                    selected_edge = random.choice(current_batch)
                    selected_edges.append(selected_edge)
                    current_batch = []
    
    # Handle any remaining edges in the last batch
    if current_batch:
        selected_edge = random.choice(current_batch)
        selected_edges.append(selected_edge)
    
    # Write selected edges to output file
    with open(output_file, 'w') as f:
        for edge in selected_edges:
            f.write(edge + '\n')

if __name__ == "__main__":
    input_file = "data/facebook_combined.txt"
    output_file = "data/random_edges_facebook_combined.txt"
    process_edges(input_file, output_file)
    print(f"Random edges have been written to {output_file}") 