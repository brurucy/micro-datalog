import networkx as nx
import random

def filter_and_sample_nodes(G, min_out_degree, max_out_degree, min_out_reachability, max_out_reachability, sample_size=10):
    """
    Filter nodes based on out-degree and out-reachability criteria and return a random sample.
    
    Args:
        G (nx.DiGraph): Input directed graph
        min_out_degree (int): Minimum out-degree threshold
        max_out_degree (int): Maximum out-degree threshold
        min_out_reachability (float): Minimum out-reachability percentage threshold
        max_out_reachability (float): Maximum out-reachability percentage threshold
        sample_size (int): Number of nodes to sample (default: 10)
    
    Returns:
        list: Random sample of nodes meeting the criteria
    """
    # Calculate out-reachability for all nodes
    num_nodes = G.number_of_nodes()
    out_reachability = {node: (len(nx.descendants(G, node)) / num_nodes * 100) for node in G.nodes()}
    
    # Filter nodes based on criteria
    filtered_nodes = [
        node for node in G.nodes()
        if (min_out_degree <= G.out_degree(node) <= max_out_degree and
            min_out_reachability <= out_reachability[node] <= max_out_reachability)
    ]
    
    # Sample from filtered nodes
    if not filtered_nodes:
        return []
    print 
    sample_size = min(sample_size, len(filtered_nodes))
    return random.sample(filtered_nodes, sample_size)

if __name__ == "__main__":
    # Example usage
    G = nx.read_edgelist('./data/facebook_combined.txt', create_using=nx.DiGraph())
    
    # Example: Find nodes with out-degree between 5-20 and reachability between 10-50%
    sampled_nodes = filter_and_sample_nodes(
        G,
        min_out_degree=1,
        max_out_degree=1,
        min_out_reachability=0.08,
        max_out_reachability=0.16
    )
    
    print(f"Found {len(sampled_nodes)} nodes meeting the criteria:")
    print(sampled_nodes)
    for node in sampled_nodes:
        print(f"Node {node}: out-degree={G.out_degree(node)}, reachability={len(nx.descendants(G, node)) / G.number_of_nodes() * 100:.2f}%") 
