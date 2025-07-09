import networkx as nx

def calculate_direct_reachability(graph_path, node_id):
    """
    Calculate the direct reachability of a node in a directed graph
    (only immediate neighbors, not the transitive closure)
    
    Parameters:
    graph_path (str): Path to the graph edge list file
    node_id (int): The node ID to analyze
    
    Returns:
    dict: Statistics about direct reachability
    """
    # Load the graph as directed
    DG = nx.DiGraph()
    with open(graph_path, 'r') as f:
        for line in f:
            if line.startswith('#'):
                continue
            try:
                u, v = map(int, line.strip().split())
                DG.add_edge(u, v)  # Only add edge in the direction specified
            except ValueError:
                continue
    
    total_nodes = DG.number_of_nodes()
    
    # Calculate direct outgoing reachability - just the immediate successors
    if node_id in DG:
        outgoing_reachability = len(nx.descendants(DG, node_id))
        outgoing_percentage = (outgoing_reachability / total_nodes) * 100
    else:
        outgoing_reachability = 0
        outgoing_percentage = 0.0

    
    return {
        "outgoing_reachability": outgoing_reachability,
        "outgoing_percentage": outgoing_percentage,
        "out_degree": DG.out_degree(node_id),
    }

graph_path = "data/facebook_combined.txt"

for node_id in [1]:
    result = calculate_direct_reachability(graph_path, node_id)
    print(f"Node {node_id}: {result['out_degree']} {result['outgoing_reachability']} {result['outgoing_percentage']}")
