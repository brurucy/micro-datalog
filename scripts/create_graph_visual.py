import networkx as nx
import matplotlib.pyplot as plt
import argparse
import sys
from pathlib import Path
import matplotlib.patches as patches
from networkx.drawing.nx_agraph import graphviz_layout

def read_edges_from_file(file_path):
    """
    Read edges from a space-separated text file.
    Each line should contain two nodes: node1 node2
    """
    edges = []
    try:
        with open(file_path, 'r') as file:
            for line_num, line in enumerate(file, 1):
                line = line.strip()
                if line and not line.startswith('#'):  # Skip empty lines and comments
                    parts = line.split()
                    if len(parts) >= 2:
                        # Take first two parts as nodes (ignore extra columns if any)
                        edges.append((parts[0], parts[1]))
                    else:
                        print(f"Warning: Line {line_num} has insufficient data: {line}")
        return edges
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading edges file: {e}")
        sys.exit(1)

def read_important_nodes_from_file(file_path):
    """
    Read important nodes from a text file.
    Each line should contain one node.
    """
    important_nodes = set()
    try:
        with open(file_path, 'r') as file:
            for line in file:
                line = line.strip()
                if line and not line.startswith('#'):  # Skip empty lines and comments
                    important_nodes.add(line)
        return important_nodes
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading important nodes file: {e}")
        sys.exit(1)

def create_and_visualize_graph(edges_file, important_nodes_file, output_file=None):
    # Read data
    print("Reading edges...")
    all_edges = read_edges_from_file(edges_file)
    print(f"Loaded {len(all_edges)} edges")
    

    sampled_edges = all_edges[::10]  
    print(f"Sampled {len(sampled_edges)} edges (every 100th from original)")
    
    print("Reading important nodes...")
    important_nodes = read_important_nodes_from_file(important_nodes_file)
    print(f"Loaded {len(important_nodes)} important nodes")
    
    # Create undirected graph from sampled edges
    G_full = nx.Graph()
    G_full.add_edges_from(sampled_edges)
    
    print(f"Graph from sampled edges: {G_full.number_of_nodes()} nodes and {G_full.number_of_edges()} edges")
    
    # Filter nodes: keep all important nodes + every 100th regular node
    all_nodes = list(G_full.nodes())
    regular_nodes = [node for node in all_nodes if node not in important_nodes]
    
    # Keep every 100th regular node (additional sampling on top of edge sampling)
    filtered_regular_nodes = regular_nodes[::10]  # Every 100th element
    
    # Combine important nodes with filtered regular nodes
    nodes_to_keep = list(important_nodes) + filtered_regular_nodes
    
    # Create final subgraph with only the selected nodes
    G = G_full.subgraph(nodes_to_keep).copy()
    
    print(f"Final graph: {G.number_of_nodes()} nodes ({len(important_nodes)} important + {len(filtered_regular_nodes)} regular) and {G.number_of_edges()} edges")
    
    # Create node colors
    node_colors = []
    for node in G.nodes():
        if node in important_nodes:
            node_colors.append('red')  # Important nodes in red
        else:
            node_colors.append('lightblue')  # Regular nodes in light blue
    
    # Set up the plot (larger for big graphs)
    plt.figure(figsize=(16, 12))
    
    # Choose layout - spring layout with adjusted parameters for large graphs
    # Increase k for more spacing, reduce iterations for faster computation
    print("Computing layout with Graphviz (sfdp)...")
    try:
        pos = graphviz_layout(G, prog='dot')  # Try 'sfdp', 'neato', or 'dot'
    except:
        print("Graphviz layout failed. Is pygraphviz installed and configured correctly?")
        sys.exit(1)

    
    # Draw all edges (thin and transparent for large graphs)
    nx.draw_networkx_edges(G, pos, alpha=0.5, width=0.2, edge_color='gray')
    
    # Draw nodes as squares (small size for large graphs)
    nx.draw_networkx_nodes(G, pos, 
                          node_color=node_colors, 
                          node_size=30, 
                          node_shape='s',  # 's' for square shape
                          alpha=0.8)
    
    # Skip labels for large graphs (too cluttered)
    # For large graphs, labels make the visualization unreadable
    # If you need to see specific node labels, consider filtering to important nodes only
    # if G.number_of_nodes() <= 100:
    #     nx.draw_networkx_labels(G, pos, font_size=6, font_weight='bold')
    # else:
    #     # Only label important nodes for large graphs
    #     important_nodes_dict = {node: node for node in G.nodes() if node in important_nodes}
    #     if important_nodes_dict:
    #         nx.draw_networkx_labels(G, important_nodes_dict, pos, font_size=6, font_weight='bold')
    
    # Add title and legend
    plt.title("Graph Visualization with Important Nodes Highlighted", 
              fontsize=16, fontweight='bold')
    
    # Create legend

    legend_elements = [
        patches.Patch(color='red', label='Important Nodes'),
        patches.Patch(color='lightblue', label='Regular Nodes')
    ]
    plt.legend(handles=legend_elements, loc='upper right')
    
    # Remove axes
    plt.axis('off')
    
    # Adjust layout to prevent clipping
    plt.tight_layout()
    
    # Save or show the plot
    if output_file:
        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        print(f"Graph saved to {output_file}")
    else:
        plt.show()
    
    # Print some graph statistics
    original_regular_count = len([node for node in all_nodes if node not in important_nodes])
    print(f"\nSampled Graph Statistics:")
    print(f"- Original edges: {len(all_edges)}")
    print(f"- Sampled edges: {len(sampled_edges)} (every 100th)")
    print(f"- Total nodes displayed: {G.number_of_nodes()}")
    print(f"- Total edges displayed: {G.number_of_edges()}")
    print(f"- Important nodes: {len(important_nodes)} (all included)")
    print(f"- Regular nodes displayed: {len(filtered_regular_nodes)} (every 100th from {original_regular_count} total)")
    print(f"- Sampling ratio: ~1% of original edges and ~{100*len(filtered_regular_nodes)/max(1,original_regular_count):.1f}% of regular nodes")
    
    # Check if all important nodes exist in the graph created from sampled edges
    missing_important = important_nodes - set(all_nodes)
    if missing_important:
        print(f"Warning: The following important nodes are not in the sampled graph: {missing_important}")

def main():
    parser = argparse.ArgumentParser(description='Visualize a graph with highlighted important nodes')
    parser.add_argument('edges_file', help='Path to the edges file (space-separated)')
    parser.add_argument('important_nodes_file', help='Path to the important nodes file')
    parser.add_argument('-o', '--output', help='Output file path (optional, will show plot if not specified)')
    
    args = parser.parse_args()
    
    # Verify files exist
    if not Path(args.edges_file).exists():
        print(f"Error: Edges file '{args.edges_file}' does not exist.")
        sys.exit(1)
    
    if not Path(args.important_nodes_file).exists():
        print(f"Error: Important nodes file '{args.important_nodes_file}' does not exist.")
        sys.exit(1)
    
    # Create and visualize the graph
    create_and_visualize_graph(args.edges_file, args.important_nodes_file, args.output)

if __name__ == "__main__":
    # Example usage if run directly (uncomment and modify paths as needed):
    create_and_visualize_graph('./data/facebook_combined.txt', './data/facebook_combined_1percent_query.txt', 'graph_output.png')
    
    #main()