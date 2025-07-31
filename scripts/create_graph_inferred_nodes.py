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
                    # Remove symbols like [, ], and , from each line
                    line = line.replace('[', '').replace(']', '').replace(',', '').replace('(', '').replace(')', '').replace('"', '')
                    parts = line.split()

                    if len(parts) >= 2:
                        # Take first two parts as nodes (ignore extra columns if any)
                        edges.append((parts[0], parts[1]))
                    elif len(parts) == 1:
                        edges.append((parts[0], parts[0]))
                    else:
                        print(f"Warning: Line {line_num} has insufficient data: {line}")
        return edges
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading edges file: {e}")
        sys.exit(1)

def read_nodes_from_file(file_path):
    """
    Read important nodes from a text file.
    Each line should contain one node.
    """
    nodes = set()
    try:
        with open(file_path, 'r') as file:
            for line in file:
                line = line.strip()
                if line and not line.startswith('#'):  # Skip empty lines and comments
                    # Remove symbols like [, ], and , from each line
                    line = line.replace('[', '').replace(']', '').replace(',', '')
                    nodes.add(line)
        return nodes
    
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found.")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading important nodes file: {e}")
        sys.exit(1)

"""
edges_file: materialised results
important_edges_file: all edges from the processed relation storage after the evaluation is done
query_nodes_file: bound values in the query
"""
def create_and_visualize_graph(edges_file, important_edges_file, query_nodes_file, output_file=None):
    # Read data
    print("Reading edges...")
    all_edges = read_edges_from_file(edges_file)
    print(f"Loaded {len(all_edges)} edges")
    
    all_edges = all_edges[::200]  
    
    print("Reading important edges...")
    important_edges = read_edges_from_file(important_edges_file)

    print("Reading query nodes...")
    query_nodes = read_nodes_from_file(query_nodes_file)
    query_node = list(query_nodes)[0]
    print(f"Query node: {query_node}")
    
    # Get all nodes from sampled edges
    all_sampled_nodes = set()
    for edge in all_edges:
        all_sampled_nodes.add(edge[0])
        all_sampled_nodes.add(edge[1])
    all_sampled_nodes.add(query_node)
    
    all_sampled_edges = []
    for edge in all_edges:
        if edge[0] in all_sampled_nodes and edge[1] in all_sampled_nodes:
            all_sampled_edges.append(edge)
    
    important_nodes = set()
    for edge in important_edges:
        important_nodes.add(edge[0]) 
        important_nodes.add(edge[1]) 
   
    sampled_important_nodes = set()
    for node in important_nodes:
        if node in all_sampled_nodes:
            sampled_important_nodes.add(node)
    
    sampled_important_edges = []
    for edge in important_edges:
        if edge[0] in sampled_important_nodes and edge[1] in sampled_important_nodes:
            sampled_important_edges.append(edge)
    

    G_full = nx.DiGraph()
    G_full.add_edges_from(all_sampled_edges)
    
    print(f"Graph from sampled edges: {G_full.number_of_nodes()} nodes and {G_full.number_of_edges()} edges")
    
    all_nodes = list(G_full.nodes())
    
    node_colors = []
    for node in G_full.nodes():
        if node in query_nodes:
            print(f"Query node exists: {node}")
            node_colors.append('red')  
        elif node in sampled_important_nodes:
            node_colors.append('blue')  
        else:
            node_colors.append('lightblue')  
    
    plt.figure(figsize=(16, 12))

    print("Computing layout with Graphviz (sfdp)...")
    try:
        pos = graphviz_layout(G_full, prog='sfdp')  # Try 'sfdp', 'neato', or 'dot'
    except:
        print("Graphviz layout failed. Is pygraphviz installed and configured correctly?")
        sys.exit(1)

    
    regular_edges = [(u, v) for u, v in G_full.edges() if (u, v) not in sampled_important_edges]
    nx.draw_networkx_edges(G_full, pos, edgelist=regular_edges, alpha=0.8, width=0.5, edge_color='gray')
    
    important_edges_in_graph = [(u, v) for u, v in G_full.edges() if (u, v) in sampled_important_edges]
    nx.draw_networkx_edges(G_full, pos, edgelist=important_edges_in_graph, alpha=0.8, width=0.5, edge_color='red')
    
    nx.draw_networkx_nodes(G_full, pos, 
                          node_color=node_colors, 
                          node_size=30, 
                          node_shape='s',  # 's' for square shape
                          alpha=0.8)
    
    plt.title("Graph Visualization with Important Nodes Highlighted", 
              fontsize=16, fontweight='bold')
    
    legend_elements = [
        patches.Patch(color='red', label='Query Nodes'),
        patches.Patch(color='blue', label='Important Nodes and edges'),
        patches.Patch(color='lightblue', label='Regular Nodes'),
        patches.Patch(color='gray', label='Regular Edges')
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
    
    
    
    print(f"All edges: {len(all_edges)}")
    print(f"Sampled edges: {len(all_sampled_edges)}")
    print(f"Important edges: {len(sampled_important_edges)}")
    print(f"All nodes: {len(all_nodes)}")
    print(f"Sampled nodes: {len(all_sampled_nodes)}")
    print(f"Important nodes: {len(sampled_important_nodes)}")
    print(f"Query nodes: {len(query_nodes)}")

    # Check if all important nodes exist in the graph created from sampled edges
    missing_important = set(sampled_important_nodes) - set(all_sampled_nodes)
    if missing_important:
        print(f"Warning: The following important nodes are not in the sampled graph: {missing_important}")


if __name__ == "__main__":
    create_and_visualize_graph('./analysis-data/grounded_facts_university_streaming_one-bound.txt', './analysis-data/grounded_facts_university_magic_one-bound.txt', './analysis-data/query_nodes.txt', './analysis-data/graph_output_university_magic_one-bound.png')
    