import networkx as nx
import random
import numpy as np
from collections import Counter

# Load your graph - potentially using a streaming approach if memory is a concern
G = nx.read_edgelist('./data/random_edges_facebook_combined.txt', create_using=nx.DiGraph())

# Get basic statistics
num_nodes = G.number_of_nodes()
num_edges = G.number_of_edges()
print(f"Graph has {num_nodes} nodes and {num_edges} edges")

# Sample nodes for degree analysis
# sample_size = min(10000, num_nodes)
# sampled_nodes = random.sample(list(G.nodes()), sample_size)

sampled_nodes = list(G.nodes())

# Get degree distributions from sample
#in_degrees = {node: G.in_degree(node) for node in sampled_nodes}
out_degrees = {node: G.out_degree(node) for node in sampled_nodes}

# Find degree percentiles
#in_percentiles = np.percentile(list(in_degrees.values()), [10, 50, 90, 99])
out_percentiles = np.percentile(list(out_degrees.values()), [20, 40, 60, 80, 100])

#print(f"In-degree percentiles [10, 50, 90, 99]: {in_percentiles}")
print(f"Out-degree percentiles [20, 40, 60, 80, 100]: {out_percentiles}")

out_reachability = {node: (len(nx.descendants(G, node)) / num_nodes * 100) for node in sampled_nodes}
out_reachability_percentiles = np.percentile(list(out_reachability.values()), [20, 40, 60, 80, 100])
print(f"Out-reachability percentiles [20, 40, 60, 80, 100]: {out_reachability_percentiles}")