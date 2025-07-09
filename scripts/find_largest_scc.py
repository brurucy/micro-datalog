import networkx as nx

# Load your graph
G = nx.read_edgelist('./data/pegasus_edges.txt', create_using=nx.DiGraph())

# Find strongly connected components
# sccs = list(nx.strongly_connected_components(G))

# # Print the size of each component
# for i, component in enumerate(sccs):
#     print(f"Component {i+1}: {len(component)} nodes")

# # Find the largest component
# largest_scc = max(sccs, key=len)
# print(f"Largest component has {len(largest_scc)} nodes")

# First compute the full transitive closure size for each node
reachability = {}
for node in G.nodes():
    reachable = nx.descendants(G, node)
    reachability[node] = len(reachable)

# Find nodes with high out-degree but limited reachability
candidates = []
for node in G.nodes():
    out_degree = G.out_degree(node)
    reach_ratio = reachability[node] / G.number_of_nodes()
    # Look for high out-degree but low reach ratio
    if out_degree > 10 and reach_ratio < 0.1:
        candidates.append((node, out_degree, reach_ratio))

# Sort by most promising (high degree, low reach)
magic_candidates = sorted(candidates, key=lambda x: x[1]/(x[2]+0.01), reverse=True)[:5]
print(magic_candidates)