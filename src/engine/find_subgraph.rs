use petgraph::graph::{Graph, NodeIndex};
use petgraph::Directed;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::time::Instant;

/// Reads an edge list from a file and creates a directed graph
fn read_graph_from_file<P: AsRef<Path>>(filepath: P) -> io::Result<Graph<String, (), Directed>> {
    let file = File::open(filepath)?;
    let reader = io::BufReader::new(file);

    let mut graph = Graph::<String, (), Directed>::new();
    let mut node_indices = HashMap::new();

    for line in reader.lines() {
        let line = line?;
        let edge: Vec<&str> = line.trim().split_whitespace().collect();

        if edge.len() >= 2 {
            let from = edge[0].to_string();
            let to = edge[1].to_string();

            // Add nodes if they don't exist
            let from_idx = *node_indices
                .entry(from.clone())
                .or_insert_with(|| graph.add_node(from));

            let to_idx = *node_indices
                .entry(to.clone())
                .or_insert_with(|| graph.add_node(to));

            // Add directed edge
            graph.add_edge(from_idx, to_idx, ());
        }
    }

    Ok(graph)
}

/// Properly count the number of edges in a directed subgraph
fn count_edges_in_subgraph(nodes: &HashSet<NodeIndex>, graph: &Graph<String, (), Directed>) -> usize {
    let mut edge_count = 0;
    
    // Count only edges where both source and target are in the subgraph
    for &node in nodes {
        for neighbor in graph.neighbors(node) {
            if nodes.contains(&neighbor) {
                edge_count += 1;
            }
        }
    }
    
    edge_count
}

/// Calculate density of a directed graph or subgraph correctly
fn calculate_density(nodes: &HashSet<NodeIndex>, graph: &Graph<String, (), Directed>) -> f64 {
    let n = nodes.len();
    
    if n <= 1 {
        return 0.0;
    }
    
    // Count edges where both endpoints are in the subgraph
    let edge_count = count_edges_in_subgraph(nodes, graph);
    
    // For directed graphs, max possible edges = n*(n-1)
    let possible_edges = n * (n - 1);
    
    // Return the density
    if possible_edges == 0 {
        0.0
    } else {
        edge_count as f64 / possible_edges as f64
    }
}

/// Find densest subgraph using optimized greedy algorithm
fn find_densest_subgraph_optimized(graph: &Graph<String, (), Directed>) -> (HashSet<NodeIndex>, f64) {
    println!("Starting optimized densest subgraph search...");
    let start_time = Instant::now();
    
    let all_nodes: HashSet<NodeIndex> = graph.node_indices().collect();
    let mut remaining_nodes = all_nodes.clone();
    
    // Calculate initial density
    let initial_density = calculate_density(&remaining_nodes, graph);
    let mut best_density = initial_density;
    let mut best_subgraph = remaining_nodes.clone();
    
    println!("Initial density: {}", initial_density);
    println!("Initial node count: {}", remaining_nodes.len());
    
    let mut removal_count = 0;
    let total_nodes = remaining_nodes.len();
    
    // Keep removing nodes until empty
    while remaining_nodes.len() > 1 {  // Stop when only 1 node left (density would be 0)
        // Find node with minimum degree within the subgraph
        let min_degree_node = remaining_nodes.iter()
            .min_by_key(|&&node| {
                graph.neighbors(node)
                    .filter(|neighbor| remaining_nodes.contains(neighbor))
                    .count()
            })
            .cloned();
        
        if min_degree_node.is_none() {
            break;
        }
        
        // Remove the node
        let node_to_remove = min_degree_node.unwrap();
        remaining_nodes.remove(&node_to_remove);
        
        // Calculate new density
        let density = calculate_density(&remaining_nodes, graph);
        
        // Update best if current is better
        if density > best_density {
            best_density = density;
            best_subgraph = remaining_nodes.clone();
        }
        
        removal_count += 1;
        if removal_count % 1000 == 0 || removal_count == total_nodes - 1 {
            println!("Removed {}/{} nodes. Current best density: {}", 
                removal_count, total_nodes, best_density);
            println!("Remaining nodes: {}", remaining_nodes.len());
            println!("Time elapsed: {:?}", start_time.elapsed());
        }
    }
    
    println!("Densest subgraph search completed in {:?}", start_time.elapsed());
    (best_subgraph, best_density)
}

/// Find a sample of densest k-subgraphs for different values of k
fn find_dense_subgraphs_by_size(graph: &Graph<String, (), Directed>, max_samples: usize) -> Vec<(usize, f64)> {
    println!("Finding dense subgraphs for different sizes...");
    let start_time = Instant::now();
    
    let mut results = Vec::new();
    let node_count = graph.node_count();
    
    // Try different sample sizes (logarithmically spaced)
    let mut sample_sizes = Vec::new();
    let mut size = 10;
    while size < node_count {
        sample_sizes.push(size);
        size = (size as f64 * 1.5) as usize;
    }
    sample_sizes.push(node_count);
    
    // Limit to max_samples
    if sample_sizes.len() > max_samples {
        let step = sample_sizes.len() / max_samples;
        sample_sizes = sample_sizes.into_iter()
            .enumerate()
            .filter(|(i, _)| i % step == 0)
            .map(|(_, size)| size)
            .collect();
    }
    
    println!("Sampling {} different subgraph sizes", sample_sizes.len());
    
    for &size in &sample_sizes {
        // Take a sample of nodes
        let mut all_nodes: Vec<NodeIndex> = graph.node_indices().collect();
        all_nodes.sort(); // For reproducibility
        
        if all_nodes.len() > size {
            all_nodes.truncate(size);
        }
        
        let sample: HashSet<NodeIndex> = all_nodes.into_iter().collect();
        
        // Calculate density properly
        let density = calculate_density(&sample, graph);
        
        results.push((sample.len(), density));
        println!("Subgraph of size {} has density {:.6}", sample.len(), density);
    }
    
    println!("Completed dense subgraph sampling in {:?}", start_time.elapsed());
    results
}

pub fn main_yo() -> io::Result<()> {
    // Read the graph from a file
    println!("Reading graph from file...");
    let start_time = Instant::now();
    let graph = read_graph_from_file("data/pegasus_edges.txt")?;
    println!("Graph loaded in {:?}", start_time.elapsed());

    // Calculate basic graph metrics
    let node_count = graph.node_count();
    let edge_count = graph.edge_count();
    
    // Calculate overall graph density correctly
    let all_nodes: HashSet<NodeIndex> = graph.node_indices().collect();
    let graph_density = calculate_density(&all_nodes, &graph);

    println!("Graph statistics:");
    println!("Number of nodes: {}", node_count);
    println!("Number of edges: {}", edge_count);
    println!("Graph density: {:.8}", graph_density);

    // For very large graphs, sample different sized subgraphs
    if node_count > 10000 {
        println!("\nGraph is large ({}K nodes). Using sampling approach.", node_count / 1000);
        let dense_samples = find_dense_subgraphs_by_size(&graph, 10);
        
        // Sort by density
        let mut sorted_samples = dense_samples.clone();
        sorted_samples.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        
        println!("\nDensest sampled subgraphs (by density):");
        for (size, density) in sorted_samples.iter().take(5) {
            println!("Size: {}, Density: {:.6}", size, density);
        }
        
        // Find the densest subgraph for a reasonable subset
        println!("\nFinding exact densest subgraph for a 5000-node subset...");
        let sample_size = 5000.min(node_count);
        let mut sample_nodes: Vec<NodeIndex> = graph.node_indices().collect();
        sample_nodes.truncate(sample_size);
        
        let sample_graph = graph.filter_map(
            |idx, weight| {
                if sample_nodes.contains(&idx) {
                    Some(weight.clone())
                } else {
                    None
                }
            },
            |_, edge| Some(edge.clone())
        );
        
        println!("Sample graph has {} nodes and {} edges", 
                 sample_graph.node_count(), sample_graph.edge_count());
        
        let (densest_subgraph, density) = find_densest_subgraph_optimized(&sample_graph);
        println!("Densest subgraph in sample: {} nodes with density {:.6}", 
                 densest_subgraph.len(), density);
        
        // If the densest subgraph is quite small, report its structure
        if densest_subgraph.len() <= 20 {
            println!("\nStructure of densest subgraph:");
            println!("Nodes: {:?}", densest_subgraph);
            
            println!("Edges:");
            let mut edge_count = 0;
            for &node in &densest_subgraph {
                for neighbor in sample_graph.neighbors(node) {
                    if densest_subgraph.contains(&neighbor) {
                        edge_count += 1;
                        println!("  {} -> {}", 
                            sample_graph[node], sample_graph[neighbor]);
                    }
                }
            }
            println!("Edge count: {}", edge_count);
            println!("Theoretical max edges: {}", 
                densest_subgraph.len() * (densest_subgraph.len() - 1));
        }
    } else {
        // For smaller graphs, use the optimized algorithm on the full graph
        let (densest_subgraph, density) = find_densest_subgraph_optimized(&graph);
        println!("Size of densest subgraph: {}", densest_subgraph.len());
        println!("Density of densest subgraph: {:.6}", density);
    }

    Ok(())
}