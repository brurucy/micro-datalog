import json
import glob
from collections import defaultdict
import statistics

def analyze_execution_times(json_files):
    """
    Analyze execution times from multiple JSON files.
    
    Args:
        json_files (list): List of paths to JSON files containing execution time data
    
    Returns:
        dict: Dictionary containing statistics for each strategy and cumulative_edges
    """
    # Dictionary to store all execution times for each strategy and cumulative_edges
    execution_times = defaultdict(lambda: defaultdict(list))
    
    # Read and process each JSON file
    for file_path in json_files:
        with open(file_path, 'r') as f:
            data = json.load(f)
            
        # Process each entry in the JSON data
        for entry in data:
            strategy = entry['strategy']
            cumulative_edges = entry['cumulative_edges']
            execution_time = entry['execution_time_micros']
            
            # Store execution time in the appropriate list
            execution_times[strategy][cumulative_edges].append(execution_time)
    
    # Calculate statistics for each strategy and cumulative_edges
    results = {}
    for strategy in execution_times:
        results[strategy] = {}
        for cumulative_edges in execution_times[strategy]:
            times = execution_times[strategy][cumulative_edges]
            results[strategy][cumulative_edges] = {
                'average': statistics.mean(times),
                'min': min(times),
                'max': max(times),
                'samples': len(times)
            }
    
    return results

def main():
    # Get all JSON files from the results directory
    json_files = glob.glob('results/*.json')
    
    if not json_files:
        print("No JSON files found in the results directory")
        return
    
    # Analyze execution times
    results = analyze_execution_times(json_files)
    
    # Save results to a new JSON file
    output_file = 'results/execution_time_statistics.json'
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"Analysis complete. Results saved to {output_file}")
    
    # Print a summary
    for strategy in results:
        print(f"\nStrategy: {strategy}")
        for cumulative_edges in sorted(results[strategy].keys()):
            stats = results[strategy][cumulative_edges]
            print(f"  Cumulative edges: {cumulative_edges}")
            print(f"    Average: {stats['average']:.2f} µs")
            print(f"    Min: {stats['min']} µs")
            print(f"    Max: {stats['max']} µs")
            print(f"    Samples: {stats['samples']}")

if __name__ == "__main__":
    main() 