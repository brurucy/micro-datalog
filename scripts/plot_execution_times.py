import json
import matplotlib.pyplot as plt
import numpy as np

def plot_execution_times(stats_file):
    """
    Create a plot of execution times with error bars from the statistics JSON file.
    
    Args:
        stats_file (str): Path to the JSON file containing execution time statistics
    """
    # Read the statistics file
    with open(stats_file, 'r') as f:
        stats = json.load(f)
    
    # Create figure and axis
    plt.figure(figsize=(12, 6))
    
    # Plot each strategy
    for strategy in stats:
        # Extract data for this strategy
        edges = sorted([int(e) for e in stats[strategy].keys()])
        averages = [stats[strategy][str(e)]['average'] for e in edges]
        mins = [stats[strategy][str(e)]['min'] for e in edges]
        maxs = [stats[strategy][str(e)]['max'] for e in edges]
        
        # Calculate error bars
        yerr_lower = [avg - min_val for avg, min_val in zip(averages, mins)]
        yerr_upper = [max_val - avg for max_val, avg in zip(maxs, averages)]
        yerr = [yerr_lower, yerr_upper]
        
        # Plot with error bars
        plt.errorbar(
            edges,
            averages,
            yerr=yerr,
            label=strategy,
            capsize=5,
            capthick=1,
            elinewidth=1,
            marker='o',
            markersize=4
        )
    
    # Customize the plot
    plt.xlabel('Number of Edges')
    plt.ylabel('Execution Time (µs)')
    plt.title('Execution Time vs Number of Edges')
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend()
    
    # Use log scale for better visualization of the wide range of values
    plt.yscale('log')
    
    # Adjust layout and save
    plt.tight_layout()
    plt.savefig('results/execution_times_plot.png', dpi=300, bbox_inches='tight')
    plt.close()

def main():
    stats_file = 'results/execution_time_statistics.json'
    plot_execution_times(stats_file)
    print(f"Plot has been saved to results/execution_times_plot.png")

if __name__ == "__main__":
    main() 