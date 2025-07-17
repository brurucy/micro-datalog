from collections import Counter

def find_most_frequent_rare_pair(filename, threshold_percent=1.0):
    pair_counter = Counter()
    total_lines = 0

    with open(filename, 'r') as f:
        for line in f:
            parts = line.strip().split()
            if len(parts) >= 2 and parts[0] != "degreeFrom":

                pair = (parts[0], parts[1])
          
                pair_counter[pair] += 1
                total_lines += 1

    if total_lines == 0:
        print("No valid lines found.")
        return

    threshold = max(1, int(total_lines * (threshold_percent / 100.0)))
    # Filter pairs that appear up to the threshold
    rare_pairs = [(pair, count) for pair, count in pair_counter.items() if count <= threshold]

    if not rare_pairs:
        print("No pairs found that appear up to 1% of the lines.")
        return

    # Find the most frequent among the rare pairs
    most_frequent_rare_pair = max(rare_pairs, key=lambda x: x[1])
    print(f"Total lines: {total_lines}")
    print(f"Threshold (1%): {threshold} occurrences or fewer")
    print(f"Most frequent pair among those appearing up to {threshold_percent}%: {most_frequent_rare_pair[0]} (appears {most_frequent_rare_pair[1]} times)")

if __name__ == "__main__":
    filename = "ascent_results_all.txt"  # Change to your file path
    find_most_frequent_rare_pair(filename, 1.0)