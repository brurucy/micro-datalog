import json

def normalize_tuple(tuple_list):
    # Converts [{"Str": "A"}, {"Str": "B"}] -> tuple of strings ("A", "B")
    return tuple(item.get("Int", "") for item in tuple_list)

def load_results(filename):
    with open(filename, "r") as f:
        data = json.load(f)
    results = {}
    for entry in data:
        strategy = entry["strategy"]
        # Normalize each tuple for set operations
        tuples = set(normalize_tuple(t) for t in entry["result_tuples"])
        results[strategy] = tuples
    return results

def compare_strategies(results):
    strategies = list(results.keys())
    for i in range(len(strategies)):
        for j in range(i+1, len(strategies)):
            s1, s2 = strategies[i], strategies[j]
            only_in_s1 = results[s1] - results[s2]
            only_in_s2 = results[s2] - results[s1]
            print(f"\n--- Comparing '{s1}' vs '{s2}' ---")
            print(f"Tuples only in '{s1}': {len(only_in_s1)}")
            for t in sorted(only_in_s1):
                print("  ", t)
            print(f"Tuples only in '{s2}': {len(only_in_s2)}")
            for t in sorted(only_in_s2):
                print("  ", t)

if __name__ == "__main__":
    filename = "./results/tc_linear_sparse/tc(_, _)_results_20250721_125059.json"  # Change to your actual file path
    results = load_results(filename)
    compare_strategies(results)
