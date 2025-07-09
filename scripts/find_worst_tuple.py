from collections import Counter

def find_most_frequent_first_number(filename):
    """
    Find the number that appears most frequently as the first number in each line.
    
    Args:
        filename (str): Path to the file containing space-separated numbers per line
        
    Returns:
        tuple: (most_frequent_number, count)
    """
    first_numbers = []
    second_numbers = []
    third_numbers = []
    try:
        with open(filename, 'r') as file:
            for line in file:
                line = line.strip()
                if line:  # Skip empty lines
                    parts = line.split()
                    if parts:  # Make sure line has at least one number
                        first_numbers.append(int(parts[0]))
                        second_numbers.append(int(parts[1]))
                        third_numbers.append(int(parts[2]))
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        return None
    except Exception as e:
        print(f"Error reading file: {e}")
        return None
    
    if not first_numbers:
        print("No numbers found in the file.")
        return None
    
    # Count occurrences of each first number
    counter = Counter(first_numbers)
    second_counter = Counter(second_numbers)
    third_counter = Counter(third_numbers)
    
    # Find the most common first number
    most_common = counter.most_common(1)[0]
    most_common_second = second_counter.most_common(1)[0]
    most_common_third = third_counter.most_common(1)[0]

    print(f"Total lines processed: {len(first_numbers)}")
    print(f"Most frequent first number: {most_common[0]} (appears {most_common[1]} times)")
    print(f"Most frequent second number: {most_common_second[0]} (appears {most_common_second[1]} times)")
    print(f"Most frequent third number: {most_common_third[0]} (appears {most_common_third[1]} times)")

    # Show top 5 most frequent first numbers
    print("\nTop 5 most frequent first numbers:")
    for number, count in counter.most_common(5):
        print(f"  {number}: {count} times")
    print("\nTop 5 most frequent second numbers:")
    for number, count in second_counter.most_common(5):
        print(f"  {number}: {count} times")
    print("\nTop 5 most frequent third numbers:")
    for number, count in third_counter.most_common(5):
        print(f"  {number}: {count} times")

  

if __name__ == "__main__":
    filename = "../results/lubm1_materialized.txt"
    find_most_frequent_first_number(filename)
    
    