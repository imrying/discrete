import re
from itertools import permutations, product, chain, combinations
import math
import numpy as np
from sympy import mod_inverse
import matplotlib.pyplot as plt
from collections import defaultdict




def is_prime(n):
    if n <= 1:
        return False

    for i in range(2, int(n**0.5) + 1):

        if n % i == 0:
            return False

    return True

def primes_below(n):
    primes = [i for i in range(2, n) if is_prime(i)]
    return f"Number of primes below {n} is {len(primes)} and the list is {primes}"

def divide_with_remainder(a, b):
    if b == 0:
        return "Division by zero is undefined."
    
    quotient = a // b
    remainder = a % b
    return f"The quotient of {a} divided by {b} is {quotient}, and the remainder is {remainder}."


# sent by jesper TA<3
def gcd(a, b):
    rlist = [a, b]
    qlist = []

    while True:
        r1 = rlist[-2]
        r2 = rlist[-1]
        if r2 == 0:
            break
        new_r = r1 % r2
        qlist.append(r1 // r2)
        rlist.append(new_r)

    slist = [1, 0]
    tlist = [0, 1]

    for q in qlist:
        s1 = slist[-2]
        s2 = slist[-1]
        t1 = tlist[-2]
        t2 = tlist[-1]
        
        slist.append(s1 - q * s2)
        tlist.append(t1 - q * t2)
    
    i = 0
    print('i \t r_i \t r_i+1 \t q_i+1 \t r_i+2 \t s_i \t t_i')
    for r1, r2, r3, q, s, t in zip(rlist, rlist[1:], rlist[2:], qlist, slist, tlist):
        print(f'{i} \t {r1} \t {r2} \t {q} \t {r3} \t {s} \t {t}')
        i += 1
    print(f'\t\t\t\t\t {slist[-2]} \t {tlist[-2]}')

    gcd_value = rlist[-2]
    s_coeff = slist[-2]
    t_coeff = tlist[-2]
    result_string = f"GCD({a}, {b}) = {gcd_value}, with coefficients {s_coeff} and {t_coeff} such that {gcd_value} = ({s_coeff})*{a} + ({t_coeff})*{b}"
    
    print(f'{result_string}')
    #return gcd_value, s_coeff, t_coeff, result_string

def lcm(a, b):
    def gcd(a, b):
        while b:
            a, b = b, a % b
        return a
    
    gcd_value = gcd(a, b)
    lcm_value = abs(a * b) // gcd_value
    
    result_string = (
        f"LCM({a}, {b}) = {lcm_value}, Here, GCD({a}, {b}) = {gcd_value}."
    )
    
    print(result_string)
    #return lcm_value, result_string



# Sent by Alexander Piepgrass <3
def _min_gcd_congruences(a,b):
    rlist = [a,b]
    qlist = []

    while True:
        r1 = rlist[-2]
        r2 = rlist[-1]
        if r2==0:
            break
        new_r = r1%r2
        qlist.append(r1//r2)
        rlist.append(new_r)

    slist = [1,0]
    tlist = [0,1]

    for q in qlist:
        s1 = slist[-2]
        s2 = slist[-1]
        t1 = tlist[-2]
        t2 = tlist[-1]
        
        slist.append(s1-q*s2)
        tlist.append(t1-q*t2)
    
    i = 0
    
    return rlist[-2], slist[-2], tlist[-2]

# sent by alexander piepgrass <3
def congruences_system_solver(system):
    m=1
    for cong in system:
        m*=cong[1]
    M_list = []
    for cong in system:
        M_list.append(m//cong[1])
    y_list=[]

    for i in range(len(M_list)):
        r,s,t= _min_gcd_congruences(M_list[i],system[i][1])
        y_list.append(s)
    
    x=0

    for i in range(len(M_list)):
        x+=system[i][0]*M_list[i]*y_list[i]
    print(f'all solutions are {x % m} + {m}k')
    return x % m, m, M_list, y_list


def some_congruences_system_solver(system):
    normalized_system = []
    for b, a, n in system:
        g = math.gcd(b, n)
        if a % g != 0:
            raise ValueError(f"No solution exists for {b}*x ≡ {a} (mod {n})")
        # Reduce b*x ≡ a (mod n) to x ≡ c (mod m)
        b = b // g
        a = a // g
        n = n // g
        b_inv = mod_inverse(b, n)
        c = (b_inv * a) % n
        normalized_system.append((c, n))
    
    # Solve the normalized system of congruences
    m = 1
    for _, n in normalized_system:
        m *= n
    M_list = []
    for _, n in normalized_system:
        M_list.append(m // n)
    y_list = []
    for i in range(len(M_list)):
        r, s, t = _min_gcd_congruences(M_list[i], normalized_system[i][1])
        y_list.append(s)
    
    x = 0
    for i in range(len(M_list)):
        x += normalized_system[i][0] * M_list[i] * y_list[i]
    
    print(f'All solutions are {x % m} + {m}k')
    return x % m, m, M_list, y_list

def solve_congruence_general(a, c, m):
    """
    Solves the congruence ax ≡ c (mod m).
    Returns a general solution in the form x ≡ x0 + k*b (mod m), 
    or 'No solution' if no solution exists.
    """
    from math import gcd

    # Step 1: Compute gcd(a, m)
    g = gcd(a, m)

    # Step 2: Check if a solution exists
    if c % g != 0:
        return "No solution"

    # Step 3: Simplify the congruence
    a, c, m = a // g, c // g, m // g

    # Step 4: Find the modular inverse of a modulo m
    def extended_gcd(a, b):
        """Helper function to compute the extended GCD."""
        if b == 0:
            return a, 1, 0
        g, x, y = extended_gcd(b, a % b)
        return g, y, x - (a // b) * y

    g, x, _ = extended_gcd(a, m)
    if g != 1:  # Sanity check for modular inverse
        return "No solution"

    x = (x % m + m) % m  # Ensure x is positive
    x0 = (c * x) % m  # Particular solution

    # General solution is x ≡ x0 + k * m
    return f"x ≡ {x0} + k * {m}"



def explain_quantifiers(logic_string):
    """
    Converts a LaTeX-style logical string into a human-readable explanation.
    Supports various quantifiers, logical types, and biimplication.
    """
    # Normalize LaTeX equivalents to symbols
    latex_to_symbol_map = {
        r"\\forall": "∀",
        r"\\exists": "∃",
        r"\\in": "∈",
        r"\\notin": "∉",
        r"\\mathbb\{R\}": "ℝ",
        r"\\neq": "≠",
        r"\\rightarrow": "→",
        r"\\leftrightarrow": "↔",
        r"\\lor": "∨",
        r"\\land": "∧",
        r"\\neg": "¬",
        r"\\leq": "≤",
        r"\\geq": "≥",
        r"\\subseteq": "⊆",
        r"\\supseteq": "⊇",
        r"\\subset": "⊂",
        r"\\supset": "⊃",
        r"\\emptyset": "∅",
    }

    for latex, symbol in latex_to_symbol_map.items():
        logic_string = re.sub(latex, symbol, logic_string)

    # Dictionary to map symbols to words
    symbol_map = {
        "∀": "For all",
        "∃": "There exists",
        "∈": "in",
        "∉": "not in",
        "ℝ": "the set of all real numbers",
        "→": "implies that",
        "↔": "if and only if",
        "∨": "or",
        "∧": "and",
        "¬": "not",
        "=": "is equal to",
        "≠": "is not equal to",
        "<": "is less than",
        ">": "is greater than",
        "≤": "is less than or equal to",
        "≥": "is greater than or equal to",
        "⊆": "is a subset of",
        "⊇": "is a superset of",
        "⊂": "is a proper subset of",
        "⊃": "is a proper superset of",
        "∅": "the empty set",
    }

    # Replace symbols with words
    for symbol, word in symbol_map.items():
        logic_string = logic_string.replace(symbol, word)

    # Custom processing for specific patterns
    # Match quantifiers and variables
    logic_string = re.sub(r"For all (\w) in (.*?),", r"Given any \1 in \2,", logic_string)
    logic_string = re.sub(r"There exists (\w) in (.*?),", r"There is a \1 in \2,", logic_string)

    # Handle logical groupings with parentheses
    logic_string = re.sub(r"\((.*?)\)", r"where \1", logic_string)

    # Ensure precise formatting
    logic_string = logic_string.strip()
    return logic_string


def get_permutations(input_string):
    """
    Returns all permutations of the given string.
    """
    # Generate permutations using itertools.permutations
    perm = permutations(input_string)
    # Convert to a list of strings
    perm_list = [''.join(p) for p in perm]
    return perm_list

def get_r_permutations(input_string, r):
    """
    Returns all r-permutations of the given string.
    
    Parameters:
        input_string (str): The string to generate permutations from.
        r (int): The length of the permutations.
    
    Returns:
        list: A list of all r-permutations as strings.
    """
    # Generate r-permutations using itertools.permutations
    r_perm = permutations(input_string, r)
    # Convert to a list of strings
    r_perm_list = [''.join(p) for p in r_perm]
    return r_perm_list



def get_binary_strings(n, as_strings=False):
    # Generate all possible bit strings of length n
    bit_combinations = product([0, 1], repeat=n)
    if as_strings:
        # Join bits as strings
        return ["".join(map(str, bits)) for bits in bit_combinations]
    else:
        # Return as lists of integers
        return [list(bits) for bits in bit_combinations]

def get_combinations(input_string):
    """
    Returns all combinations of the given string (for all lengths).
    
    Parameters:
        input_string (str): The string to generate combinations from.
    
    Returns:
        list: A list of all combinations as strings.
    """
    comb_list = []
    for r in range(1, len(input_string) + 1):
        comb_list.extend([''.join(c) for c in combinations(input_string, r)])
    return comb_list + ['']

def get_r_combinations(input_string, r):
    """
    Returns all r-combinations of the given string.
    
    Parameters:
        input_string (str): The string to generate combinations from.
        r (int): The length of the combinations.
    
    Returns:
        list: A list of all r-combinations as strings.
    """
    r_comb = combinations(input_string, r)
    r_comb_list = [''.join(c) for c in r_comb]
    return r_comb_list
    

def calculate_number_of_derangements(n):

    """

    Calculate the number of derangements (Dn) for n elements

    using the formula:

    Dn = n! * (1 - 1/1! + 1/2! - 1/3! + ... + (-1)^n/n!)

    """

    result = 0

    for i in range(n + 1):

        result += ((-1)**i) / math.factorial(i)

    return round(math.factorial(n) * result)

def is_derangement(original, perm):
    """
    Checks if a permutation is a derangement of the original string.
    """
    return all(original[i] != perm[i] for i in range(len(original)))

def get_derangements(input_string):
    """
    Returns all derangements of a given string as an array of strings.
    """
    original = list(input_string)
    all_permutations = permutations(original)
    derangements = ["".join(perm) for perm in all_permutations if is_derangement(original, perm)]
    return derangements


def multiplicative_inverse(n, mod):
    def gcd_extended(a, b):
        if a == 0:
            return b, 0, 1
        gcd, x1, y1 = gcd_extended(b % a, a)
        x = y1 - (b // a) * x1
        y = x1
        return gcd, x, y

    gcd, x, _ = gcd_extended(n, mod)

    if gcd != 1:  # If gcd of n and mod is not 1, inverse doesn't exist
        return "Does not exist"
    else:
        # Make the result positive
        return x % mod
    

def minimum_selections_for_sum(numbers, target_sum):
    selected_numbers = set()

    for num in numbers:
        if target_sum - num in selected_numbers:
            # Pair found
            return len(selected_numbers) + 1

        selected_numbers.add(num)

    # No pair found within the set
    return None


def is_transitive(R):
    for a, b in R:
        for c, d in R:
            if b == c and ((a, d) not in R):
                return False
    return True


def is_reflexive(S, R):
    newSet = {(a, b) for a in S for b in S if a == b}
    if R >= newSet:
        return True

    return False


def is_symmetric(R):
    if all(tup[::-1] in R for tup in R):
        return True

    return False


def is_antisymmetric(R):
    return all((y, x) not in R for x, y in R if x != y)


def is_equivalence_relation(S, R):
    return is_symmetric(R) and is_reflexive(S, R) and is_transitive(R)


def is_partial_order(S, R):
    """Check if the relation R on set S is a partial order."""
    return is_antisymmetric(R) and is_reflexive(S, R) and is_transitive(R)


def check_func(func_to_check, domain, codomain):
    """
    Check if a function is "well-defined" over a given domain and codomain constraint.
    
    Parameters:
        func_to_check: callable
            The function to check. It should take one argument.
        domain: list
            A list of values to test the function with.
        codomain: callable
            A callable that takes the output of the function and returns True if it satisfies the codomain constraint.
    
    Returns:
        bool
            True if the function is well-defined over the domain and codomain, otherwise False.
    """
    well_defined = True

    for x in domain:
        try:
            # Evaluate the function
            output = func_to_check(x)
            
            # Check the codomain constraint
            if not codomain(output):
                print(f"Input {x}: Output {output} is INVALID.")
                well_defined = False
        except Exception as e:
            # Catch errors in evaluation
            print(f"Input {x}: Error occurred - {str(e)}.")
            well_defined = False

    if well_defined:
        print("The function is well-defined over the given domain.")
    else:
        print("The function is NOT well-defined over the given domain.")
    
    return well_defined



def plot_function(functions: list, plot_range: list):
    """Takes a function and plots the graph using the plot_range.
    The plot_rage should be a list containing two elements: the minimum value to plot, up to the max value.
    function should be a list of functions to be drawn. The functions in the list should take one parameter and return a value. 
    """
    x_values = range(plot_range[0],plot_range[1])
    for func in functions:
        y_points = []
        x_points = []
        for i in range(plot_range[0], plot_range[1]):
            y_points.append(func(i))
            x_points.append(i)
        plt.plot(x_points, y_points, label=func.__name__)
    plt.xlabel('x')
    plt.ylabel('y')
    plt.title('Function Plots')
    plt.legend()
    plt.grid(True)
    plt.show()

def count_subsets1(A, size=None, max_element=None, even_elements=False):
    if size is not None:
        # Count subsets of exact size
        return math.comb(len(A), size)
    elif max_element is not None:
        # Count subsets that do not contain any element greater than max_element
        filtered_A = [elem for elem in A if elem <= max_element]
        return 2 ** len(filtered_A)
    elif even_elements:
        # Count subsets with an even number of elements
        total_subsets = 2 ** len(A)
        even_subsets = sum(math.comb(len(A), k) for k in range(0, len(A) + 1, 2))
        return even_subsets
    else:
        return 0
    


def count_subsets(
    A,
    size=None,
    max_element=None,
    even_elements=False,
    odd_elements=False,
    sum_equals=None,
    sum_range=None,
    must_contain=None,
    exclude=None,
    predicate=None
):
    # Filter based on max_element and exclude
    if max_element is not None:
        A = [x for x in A if x <= max_element]
    if exclude is not None:
        exclude_set = set(exclude)
        A = [x for x in A if x not in exclude_set]

    # If must_contain is specified:
    must_contain_elem = None
    if must_contain is not None:
        if must_contain not in A:
            # If we must contain an element not in the set, no subsets possible
            return 0
        # Remove must_contain from A and we will add it back after computations
        must_contain_elem = must_contain
        A = [x for x in A if x != must_contain]

    n = len(A)

    # If a general predicate is given, we must test every subset.
    # This can be very slow for large sets, but let's just be honest:
    if predicate is not None:
        # Brute force as a fallback for arbitrary predicate
        # (User must be aware this could be slow if n is large)
        count = 0
        for r in range(n+1):
            for subset in combinations(A, r):
                # Add must_contain element if needed
                if must_contain_elem is not None and must_contain_elem not in subset:
                    subset = subset + (must_contain_elem,)
                if not check_conditions(subset, size, even_elements, odd_elements, sum_equals, sum_range, must_contain_elem, predicate):
                    continue
                count += 1
        return count

    # If no sum conditions and no complicated predicate, we can try closed-form:
    if sum_equals is None and sum_range is None and must_contain_elem is None:
        # Conditions are now just size/even/odd
        # Count how many subsets from A:
        total_subsets = 2**n

        if size is not None:
            # number of subsets of given size:
            return math.comb(n, size)

        if even_elements and not odd_elements:
            # Count even-sized subsets
            even_count = sum(math.comb(n, k) for k in range(0, n+1, 2))
            return even_count
        if odd_elements and not even_elements:
            # Count odd-sized subsets
            odd_count = sum(math.comb(n, k) for k in range(1, n+1, 2))
            return odd_count
        if even_elements and odd_elements:
            # No subset can be both even and odd sized
            return 0

        # If no conditions at all:
        return total_subsets

    # Handle must_contain:
    # If must_contain_elem is not None, we will incorporate it by adjusting conditions:
    # Adding must_contain_elem to a subset changes:
    #  - The subset size: effectively size_needed = size - 1 (if size is given)
    #  - The sum conditions: sum_needed = sum_equals - must_contain_elem (if sum_equals given)
    #    or sum_range = (low - must_contain_elem, high - must_contain_elem) for sum_range.
    # We must ensure that every counted subset does not contain must_contain_elem,
    # but we add it at the end. Actually, we DO want them to contain it. So we must count subsets
    # from A that meet adjusted conditions as if must_contain_elem was included automatically.
    adj_size = size - 1 if (size is not None) else None
    if sum_equals is not None and must_contain_elem is not None:
        adj_sum_equals = sum_equals - must_contain_elem
    else:
        adj_sum_equals = sum_equals

    if sum_range is not None and must_contain_elem is not None:
        low, high = sum_range
        sum_range = (low - must_contain_elem, high - must_contain_elem)

    # If even_elements or odd_elements are given, adjusting for the must_contain_elem:
    # Including must_contain_elem always adds 1 to the size, so even becomes odd and odd becomes even.
    # If must_contain_elem is forced in:
    # - If we wanted even subsets including must_contain_elem, now we must look for odd subsets in A.
    # - If we wanted odd subsets including must_contain_elem, now we must look for even subsets in A.
    adj_even_elements = even_elements
    adj_odd_elements = odd_elements
    if must_contain_elem is not None:
        if even_elements and not odd_elements:
            adj_even_elements = False
            adj_odd_elements = True
        elif odd_elements and not even_elements:
            adj_even_elements = True
            adj_odd_elements = False
        # If both even and odd requested, still 0.

    # After these adjustments, we count subsets in A that have:
    # - size == adj_size (if size given)
    # - even/odd parity adjusted
    # - sum equals adj_sum_equals (if given) or sum in adjusted sum_range
    # 
    # We will use a meet-in-the-middle approach for sum conditions if n is large:

    if n == 0:
        # If there's nothing in A and must_contain_elem was specified, 
        # the only subset is {must_contain_elem}.
        # Check if that meets the conditions:
        single_subset = [must_contain_elem] if must_contain_elem is not None else []
        return 1 if check_conditions(single_subset, size, even_elements, odd_elements, sum_equals, sum_range, must_contain_elem, None) else 0

    # Meet-in-the-middle:
    mid = n // 2
    A1 = A[:mid]
    A2 = A[mid:]

    # Generate subsets of A1
    A1_data = []  # Will store tuples (sum, size)
    for r in range(len(A1)+1):
        for c in combinations(A1, r):
            A1_data.append((sum(c), len(c)))

    # Generate subsets of A2
    A2_data = []
    for r in range(len(A2)+1):
        for c in combinations(A2, r):
            A2_data.append((sum(c), len(c)))

    # We need to efficiently count how many subsets from A2 complement A1's subsets to meet conditions.
    # Conditions:
    # - sum condition: If sum_equals is given, sum(A1)+sum(A2) = adj_sum_equals
    #                  If sum_range is given, sum_range[0] <= sum(A1)+sum(A2) <= sum_range[1]
    # - size condition: If adj_size is given, size(A1)+size(A2) = adj_size
    # - parity: If adj_even_elements, total size mod 2 == 0; if adj_odd_elements, total size mod 2 == 1

    # Let's store A2 subsets in a dictionary keyed by (sum, size) to quickly lookup counts
    from collections import Counter
    A2_count = Counter(A2_data)

    count = 0
    for (s1, sz1) in A1_data:
        # Determine required conditions for the complementary subset (s2, sz2)
        
        # Size condition:
        # If adj_size is given: sz2 must be adj_size - sz1
        # If not given but parity is given:
        #    if adj_even_elements: (sz1 + sz2) % 2 == 0 => sz2 % 2 == sz1 % 2
        #    if adj_odd_elements: (sz1 + sz2) % 2 == 1 => sz2 % 2 != sz1 % 2

        possible_sizes = []
        if adj_size is not None:
            needed_size = adj_size - sz1
            if needed_size < 0 or needed_size > len(A2):
                continue
            # Only that size is possible
            possible_sizes.append(needed_size)
        else:
            # no exact size condition, but we might have parity:
            if adj_even_elements and not adj_odd_elements:
                # total size even => sz2 % 2 == (even - sz1%2)
                # For total even: (sz1 + sz2)%2=0 => sz2%2=sz1%2
                possible_sizes = [sz2 for sz2 in range(len(A2)+1) if sz2 % 2 == sz1 % 2]
            elif adj_odd_elements and not adj_even_elements:
                # total size odd: (sz1 + sz2)%2=1 => sz2%2 != sz1%2
                possible_sizes = [sz2 for sz2 in range(len(A2)+1) if sz2 % 2 != sz1 % 2]
            else:
                # no parity condition
                possible_sizes = range(len(A2)+1)

        # Sum condition:
        # If adj_sum_equals is given: s1 + s2 = adj_sum_equals => s2 = adj_sum_equals - s1
        # If sum_range is given: low <= s1+s2 <= high => low - s1 <= s2 <= high - s1

        if adj_sum_equals is not None:
            needed_s2 = adj_sum_equals - s1
            # Only one sum needed
            sums_to_check = [needed_s2]
        elif sum_range is not None:
            low, high = sum_range
            # s2 must be in [low - s1, high - s1]
            low_s2 = low - s1
            high_s2 = high - s1
            # We'll just iterate over possible sizes and sum over all subsets in that sum range.
            # This might still be slow if sum range is large. We can optimize by precomputing sums per size.
            # Let's precompute a dictionary of sums by size for A2 to avoid large loops.

            # Precompute if not done
            # We have A2_count indexed by (sum, size).
            # We'll sum over sums in range. If range is large, this could be slow.
            # As an optimization, let's store A2 subsets by size in a sorted list by sum.

            # Precomputation (done once, cached):
            # Create a dictionary: size -> sorted list of sums
            # We'll do binary search over this list for [low_s2, high_s2]
            pass
        else:
            # No sum condition, sums_to_check = all sums
            # We can just sum over all sums in A2_count with given sizes
            sums_to_check = None

        # To handle large ranges efficiently, let's do a precomputation outside the loop:
        # We'll build a dictionary: by_size = { sz2: sorted list of (sum, count) } for A2
        # We do this once:
        # (Move this precomputation outside the loop for efficiency)
        # Since this is a code snippet, we implement it directly here:

    # Let's move precomputation outside the loop to avoid repeated work:
    # Construct by_size dict:
    by_size = {}
    for (s2, sz2), cnt in A2_count.items():
        if sz2 not in by_size:
            by_size[sz2] = []
        by_size[sz2].append((s2, cnt))
    for sz2 in by_size:
        by_size[sz2].sort(key=lambda x: x[0])  # sort by sum

    # Now re-run the counting loop with this optimization
    count = 0
    for (s1, sz1) in A1_data:
        if adj_size is not None:
            needed_size = adj_size - sz1
            if needed_size < 0 or needed_size > len(A2):
                continue
            size_candidates = [needed_size]
        else:
            if adj_even_elements and not adj_odd_elements:
                size_candidates = [sz2 for sz2 in by_size.keys() if sz2 % 2 == sz1 % 2]
            elif adj_odd_elements and not adj_even_elements:
                size_candidates = [sz2 for sz2 in by_size.keys() if sz2 % 2 != sz1 % 2]
            else:
                size_candidates = by_size.keys()

        # Check sum conditions
        if adj_sum_equals is not None:
            needed_s2 = adj_sum_equals - s1
            # For each candidate size:
            for sz2 in size_candidates:
                # binary search in by_size[sz2] for s2 == needed_s2
                arr = by_size[sz2]
                # binary search:
                lo, hi = 0, len(arr)-1
                while lo <= hi:
                    mid = (lo+hi)//2
                    if arr[mid][0] == needed_s2:
                        count += arr[mid][1]
                        break
                    elif arr[mid][0] < needed_s2:
                        lo = mid+1
                    else:
                        hi = mid-1
        elif sum_range is not None:
            low, high = sum_range
            low_s2 = low - s1
            high_s2 = high - s1
            # For each candidate size, we find all sums in range [low_s2, high_s2]
            for sz2 in size_candidates:
                arr = by_size[sz2]
                # find left boundary:
                left_idx = binary_search_left(arr, low_s2)
                # find right boundary:
                right_idx = binary_search_right(arr, high_s2)
                if left_idx <= right_idx and 0 <= left_idx < len(arr):
                    # sum all counts in that range
                    for i in range(left_idx, min(right_idx+1, len(arr))):
                        count += arr[i][1]
        else:
            # No sum condition, just sum all subsets of given sizes
            for sz2 in size_candidates:
                # sum all counts in by_size[sz2]
                arr = by_size[sz2]
                for (_, cval) in arr:
                    count += cval

    # After counting subsets from adjusted conditions, if must_contain_elem was included, we have the correct count.
    return count

def check_conditions(subset, size, even_elements, odd_elements, sum_equals, sum_range, must_contain, predicate):
    # This function checks conditions on a fully formed subset that should already include must_contain if needed.
    # It's used in fallback cases.
    if must_contain is not None and must_contain not in subset:
        return False
    length = len(subset)
    if size is not None and length != size:
        return False
    if even_elements and (length % 2 != 0):
        return False
    if odd_elements and (length % 2 == 0):
        return False
    s = sum(subset)
    if sum_equals is not None and s != sum_equals:
        return False
    if sum_range is not None:
        low, high = sum_range
        if not (low <= s <= high):
            return False
    if predicate is not None and not predicate(subset):
        return False
    return True

def binary_search_left(arr, val):
    # arr is sorted by first element (sum)
    # find leftmost position to insert val
    lo, hi = 0, len(arr)
    while lo < hi:
        mid = (lo+hi)//2
        if arr[mid][0] < val:
            lo = mid+1
        else:
            hi = mid
    return lo

def binary_search_right(arr, val):
    # find rightmost position where arr[i][0] <= val
    lo, hi = 0, len(arr)
    while lo < hi:
        mid = (lo+hi)//2
        if arr[mid][0] <= val:
            lo = mid+1
        else:
            hi = mid
    return lo-1