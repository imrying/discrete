import re
from itertools import permutations, product, chain, combinations
import math
import numpy as np
from sympy import mod_inverse
import matplotlib.pyplot as plt




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
    return comb_list

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

