import re
from itertools import permutations, product, chain, combinations
import math
import numpy as np




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


def get_binary_strings(n, as_strings=False):
    # Generate all possible bit strings of length n
    bit_combinations = product([0, 1], repeat=n)
    if as_strings:
        # Join bits as strings
        return ["".join(map(str, bits)) for bits in bit_combinations]
    else:
        # Return as lists of integers
        return [list(bits) for bits in bit_combinations]



def calculate_derangements(n):

    """

    Calculate the number of derangements (Dn) for n elements

    using the formula:

    Dn = n! * (1 - 1/1! + 1/2! - 1/3! + ... + (-1)^n/n!)

    """

    result = 0

    for i in range(n + 1):

        result += ((-1)**i) / math.factorial(i)

    return round(math.factorial(n) * result)




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