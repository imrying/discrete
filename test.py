from sympy import *

def check_injective_surjective(func, var, domain, codomain):
    x, y = symbols('x y')
    
    # Check if the function is well-defined
    outputs = {}
    for val in domain:
        output = func.subs(var, val)
        if output in outputs:
            # If the same output occurs for different inputs, it's not well-defined
            if outputs[output] != val:
                return "The function is not well-defined."
        else:
            outputs[output] = val
    
    # Check injectivity
    injective = True
    for val1 in domain:
        for val2 in domain:
            if val1 != val2:
                if func.subs(var, val1) == func.subs(var, val2):
                    injective = False
                    break
    
    # Check surjectivity
    surjective = True
    for c_val in codomain:
        try:
            solutions = solve(Eq(func, c_val), var)
            if not any(s in domain for s in solutions):
                surjective = False
                break
        except:
            surjective = False
            break
    
    # Results
    if injective and surjective:
        return "The function is bijective (both injective and surjective)."
    elif injective:
        return "The function is injective only."
    elif surjective:
        return "The function is surjective only."
    else:
        return "The function is neither injective nor surjective."

# Define the function and its domain/codomain
x = symbols('x')
func = Piecewise((2*x, x >= 0), (-2*x-1, x < 0))
domain = range(-20, 20)  # For example, integers from -20 to 20
codomain = range(0, 40)  # Adjusted codomain to include all possible outputs

result = check_injective_surjective(func, x, domain, codomain)
print(result)

print("please double check it yourself")
