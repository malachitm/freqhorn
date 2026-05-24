import sys
import os
import json
import sympy
from sympy import symbols, linear_eq_to_matrix, sympify
import time

# Add tools/polar to sys.path
sys.path.append(os.path.join(os.getcwd(), "tools/polar"))

from inputparser import Parser
from program import normalize_program
from recurrences import RecBuilder
from recurrences.solver.cyclic_solver import CyclicSolver

def main():
    prob_file = "out.prob"
    target_monomial = "_fh_5"

    if not os.path.exists(prob_file):
        print(f"Error: {prob_file} not found.")
        return

    print(f"Loading {prob_file}...")
    with open(prob_file, "r") as f:
        prob_content = f.read()

    parser = Parser()
    program = parser.parse_program(prob_content)
    program = normalize_program(program)
    
    print("Building recurrence system...")
    rec_builder = RecBuilder(program)
    recurrences = rec_builder.get_recurrences(sympify(target_monomial))
    
    print("Initializing CyclicSolver...")
    solver = CyclicSolver(recurrences)
    
    monomial = sympify(target_monomial)
    number_equations = len(solver.gen_sol_unknowns)
    monom_index = solver.monom_to_index[monomial]
    
    print(f"Number of unknowns: {number_equations}")
    
    concrete_values = [solver.recurrences.init_values_vector]
    equations = []
    
    print("Constructing equations...")
    for n_val in range(1, number_equations + 1):
        concrete_values.append(
            solver.recurrences.recurrence_matrix * concrete_values[-1]
        )
        eq = (
            solver.general_solution.xreplace({solver.n: n_val})
            - concrete_values[n_val][monom_index]
        ).expand()
        equations.append(eq)
    
    print(f"Constructed {len(equations)} equations.")
    
    print("Converting to matrix form...")
    try:
        start_time = time.time()
        A, b = linear_eq_to_matrix(equations, solver.gen_sol_unknowns)
        end_time = time.time()
        print(f"Matrix conversion took {end_time - start_time:.2f} seconds.")
        print(f"Matrix dimensions: {A.rows}x{A.cols}")
        
        print("Solving using gauss_jordan_solve...")
        start_time = time.time()
        sol, pivots = A.gauss_jordan_solve(b)
        end_time = time.time()
        print(f"gauss_jordan_solve took {end_time - start_time:.2f} seconds.")
        
        print("Solving using LUsolve...")
        start_time = time.time()
        sol_lu = A.LUsolve(b)
        end_time = time.time()
        print(f"LUsolve took {end_time - start_time:.2f} seconds.")
        
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == '__main__':
    main()
