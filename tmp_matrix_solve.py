import os
import sys
import time

ROOT = "/home/mtm20cb/tools/freqhorn/tools/polar"
sys.path.insert(0, ROOT)
os.chdir(ROOT)

from inputparser import Parser
from program import normalize_program
from recurrences import RecBuilder
from recurrences.solver.cyclic_solver import CyclicSolver
from sympy import linear_eq_to_matrix, Matrix, simplify

program = Parser().parse_file("/home/mtm20cb/tools/freqhorn/out.prob")
program = normalize_program(program)
rec_builder = RecBuilder(program)
recurr = rec_builder.get_recurrences("_fh_5")
solver = CyclicSolver(recurr)

number_equations = len(solver.gen_sol_unknowns)
monom_index = solver.monom_to_index[solver.monomials.intersection({solver.monomials.__iter__().__next__()}).pop()]  # placeholder to keep style quiet
monom_index = solver.monom_to_index[next(m for m in solver.monomials if str(m) == "_fh_5")]
concrete_values = [solver.recurrences.init_values_vector]
equations = []
for n in range(1, number_equations + 1):
    concrete_values.append(solver.recurrences.recurrence_matrix * concrete_values[-1])
    eq = (solver.general_solution.xreplace({solver.n: n}) - concrete_values[n][monom_index]).expand()
    equations.append(eq)

print(f"unknowns={len(solver.gen_sol_unknowns)} equations={len(equations)}")
start = time.time()
A, b = linear_eq_to_matrix(equations, solver.gen_sol_unknowns)
print(f"matrix built in {time.time() - start:.3f}s shape={A.shape}")

start = time.time()
try:
    sol, params = A.gauss_jordan_solve(b)
    elapsed = time.time() - start
    print(f"gauss_jordan_solve finished in {elapsed:.3f}s")
    print(f"params={params}")
    print(f"sample={sol[:min(3, len(sol)), :].tolist()}")
except Exception as exc:
    elapsed = time.time() - start
    print(f"gauss_jordan_solve failed in {elapsed:.3f}s: {type(exc).__name__}: {exc}")

if A.rows == A.cols:
    start = time.time()
    try:
        sol = A.LUsolve(b)
        elapsed = time.time() - start
        print(f"LUsolve finished in {elapsed:.3f}s")
        print(f"sample={sol[:min(3, len(sol)), :].tolist()}")
    except Exception as exc:
        elapsed = time.time() - start
        print(f"LUsolve failed in {elapsed:.3f}s: {type(exc).__name__}: {exc}")
