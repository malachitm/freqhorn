import sympy
from sympy.abc import x

targets = [sympy.sqrt(17), sympy.root(2, 3), sympy.CRootOf(x**2 - 17, 1)]

for t in targets:
    print(f"--- Target: {t} ---")
    try:
        mp = sympy.minpoly(t, x)
        print(f"Minimal polynomial: {mp}")
        
        p = sympy.Poly(mp, x)
        print(f"Intervals: {p.intervals()}")
        print(f"Roots: {p.all_roots()}")
        
        if hasattr(t, 'index'):
            print(f"Index: {t.index}")
        
    except Exception as e:
        print(f"Error: {e}")
    print()

print("--- Root Ordering Test ---")
poly_x2_17 = x**2 - 17
for i in range(2):
    root = sympy.CRootOf(poly_x2_17, i)
    print(f"CRootOf(x**2 - 17, {i}) = {root.evalf()} (index {i})")
