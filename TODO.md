# Hello

- [X] Check satisfiability of CHCs with a given invariant
- [X] Insert auxiliary variables into CHCs (BoundSolver.hpp)
    - [X] Invariant (x=2i /\ y=i /\ (x,y,i)>=0 ) holds for test.smt2
- [X] Convert CHCs into Polar file
- [X] Call Python script from inside C++ Function (Boost.Python) (Recurrence Class?)
- [ ] Convert SMT file into Expr (z3_from_smtlib())
- [ ] Insert roots & expressions from Polar correctly into invariants
- [ ] Insert conditional intervals of the roots (widening algorithm) until invariant found.
    - [ ] Simple increasing loop (no bounds for initial variables)
    - [ ] Inequality loop 
    - [ ] P Controller (no bounds for initial variables)
    - [ ] P Controller (bounds for initial variables)
    - [ ] PI Controller (no bounds)
    - [ ] PI Controller (bounds)
    - [ ] Simple Cyclic Loop
- [ ] Have a way to determine if CHCs cannot be solved by technique (includes integers, nonlinear, etc)


