# NRA Solver Fallback Investigation

## Background

The `--phaserr` mode uses `checkCHC2` (in `include/deep/RndLearnerV5.hpp`) to verify
invariant candidates at each CEGAR iteration.  Each call submits a QF_NRA query to Z3's
`nlsat` tactic pipeline via a `ZSolver<EZ3>` constructed with the `NoPush` flag and a
30-second timeout.

When solving `a6.smt2` (a 3-variable dense matrix system whose closed form involves the
complex eigenvalue `(9/10)·e^{iθ}`, cos θ = 4/5, sin θ = −3/5, plus a real eigenvalue
9/20), the tool produces 9 QF_NRA queries across 3 CEGAR iterations before hanging.

## Observed Behaviour

The queries were extracted from `debug_queries/` and tested against five solvers with a
15-second per-query wall-clock limit.  Results:

| Query | Role | Z3 | cvc5 | yices-smt2 | mathsat | smtrat-shared |
|-------|------|----|------|------------|---------|---------------|
| 0 | iter-0 init | unsat | unsat | unsat | unsat | unsat |
| 1 | iter-0 inductive | unsat | TO | TO | TO | unsat |
| 2 | iter-0 sat-check | sat | TO | sat | TO | sat |
| 3 | iter-1 init | unsat | TO | unknown | TO | unsat |
| 4 | iter-1 inductive | unsat | TO | TO | TO | unsat |
| **5** | **iter-1 sat-check** | **TO** | TO | **sat** | TO | **sat** |
| 6 | iter-2 init | unsat | TO | unknown | TO | unsat |
| 7 | iter-2 inductive | unsat | TO | TO | TO | unsat |
| **8** | **iter-2 sat-check** | **TO** | sat | **sat** | TO | **sat** |

`TO` = timed out at 15 s.  Queries 5 and 8 are the blocking ones: Z3 cannot decide them
within the timeout (or beyond — gdb confirmed Z3 was still inside `Z3_solver_check` after
45 s), while yices-smt2 and smtrat-shared answer `sat` almost immediately.

The `sat` result means the invariant candidate is not yet inductive.  The tool needs this
answer to proceed with refinement, but never gets it because Z3 hangs.

## Root Cause

The queries that are hard for Z3 but easy for yices/smtrat share a common structure: they
are **inductiveness counter-example checks** (the "third" check per iteration).  These
involve products of symbolic initial values (`_FH_0_INIT`, `_FH_1_INIT`, `_FH_2_INIT`)
with the trig auxiliary variables (`_ccos_0`, `_csin_0`) and the magnitude variable
`_mag_0`.  The unit-circle constraint `_ccos_0² + _csin_0² = 1` combined with bilinear
products of these variables appears to be what trips up Z3's variable-elimination order in
`nlsat`.

Conversely, the UNSAT queries (1, 3, 4, 6, 7) are easy for Z3 but hard or impossible for
cvc5, yices, and mathsat.  **smtrat-shared** is the only solver that handles both roles
correctly within the time limit across all 9 queries.

## Solver Coverage Summary

| Solver | unsat queries | sat queries | Notes |
|--------|--------------|-------------|-------|
| Z3 nlsat | ✓ all | ✗ hangs on 5, 8 | 30 s timeout not respected |
| cvc5 | ✗ most | partial | too slow for these |
| yices-smt2 | partial | ✓ fast | wrong on a few unsat |
| mathsat | ✗ most | ✗ most | not competitive here |
| smtrat-shared | ✓ all | ✓ all | best overall |

## Goal: Investigate Solver Fallback in `checkCHC2`

The immediate goal is to make the tool not hang on queries like 5 and 8.  Options to
evaluate, roughly in order of implementation effort:

### Option 1 — smtrat-shared as a second solver (parallel or sequential)

When `nlsolver->solve()` returns `unknown` (timeout), fall back to an external solver
subprocess.  A simple implementation:

1. Write the current assertion set to a temp `.smt2` file (the infrastructure for this
   already exists in `toSmtLib`).
2. Invoke `smtrat-shared <file>` as a subprocess and parse `sat`/`unsat`/`unknown` from
   stdout.
3. Return the fallback result to the caller.

Since smtrat-shared solved all 9 queries correctly, this would unblock `a6.smt2`
completely.

### Option 2 — yices-smt2 as a fallback for SAT queries

Similar subprocess approach but using `yices-smt2`.  Handles the `sat` queries fast, but
would still fail on the hard UNSAT queries (3, 4, 6, 7) within any reasonable timeout.
Not sufficient on its own.

### Option 3 — Portfolio: run Z3 and smtrat in parallel, take first answer

Spawn both solvers in separate threads or subprocesses, return whichever finishes first,
cancel the other.  This avoids the sequential overhead and would be optimal for both query
types.  More complex to implement.

### Option 4 — Pre-simplify the QF_NRA query before handing to Z3

The trig auxiliary variables `_ccos_0`, `_csin_0` have known rational values in the initial
state (`_ccos_0 = 1, _csin_0 = 0` at n = 0) and known recurrences.  If the tool can
substitute known rational values into the query before calling Z3, the nonlinear products
disappear and Z3 handles the resulting linear arithmetic trivially.  This would be a more
structural fix but requires understanding which variables are already constrained.

## Recommended Next Step

Implement **Option 1** (smtrat-shared subprocess fallback) as a targeted fix:
- Locate the `unknown` return path in `checkCHC2` (after `nlsolver->solve()`).
- When result is `unknown`, write assertions to a temp file and call `smtrat-shared`.
- Return the subprocess result.

This is low-risk (only activates on timeout), requires no changes to the Z3 solver setup,
and is confirmed to work on all 9 observed queries.

## Future Work: Integer-Typed Loop Index

Currently the loop counter `_i_0` is declared as `Real` in the QF_NRA queries.  A natural
improvement is to declare it as `Int` (promoting the logic to QF_NIRA or QF_NIA), which
would allow the solver to exploit the integral structure of the induction step and tighten
bounds without floating-point approximations.

**smtrat-shared does not support mixed integer/nonlinear arithmetic** (QF_NIRA / QF_NIA)
in the version tested.  Switching to an integer index would therefore break the smtrat
fallback described in Option 1 above.  Any fallback strategy adopted before or alongside
the integer-index change must either:
- retain a pure-Real encoding of `_i_0` for the external solver call while using `Int`
  internally, or
- find a different fallback solver that handles QF_NIRA (e.g., Z3 with a different tactic,
  or a combination of Z3 + yices).

This constraint should be weighed when choosing which option to implement first.

## Ideas for Reconfiguring Z3 to Handle These Queries Better

The hanging queries (5 and 8) are `sat` instances where Z3's `nlsat` cannot find a
satisfying assignment within the timeout.  Several Z3 knobs are worth exploring:

### 1 — Tactic pipeline overrides

Z3's `QF_NRA` logic is dispatched through `combined_solver`, which selects `nlsat` as
`solver1`.  The variable-elimination order used by `nlsat` appears to be the bottleneck.
Possible overrides:

```smt2
(set-option :tactic.nlsat.reorder true)   ; let nlsat pick its own var order
(set-option :tactic.nlsat.shuffle_vars true)
(set-option :sat.random_seed 42)          ; different seed may hit easier order
```

These can be set via `ZParams` in C++ before calling `solve()`:

```cpp
ZParams<EZ3> p(m_z3);
p.set("nlsat.reorder", true);
p.set("nlsat.shuffle_vars", true);
p.set("sat.random_seed", 42u);
nlsolver->set(p);
```

### 2 — Substitute known algebraic constants before calling Z3

In queries 5 and 8, `_mag_0` is already pinned to `9/10` by two constraints
(`<= 9/10 _mag_0` and `<= _mag_0 9/10`).  If `checkCHC2` substituted this equality
(and similar fully-determined values for `_ccos_0`, `_csin_0` at initial steps) into
the assertion set before calling `solve()`, the nonlinear products would reduce to linear
arithmetic and Z3 could answer instantly.  The substitution can be done at the `Expr`
level using `replaceAll` before `assertExpr`.

### 3 — Split the query into phases

The hard queries combine an initial-state guard (`0 ≤ _i_0 < 1 ⇒ …`) with a general
closed-form assertion (`_i_0 ≥ 0 ⇒ _FH_k = …`).  These interact poorly.  Separating
them into two sequential `check-sat` calls — one with `_i_0 = 0` asserted and one with
`_i_0 ≥ 1` asserted — would give Z3 smaller, structurally simpler subproblems that it
is more likely to handle quickly.

### 4 — Use `z3::solver::check` with assumptions instead of full assertions

Incrementally asserting the static parts once (root bounds, trig constraints) and adding
the variable-specific parts as assumptions avoids re-parsing and may let Z3 reuse lemmas
across CEGAR iterations.  This is compatible with the `NoPush`/`resetNoPush` approach
already in use if the static assertions are added before any `resetNoPush` call.

### 5 — Bounded integer unrolling

For queries where `_i_0` is bounded (e.g., query 5 checks step `_i_0 = 1`), replacing
the real-valued `_i_0` with a concrete integer and simplifying the closed-form expression
symbolically (in Python, before emitting the query) would eliminate the nonlinear
`_mag_0^n` terms entirely.  This is only applicable to the finite-step counterexample
checks, not to the general inductive-step queries.

## Relevant Files

- `include/deep/RndLearnerV5.hpp` — `checkCHC2` method (~line 2340); `nlsolver` optional member
- `include/ufo/Smt/Z3n.hpp` — `ZSolver`, `NoPush` constructor, `resetNoPush`
- `debug_queries/freqhorn_query_{0..8}.smt2` — the 9 QF_NRA queries from one run of `a6.smt2`
- `pwa-horn-benchmarks/possible_features/algebraic_numbers/a6.smt2` — the benchmark
