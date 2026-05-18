# Algebraic Number Isolating Interval — Implementation Plan

## Goal
Replace the hacky `sqrt{N}` string-matching system with a robust algebraic number
representation using Isolating Interval Representation: a number defined by its
minimal polynomial `P(x)` and a rational bounding box `[a, b]`.

---

## What Is Already In Place (Do Not Reimplement)

- **`include/ufo/Expr.hpp`** line ~880: `struct AlgebraicNum` with `poly` (vector of
  `mpz_class` coefficients), `rootIdx` (0-based), `lower`/`upper` (`mpq_class`), plus
  `midpoint()`, `to_double()`, `isRational()`, `degree()`.
- **`include/ufo/Smt/ZExprConverter.hpp`** line ~115: Full Z3 marshaling of `ALNUM`
  nodes via `Z3_algebraic_roots`. Already works. No changes needed.
- **`tools/polar/utils/expressions.py`** line 202: `resolve_real_croot(root, eps=1e-10)`
  — extracts minimal polynomial + refined isolating interval from a SymPy `ComplexRootOf`.
  Returns `("real", (poly_expr, low, high))`.
- **`tools/polar/utils/algebraic_numbers.py`**: has `minpoly` usage patterns already.
- **`checkCHC2` in `RndLearnerV5.hpp`**: already uses NoPush `ZSolver` in nlsat tactic
  mode. No solver infrastructure changes needed.
- **`std::optional<ZSolver<EZ3>> nlsolver`**: already declared as class member.

---

## JSON Schema Change

Current output from `closedforms2.py`:
```json
{ "x": [ { "bases": ["sqrt17", "1.0"], "coeffs": ["...","..."] } ] }
```

New output adds a top-level `"aux_roots"` array:
```json
{
  "aux_roots": [
    {
      "name": "_alg_0",
      "poly_coeffs": ["-17", "0", "1"],
      "low": "4",
      "high": "5"
    }
  ],
  "x": [ { "bases": ["_alg_0", "1.0"], "coeffs": ["...","..."] } ]
}
```
- `poly_coeffs[k]` = coefficient of `x^k` as a string (integer, GMP-parseable).
- `low`, `high` = rational strings in `p/q` or integer form.
- `name` = identifier used in place of `sqrt{N}` tokens in `bases` and `coeffs`.
- `root_idx` is NOT emitted — the interval selects the root unambiguously.

---

## Phase 1 — Python Changes

### `tools/polar/closedforms2.py`

1. **Remove** the `exponent == Rational(1, 2)` branch in `sympy_to_pysmt2()` that
   creates `"sqrt{N}"` PySMT Symbol names.

2. **Add** a `RootRegistry` class (or just a `dict[sympy.Expr, str]`) at module scope
   mapping each unique algebraic root to an assigned name `_alg_0`, `_alg_1`, etc.

3. **Add** `extract_algebraic_roots(expr, registry: dict) -> None` — recursive SymPy
   tree walker that finds `ComplexRootOf` and irrational `Pow(base, Rational(1,n))`
   sub-expressions, calls `resolve_real_croot()`, and registers them.

4. **Two-pass main loop**: Pass 1 — call `extract_algebraic_roots` on the closed form
   to populate the registry. Pass 2 — substitute each registered root with its
   `_alg_k` SymPy `Symbol` before calling `sympy_to_pysmt2()`.

5. **Updated JSON output**: after building `var_dict`, build `aux_roots` list from
   the registry using `poly_to_int_coeffs()` and `resolve_real_croot()` output.
   Emit as `{"aux_roots": [...], ...var_dict}`.

### `tools/polar/utils/expressions.py`

- Add helper `poly_to_int_coeffs(poly_expr) -> list[str]` — converts a SymPy `Poly`
  to ascending-degree integer coefficient string list for JSON serialization.

### `tools/polar/utils/__init__.py`

- Add `resolve_real_croot` to the exports list (currently missing).

---

## Phase 2 — C++ JSON Parsing + IR (`RndLearnerV5.hpp`)

### New struct (add near top of class or just above class):
```cpp
struct AlgRootEntry {
    std::string name;      // "_alg_0"
    AlgebraicNum alnum;    // poly, lower, upper, rootIdx (set to 0, interval selects)
    Expr var;              // unprimed real const
    Expr varPrime;         // primed real const
};
```

### New class member:
```cpp
map<int, std::vector<AlgRootEntry>> algRootRegistry;
```

### Remove dead members:
- `map<int, set<std::string>> squareRootExists` — replaced by `algRootRegistry`
- `map<int, ExprVector> squareRoots` — replaced by `algRootRegistry`

### New method `parseAuxRoots(int i, nlohmann::json &auxRoots)`:
```
For each entry in auxRoots array:
  1. Parse "poly_coeffs" into vector<mpz_class>.
  2. Parse "low" and "high" into mpq_class using mpq_class::set_str(..., 10).
     Handle "/" separator for rational strings (split on '/').
  3. Construct AlgebraicNum: alnum.poly = coeffs, alnum.lower = low,
     alnum.upper = high, alnum.rootIdx = 0.
  4. Create var  = bind::realConst(mkTerm<string>(entry["name"], m_efac))
     Create varPrime = bind::realConst(mkTerm<string>(name+"'", m_efac))
  5. Push AlgRootEntry into algRootRegistry[i].
```
Correct order in `learnInvariants5()`:
- Call `parseAuxRoots` right after parsing `closedformJson`, before
  `generateSymbolicClosedForms`. This populates `algRootRegistry` so that
  `insertRoots` (called internally by `generateSymbolicClosedForms`) can use it.

---

## Phase 3 — C++ CHC Injection (`RndLearnerV5.hpp`)

### `createRootConstraint(Expr var, const AlgebraicNum &alnum)` — REWRITE

Current version is hard-coded degree-2 only (`value = x*x`).

New version for arbitrary degree:
```
Build Expr polynomial P(var) from alnum.poly coefficients:
  sum_k ( alnum.poly[k] * var^k )
  (use MULT for product, PLUS for sum, mkTerm<mpq_class> for coefficients)
Emit:
  AND( GEQ(var, alnum.lower), LEQ(var, alnum.upper), EQ(polynomial, zeroReal) )
```
Degree-guard: if `alnum.degree() >= 5`, omit the `EQ(polynomial, zeroReal)` conjunct
and log a warning. Emit only the interval bounds (sound over-approximation).

### `insertRoots(int i, json &closedformJson, EZ3 &z3)` — REWRITE

Current version: scans base strings for `"sqrt"` prefix, calls `extractRootValue`,
creates `squareRootExists` entries.

New version:
```
For each AlgRootEntry in algRootRegistry[i]:
  - Follow same positional-append discipline as current sqrt block (lines ~2420-2497).
  - Append var to invarVarsShort[i].
  - Update ruleManager.invVars[rel] and invVarsPrime[rel].
  - For fact CHC: push varPrime to dstVars, add createRootConstraint() to body.
  - For inductive CHC: push var/varPrime to srcVars/dstVars,
    add var' = var (constant across iterations) to body.
  - For query CHC: push var to srcVars.
```
IMPORTANT: algRootRegistry entries must be appended AFTER all `_r_N` roots from
`addRoot()` calls, for the same positional reason documented in existing comments.
The registry is built in `parseAuxRoots` which runs before `generateSymbolicClosedForms`,
but the CHC injection (appending to srcVars/dstVars) must happen in a second pass
after all `addRoot()` calls complete.

### `generateRootBounds(int i)` — REWRITE

Current version: iterates `squareRootExists[i]`, calls old `createRootConstraint`.

New version: iterates `algRootRegistry[i]`, calls new `createRootConstraint`.

### `str_to_expr(string exprString, ...)` — FIX

Current version: declares `"sqrt{N}"` as `Real` constants in the inline SMT2 string.

New version: declare `"_alg_k"` variables from `algRootRegistry[i]` instead.
Also update the `sqrts` parameter name/semantics or add a new `algNames` parameter.

### `evaluateBaseString(string baseStr)` — SIMPLIFY

Current version: replaces `"sqrt{N}"` tokens with `std::sqrt(N)` numerically.

New version: look up `baseStr` in `algRootRegistry[i]` by name field. If found,
return `alnum.midpoint().get_d()`. If not found (it's a plain numeric string),
parse directly. Remove the "sqrt" token scan loop.

### Delete dead helpers:
- `getAllSqrtWords(const string &input)` — free function, lines ~95-128
- `extractRootValue(const string &input)` — method, lines ~2248-2289

---

## Phase 4 — Wiring in `learnInvariants5()`

After `closedformJson = nlohmann::json::parse(output_test)`, insert:
```cpp
if (closedformJson.contains("aux_roots") && closedformJson["aux_roots"].is_array()) {
    ds.parseAuxRoots(i, closedformJson["aux_roots"]);
}
```
This must come BEFORE `ds.generateSymbolicClosedForms(i, closedformJson)`.

The `generateSymbolicClosedForms` call triggers `insertRoots` internally — check
whether `insertRoots` is called from there or separately. In the current code,
`insertRoots` is called FROM `generateSymbolicClosedForms` (it calls `insertRoots`
then uses `rootMaps`). So `parseAuxRoots` must populate `algRootRegistry` before
that call, and the CHC-injection part of the new `insertRoots` must use the registry.

---

## NRA Safety Strategy

1. **Interval-first ordering**: in fact CHC body, emit `a <= x <= b` BEFORE `P(x) = 0`.
   nlsat's `propagate_values` boxes the search space linearly before nonlinear eval.
2. **Degree guard**: skip polynomial equality for degree >= 5 (use interval only).
3. **Existing timeout**: `_to` parameter already caps each `checkCHC2` call. No change.
4. **No new solver context**: use existing nlsolver member.

---

## Key Invariant to Preserve (Positional Ordering)

Variables appended to `invarVarsShort[i]`, `ruleManager.invVars[rel]`, and each
CHC's `srcVars`/`dstVars` MUST be in the same order. The pattern is:
  1. Original CHC variables (from parse)
  2. `_i_0` index variable (from `addIndex`)
  3. `_r_0`, `_r_1`, ... root variables (from `addRoot` calls in `insertRoots`)
  4. `_alg_0`, `_alg_1`, ... algebraic constant variables (new, from registry)

Breaking this order causes silent `replaceAll` substitution errors — a runtime bug
with no compile-time signal. Test after each CHC-modification step with a real `.smt2`.

---

## Files Changed Summary

| File | Change Type | Effort |
|---|---|---|
| `tools/polar/closedforms2.py` | Major rewrite of sympy_to_pysmt2 + main loop | Large |
| `tools/polar/utils/expressions.py` | Add `poly_to_int_coeffs` | Small |
| `tools/polar/utils/__init__.py` | Export `resolve_real_croot` | Trivial |
| `include/deep/RndLearnerV5.hpp` | Rewrite 6 methods, delete 2, add 2, new struct+member | Large |
| `include/ufo/Expr.hpp` | No changes | — |
| `include/ufo/Smt/ZExprConverter.hpp` | No changes | — |

---

## Test Benchmarks to Verify Against

- `bench_horn/array_init_const.smt2` — simple, no roots
- Any benchmark that currently triggers sqrt handling (check `squareRootExists` usage)
- Run full `bench_horn/` suite after Phase 3 and compare pass/fail counts to baseline
