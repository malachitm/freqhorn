# Algebraic Number Isolating Interval — Implementation Plan

## Goal
Replace the hacky `sqrt{N}` string-matching system with a robust algebraic number
representation using Isolating Interval Representation: a number defined by its
minimal polynomial `P(x)` and a rational bounding box `[a, b]`.

## Status Snapshot (May 27, 2026)

### Completed

- **Feature 1.1**: algebraic base classification and registration landed in `closedforms2.py` (`RootRegistry`, algebraic extraction walk).
- **Feature 1.2**: `aux_roots` JSON emission landed in the POLAR output path.
- **Feature 1.3**: `AlgRootEntry` plus `parseAuxRoots()` landed in `RndLearnerV5.hpp`.
- **Feature 1.4**: `createRootConstraint()` now handles arbitrary polynomial degree with the degree-5 guard.
- **Feature 1.5**: the `algRootRegistry` insertion path is wired while preserving CHC positional ordering.
- **Feature 1.7**: `parseAuxRoots()` is wired before `generateSymbolicClosedForms()`.
- **Feature 1.9**: the algebraic simplifier generalisation (`simplifyAlgExpr`, `toAlgVec`, `mulModP`, `fromAlgVec`) landed and is used in learner-side bound simplification.
- **Feature 1.10**: Python-side complex-root magnitude metadata helpers landed (`mag_poly_from_complex_root`, periodicity helpers, complex metadata extraction).
- **Feature 1.11 (core path)**: end-to-end `complex_pairs` support is wired across Python emission and C++ consumption (`parseComplexPairs`, CHC variable threading for `_mag_k/_ccos_k/_csin_k`, trig recurrences, unit-circle invariant).
- **Benchmark smokes for algebraic_numbers targets**:
  - `a3.smt2` direct smoke test exists.
  - `a4.smt2`, `a5.smt2`, and `a7.smt2` direct smoke tests were added and pass.

### Partial / In Progress

- **Feature 1.6**: `generateRootBounds`, `evaluateBaseString`, and `_alg_k` declaration support in `str_to_expr` are updated, but the legacy sqrt-only helpers and fallback path are still present for compatibility.
- **Feature 1.8**: targeted regressions and smoke tests were run (including `a3/a4/a5/a7` and complex/phase serializer tests), but a full `bench_horn` sweep remains pending.
- **Feature 5 periodic-strengthening path**: `is_periodic` / `period` metadata is parsed and stored, but explicit modulo-index implication lemmas are not injected yet; current implementation relies on the generic trig recurrence path.
- **Solver robustness for oscillatory NRA**: infrastructure is in place, but difficult nonlinear query shapes can still require fallback tactics (tracked separately in `docs/nra-solver-fallback.md`).

### Not Yet Started In This Plan

- No **Feature 3** subtasks are counted as completed yet.
- No **Feature 4** subtasks are counted as completed yet.
- Full retirement of legacy sqrt token plumbing is still pending a compatibility cutover.

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

## Phase 4b — Generalise `simplifySqrtExpr` to Arbitrary Algebraic Degree

### The Gap

`simplifySqrtExpr` and its five helper functions (`isSqrtConst`, `getSqrtVal`,
`toSqrtPair`, `fromSqrtPair`, `findSqrtConst`) in `include/ae/ExprSimpl.hpp` are
**not mentioned anywhere else in this plan**, yet they will silently break once
`"sqrt{N}"` constant names are replaced by `"_alg_k"` names. They must be rewritten.

### Mathematical Foundation

The current code works in `Q(√N) = Q[x]/(x² − N)`: every expression reduces to
`rat + irr·√N`, a 2-element coefficient vector. `simplifySqrtExpr` handles MULT via
the identity `(√N)² = N`, which is just polynomial reduction modulo `P(x) = x² − N`.

The **exact same algorithm** works for any degree-`d` algebraic number `α` with
monic minimal polynomial `P(x) = x^d + a_{d-1}x^{d-1} + … + a_0`:

- Every element of `Q[α] = Q[x]/(P(x))` is represented as a **length-`d` coefficient
  vector** `[c_0, c_1, …, c_{d-1}]` meaning `c_0 + c_1·α + … + c_{d-1}·α^{d-1}`.
- **Addition**: element-wise sum.
- **Multiplication**: polynomial multiply the two vectors (yielding degree ≤ `2d−2`),
  then take the remainder modulo `P` via polynomial long division. This is exact and
  in `O(d²)` `mpq_class` operations.
- **Reduction of `α^n`**: repeatedly multiply the length-`d` vector for `α^1` by
  itself and reduce. Any product of powers of a single `_alg_k` reduces exactly.

The degree-2 case (`√N`) is the current code with `d=2`, `a_0 = −N`, `a_1 = 0`:
reduction gives `c_0·1 + c_1·α` with `α^2 ↦ N`. No algorithmic change is needed,
only generalisation from a hardcoded pair to a variable-length vector.

### What Can and Cannot Be Simplified

| Expression pattern | Simplifiable? | How |
|---|---|---|
| `_alg_k^n` for any `n` | Yes | Reduce `x^n mod P_k(x)` via poly reduction |
| Products/sums of powers of **one** `_alg_k` | Yes | Q[x]/(P_k) arithmetic |
| `_alg_k * _alg_j` for `k ≠ j` | No | No known joint minimal polynomial |
| `_mag_k^2` (degree-2 poly: `x²−r²`) | Yes | Reduces to rational constant `r²` |
| `_ccos_k^2 + _csin_k^2` | Special case only | Not derivable from individual polys; requires a named identity rule (see Phase 5) |

### Implementation

The key design decision is **where the minimal polynomial comes from**. Because
`simplifySqrtExpr` is a static method in `ExprSimpl.hpp` with no access to
`algRootRegistry` (which lives in `RndLearnerV5.hpp`), the cleanest approach is to
add a **parameterised variant** rather than modifying the generic `simplifyArithm`
path:

**New free function in `ExprSimpl.hpp`**:
```cpp
/// Generalised algebraic simplification in Q[x]/(P).
/// \p algConst  — the Expr representing _alg_k (a realConst).
/// \p poly      — minimal polynomial P coefficients ascending, i.e. poly[k] = coeff of x^k.
/// Returns a simplified Expr, or \p e unchanged if no reduction applies.
static Expr simplifyAlgExpr(Expr e, Expr algConst,
                             const std::vector<mpq_class> &poly);
```

Internally mirrors `simplifySqrtExpr` but generalises `toSqrtPair` /
`fromSqrtPair` to `toAlgVec` / `fromAlgVec` operating on `std::vector<mpq_class>`
of length `d = poly.size() − 1`.

**`toAlgVec(Expr e, Expr algConst, vector<mpq_class> &poly, vector<mpq_class> &coeffs)`**:
Decomposes `e` into its coefficient vector in `Q[α]` for the given `algConst`.
Returns `false` if `e` contains a different algebraic constant (cannot decompose).
Handling of MULT, PLUS, MINUS, UN_MINUS, and powers-of-`algConst` is analogous to
`toSqrtPair`. Powers `algConst^n` are computed by repeated `mulModP` calls.

**`mulModP(vector<mpq_class> a, vector<mpq_class> b, const vector<mpq_class> &P)`**:
Polynomial multiply `a * b` then reduce modulo `P` via long division. Length `d`.

**`fromAlgVec(const vector<mpq_class> &coeffs, Expr algConst, ExprFactory &efac)`**:
Reconstruct `c_0 + c_1·algConst + c_2·algConst² + …` as an Expr PLUS/MULT tree.
Higher powers `algConst^k` (for `k ≥ 2`) are emitted as `MULT(MULT(…))` chains
since the Expr IR has no `POW` for reals.

**Call sites**: call `simplifyAlgExpr` from `generateRootBounds` and any place in
`learnInvariants5` that builds expressions involving `_alg_k` symbols. Do NOT
inject it into the generic `SimplifyArithmExpr::operator()` path — that would
require passing the registry through many unrelated code paths.

**Keep `simplifySqrtExpr` as-is** for the transition period (it handles any
remaining `"sqrt{N}"` constants that appear in non-`_alg_k` contexts). Delete it
only after the `"sqrt{N}"` names are fully eliminated.

**`isSqrtConst` / `getSqrtVal` / `findSqrtConst`**: add parallel `isAlgConst` /
`getAlgName` / `findAlgConst` helpers that match the `"_alg_[0-9]+"` name pattern.

### Degree Guard

For `d ≥ 5`, the `mulModP` cost is still `O(d²)` mpq operations (cheap). But emitting
`algConst^4` in the reconstructed Expr as a MULT chain `algConst*algConst*algConst*algConst`
is verbose. Optionally introduce a named intermediate Expr for repeated powers. This
is an optimisation, not a correctness concern.

---

## Phase 5 — Complex Conjugate Root Pair Handling

### Background and Gap

The existing phases only handle **real** algebraic roots. POLAR's closed forms can
contain complex numbers when the characteristic polynomial of the recurrence has
complex conjugate root pairs. A pair `α = r·e^(iθ)`, `ᾱ = r·e^(-iθ)` (with
`r > 0`, `θ ∈ (0, π)`) contributes a term to the closed form of the shape:

```
c₁·αⁿ + c₂·ᾱⁿ  =  rⁿ · (A·cos(nθ) + B·sin(nθ))
```

where `A` and `B` are real coefficients derived from `c₁` and `c₂`. Since Z3 and
dReal have no native complex number type, this trigonometric reformulation is the
only viable path. `resolve_real_croot` rejects imaginary `ComplexRootOf` nodes, so
the existing plan produces wrong output whenever a complex root pair is present.

### Mathematical Representation

For a complex conjugate pair with root `α = r·e^(iθ)`:

- **Magnitude** `r = |α|`: a positive real algebraic number. Its minimal polynomial
  is obtained from the constant term of the quadratic factor `(x - α)(x - ᾱ) =
  x² - 2·Re(α)·x + |α|²`, giving `|α|² = ` constant term, so `|α|` is a root of
  `x² - |α|²`. Use `resolve_real_croot` on this derived polynomial.
- **Angle** `θ = arg(α)`: not generally algebraic, but `cos(θ) = Re(α)/|α|` and
  `sin(θ) = Im(α)/|α|` are real algebraic numbers (ratios of algebraic numbers).

The trig recurrence relations are the standard addition formulas:
```
cos((n+1)θ) = cos(nθ)·cos(θ) − sin(nθ)·sin(θ)
sin((n+1)θ) = sin(nθ)·cos(θ) + cos(nθ)·sin(θ)
```
with initial conditions `cos(0) = 1`, `sin(0) = 0`.

### Angle Periodicity Classification

Whether `θ` is a rational multiple of `π` determines the encoding strategy:

1. **Rationally periodic** (`θ = (p/q)·π`, integers `p`, `q` coprime): The trig
   terms cycle with period `q`. For each residue class `k ∈ {0,…,q−1}`, assert:
   `(_i_0 mod q = k) ⟹ (ccosVar = cos(kθ) ∧ csinVar = sin(kθ))`.
   By Niven's theorem, the only rational values of `cos(pπ/q)` are 0, ±½, ±1
   (i.e., q ∈ {1,2,3,4,6}), so these are numerically exact as rationals.
   For larger periods, use floating-point constants.

2. **Non-rationally periodic**: Use the trig addition transition equations above
   with `cos(θ)` and `sin(θ)` encoded as numerical constants (doubles), plus the
   unit-circle invariant `ccosVar² + csinVar² = 1` as a CHC body conjunct.

**Detection heuristic**: Compute `θ` to 50 decimal places via SymPy `.evalf(50)`.
For q = 1 through 12, check if `|θ·q/π − round(θ·q/π)| < 1e-40`. If so, mark
periodic with that q. This covers all common engineering cases.

### JSON Schema Extension

Add a `"complex_pairs"` array to the existing JSON output, alongside `"aux_roots"`:

```json
{
  "aux_roots": [...],
  "complex_pairs": [
    {
      "mag_name":   "_mag_0",
      "ccos_name":  "_ccos_0",
      "csin_name":  "_csin_0",
      "mag_poly":   ["-2", "0", "1"],
      "mag_low":    "1",
      "mag_high":   "2",
      "cos_theta":  "1/2",
      "sin_theta":  "0.8660254037844387",
      "is_periodic": true,
      "period":     6
    }
  ],
  "x": [...]
}
```

- `mag_poly` / `mag_low` / `mag_high`: isolating interval for `r = |α|`, same format
  as `aux_roots` entries.
- `cos_theta`, `sin_theta`: rational string (`"p/q"`) when periodic and exact;
  decimal string otherwise.
- `is_periodic` / `period`: periodicity flag and period `q` (null if not periodic).
- All six name fields (`mag_name`, `ccos_name`, `csin_name`) are used as placeholder
  tokens in the `bases` / `coeffs` arrays of the closed form JSON, analogous to
  `_alg_k` names.

### Python Changes (extends Phase 1)

**In `tools/polar/closedforms2.py`**:

1. **Add `detect_complex_pairs(cf_expr) -> list[dict]`**: Walk the SymPy expression
   tree. For each `ComplexRootOf` node with nonzero imaginary part, locate its
   conjugate (same minimal polynomial, conjugate root index). Group into pairs.
   For each pair:
   - Compute `r_squared = sympy.Abs(alpha)**2` (= product of the quadratic factor's
     constant term) and call `resolve_real_croot` on the polynomial `x² - r_squared`
     to get the magnitude's isolating interval.
   - Compute `cos_theta = sympy.re(alpha) / sympy.Abs(alpha)` and
     `sin_theta = sympy.im(alpha) / sympy.Abs(alpha)`.
   - Run the periodicity check (q = 1..12 rational test at 50 digits precision).
   - Assign names `_mag_k`, `_ccos_k`, `_csin_k` from a running counter.
   - Return a list of dicts matching the JSON schema above.

2. **Add `complex_pair_to_trig(c1, alpha, c2, alpha_bar, n_sym)`**: Symbolically
   expand `c1*alpha**n + c2*alpha_bar**n` into `r**n * (A*cos(n*theta) +
   B*sin(n*theta))` using SymPy `re`/`im`. Return `(A, B)` as SymPy rationals
   (these are the coefficients that multiply the trig variables in the closed form).

3. **Extend two-pass loop**:
   - Pass 1: after `extract_algebraic_roots`, call `detect_complex_pairs` on the
     closed form. Store results in a `complex_registry` list local to the loop body.
   - Pass 2: before calling `sympy_to_pysmt2`, substitute each complex pair's
     contribution `c1*alpha**n + c2*alpha_bar**n` with a symbolic expression
     `A * _mag_k_sym**n * _ccos_k_sym + B * _mag_k_sym**n * _csin_k_sym`
     (where `_mag_k_sym`, `_ccos_k_sym`, `_csin_k_sym` are SymPy `Symbol`s).
     The `_mag_k_sym**n` term is treated as a new "base" like `_r_k` roots.

4. **Emit `"complex_pairs"` in JSON**: After building `aux_roots`, build the
   `complex_pairs` list from `complex_registry` and include it in the output dict.

**In `tools/polar/utils/expressions.py`**:

- Add `mag_poly_from_complex_root(alpha_sympy) -> tuple[list[str], str, str]`:
  Given a SymPy `ComplexRootOf` α, compute `r_sq = Abs(alpha)**2` (symbolic),
  then call `resolve_real_croot` on the polynomial `x**2 - r_sq` to get
  `(poly_coeffs, low, high)` for the magnitude.

### C++ Changes (extends Phases 2–3)

**New struct** (add immediately after `AlgRootEntry`):

```cpp
struct ComplexPairEntry {
    std::string magName;     // "_mag_0" — magnitude r = |α|
    std::string ccosName;    // "_ccos_0" — tracks cos(nθ)
    std::string csinName;    // "_csin_0" — tracks sin(nθ)
    AlgebraicNum magAlnum;   // isolating interval for |α| (reuses AlgebraicNum)
    double cosTheta;         // cos(θ), numerical
    double sinTheta;         // sin(θ), numerical
    bool isPeriodic;
    int period;              // q if isPeriodic, else 0
    Expr magVar,  magVarPrime;
    Expr ccosVar, ccosVarPrime;
    Expr csinVar, csinVarPrime;
};
```

**New class member** (add alongside `algRootRegistry`):

```cpp
map<int, std::vector<ComplexPairEntry>> complexPairRegistry;
```

**New method `parseComplexPairs(int i, nlohmann::json &complexPairs)`**:

```
For each entry in complexPairs array:
  1. Parse mag_poly/mag_low/mag_high into AlgebraicNum (identical logic to parseAuxRoots).
  2. Parse cos_theta, sin_theta as doubles (handle "p/q" strings by splitting on '/').
  3. Parse is_periodic bool and period int.
  4. Create magVar  = bind::realConst(mkTerm<string>(entry["mag_name"],  m_efac))
     Create magVarPrime  = bind::realConst(mkTerm<string>(mag_name+"'",  m_efac))
     Create ccosVar = bind::realConst(mkTerm<string>(entry["ccos_name"], m_efac))
     Create ccosVarPrime = bind::realConst(mkTerm<string>(ccos_name+"'", m_efac))
     Create csinVar = bind::realConst(mkTerm<string>(entry["csin_name"], m_efac))
     Create csinVarPrime = bind::realConst(mkTerm<string>(csin_name+"'", m_efac))
  5. Push ComplexPairEntry into complexPairRegistry[i].
```

**Extension to `insertRoots`** (runs after all `_alg_k` entries are appended):

For each `ComplexPairEntry` in `complexPairRegistry[i]`, append in the order
`magVar`, `ccosVar`, `csinVar` (grouped by pair). For each CHC type:

- **Fact CHC** (`dstVars` only): push `magVarPrime`, `ccosVarPrime`, `csinVarPrime`.
  Add to body:
  - `createRootConstraint(magVarPrime, entry.magAlnum)` — magnitude algebraic constraint
  - `EQ(ccosVarPrime, mkTerm<mpq_class>(1, m_efac))` — cos(0) = 1
  - `EQ(csinVarPrime, mkTerm<mpq_class>(0, m_efac))` — sin(0) = 0

- **Inductive CHC** (push `var`/`varPrime` pairs). Add to body:
  - `EQ(magVarPrime, MULT(magConst, magVar))` where `magConst =
    mkTerm<mpq_class>(mpq_class(entry.magAlnum.midpoint()), m_efac)` (numerical).
    Note: for a precise encoding, instead use `EQ(magVarPrime, MULT(magVar, magAlnumVar))`
    where `magAlnumVar` is pinned by its own `createRootConstraint` — but the numerical
    approximation is acceptable for the bounds use-case.
  - **Non-periodic case**: add the trig addition equations:
    - `EQ(ccosVarPrime, MINUS(MULT(ccosVar, cosC), MULT(csinVar, sinC)))`
    - `EQ(csinVarPrime, PLUS(MULT(csinVar, cosC), MULT(ccosVar, sinC)))`
    where `cosC = mkTerm<mpq_class>(...)` and `sinC` are rational approximations
    of `cos(θ)` and `sin(θ)` to 6 significant digits (adequate for invariant bounds).
    Also add: `EQ(PLUS(MULT(ccosVar, ccosVar), MULT(csinVar, csinVar)), one)` —
    unit-circle invariant (keeps nlsat bounded in the angular dimension).
  - **Periodic case**: for each `k ∈ {0,…,q-1}`, add the implication
    `(MOD(_i_0_var, period_const) = k_const) ⟹ (ccosVar = cos_k ∧ csinVar = sin_k)`.
    If `MOD` is not available in the IR, fall back to the non-periodic trig encoding.

- **Query CHC** (`srcVars` only): push `magVar`, `ccosVar`, `csinVar`.

**Extension to `generateRootBounds(int i)`**:

For each `ComplexPairEntry`, add bounds based on the unit-circle property
`|A·cos(nθ) + B·sin(nθ)| ≤ sqrt(A²+B²)`. The magnitude variable itself is already
bounded by `createRootConstraint(magAlnum)`. No additional range lemma is needed
beyond what the invariant synthesis will discover, but optionally add:
- `LEQ(NEG(magVar), MULT(ccosVar, magVar)) AND LEQ(MULT(ccosVar, magVar), magVar)` —
  bounds the cosine-scaled magnitude component between `[-r^n, r^n]`.
- Same for `csinVar`.

**Extension to `str_to_expr`**:

Declare `_mag_k`, `_ccos_k`, `_csin_k` as `Real` constants in the inline SMT2
string, alongside the `_alg_k` declarations. Iterate `complexPairRegistry[i]` and
emit one `(declare-const name Real)` for each of the three names per entry.

**Extension to `evaluateBaseString`**:

Check `complexPairRegistry[i]` entries: if `baseStr == entry.magName`, return
`entry.magAlnum.midpoint().get_d()`. If `baseStr == entry.ccosName`, return
`entry.cosTheta`. If `baseStr == entry.csinName`, return `entry.sinTheta`.

**Wiring in `learnInvariants5()`** (extends Phase 4):

After the `parseAuxRoots` call, add:
```cpp
if (closedformJson.contains("complex_pairs") && closedformJson["complex_pairs"].is_array()) {
    ds.parseComplexPairs(i, closedformJson["complex_pairs"]);
}
```
This must also come BEFORE `ds.generateSymbolicClosedForms(i, closedformJson)`.

### Updated Positional Ordering (extends Key Invariant)

The full variable ordering is now:
1. Original CHC variables (from parse)
2. `_i_0` index variable (from `addIndex`)
3. `_r_0`, `_r_1`, … real root variables (from `addRoot` calls)
4. `_alg_0`, `_alg_1`, … real algebraic constant variables (from `algRootRegistry`)
5. `_mag_0`, `_ccos_0`, `_csin_0`, `_mag_1`, `_ccos_1`, `_csin_1`, … complex pair
   triples (from `complexPairRegistry`), grouped by pair, in registration order

All six of `insertRoots`, `generateRootBounds`, `str_to_expr`, `evaluateBaseString`,
`parseComplexPairs`, and `learnInvariants5` wiring must respect this order.
Breaking it causes the same silent `replaceAll` substitution bugs as before.

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
| `tools/polar/closedforms2.py` | Major rewrite of sympy_to_pysmt2 + main loop; add `detect_complex_pairs`, `complex_pair_to_trig`, extend two-pass loop, emit `complex_pairs` JSON | Large |
| `tools/polar/utils/expressions.py` | Add `poly_to_int_coeffs`; add `mag_poly_from_complex_root` | Small |
| `tools/polar/utils/__init__.py` | Export `resolve_real_croot` | Trivial |
| `include/deep/RndLearnerV5.hpp` | Rewrite 6 methods, delete 2, add 4 (incl. `parseComplexPairs`), new structs (`AlgRootEntry`, `ComplexPairEntry`) + 2 new registry members | Large |
| `include/ufo/Expr.hpp` | No changes | — |
| `include/ufo/Smt/ZExprConverter.hpp` | No changes | — |

---

## Benchmark Readiness (a3/a4/a5/a7)

The following matrix tracks how far we are from generic algebraic support
including imaginary components for the concrete targets under:
`pwa-horn-benchmarks/possible_features/algebraic_numbers`.

| Benchmark | Required capability | Observed payload shape | Direct smoke test | Status |
|---|---|---|---|---|
| `a3.smt2` | Algebraic + complex-pair path | `aux_roots > 0`, `complex_pairs > 0`, periodic entry present | `tools/polar/tests/test_freqhorn_a3_smoke.py` | Passing |
| `a4.smt2` | Complex-pair path for oscillatory rational case | `complex_pairs = 1`, `period = 8` | `tools/polar/tests/test_freqhorn_a4_smoke.py` | Passing |
| `a5.smt2` | Negative-real phase rewrite path | `complex_pairs = 1`, `period = 2` | `tools/polar/tests/test_freqhorn_a5_smoke.py` | Passing |
| `a7.smt2` | Non-periodic complex-pair path in dense 3x3 system | `complex_pairs = 1`, `period = null` | `tools/polar/tests/test_freqhorn_a7_smoke.py` | Passing |

Current interpretation:
- The end-to-end serializer/consumer path is now directly exercised on all
  requested `a3/a4/a5/a7` benchmarks.
- Remaining risk is solver difficulty on some nonlinear oscillatory queries,
  not missing JSON schema wiring or placeholder substitution.

Completion gate for this feature family:
1. Keep `a3/a4/a5/a7` smoke tests green.
2. Complete at least one full `bench_horn` regression pass after any major
   solver or placeholder-ordering change.
3. Remove legacy sqrt fallback once downstream compatibility is no longer
   required.