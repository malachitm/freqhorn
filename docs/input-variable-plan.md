# Input Variable Support — Implementation Plan

## Goal
Support **bounded non-deterministic input variables** in CHCs, analogous to an LTI
input `u_k`, where each step may choose a fresh value inside a bounded region.

Chosen semantics for the initial version:

- **Worst-case** semantics, not expectation.
- Inputs are modeled as **fresh choices each iteration**, not fixed unknown
  constants.
- Final phase lemmas must contain **numeric bounds only**; raw per-step input
  variables must not appear in the lemma body.
- Supported input constraints are restricted to **state-independent interval bounds**
  on each input variable.
- If the resulting system is unstable and no finite numeric bound is found, keep the
  current behavior (timeout / no proof) rather than adding explicit instability
  reporting.

This plan expands Feature 4 from `feature1_subtask_estimates.csv` into a tool-facing
pipeline under those simplified assumptions.

---

## Design Decision

Do **not** use POLAR distributions in the initial version.

Instead:

1. Serialize each input variable to POLAR as a **symbolic parameter** so POLAR can
   return closed forms in terms of that symbol.
2. Keep the actual **bounded non-determinism at the CHC layer**, where the inductive
   rule body retains only interval-style constraints such as `0 <= u'` and `u' <= 1`.
3. Compute a **sound numeric worst-case bound** from the closed-form coefficients and
   inject that numeric bound back into the phase lemmas / root-bound generation.

No separate optimization engine is needed in the initial version. For interval-bounded
inputs, worst-case values are obtained by endpoint reasoning on the coefficient sign.

---

## What Is Already In Place (Do Not Reimplement)

- **`include/deep/RndLearnerV5.hpp::generatePolarFile2()`**: already turns unknown
  initial values into symbolic `_INIT` parameters via `initialValueMap`,
  `initVarNameMap`, and `pendingInitVarPairs`.
- **`registerInitRealVar()` / `materializeInitRealVars()`**: already materialize
  those `_INIT` names as additional CHC variables and rewrite identity transitions
  `v' = v` into `v' = v_init'`.
- **`checkCHC2()` / `buildCHCExprs()`**: already assert the actual inductive and
  query bodies, so if bounded-input constraints remain in `hr.body`, the solver will
  respect them.
- **`exprToPolarString()`** already serializes arithmetic expressions well enough for
  symbolic-parameter POLAR programs.
- **`docs/random_val.md`** already captures the feature intent: bounds should reflect
  the fact that the input may vary per step.

---

## Key Gap in the Current `_INIT` Mechanism

The existing `_INIT` flow is correct for **unknown-but-fixed** values and wrong for
**fresh per-step inputs**.

Today, `registerInitRealVar()` does both of the following:

1. gives POLAR a symbolic parameter name, and
2. rewrites the CHC so the value is constant across transitions (`v' = v_init'`).

Feature 4 needs only the first behavior for POLAR. It must **not** turn an input
variable into a transition-invariant constant.

This means the first engineering task is to split the existing mechanism into:

- **POLAR-only symbolic parameter naming**, and
- **CHC constant-materialization for true init variables**.

---

## Supported Input Fragment (Initial Version)

Support input variables whose inductive-step constraints are interval bounds on the
primed input variable, for example:

- `0 <= u'`
- `u' <= 1`
- `a <= u'` and `u' <= b`

where `a` and `b` are numeric constants or symbols that denote fixed constants across
the run, such as algebraic-number variables from Feature 1.

Out of scope for the initial version:

- probabilistic distributions / expectations,
- joint constraints over multiple inputs (for example `u1 + u2 <= 1`),
- nonlinear constraints,
- input constraints mentioning loop-state variables (`u' <= x + 1`),
- time-varying bounds depending on the iteration counter,
- final lemmas that mention raw input variables.

Reject unsupported input formats explicitly rather than weakening them.

---

## JSON Schema Extension

The existing closed-form JSON needs an additional decomposition for input
parameters. A first-cut schema can be:

```json
{
  "x": [ { "bases": ["_r_0", "1.0"], "coeffs": ["...", "..."] } ],
  "input_coeffs": {
    "x": {
      "constant": {
        "bases": ["_r_0", "1.0"],
        "coeffs": ["...", "..."]
      },
      "coefficients": {
        "_FH_U_INPUT": {
          "bases": ["_r_0", "1.0"],
          "coeffs": ["...", "..."]
        }
      }
    }
  }
}
```

Interpretation:

- `constant`: the part of the closed form independent of the input variables.
- `coefficients[inputName]`: the coefficient function `c_i(n)` for that input.
- The state value is reconstructed as:
  `state(n) = constant(n) + Σ_i c_i(n) * u_i`.

The final C++ pipeline then eliminates each `u_i` by interval endpoint reasoning,
producing a purely numeric upper and lower bound.

---

## Pipeline Overview

1. Split the current `_INIT` mechanism into constant-init and input-parameter paths.
2. Detect and classify interval-bounded input variables from the inductive CHC.
3. Extract state-independent interval bounds only.
4. Serialize inputs to POLAR as symbolic parameters only.
5. Extend the closed-form JSON with per-input coefficient decomposition.
6. Compute sound numeric worst-case bounds by interval endpoint reasoning.
7. Generate CHC lemmas that combine homogeneous root bounds with numeric input
   bounds.
8. Preserve bounded non-determinism in the actual CHC transition relation.
9. Build a regression suite covering interval-bounded inputs.

---

## Phase 0 — Semantics and Registry Split

### Purpose
Stabilize the distinction between three different variable classes:

- ordinary loop-state variables,
- unknown-but-fixed initial parameters,
- fresh per-step input variables.

### Tasks

1. **Introduce an `InputVarRegistry`** (name flexible) scoped by invariant index.
2. **Split the current init-variable path** into:
   - a POLAR-only symbolic-parameter naming path, and
   - the existing CHC constant-materialization path for true `_INIT` variables.
3. **Document the soundness rule**:
   input variables may reuse the naming machinery, but they must never reuse the
   `v' = v_init'` rewrite.

### Deliverable
A clear internal distinction between “fixed parameter” and “per-step bounded input”.

---

## Phase 1 — Detect and Classify Input Variables

### 1A. Scan the inductive CHC for primed-input patterns

Walk inductive-body conjuncts and detect variables that appear in bounded forms like:

- `c1 <= u'`
- `u' <= c2`

where `c1` and `c2` are constants or constant-like symbols.

### 1B. Distinguish true inputs from identity transitions

Do not classify a variable as an input if the inductive body already enforces
`u' = u` and no bounded non-deterministic constraints appear. That is still a fixed
parameter / state variable case.

### 1C. Populate per-variable metadata

For each candidate input, record:

- canonical variable name,
- primed expression,
- scalar lower/upper bounds when available,
- the POLAR parameter name that will stand in for it.

### 1D. Reject unsupported mixed constraints

If a purported input constraint mentions loop-state variables or multiple distinct
input variables in the same inequality, reject it in the initial version.

---

## Phase 2 — Extract State-Independent Interval Bounds

### 2A. Normalize inequalities

Convert supported inequalities into a canonical interval form for each input:

`lower_i <= u_i' <= upper_i`

### 2B. Separate lower and upper evidence

Collect lower-bound and upper-bound conjuncts independently, then combine them into a
single stored interval.

### 2C. Boundedness check

Require every input used in the feature to have both a lower and an upper bound.
If either side is missing, reject the feature for that CHC rather than guessing an
infinite interval.

### 2D. Constant-bound check

Require the interval endpoints to be numeric constants or constant-like symbols.
State-dependent bounds remain out of scope.

---

## Phase 3 — POLAR Parameterization Without CHC Const-ification

### 3A. Reuse naming, not rewriting

Route input variables through a parameter naming scheme analogous to `_INIT`, but do
not call the part of the code that adds constant CHC variables and rewrites
transitions.

### 3B. Generate symbolic parameters in the POLAR init/loop program

When `generatePolarFile2()` emits the loop body, replace input-variable occurrences
with their POLAR parameter names so POLAR returns closed forms in those symbols.

### 3C. Keep the original CHC variables untouched

In the CHC, the input remains an ordinary program variable with bounded interval
constraints in the inductive body. No auxiliary invariant variable is introduced
merely to make POLAR happy.

### 3D. Guard against accidental materialization

Add a defensive check so `materializeInitRealVars()` or related plumbing cannot pick
up input-variable parameter names by mistake.

---

## Phase 4 — Emit Per-Input Coefficient Decomposition from POLAR

### 4A. Affine-in-input decomposition

In `closedforms2.py`, decompose each state closed form into:

- input-independent constant part,
- one coefficient expression per input variable.

The initial version assumes the closed form is affine in the designated input
parameters. If a higher-order term like `u^2` appears, reject it rather than
guessing.

### 4B. Extend the output JSON

Emit the `input_coeffs` section described above.

### 4C. Preserve compatibility with the existing root/base machinery

Coefficient expressions should reuse the same `bases` / `coeffs` encoding as ordinary
closed forms so the C++ side can pass them through existing parsing/evaluation code.

### 4D. Add decomposition validation examples

Use a few small recurrences where the analytic solution is known, for example:

- `x' = a*x + u`
- `x' = a*x - u`

---

## Phase 5 — Numeric Worst-Case Bound Engine

### 5A. Coefficient-bound extraction

For each coefficient function `c_i(n)`, build the symbolic/interval bound needed to
bound `c_i(n) * u_i` soundly. Reuse existing root-bound infrastructure when possible
rather than inventing a second bound engine.

### 5B. Interval endpoint reasoning

When inputs are interval-bounded, compute:

- upper bound by choosing `u_i = upper_i` if `c_i(n) >= 0`, else `lower_i`,
- lower bound by choosing the opposite endpoint.

### 5C. Sign-uncertain fallback

If the sign of a coefficient cannot be proved on the current phase, use the sound
fallback:

`|c_i(n)| * max(|lower_i|, |upper_i|)`

This is wider but safe.

### 5D. Numeric-only output rule

Do not leave raw input variables in the final bound. The output of this phase must be
a numeric upper/lower bound expression suitable for direct insertion into a phase
lemma.

---

## Phase 6 — Generate Numeric CHC Lemmas

### 6A. Separate homogeneous and input-driven parts

For each state bound, produce the shape:

`state_bound(n) = homogeneous_bound(n) + input_bound(n)`

where `homogeneous_bound` comes from the root analysis and `input_bound` comes from
Phase 5.

### 6B. Extend the root-bound generation path

Implement this either in `generateRootBounds()` or in a dedicated helper that is
invoked alongside it. Keep the change narrow: do not rewrite unrelated invariant
synthesis logic.

### 6C. Preserve phase-lemma structure

The resulting lemmas should still fit the existing phase style, for example:

`(i > k) => x <= B_hom(i) + B_input(i)`

with a symmetric lower-bound version where needed.

### 6D. Numeric-only lemma rule

The final lemma may contain numeric constants and symbols that denote fixed constants
across the run, but it must not contain raw per-step input variables.

---

## Phase 7 — Preserve Bounded Non-Determinism in the CHC

### 7A. Do not add `u' = u` for inputs

Where the current augmentation path adds identity equations for constant parameters,
input variables must be excluded.

### 7B. Keep original interval constraints in the inductive body

The inductive CHC body should still contain the lower/upper constraints over the
primed input variables.

### 7C. Query/fact behavior

- Fact CHCs may contain initial-state constraints on the input variables if present,
  but those are not what defines them as inputs.
- Query CHCs should continue to see the same program variables; no extra input-only
  invariant variables are necessary in the initial version.

### 7D. Audit any helper that assumes `_INIT` means constant across time

The `_INIT` naming scheme is no longer sufficient to infer constancy once input
support exists. Any helper making that assumption must be narrowed.

---

## Phase 8 — Regression Pipeline

### 8A. Classification tests

Add small CHCs that distinguish:

- fixed unknown initial constants,
- true interval-bounded inputs,
- unsupported mixed state/input constraints.

### 8B. Interval-bound tests

Use benchmarks with closed-form analytic expectations for worst-case bounds, for
example:

- `x' = a*x + u`, `u in [0,1]`
- `x' = a*x - u`, `u in [0,1]`
- multi-state systems with separate interval-bounded inputs.

### 8C. Instability / timeout tests

Confirm that unstable cases do not accidentally produce unsound finite bounds.
Current acceptable behavior is timeout / no proof.

### 8D. Bug-fix sweep

Reserve time for the predictable failure modes:

- input variables accidentally treated as `_INIT` constants,
- coefficient decomposition failing on non-affine forms,
- sign handling producing optimistic instead of worst-case bounds,
- final lemmas still mentioning raw input variables,
- CHC augmentation silently dropping interval constraints.

---

## Key Invariants to Preserve

1. **Never const-ify an input**: do not reuse `registerInitRealVar()` semantics for a
   per-step bounded input.
2. **Keep optimization sound**: if a coefficient sign is unknown, overapproximate.
3. **Keep the CHC as the source of truth**: POLAR only computes parameterized closed
   forms; the actual bounded non-determinism lives in the inductive CHC body.
4. **Keep final lemmas numeric**: raw input variables must be eliminated before the
   SMT-facing phase lemmas are emitted.
5. **Reject unsupported input formats early**: joint, nonlinear, or state-dependent
   input constraints are outside the initial version.

---

## Files Likely Touched

| File | Change Type | Effort |
|---|---|---|
| `include/deep/RndLearnerV5.hpp` | Add input detection, split `_INIT` handling, preserve interval constraints, generate numeric input bounds | Large |
| `tools/polar/closedforms2.py` | Add affine-in-input decomposition and emit `input_coeffs` JSON | Medium |
| `docs/random_val.md` | No changes required; source note only | — |
| benchmark files under `bench_horn/` or a new input subset | Add interval-bounded input regressions | Medium |
