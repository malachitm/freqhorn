# Input Variable Support — Implementation Plan

## Goal
Support **bounded non-deterministic input variables** in CHCs, analogous to an LTI
input `u_k`, where each step may choose a fresh value inside a bounded region.

Chosen semantics for the first cut:

- **Worst-case** semantics, not expectation.
- Inputs may have **independent interval bounds** and also **joint rational linear
  constraints** (for example `u1 + u2 <= 1`).
- Inputs are modeled as **fresh choices each iteration**, not fixed unknown
  constants.
- If the resulting system is unstable and no finite bound is found, keep the current
  behavior (timeout / no proof) rather than adding explicit instability reporting.

This plan expands Feature 4 from `feature1_subtask_estimates.csv` into a tool-facing
pipeline. Every Feature 4 CSV item is expanded further because each one has AI
pessimistic estimate at least 3x the AI optimistic estimate.

---

## Design Decision

Do **not** use POLAR distributions for the first cut.

Instead:

1. Serialize each input variable to POLAR as a **symbolic parameter** so POLAR can
   return closed forms in terms of that symbol.
2. Keep the actual **bounded non-determinism at the CHC layer**, where the inductive
   rule body retains constraints such as `0 <= u'`, `u' <= 1`, or `u1' + u2' <= 1`.
3. Compute a **sound worst-case bound** from the closed-form coefficients and inject
   that bound back into the phase lemmas / root-bound generation.

This is a partial reuse of the existing `_INIT` mechanism, not a direct reuse of all
its CHC rewriting logic.

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

## Supported Input Fragment (First Cut)

Support input variables whose inductive-step constraints are:

- interval bounds on primed inputs, e.g. `0 <= u'`, `u' <= 1`,
- joint rational linear constraints over primed inputs only, e.g. `u1' + u2' <= 1`,
- optionally repeated in canonicalized `<=` / `>=` / equality forms.

Out of scope for the first cut:

- probabilistic distributions / expectations,
- nonlinear joint constraints (e.g. `u1*u2 <= 1`),
- input constraints mentioning loop-state variables (`u' <= x + 1`),
- time-varying bounds depending on the iteration counter,
- explicit instability diagnosis beyond existing timeout/no-proof behavior.

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
        },
        "_FH_V_INPUT": {
          "bases": ["_r_1", "1.0"],
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

This keeps the worst-case optimization problem small and explicit on the C++ side.

---

## Pipeline Overview

1. Split the current `_INIT` mechanism into constant-init and input-parameter paths.
2. Detect and classify input variables from the inductive CHC.
3. Extract independent bounds and joint linear constraints.
4. Serialize inputs to POLAR as symbolic parameters only.
5. Extend the closed-form JSON with per-input coefficient decomposition.
6. Compute sound worst-case bounds for independent and jointly constrained inputs.
7. Generate CHC lemmas that combine homogeneous root bounds with input bounds.
8. Preserve bounded non-determinism in the actual CHC transition relation.
9. Build a regression suite covering independent and joint-constraint inputs.

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

This phase expands CSV sub-task 1.

### 1A. Scan the inductive CHC for primed-input patterns

Walk inductive-body conjuncts and detect variables that appear in bounded forms like:

- `c1 <= u'`
- `u' <= c2`
- `A*u' + B*v' <= c`

### 1B. Distinguish true inputs from identity transitions

Do not classify a variable as an input if the inductive body already enforces
`u' = u` and no bounded non-deterministic constraints appear. That is still a fixed
parameter / state variable case.

### 1C. Populate per-variable metadata

For each candidate input, record:

- canonical variable name,
- primed expression,
- scalar lower/upper bounds when available,
- whether it participates in a joint constraint block,
- the POLAR parameter name that will stand in for it.

### 1D. Reject mixed constraints in the first cut

If a purported input constraint mentions both input variables and ordinary state
variables, reject it for now. That is a different problem from bounded exogenous
inputs.

---

## Phase 2 — Extract Independent and Joint Constraints

This phase expands CSV sub-task 2.

### 2A. Normalize inequalities

Convert supported inequalities to a standard rational linear form:

`A * u <= b`

where `u` is the vector of input variables for the current step.

### 2B. Separate independent interval bounds

When a constraint involves only one input variable, store it as a simple scalar
interval bound.

### 2C. Build joint-constraint blocks

When a constraint involves two or more inputs, group those inputs into a shared
polytope block and build a rational matrix representation `A*u <= b`.

### 2D. Boundedness check

Require that every input participating in optimization has either:

- explicit independent bounds, or
- membership in a bounded joint polytope.

If boundedness cannot be established syntactically, reject the feature for that CHC.

---

## Phase 3 — POLAR Parameterization Without CHC Const-ification

This phase expands CSV sub-task 3 and part of CSV sub-task 7.

### 3A. Reuse naming, not rewriting

Route input variables through a parameter naming scheme analogous to `_INIT`, but do
not call the part of the code that adds constant CHC variables and rewrites
transitions.

### 3B. Generate symbolic parameters in the POLAR init/loop program

When `generatePolarFile2()` emits the loop body, replace input-variable occurrences
with their POLAR parameter names so POLAR returns closed forms in those symbols.

### 3C. Keep the original CHC variables untouched

In the CHC, the input remains an ordinary program variable with bounded constraints
in the inductive body. No auxiliary invariant variable is introduced merely to make
POLAR happy.

### 3D. Guard against accidental materialization

Add a defensive check so `materializeInitRealVars()` or related plumbing cannot pick
up input-variable parameter names by mistake.

---

## Phase 4 — Emit Per-Input Coefficient Decomposition from POLAR

This phase expands CSV sub-task 4.

### 4A. Affine-in-input decomposition

In `closedforms2.py`, decompose each state closed form into:

- input-independent constant part,
- one coefficient expression per input variable.

The first cut assumes the closed form is affine in the designated input parameters.
If a higher-order term like `u1*u2` or `u^2` appears, reject it rather than guessing.

### 4B. Extend the output JSON

Emit the `input_coeffs` section described above.

### 4C. Preserve compatibility with the existing root/base machinery

Coefficient expressions should reuse the same `bases` / `coeffs` encoding as ordinary
closed forms so the C++ side can pass them through existing parsing/evaluation code.

### 4D. Add decomposition validation examples

Use a few small recurrences where the analytic solution is known, e.g.:

- `x' = a*x + u`
- `x' = a*x + b*u1 + c*u2`
- `x' = a*x + u1 - u2`

---

## Phase 5 — Worst-Case Bound Engine

This phase expands CSV sub-task 5 and is the highest-risk part of the feature.

### 5A. Coefficient-bound extraction

For each coefficient function `c_i(n)`, build the symbolic/interval bound needed to
optimize `Σ c_i(n) * u_i` soundly. Reuse existing root-bound infrastructure when
possible rather than inventing a second bound engine.

### 5B. Independent-interval optimization

When inputs are independently bounded, compute:

- upper bound by choosing `u_i = upper_i` if `c_i(n) >= 0`, else `lower_i`,
- lower bound by choosing the opposite endpoint.

### 5C. Sign-uncertain fallback

If the sign of a coefficient cannot be proved on the current phase, use the sound
fallback:

`|c_i(n)| * max(|lower_i|, |upper_i|)`

This is wider but safe.

### 5D. Joint-constraint optimization

For a joint constraint block `A*u <= b`, optimize `c(n)^T u` over the bounded
polytope. First cut strategy:

1. enumerate vertices for small dimensions,
2. evaluate the objective at each vertex,
3. keep the best value.

If dimension grows too large, add a guarded fallback or reject with a diagnostic.
Do not start with a full simplex implementation unless vertex enumeration proves too
limiting.

### 5E. Rational-first arithmetic

Keep the optimization layer rational when possible, because the constraints come from
CHCs and are naturally rational. Use doubles only as a last-mile approximation layer
if necessary.

---

## Phase 6 — Generate Input-Aware CHC Lemmas

This phase expands CSV sub-task 6.

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

The resulting lemmas should still fit the existing phase style, e.g. a thresholded
form like:

`(i > k) => x <= B_hom(i) + B_input(i)`

with a symmetric lower-bound version where needed.

### 6D. Prefer soundness over tightness

If the exact best input bound cannot be computed for a phase, fall back to a wider
but sound bound rather than skipping the lemma.

---

## Phase 7 — Preserve Bounded Non-Determinism in the CHC

This phase expands CSV sub-task 7.

### 7A. Do not add `u' = u` for inputs

Where the current augmentation path adds identity equations for constant parameters,
input variables must be excluded.

### 7B. Keep original input constraints in the inductive body

The inductive CHC body should still contain the range/polytope constraints over the
primed input variables.

### 7C. Query/fact behavior

- Fact CHCs may contain initial-state constraints on the input variables if present,
  but those are not what defines them as inputs.
- Query CHCs should continue to see the same program variables; no extra input-only
  invariant variables are necessary in the first cut.

### 7D. Audit any helper that assumes `_INIT` means constant across time

The `_INIT` naming scheme is no longer sufficient to infer constancy once input
support exists. Any helper making that assumption must be narrowed.

---

## Phase 8 — Regression Pipeline

This phase expands CSV sub-task 8.

### 8A. Classification tests

Add small CHCs that distinguish:

- fixed unknown initial constants,
- true bounded inputs,
- unsupported mixed state/input constraints.

### 8B. Independent-interval tests

Use benchmarks with closed-form analytic expectations for worst-case bounds, e.g.:

- `x' = a*x + u`, `u in [0,1]`
- `x' = a*x - u`, `u in [0,1]`
- multi-state systems with separate inputs.

### 8C. Joint-polytope tests

Add at least one benchmark with a shared bound such as:

- `u1 >= 0`, `u2 >= 0`, `u1 + u2 <= 1`

and check that the chosen worst-case endpoint matches analytic reasoning.

### 8D. Instability / timeout tests

Confirm that unstable cases do not accidentally produce unsound finite bounds.
Current acceptable behavior is timeout / no proof.

### 8E. Bug-fix sweep

Reserve time for the predictable failure modes:

- input variables accidentally treated as `_INIT` constants,
- coefficient decomposition failing on non-affine forms,
- sign handling producing optimistic instead of worst-case bounds,
- vertex enumeration missing a feasible extreme point,
- CHC augmentation silently dropping input constraints.

---

## Key Invariants to Preserve

1. **Never const-ify an input**: do not reuse `registerInitRealVar()` semantics for a
   per-step bounded input.
2. **Keep optimization sound**: if a coefficient sign is unknown, overapproximate.
3. **Keep the CHC as the source of truth**: POLAR only computes parameterized closed
   forms; the actual bounded non-determinism lives in the inductive CHC body.
4. **Reject unsupported joint constraints early**: state-dependent or nonlinear input
   constraints are a different feature.

---

## Files Likely Touched

| File | Change Type | Effort |
|---|---|---|
| `include/deep/RndLearnerV5.hpp` | Add input detection, split `_INIT` handling, preserve non-det CHC constraints, generate input-aware lemmas | Large |
| `tools/polar/closedforms2.py` | Add affine-in-input decomposition and emit `input_coeffs` JSON | Medium |
| `docs/random_val.md` | No changes required; source note only | — |
| benchmark files under `bench_horn/` or a new input subset | Add independent-interval and joint-constraint regressions | Medium |
