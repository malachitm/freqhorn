# Loop Guard Support — Implementation Plan

## Goal
Support guarded loops in the PHASER/POLAR pipeline for two proof modes:

1. **Inside-loop safety**: prove properties that must hold on every iteration in
   which the loop guard is true.
2. **Post-loop safety**: prove properties that must hold after control exits the
   loop, i.e. on the path where the guard is false.

This plan expands Feature 3 from `feature1_subtask_estimates.csv` into a pipeline
that is safe for a future coding agent to execute. Every Feature 3 CSV item is
expanded further because each one has AI pessimistic estimate at least 3x the AI
optimistic estimate.

---

## What Is Already In Place (Do Not Reimplement)

- **`tools/polar/inputparser/syntax.lark`**: the POLAR grammar already supports
  boolean conditions, comparisons, conjunction, disjunction, and negation:
  `condition`, `atom`, `AND`, `OR`, `NOT`, `<`, `<=`, `>`, `>=`, `==`, `/=`.
  No parser grammar work is needed for the first cut.
- **`include/deep/RndLearnerV5.hpp::generatePolarFile2()`**: already identifies the
  fact CHC and inductive CHC, builds the POLAR init line, rewrites identity
  variables into `_INIT` parameters, and writes the loop body assignments.
- **`include/deep/RndLearnerV5.hpp::exprToPolarString()`**: already serializes
  arithmetic (`+`, `-`, unary minus, `*`, `/`) for POLAR, but currently returns
  `unsupported_expr(...)` for comparisons and boolean expressions.
- **`include/deep/RndLearnerV5.hpp::checkCHC2()` / `buildCHCExprs()`**: already use
  the CHC body for consecution and query checks. Guard conjuncts that remain in the
  CHC body are therefore already visible to the SMT solver.
- **`generatePolarFile2()` currently hardcodes `while true:`**: this is the main
  serialization gap, not a POLAR parser limitation.

---

## Supported Guard Fragment (First Cut)

Support only guards that are boolean combinations of comparisons over:

- loop-state variables,
- `_INIT` parameters,
- rational constants,
- arithmetic expressions already serializable by `exprToPolarString()`.

Examples supported in the first cut:

- `x < 10`
- `(x + y <= n_INIT) && (0 <= z)`
- `!(x == 0)`
- `(x <= y) || (a + b < 7/3)`

Out of scope for the first cut:

- quantified guards,
- arrays/select/store in guards,
- non-boolean ITE terms inside guards,
- unsupported arithmetic operators that POLAR cannot parse from the existing
  serializer,
- guards whose meaning depends on auxiliary PHASER-only variables that are not
  valid POLAR program variables.

Reject unsupported guards explicitly rather than silently widening to `true`.

---

## Pipeline Overview

1. Define the supported guard fragment and how CHC conjuncts are classified.
2. Extend expression serialization so guard formulas can be emitted to POLAR.
3. Extract guard conjuncts from the inductive CHC without disturbing update
   equations or global equalities.
4. Generate guarded POLAR programs instead of unconditional `while true` loops.
5. Audit the inside-loop proof path so guard semantics remain aligned between
   POLAR and the CHC solver.
6. Handle post-loop queries where safety is checked on the exit path.
7. Build a regression suite covering both inside-loop and after-loop properties.

---

## Phase 0 — Guard Semantics Contract

### Purpose
Stabilize the meaning of a “guard conjunct” before editing code. The current
implementation walks inductive-body conjuncts to build update assignments; guard
support depends on partitioning those conjuncts correctly.

### Tasks

1. **Classify conjunct roles in the inductive CHC body**:
   - update equations of the form `dstVar = rhs`,
   - guard comparisons over source-state variables and constants,
   - global equalities that should stay outside the POLAR guard,
   - PHASER-only auxiliary constraints that should not be emitted to POLAR.
2. **Define the first-cut acceptance rule**:
   a conjunct is a guard candidate only if it is a comparison or boolean formula
   over non-auxiliary variables that appear in the POLAR loop state/parameters.
3. **Define rejection behavior**:
   if the inductive CHC contains a non-update conjunct that cannot be serialized as
   a POLAR condition, fail generation with a clear diagnostic instead of emitting an
   unsound `while true` program.

### Deliverable
A helper predicate and/or partitioning routine used by later phases.

---

## Phase 1 — Guard Serializer Layer

This phase expands CSV sub-task 2.

### 1A. Comparison emission

Extend `exprToPolarString()` (or introduce `exprToPolarConditionString()`) to emit:

- `<`, `<=`, `>`, `>=`, `==`, `/=`

Use fully parenthesized output to avoid precedence mistakes.

### 1B. Boolean emission

Add support for:

- `AND` -> `&&`
- `OR` -> `||`
- `NOT` -> `!(...)`
- nested parenthesized conditions

### 1C. Unsupported-condition detection

Replace the current `unsupported_expr(...)` fallback for guard contexts with a hard
error path. It is acceptable for arithmetic-only contexts to keep the current
behavior temporarily, but guard emission must not silently degrade.

### 1D. Serialization smoke tests

Create a minimal set of conversion examples and expected strings:

- `x < 10`
- `(x < 10) && (y <= 3)`
- `!(x == y)`
- `(x + 1 < y) || (z >= 0)`

These can be doc-tested manually or wired into a lightweight regression harness.

---

## Phase 2 — Extract Guard Conjuncts from the Inductive CHC

This phase expands CSV sub-task 1.

### 2A. Partition conjuncts

Inside `generatePolarFile2()`, after collecting `inductiveConjuncts`, split them into:

- **update equations**: define loop assignments,
- **guard conjuncts**: become the POLAR loop condition,
- **non-guard structural constraints**: remain only in the CHC world.

### 2B. Distinguish updates from comparisons

Current code treats equalities as candidate destination definitions. Tighten the rule:

- `dstVar = rhs` where `dstVar` is a loop destination variable -> update equation
- any non-update comparison over source variables -> guard candidate
- equality linking an identity variable to its `_INIT` parameter -> global fact,
  not a guard

### 2C. Preserve canonical naming before lowercasing

Guard extraction must happen before the POLAR writer lowercases names. Reuse the same
`srcVarRenames` / `initialValueMap` logic already used for RHS serialization so the
same names appear in the guard and assignment body.

### 2D. Guard normalisation

Conjoin multiple guard conjuncts with `&&`. Preserve original boolean structure when
possible rather than flattening through ad-hoc string concatenation.

### Deliverable
A single `Expr` or string representing the loop guard, plus the remaining assignment
set used to emit the loop body.

---

## Phase 3 — Generate Guarded POLAR Programs

This phase expands CSV sub-task 3.

### 3A. Replace the hardcoded loop header

Replace:

```text
while true:
```

with:

```text
while <guard-string>:
```

when a supported guard exists. If no guard conjuncts are present, keep `while true:`.

### 3B. Parameter/identity-variable handling inside the guard

If an identity-transition variable has already been promoted to `_INIT`, the guard
must reference the parameter name consistently, just like the RHS expressions.

### 3C. Emit only POLAR-valid variables

Do not include PHASER auxiliary variables, roots, indices, or solver-only symbols in
`while <guard>:`. If the extracted guard mentions one, reject the program rather than
emit invalid POLAR syntax.

### 3D. Parser round-trip check

After generating a guarded `.prob`, validate that POLAR's parser accepts the file.
The grammar already supports guards, so a failure here indicates serializer or naming
bugs.

---

## Phase 4 — Inside-Loop Property Verification Audit

This phase expands CSV sub-task 4.

### 4A. Confirm CHC-side semantics already include the guard

`checkCHC2()` already asserts `hr.body` for consecution. Therefore the main risk is
not the SMT check itself; it is semantic drift between the CHC body and the POLAR
program emitted from it.

### 4B. Audit candidate generation assumptions

Confirm that the candidate-generation path does not rely on the loop being
unconditional. In particular, check whether:

- sample generation assumes every update fires every iteration,
- initial-condition preprocessing accidentally moves guard-relevant constraints into
  step-0-only facts,
- learned bounds are interpreted as global when they should be conditional on the
  guard being true.

### 4C. Degenerate guards

Handle explicitly:

- `while true:` -> current behavior,
- `while false:` -> no loop iterations; the tool should not try to infer a non-empty
  transition system from POLAR output,
- contradictory guards -> reject or reduce to the `while false` case.

### 4D. Soundness rule

Never drop a guard conjunct from the CHC body just because it is also emitted to the
POLAR file. POLAR gets an additional serialized view; the solver must keep the
original logical constraint.

---

## Phase 5 — Post-Loop / Exit-Path Verification

This phase expands CSV sub-task 5.

### 5A. Classify exit-path queries

Identify which query CHCs correspond to the state after loop termination. In the
common encoding this is the query whose body contains the negated loop guard plus the
postcondition violation.

### 5B. Preserve the negated guard in the query path

Ensure `learnInvariants5()` and any helper around `qr` / `checkQuery()` do not treat
negated-guard conjuncts as noise. They are the whole meaning of “after the loop”.

### 5C. Decide the first-cut proof rule

Use the standard shape:

- learn an invariant for states satisfying the guard,
- prove the post-loop safety query using the query CHC body that contains `!guard`.

Do not attempt full strongest-postcondition reasoning in the first cut.

### 5D. Generate focused post-loop benchmarks

Create a few examples where:

- the invariant is true inside the loop but the desired property is about the exit
  state only,
- the query body explicitly contains the negated guard,
- a wrong guard serializer would cause a false proof or false alarm.

---

## Phase 6 — Regression Pipeline

This phase expands CSV sub-task 6.

### 6A. Guard-string unit smoke tests

Validate the string output for representative conditions.

### 6B. Parser acceptance tests

Run POLAR on generated guarded `.prob` files and confirm parsing succeeds.

### 6C. Inside-loop verification tests

Add or adapt CHC benchmarks where the property is checked while the guard is true.
Examples should cover:

- linear threshold guards,
- conjunctions of comparisons,
- negated equalities,
- guards that refer to `_INIT` parameters.

### 6D. Post-loop verification tests

Add or adapt benchmarks where safety is checked only after loop exit.

### 6E. Bug-fix sweep

Reserve explicit time for the likely failure modes:

- name mismatches after lowercasing,
- `unsupported_expr(...)` leaking into `.prob` files,
- guard conjuncts accidentally consumed as update equalities,
- query CHCs not recognized as exit-path checks.

---

## Key Invariants to Preserve

1. **Do not serialize unsoundly**: if a guard cannot be represented in POLAR, stop.
   Never widen it to `true`.
2. **Do not remove the guard from the CHC**: the SMT check must still see the
   original inductive/query body.
3. **Preserve naming consistency**: the same variable-renaming rules used in the loop
   RHS must apply to the guard.
4. **Keep identity-variable semantics intact**: if a variable becomes an `_INIT`
   parameter, the guard must reference that parameter consistently.

---

## Files Likely Touched

| File | Change Type | Effort |
|---|---|---|
| `include/deep/RndLearnerV5.hpp` | Add guard partitioning, extend condition serialization, replace hardcoded `while true`, audit query handling | Large |
| `tools/polar/inputparser/syntax.lark` | No changes expected in the first cut | — |
| `docs/loop_guard.md` | No changes required; source note only | — |
| benchmarks under `bench_horn/` or a new guarded subset | Add guarded inside-loop and post-loop regressions | Medium |
