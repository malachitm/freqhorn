# Feature 4: Input Variable

Let's say we wanted to represent a variable that could be any value between a
minimum and maximum value. This is equivalent to an input variable `u` in an LTI
system. In this case, how could this tool support it soundly?

The key design decision is that the final phase lemmas should **not** contain the
raw per-step input variable itself. A lemma such as `(i > k) => (r < 0.7*u)` is not
the right shape when `u` may change on each loop iteration, because the current
value of `u` does not summarize the earlier values of `u` that contributed to the
current state. Instead, the tool should compute a **purely numeric worst-case
bound** for the input contribution and place that numeric bound in the lemma.

So the intended shape is:

- `(i > k) => (r < B(i))`

where `B(i)` is a bound computed from the allowed interval for `u`, the closed-form
coefficient multiplying `u`, and any other fixed constants in the system.

For the initial version, keep the supported input format narrow:

- only **state-independent interval bounds** on the primed input variable,
	such as `0 <= u'` and `u' <= 1`
- no joint constraints over multiple inputs
- no state-dependent bounds like `u' <= x + 1`
- no probabilistic/distribution semantics

The POLAR side should still treat the input as a symbolic parameter so closed forms
can be computed in terms of it, but the CHC-facing lemma generation must eliminate
the raw variable numerically.

If the closed form contains a term `c(i) * u`, then the numeric bound is computed by
interval endpoint reasoning:

- if `c(i) >= 0`, the upper bound uses `u_max` and the lower bound uses `u_min`
- if `c(i) < 0`, the upper bound uses `u_min` and the lower bound uses `u_max`
- if the sign of `c(i)` cannot be proved, use a sound fallback such as
	`|c(i)| * max(|u_min|, |u_max|)`

This means the final lemma can still mention fixed constants, including algebraic
constants from the other feature, but it should never mention the raw per-step input
variable itself.