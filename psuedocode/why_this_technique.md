For one, for a simple program that goes from an initial value to a final value, my technique already
can reason about the structure of the problem more effectively, so it can generate an invariant
equivalent to one that Z3 makes in less time.

For more complex problems, like when the initial value is a bound, this technique also works, where for
the Z3 tool it does not.

Further, for affine systems where the maximum bound increases and decreases over time, my technique, which
reduces the problem into only looking at the rate that the roots decrease / increase over time, simplifies
the problem and makes it easier to do reasoning with.