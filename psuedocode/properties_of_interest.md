Let all variables specified be program variables in an affine loop.

1) (i > 50) => ((-0.1 <= x - a) /\ (x - a <= 0.1)) <=> ~(i > 50) \/ ((-0.1 <= x - a) /\ (x - a <= 0.1))
2) (i < 50) => (x < 1000) <=> ~(i < 50) \/ (x < 1000)

Let's say x increases after each transformation and has no upper bound, BUT #2 does in fact hold because
it doesn't increase fast enough to break the property for any value of a within a specified range.
How could we use the closed form of this transformation in order to find an invariant?

Initially, I think of a list of implications that give an upper bound to the value of x for each incremental
step. This could be done until you get to the final value. But, this would mean I would have to explicitly
write out each individual step UNTIL i=50, so it would always be a very long invariant.

Interesting, I placed a set of CHCs into Z3 to see what it would output, and it did exactly that. It said
that the values were bounded for each step until the index was right before the marker. I suppose that
_does_ count as an invariant, but it feels almost like cheating. One advantage of my technique is that,
in my opinion, this would make the relationship between how the loop changes much more ledgible.

One way of thinking of my technique is that it is somewhat similar to that of Z3, but it takes advantage
of the underlying structure of this particular problem and optimizes the types of lemmas to check
in accordance with its structure. Also, if my idea is correct, this may work for floating point variables,
which may have never been done before?

One thing I just realized is that if the root is greater than 1, then that means my approach for computing
the first interval of computing the average of the previous and current values wouldn't work. Why?

When it's between 0 and 1, the previous value will always be greater than the current value. This means,
using the average of both will make it a little "taller" than the actual value, which should widen it
enough for the interval. But if it is greater than 1, then the previous value will always be greater. That
means, the widened interval must be the average of the following value and the current value. There may
be an argument to make that this averaging of the previous/next value with the present value may be too
simplistic or crude. For one, it seems to pre-maturely widen. Second, it 

Also, here's another thing. If I check to see if an implication lemma holds, and it doesn't, it should give me a satisfying solution for the step that tells me what value of what root caused the system to fall through, and
so you can use a form of CEGAR to improve the performance of finding proper widenings of the intervals.

Let's give an example. Let's say, for a given lemma I want to generate, my purposed upper bound is 0.764 for x.
We check to see if the lemma holds for initiation (I'd be befuddled if not), and consecution