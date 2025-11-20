What about situations where the form doesn't end up being something like (constant)**n?

Well, if that ends up happening, just directly insert the n, but replace it with i. Thus, you can easily
prove the property x >= y by having the invariant

Also, right now I can do basic loops, but now I need to think about the format where there is a chain of dependence, such as
fc:
c=24

tr:
a' = c + 1.9
b' = a' * 4.2
c' = b' * 3.5 - c * 2.3

How do I ensure that these kinds of loops can be parsed such that I can write them out "in order".
For instance, for this to work, I would need to write the Polar loop

c = 24
while true:
    a = c + 1.9
    b = a * 4.2
    c = b * 3.5 - c * 2.3
end

In this particular situation, it MUST be ensured that the first assignment is for a, because if not then the
assignment for b will be false.

And, just so I know to write this down, I'm running into weird errors where the output for closedforms.py is
giving inaccurate data compared to the original? I don't know why if I am being genuine. Thus, I have to spend
time debugging this before being able to meaningfully make accurate steps forward.