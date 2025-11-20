Okay, so how can we check that an arbitrary CNF formula of inequalities of 1 variable
will or will not work for this system? We could use Asymptotic Analysis.

Let's say we have a property
(y > -10) /\ (x < 29)

And we have the closed forms of both variables as
x = 2.0(1.5)^n - 1.2(0.4)^n /\ y = 1.3*(0.9)^n

We look at the dominant (i.e. largest) root of each closed form
(for x, 1.5, and for y, 0.9)
for each variable:
    if it's dominant root is greater than 1.0:
        it's asymptotic behavior is either \inf or -\inf depending on
        it's coefficient
    if it is less than 1.0:
        it's asymptotic behavior is towards 0.

So now, let's assume that we are approaching infinity in our formula,
and evaluate each expression accordingly.

Because y approaches 0 as n approaches infinity, y > -10 will be replaced with
True in the formula. We now have

True /\ (x < 29)

Now, looking at the next expression, because the asymptotic behavior of x is that
it approaches infinity, x < 29 is False.

True /\ False = False

(2.0(1.5)^n - 1.2(0.4)^n >= 29)

Thus, the closed forms proved the property cannot be proven, and the program exits.

If the property were instead that x > 29, we would find that

True /\ (x > 29) = True /\ True = True

Then, this means the property may hold for the system. It could be the case that
the initial value of x is 0, and so it immediately fails, but we're not worried
about checking those kinds of things at this step.
