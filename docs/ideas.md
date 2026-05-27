# Title

I'm getting this overwhelming idea that all systems should have some kind of closed form, even systems with saturation. Like, think of a PI controller with Saturation. Given the initial value of the system, it has an exact trajectory. It may not have a trajectory that could be reducible to an algebraic-exponential expression, but a closed form nonetheless. The question is not, then, whether there _is_ a closed form, but rather whether we can meaningfully express it algorithmically and in a way that our SMT solvers can work with effectively.

I like to think about things like how a simplified Pulse-Width Modulation (PWM) system could be implemented in C. In this case, you are basically having a value either be set to 0 or 1 depending on whether it is passed a specified value. Here, this is what it could look like:

```C
void pwm_step(struct pwm_param& x)
{
    x->step++;
    if(x->step > x->max_step){
        x->step=0;
    }

    if(x->step < x->drop){
        x->curr = 1;
    } else {
        x->curr = 0;
    }
}

```

Imagine that this function is called indefinitely, this isn't a terrible way of making sense of a PWM. In actuality, even if the variables max_step and drop can vary as the program is progressing, there is an exact closed form. In this case, the variable `n` does not have an exact correlation between the index of the loop, it holds a value such as "how many steps after doing something", which is distinct from what we have been interested in, but it could still be adjusted if we support something like "this value could be either 0 or 1, and it is undetermined", since there could be systems where you may want to force it to reset. But for the regular conditional, that is as simple as stating something akin to this (assuming the new definition of n):

```c
(= x (ite (< n drop) 1 0))
```

Because really, it is two closed forms merged into one. I would be interested to see if I can add an auxiliary variable that would make it so that I could write the above closed form using the actual index, but the auxiliary variable shifts in specific instances.

If I had to solve the problem right this moment, this would be my idea. This would not be directly supported by Polar, but if I could split this into a PWA system, I could find a closed form for each cell. I am _sure_ there are ways to complete this PWA task. Then, we get closed forms for each of the cells. We then come back here and state that when the condition is met, then the closed form is met, and if the other condition is met, then the other one is met. We don't deliver the conditionals to Polar, we shouldn't have to. Now, I can imagine almost we have a true index and then a counter, and we have an expression in our invariant like `i=(n % max)`, where everything is a variable.
