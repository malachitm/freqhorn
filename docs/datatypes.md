# Feature: new data types

Here are ideas for trying to implement new data types into the system.

The easiest would be integers, since it would just have to ensure that I do not assume that the types are Reals, and then it should be straightforward from there. Though I will say that I am unsure how Polar supports things like modulo operations and integer division.

For Boolean types, I would need to convert normal boolean operations into a boolean algebra, negation of x becomes 1-x, so on.

For floating points and bit-vectors, this will be more involved. This would require needing to make sure that we handle drift not just from roots but also from basic arithmetic, such as adding 1 to a floating point number. This could be addressed by using 1^n as a genuine root that morphs over time compared to previous implementations that just keep staying the same. I will also need to find a way to address things like Max and Min in this system, which I first thought could be address using a modulo operator that would involve both the minimum and the maximum. I may just need to find a method that would check if the system will inevitably overflow, and if so it treats it as a bug. This is easy for something like an infinite loop, since the roots will tell you everything you need to know. But for a system that could exit before overflowing, it would need to be determined what the max and min values are for that system before said system.

When it comes to supporting mixed data types, we may be able to just remove the assignment types, or do it in a particular way that I'm unaware of right now. It might be worth it to not think about that right now.
