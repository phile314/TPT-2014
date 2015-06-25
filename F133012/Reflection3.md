Exercise 1 and 2
================

My solutions are very close to the sugested solutions.
I prefered to stick with monadic code. I assign
myself `0.5 + 2.5` here.

Exercise 3
==========

My implementation of `children` is also correct.
Mark: `2`

Exercise 4
==========

I had a radically different approach here. By definition, the parents
are the subexpressions with a non-empty list of children. I went through
that path instead of defining the `Subelems` typeclass.

I have just tested my code with the `example5` given in the solutions, and it passed.
I noticed the subtle difference from `Children R.I` to `Subelems R.I`, but
in my function this is done by recursively calling parents on the non-empty
children list just returned. In case it's an `R.I r`, we will add `r` to the head
and call the parents in those children. I believe it is the same but I did not prove this.
On this note, I'll mark it with `1.75`, as I might have a slightly different parents function.

Exercise 5
==========

I see where I went wrong in the fixpoint proofs. Besides not being able to finish it, the
signature of my `from\muRegular` and `to\muRegular` are wrong. I will assign myself `1.75` here.

Final Mark
==========

`0.5 + 2.5 + 2 + 1.75 + 1.75 = 8.5`
