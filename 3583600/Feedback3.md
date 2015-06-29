Exercise 1
==========

Kinds are all correct!

Mark: `0.5`

Exercise 2
==========

a)
> Implementation of `eval` is correct. Some monads here and there could
> help. Note that you inlined the definition of `_>>=_` for the Maybe monad
> in your code.
Mark: `0.4`

b)
> Correct!
Mark: `0.5`

c)
> Your `evalAlg` is missing a few cases. One easy way to fix it is
> to append another line: `evalAlg _ = Nothing`, which maps every
> ExpF element with a Nothing inside to Nothing itself.
> This is rather important, as Haskell will break at run-time if
> you ask for the evaluation of a non-well-formed term. For instance,
> 
>     *TPTGeneric> let n = TPTGeneric.In (IntF 45)
>     *TPTGeneric> let m = TPTGeneric.In (BoolF False)
>     *TPTGeneric> let break = TPTGeneric.In (GTF n m)
>     *TPTGeneric> :t break
>        break :: Fix ExpF
>     *TPTGeneric> eval' break
>     *** Exception: generic.lhs:(89,1)-(94,57): Non-exhaustive patterns in 
>                    function evalAlg
> 
Mark: `0.3`


d)
> Your definition is correct, and the example is also correct.
Mark: `0.5`

e)
> Your `evalT'` and `ExpTF` are correct!
Mark: `0.5`

Exercise 3
==========

The correct typeclass was identified by you and your instances are correct.
Mark: `2`

Exercise 4
==========

Your solution is very close to the proposed solution by Johan. You are not
eliminating duplicates nor empty lists. Take into account that
the parents are those who have children, that is, a sub-expression `x`
of `y` should be in `parents y` whenever `children x /= []`.
I don't quite get the use of `init` there.

Mark: `1.5` 

Exercise 5
==========

Unavailable. :(
Mark: `0`

Final Mark
==========

`0.5 + 0.4 + 0.5 + 0.3 + 0.5 + 0.5 + 2 + 1.5 + 0 = 6.2`

