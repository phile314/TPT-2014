# Feedback

|Free point | Ex 1 | Ex 2 | Ex 3 | Ex 4 | Ex 5 | Ex 6 | Ex 7 | Ex 8 | Ex 9 | TOTAL |
|-----------|------|------|------|------|------|------|------|------|------|-------|
| 1         | 1    | 1    | 1    | 1    | 1    | 0.6  | 1    | 1    | 1    | 9.6   |
(rounded to 9.5)

Overall impression: the code is nice and there were some elegant / non-standard solutions, but the code definitely needs more comments. Sometimes, it is impossible to tell what exactly is going on and what the underlying concepts are (e.g. why some helper functions are useful, what they are meant to do exactly, etc). It could also help to choose variable names in a more consistent way (e.g. use `xs`/`ys` for lists, `f`/`g` for functions, `fs`/`gs` for lists of functions, etc.)

####Exercise 1
1.0/1.0

####Exercise 2
1.0/1.0
* If you want to use the `+` function as an argument for other functions, you can refer to it as `_+_` (no need to define a separate `plus` function for this)
* The extra `append` in the `idMatrix` definition is superfluous (instead of `append`, you could have put the second argument in the place of `Nil`)

####Exercise 3
1.0/1.0

####Exercise 4
1.0/1.0
* A separate `cmp->nat` function was not needed (you could have used the `with` keyword)

####Exercise 5
1.0/1.0
* `plusCommutes` was longer than necessary because of overenthousiastic pattern matching.

####Exercise 6
0.6/1.0
* Termination checking failed for SubListAntiSym (-0.4 points). This is due to the final case; observe that in this case, you have to prove the something strange: `x:xs` is a sublist of `ys`, but simultaneously `y:ys` is a sublist of `xs`. This would imply that `y:x:xs` is a sublist of `xs`, which is impossible. For this case, an auxiliary lemma stating that any `z:zs` can never be a sublist of `zs` would have been helpful to help Agda infer that there is no possible pattern to satisfy this case.

####Exercise 7
1.0/1.0
* Overly complicated, but correct. Your life would have been somewhat easier if you had made the `(n : Nat)` and `(n m : Nat)` arguments optional in your definition of `LEQ`.
* Your definition of `LEQ` is completely correct, but the solution provided in the example solution set would have made for shorter proofs / function definitions later on. The advantage of that other definition is that you don't need the `leqWeaken` and `leqDecr` functions in order to transform the proof to a proof for smaller numbers (it's already in there), and the proof for `leqAntiSym` would become less complicated. It is also structurally more similar to the `_<=_` function

####Exercise 8
1.0/1.0
* In `step1`, observe that most of your function defintion is identical to `notNotExcludedMiddle`. I would have been possible to reuse that proof.
* Some more comments/explanation as to what is going on might be useful in order to help me understand what you did, and convince me that this really is your own work (especially since you are inconsistent in your notation).

####Exercise 9
1.0/1.0
* Again, comments please! I cannot completely see what is going on (why do you need the `Inspect` data type? What do all those different cases in `checkScope` do? etc etc)
