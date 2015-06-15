## I. filling in the holes in the initial exercise 2a

All holes filled. Looks good. **3/3 points**.

## II. adding pairs, fst and snd and extending the proofs

 *  Pair was added to the available types, terms and values, although it is unclear why there is an extra `Pair` datatype.
 *  Everything looks good up to the evaluation.
 *  You have noted yourself that you are unsure of your small-step semantics. You are correct in your assumption. Check Pierce's book "Type Systems for Programming Languages" on page 126 (figure 11-5).
   *  Your `E-Fst` and `E-Snd` rules are wrong, they allow to step any expression `fst t` to any other term `t'`. You need to specify the form of `t` more precisely. The book chooses to force the evaluation of `fst` and `snd` to work only on pairs of values, otherwise known as totally reduced terms. These are the *E-Proj1* and *E-Proj2* rules.
   *  Your `E-Pair-Fst` and `E-Pair-Snd` rules are not deterministic. You could reduce a given pair on the first element first, and on the second element after. The other way around is also possible. In order to fix this, you need to be more specific about the form of your pair term. The book chooses to only allow the second rule to work if the first element of the pair is totally reduced. These are the *E-Pair1* and *E-Pair2* rules.
   *  You are missing two rules from the book, namely the projection rules. With these rules, you wouldn't be able to reduce a term akin to `fst (if true then (1, 2) else (3, 4))`, because you don't have a rule that can reduce the argument of `fst`.

 * You have trouble proving determinism, progress and termination. This makes sense due to the chosen rules. Still, you have managed to fill a few of the holes.
 * You have similar trouble with your big step semantics, as indicated by yourself.

**1/3 points** for the completed parts.

## III. completing the termination proof of the simply typed lambda calculus

 * Almost finished the `normalizableStep` proof.
 * Good attempt at `closure-normalization`.

Most of the work is done. **2.5/3 points**.

## Adjusted total:

3 + 1 + 2.5 + 1 = **7.5**
