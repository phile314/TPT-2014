# Reflection
| Part | 0 | 1 | 2 | 3 |
|------|---|---|---|---|
|      | 1 | 3 | 3 | 3 |

Total: 10

#### Part 1 and 2

All holes are filled. In general, my solutions are very similar to Wouter's.

My constructor names in `Step` are not very descriptive.

We both chose to use "lifted values" directly in the constructors' types, which is not what Conor McBride recommends. This makes our implementations of `deterministic` more complex -- I used inline lemmas where Wouter defined `stepCoerce`, `pairInj`, `fst-step-lemma` and `snd-step-lemma`. Interestingly, my implementation of `⇓-sound` doesn't need sublemmas.

#### Part 3

There's not much that can go wrong here, at least if one manages to find the intricate (mutually) recursive calls and pick the right argument from the many arguments in scope in most holes. I didn't use `IsValue` at all: instead of the quite surprising `normal-values U` I used a separate inline lemma. (I later learned that there probably is something like a "pattern-matching lambda" in Agda...)
