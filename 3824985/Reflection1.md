# Reflection

| Exercise | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|----------|---|---|---|---|---|---|---|---|---|---|
|          | 1 | 1 |0.7| 1 | 1 | 1 | 1 | 1 |1.2| 1 |

Total: 9.9, 0.5-rounded to 10

In general, my solutions did not differ significantly from Wouters'.

#### `idMatrix`

My `idMatrix` is clearly completely wrong: the only correct thing about it is the size of the resulting matrix (unfortunately the only thing required by the type signature).

#### `transpose`

Wouter's solution is prettier.

#### `SubListAntiSym`

Wouter and I chose to prove that all cases other than Keep-Keep are impossible, which requires some additional lemmas. It looks like some students managed to prove all cases recursively - interesting...

#### Exercise 8

I added the 0.2 bonus points for the proofs about Peirce's Law. They're not very readable, but Agda says they work.

#### Exercise 9

Wouter's use of (what comes down to) the Maybe applicative is more compact and nicer than my `infer`. On the other hand, he appears not to have defined anything like `erase`, a construct that helps to confirm the output is really a scoped version of the input.
