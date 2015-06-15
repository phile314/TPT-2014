# Feedback

| Part | 0 | 1 | 2 | 3 |
|------|---|---|---|---|
|      | 1 |1.5| 1 | 1 |

Total: 4.5

#### Part 1

Your big-step semantics look great. `big-to-small` is missing some cases, but `prepend-step` and `small-to-big` work fine. `⇓-complete` and `⇓-sound` are not implemented; unfortunately, those two are the ones that need the more complex proofs.

#### Part 2

The small-step rules you created almost exactly match those in the solution. The only difference is that you extracted equalities to hold information about terms being values. Wouter puts this information directly into the constructors' types. (What you did should make some of the lemmas easier to prove/more elegant.)

Unfortunately, most of the proofs have holes related to tuples.

Your big-step semantics do not have any rules for evaluating tuples.

#### Part 3

The only filled holes were `normalizableStep` and `normalizableSteps`.
