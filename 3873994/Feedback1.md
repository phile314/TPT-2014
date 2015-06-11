# Feedback

| Exercise | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|----------|---|---|---|---|---|---|---|---|---|---|
|          | 1 | 1 | 1 | 1 | 1 |0.8| 1 | 1 |0.6| 1 |

Total: 9.4, 0.5-rounded to 9.5

Most of the exercises were solved in the same (or similar) way as in Wouters' solutions.

#### Exercise 5

Your solution for `distributivity` contains a high number - apparently 98 - of "yellow problems" (unsolved meta-variables), at least according to my version of Agda (2.4.2.2). "Yellow problems" can simply mean there's more than one candidate and Agda is too lazy to search for the right one, but as https://www.cl.cam.ac.uk/teaching/1112/L108/agda/colours.agda shows, it can also mean that the proof is incorrect and cannot be corrected.

I therefore set to work providing explicit values for implicit arguments to fix the "yellow problems". Almost all of them were caused by applications of `+-substitute-right_by_`. The problem on line 391 couldn't be solved just by providing values because `n * Zero != (n * Zero) + 0`. `+-substitute-left_by_` worked. The same problem presented itself on line 408; there I had to add a `plusZero` step.

All in all, your solution was almost completely correct (the only exception was where `plusZero` was needed).

#### Exercise 8

In `step1`, you proved `{P : Set} -> Not (Not P) -> P -> Or P (Not P)` instead of `{P : Set} -> (Not (Not P) -> P) -> Or P (Not P)`, which is a little harder to prove. `step3` still has a hole.
