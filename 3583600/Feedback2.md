# Feedback

|Free point | Ex 2a1 | Ex 2a2 | Ex 2b | TOTAL |
|-----------|--------|--------|-------|-------|
| 1         | 3      | 0.5    | 2     | 6.5   |

####Exercise 2a1 (big-step semantics)
3.0/3.0
In some cases the pattern matching could have been done in a different order, which would have resulted in smaller function definitions.
(For example in ``\downarrow-complete``)

####Exercise 2a2 (adding pairs)
0.5/3.0
* In the data type Step, the constructors for the pairs are not working conceptually. For example, there is no constructor that can take a step starting at ``fst (if true true true, true)``.
* This results in some function definitions being oversimplified (e.g. ``valuesDoNotStep``), while other proofs turned out to be impossible (e.g. ``fst-reduces``). 
* In general, a lot of holes have not been filled in.

####Exercise 2b 
2.0/3.0
* Again, some overenthousiastic pattern-matching, but not technically incorrect.
* Some of the main functions were not filled in.
