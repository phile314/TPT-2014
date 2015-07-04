# Feedback

| Part | 1 | 2 | 3 | 4 | 5 |
|------|---|---|---|---|---|
|      |0.5| 2 | 2 | 2 | 3 |

Total: 9.5

#### Exercise 2

2a looks great.

In 2b (and of course 2c), you used `ExpF t` at recursive positions instead of `t`. (One of) the main reason(s) for using this construct is that the recursion in your data type is handled by `Fix` and `fmap` and your `evalAlg` does not need to make recursive calls. Using `ExpF t` effectively disables this, making `t` a dummy type parameter: there are no *values* of type `t` in anywhere your data type. As a result, you can't apply `f` to anything in your `fmap` implementation, which makes your `fmap` just the identity function; of course this means it cannot be used in `evalAlg` either.

In 2d and 2e, you *do* use `Fix` (in this case `HFix`) as intended.

#### Exercises 4 and 5

Your implementations almost exactly match Wouter's.
