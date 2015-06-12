# Reflection Exercise 2

```
3
2.4
2.5
1
--- +
8.9

```


# Part 1
I've managed to fill in all holes for all functions (without tuple). 3 points.

# Part 2

The answers have some minor differences in the handling of fst and snd steps, that might have made it easier for me (The answer creates a step that looks like this: `Step (fst ⌜ vpair v v' ⌝) ⌜ v ⌝`, while mine looks like this: `Step (fst (tuple ⌜ l ⌝ ⌜ r ⌝)) ⌜ l ⌝`). My definition is not *wrong*, but it is harder to prove.

But hey I understood that the left side of the tuple must be fully evaluated before the right side is (or the other way around) because determinism cannot be proven otherwise.

I thought my definition of determinism was bad, but it's not *that* bad considering. That said I still have some holes.

Achievement unlocked: My termination proof is shorter than that of the teacher.

I still have some holes in prepend-step with tuples.


** Minus 0.6 for holes in deterministic and prepend-step. **

2.4 points

# Part 3
The separation between function types and their definitions in the answers are slightly confusing. That said it looks like I took a different approach with most functions, but got pretty much everything except for `closure-normalization`. That one was difficult. -0.5

2.5 points
