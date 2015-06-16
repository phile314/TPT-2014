## Exercise 2a

- The small step rules for evaluating pairs are correct.
  I likw how you used the Is-Value predicate implicetely,
  but it causes some unsolved metas in your file.
  
- Reduction proof for `proj_r` is unfinished.

- Style points for the cong-map!

- Prepending steps is also unfinished.

- soundness and completness are a bit bigger than necessary. They typecheck nevertheless.

I would sugest using a bit more identation to fit your
code to the 80 column line. It's a bit har to read so 
many wrapped lines.

Filling the holes and extending the proofs: `2`.
Adding pairs to the language: `3`.

## Exercise 2b

- Your normalizable-step could have been made simpler by using
  transitivity of termination over steps. That is `Terminates c2 → Step c1 c2 → Terminates c1`,
  for `c2 , c1` Terms.
  
Still, the proof is there and it typechecks.
Exercise 2b mark: `2.7`.

## Final Mark

`2 + 3 + 2.7 + 1 = 8.7`
