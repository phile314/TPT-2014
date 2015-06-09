# Feedback

|Free point | Ex 1 | Ex 2 | Ex 3 | Ex 4 | Ex 5 | Ex 6 | Ex 7 | Ex 8 | Ex 9 | TOTAL |
|-----------|------|------|------|------|------|------|------|------|------|-------|
| 1         | 0.9  | 0.9  | 0.9  | 0.7  | 0.5  | 1    | 1    | 0.1  | 0.8  | 6.8   |
(rounded to ?)

#### Overall impression

I get a feeling that you don't really see the big picture. The technical stuff is ok, 
that's ok for now, but in this case I think it would have been more
efficient to think one step further and reuse the stuff you have
written above where you are working.


#### Exercise 1

The case for `pure {Succ Zero}` is redundant. A case for `{Succ n}` is sufficient.

0.9 points

#### Exercise 2

`madd`: Correct. You could have used the applicative instance though.
`createZeroes`: Also redundant (`pure 0`)
`takeHeads`, `takeTails`, `transpose`: These are all `vmap`s

0.9 point

#### Exercise 3

`forget`, `embed`: no need to match on `{n}`
Commented code... why? It is correct.

0.9 points

#### Exercise 4

Silly mistake

1 point

#### Exercise 5

plusSucc, plusCommutes: some redundant cases
You might generally want to try to remove similar cases, to see if that works

`Refl -- (Succ (b + a)) `: `Succ (b + a) \qed`

distributivity is unfinished

0.5 points

#### Exercise 6

The `SubListAntiSym (Drop a) (Drop b)` case yields no proof.
My solution had the same problem, because my version of agda did not tell me (2.3.2.2)

0.6 point


#### Exercise {7,8} LEQ

Would be spotless if you removed the commented code

1 point


#### Exercise {7,8} classical logic

This shows you have figured out C-c C-a

0.1 point

#### Exercise 9

The names are odd: `scooby`? You should prefer to use `f` for function

The code is a bit verbose, but easy to understand

0.8
