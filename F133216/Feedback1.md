## Exercise 1

The `pure` function is unfinished, however, `consn` is pretty much `pure` in disguise. The others two are fairly standard.

> 0.7

## Exercise 2

Defining `madd` by using a helper vector addition is fair. Yet, this
vector adition is expecting an unused implicit parameter `m`, which
is triggering `unresolved-metas`. 

`idMatrix` and `transpose` are undefined.

> 0.3

## Exercise 3

`plan` is the only defined function. It is indeed correct. The attempt
of converting a `n : Nat` to a `Fin n` is not correct. The proper signature
should be `(n : Nat) -> Fin (suc n)`, since the type `Fin Zero` is
 uninhabited. 

> 0.1

## Exercise 4

The `cmp` function was left as a hole. The `difference` implementation
shows a careless use of `C-c C-a`, or a careless reading of the description...

> 0

## Exercise 5

`plusSucc` and `plusCommutes` are correct. `plusZero` is asking for an implicit
parameter for `dis`.

`SuccEq` could have been spoted as being `cong Succ`. 

`distributivity` was left unproved.

> 0.5

## Exercise 6

No answers whatsoever.

> 0

## Exercise 7

If the `LEQ` datatype is not defined, then it is obvious we will find
contradictions. I can only assume that `C-c C-a` was the weapon of choice here,
prior to defining `LEQ`.

The `_<=_` is correct.

> 0.1

## Exercise 8

Same as above. No consistent answers, just some `C-c C-a` around.

> 0

## Exercise 9

Blank.

> 0

## Final Grade

I assess the final grade for `F133216` as `1 + 0.7 + 0.3 + 0.1 + 0 + 0.5 + 0 + 0.1 + 0 + 0 = 2.7`


## Notes

The file `homework.agda`, as is, do not typecheck. 
There is a repeated variable in line 163.


