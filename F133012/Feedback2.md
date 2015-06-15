## 2a: Fill in the holes ##
All holes are implemented correctly
## 3 points ##

## 2a: Pairs ##
+ Nice use of <_,_> and product type.
+ Nice use of BUILTIN EQUALITY and it's use for rewrite.
- Prepend step is overly complicated; but still correct

Hint use something like, safes you a lot of work:
prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v

prepend-step E-If-True b = E-If-True E-True b

prepend-step E-If-False b = E-If-False E-False b

prepend-step (E-If-If s) (E-If-True b bs) = E-If-True (prepend-step s b) bs

prepend-step (E-If-If s) (E-If-False b bs) = E-If-False (prepend-step s b) bs

## 3 points ##

## 2b: Fill in the holes ##
Seems to be fully correct as well
## 3 points ##

Good job!
