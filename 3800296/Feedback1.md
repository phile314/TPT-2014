# Feedback 3800296

## Changes made to the program to make it compile:
- Termination failed for `SubListAntiSym`, commented it out.
- Syntax errors on the proofs (Agda 2.4.3 git version). The operator parsing changed. The solution was to define precedences for all operators:

```
infixr 4 _+_
infixr 5 _*_
```


Thanks Agda.
```
Could not parse the application
n + Succ m ⟨ sym (plusSucc n m) ⟩ Succ (n + m) ⟨ cong Succ
(plusCommutes n m) ⟩ Succ m + n □
Operators used in the grammar:
  +     (infix operator, unrelated)           [_+_ (/home/falco/Documents/uni/tpt/TPT-2014/3800296/Exercise1.agda:27,1-4)]   
  _+    (prefix operator section, unrelated)  [_+_ (/home/falco/Documents/uni/tpt/TPT-2014/3800296/Exercise1.agda:27,1-4)]   
  +_    (postfix operator section, unrelated) [_+_ (/home/falco/Documents/uni/tpt/TPT-2014/3800296/Exercise1.agda:27,1-4)]   
  □     (postfix operator, level 3)           [_□ (/home/falco/Documents/uni/tpt/TPT-2014/3800296/Exercise1.agda:207,1-3)]   
  ⟨_⟩   (infixr operator, level 2)            [_⟨_⟩_ (/home/falco/Documents/uni/tpt/TPT-2014/3800296/Exercise1.agda:203,1-6)]
  _⟨_⟩  (prefix operator section, unrelated)  [_⟨_⟩_ (/home/falco/Documents/uni/tpt/TPT-2014/3800296/Exercise1.agda:203,1-6)]
  ⟨_⟩_  (postfix operator section, unrelated) [_⟨_⟩_ (/home/falco/Documents/uni/tpt/TPT-2014/3800296/Exercise1.agda:203,1-6)]
  _⟨_⟩_ (closed operator section)             [_⟨_⟩_ (/home/falco/Documents/uni/tpt/TPT-2014/3800296/Exercise1.agda:203,1-6)]
(the treatment of operators has changed, so code that used to parse
may have to be changed)
when scope checking
n + Succ m ⟨ sym (plusSucc n m) ⟩ Succ (n + m) ⟨ cong Succ
(plusCommutes n m) ⟩ Succ m + n □
```


## Exercise 1
Correct

## Exercise 2
I like the vzip and vreplicate solutions.
Correct

## Exercise 3
That's what I had too! Nice work.
Correct.

## Exercise 4
Nice one noting that one needs to be added in the difference function.
Correct


## Exercise 5
Besides the fact that it doesn't compile immediately, the ⟨ ⟩ stuff *IS* super fancy.
Everything is correct.

## Exercise 6
SubListAntiSym doesn't have its recursive case properly defined. 
-0.2

## Exercise 7
Nicely done.

## Exercise 8
You got slightly further than I did, still holes in step3 and piercesLaw.
Is piercesLaw even mandatory?
-0.2

## Exercise 9:
Not made. 
-1
