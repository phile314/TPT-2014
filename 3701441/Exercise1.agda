module Exercise1 where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits. 

If you have any questions, don't hesitate to email me or ask in class.
-}


---------------------
------ Prelude ------
---------------------

data Bool : Set where
  True : Bool
  False : Bool

data Nat : Set where
  Zero : Nat 
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ k + m = Succ (k + m)

_*_ : Nat -> Nat -> Nat
Zero * n = Zero
(Succ k) * n = n + (k * n)

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a 0
  Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

head : {a : Set} {n : Nat}-> Vec a (Succ n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} -> Empty -> a
magic ()

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

data Fin : Nat -> Set where
  Fz : forall {n} -> Fin (Succ n)
  Fs : forall {n} -> Fin n -> Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a


----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero} x = Nil
pure {Succ n} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons f fs <*> Cons x xs = Cons (f x) (fs <*> xs)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m

-- Vector addition
vadd : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
vadd Nil Nil = Nil
vadd (Cons x xs) (Cons y ys) = Cons (x + y) (vadd xs ys)

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons xs xss) (Cons ys yss) = Cons ( vadd xs ys) (madd xss yss)  -- Using self-defined function for vector addition above

prefixWithZero : {n : Nat} -> Matrix Nat n n -> Matrix Nat (Succ n) n
prefixWithZero m = vmap (append (Cons Zero Nil)) m 

firstRow : (n : Nat) -> Vec Nat (Succ n)
firstRow n = Cons (Succ Zero) (pure {n} Zero)

idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
-- idMatrix {Succ n} can be defined  in terms of idMatrix {n} by:
--    1: Prefexing every inner vectors of idMatrix {n} by Zero. This is done by prefixWithZero
--    2: Prepending a vector of a single 1 followed by n 0's to the new matrix defined above
idMatrix {Succ n} = Cons (firstRow n) (prefixWithZero (idMatrix {n}))

appendVector : {n m : Nat} {a : Set} -> Vec a n -> Matrix a m n -> Matrix a (Succ m) n
appendVector Nil Nil = Nil
appendVector (Cons x xs) (Cons ys yss) = Cons (Cons x ys) (appendVector xs yss)

-- Define matrix transposition
-- Matrix transposition is defined by recursively appending the xth element of the first row to the xth row of that same matrix minus the first row transposed.
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = pure Nil
transpose (Cons x xs) = appendVector x (transpose xs)

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs (plan {n}))

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Succ Zero
forget (Fs fn) = Succ (forget fn)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs fn) = Fs (embed fn)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs fn) = cong Succ (correct fn)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

-- Show that there is a 'covering function'
cmp : (n m : Nat) -> Compare n m 
cmp Zero Zero = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k = LessThan k
cmp (Succ n) (Succ .n) | Equal = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k = Succ k
difference n .n | Equal = 0
difference .(m + Succ k) m | GreaterThan k = Succ k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation introduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)

plusCommutes n Zero = plusZero n
-- Goal: (n + Succ m) == Succ (m + n)
-- (n + Succ m) ==[plusSucc]==> Succ (n + m) ==[congruence]==> Succ (m +n) 
plusCommutes n (Succ m) = trans (sym (plusSucc n m)) (cong Succ (plusCommutes n m))

--timesZero : (n : Nat) -> (n * 0) == 0
--timesZero Zero = Refl
--timesZero (Succ n) = {!!}

--timesCommutes : (n m : Nat) -> (n * m) == (m * n)
--timesCommutes Zero m = {!!}
--timesCommutes (Succ n) m = {!!}

-- UNFINISHED!
distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) Zero Zero = {!!}
distributivity (Succ n) Zero (Succ k) = {!!}
distributivity (Succ n) (Succ m) k = {!!}

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {xs = Nil} = Base
SubListRefl {xs = Cons y ys} = Keep (SubListRefl {xs = ys})

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base Base = Base
SubListTrans Base (Drop b) = Drop b
SubListTrans (Keep a) (Keep b) = Keep (SubListTrans a b)
SubListTrans (Keep a) (Drop b) = Drop (SubListTrans (Keep a)  b)
SubListTrans (Drop a) (Keep b) = Drop (SubListTrans a b)
SubListTrans (Drop a) (Drop b) = Drop (SubListTrans (Drop a)  b)

contradiction : (a : Set) -> Empty
contradiction = {!!}

-- UNFINISHED!
SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym {xs = Nil} {Nil} slx sly = Refl
SubListAntiSym {xs = Nil} {Cons x ys} slx ()
SubListAntiSym {xs = Cons x xs} {Nil} () sly
SubListAntiSym {xs = Cons x xs} {Cons .x ys} (Keep slx) (Keep sly) with SubListAntiSym slx sly
SubListAntiSym {a} {Cons x xs} {Cons .x .xs} (Keep slx) (Keep sly) | Refl = Refl
SubListAntiSym {xs = Cons x xs} {Cons .x ys} (Keep slx) (Drop sly) = {!!}
SubListAntiSym {xs = Cons x xs} {Cons y ys} (Drop slx) sly = {!!}

---------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Base : forall {n} -> LEQ Zero n
  Step : forall {n m} -> LEQ n m -> LEQ (Succ n) (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base l2 = Base
leqTrans (Step l1) (Step l2) = Step (leqTrans l1 l2)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step l1) (Step l2) = cong Succ (leqAntiSym l1 l2)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= {Zero} {m} l = Refl
leq<= {Succ n} {Succ m} (Step l) = leq<= l

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m x = Base
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) x = Step (<=leq n m x) 

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP = \p f -> f p --?

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

\ ()  

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle = {!!} 

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.


doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...


step1 : doubleNegation -> excludedMiddle
step1 dn = {!!} 

step2 : excludedMiddle -> impliesToOr
step2 = {!!}

step3 : impliesToOr -> doubleNegation
step3  ito {P} h = {!!}

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

----------------------
----- Exercise 9 -----
----------------------

-- Here is a data type for 'Raw' lambda terms that have not yet
--   been type checked.

data Raw : Set where
  Lam : Raw -> Raw
  App : Raw -> Raw -> Raw
  Var : Nat -> Raw

-- The Agda tutorial shows how to define a type for the well-typed
--   lambda terms, and a type checker mapping Raw terms to well-typed
--   terms (or an error)
--
-- Adapt their development to instead restrict yourself to
-- 'scope checking' -- i.e. give a data type for the well-scoped
-- lambda terms and a function that maps a raw term to a well-scoped
-- lambda term.
--
-- This makes it possible to represent ill-typed terms such as (\x . x
-- x).
