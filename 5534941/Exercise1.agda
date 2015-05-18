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

tail : {a : Set} {n : Nat} -> Vec a (Succ n) -> Vec a n
tail (Cons x xs) = xs

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

-- Used info found here: http://en.wikibooks.org/wiki/Haskell/Applicative_Functors
-- vmap is same as tutorial.

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {n = Zero}    _ = Nil
pure {n = Succ _} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> _ = Nil
(Cons f fs) <*> (Cons x xs) = Cons (f x) (fs <*> xs)

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

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons x xs) (Cons y ys) = Cons ((vmap (_+_) x) <*> y) (madd xs ys)

-- Define the identity matrix
-- Take idMatrix of 1 smaller; prepend all rows in there with a zero; add a new row infront of those starting with 1.
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {n = Zero} = Nil
idMatrix {n = Succ n} = Cons (Cons 1 (pure 0)) (vmap (Cons 0) idMatrix)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {m = Zero} _ = Nil
transpose {n = Zero} _ = pure Nil
transpose {m = Succ _} c = Cons (vmap head c) (transpose (vmap tail c))
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {n = Zero}   = Nil
plan {n = Succ _} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz      = Zero
forget (Fs x) = Succ (forget x)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz      = Fz
embed (Fs x) = Fs (embed x)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs n) with forget (embed n) | correct n
... | .(forget n) | Refl = Refl

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
cmp Zero      Zero      = Equal
cmp Zero      (Succ y) = LessThan y
cmp (Succ x) Zero      = GreaterThan x
cmp (Succ x) (Succ y) with cmp x y
cmp (Succ .x)                   (Succ .x)                   | Equal {x} = Equal
cmp (Succ .x)                   (Succ .(x + Succ y)) | LessThan {x} y = LessThan y
cmp (Succ .(x + Succ y)) (Succ .x)                   | GreaterThan {x} y = GreaterThan y

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference x y with cmp x y
difference .x                   .x                   | Equal            {x}    = 0
difference .x                   .(x + Succ y) | LessThan      {x} y = y
difference .(x + Succ y) .x                   | GreaterThan {x} y = y

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

-- Taken from Tutorial section 2.6 (lem-plus-zero)
plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) with n + 0 | plusZero n
... | .n | Refl = Refl

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero       _       = Refl
plusSucc (Succ n) m with Succ (n + m) | plusSucc n m
... | .(n + Succ m) | Refl = Refl

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero = Refl
plusCommutes Zero (Succ m) with (m + 0) | plusCommutes Zero m
... | .(0 + m) | Refl    = Refl
plusCommutes (Succ n) m with (n + m) | plusCommutes n m
... | .(m + n) | Refl = plusSucc m n

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero _ _ = Refl
distributivity (Succ n) Zero Zero with ((n * 0) + (n * 0)) | distributivity n Zero Zero
...| .(n * 0) | Refl = Refl
distributivity (Succ n) Zero (Succ k) with ((n * 0) + (n * k)) | distributivity n Zero k
... | .(n * k) | Refl = {!!}
distributivity (Succ n) m k with ((n * m) + (n * k)) | distributivity n m k
... | .(n * (m + k)) | Refl = {!!}

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
SubListRefl {xs = Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base Base = Base
SubListTrans (Keep a) (Keep b) = Keep (SubListTrans a b)
SubListTrans (Drop a) (Keep b) = Drop (SubListTrans a b)
SubListTrans a (Drop b) = Drop (SubListTrans a b)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base Base = Refl
SubListAntiSym (Keep xs) (Keep ys) with SubListAntiSym xs ys
... | Refl = Refl
SubListAntiSym (Drop xs) (Keep ys) = {!!}
SubListAntiSym a (Drop b) = {!!}


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  LEQ-Zero : {n : Nat} -> LEQ Zero n
  LEQ-Succ : {m n : Nat} -> LEQ m n -> LEQ (Succ m) (Succ n)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = LEQ-Zero
leqRefl (Succ n) = LEQ-Succ (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans LEQ-Zero _ = LEQ-Zero
leqTrans (LEQ-Succ p) (LEQ-Succ q) = LEQ-Succ (leqTrans p q)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym LEQ-Zero LEQ-Zero = Refl
leqAntiSym (LEQ-Succ n) (LEQ-Succ m) with leqAntiSym n m
... | Refl = Refl

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= LEQ-Zero = Refl
leq<= {n = Succ n} {m = Succ m} (LEQ-Succ a) with n <= m | leq<= a
... | True | Refl = Refl

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero _ _ = LEQ-Zero
<=leq (Succ n) m p = {!!} 

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP p f = f p

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle f = f (Inr (\x -> f (Inl x))) 

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
step1 dn = dn ( \f -> f (Inr (\x -> f (Inl x)))) 

step2 : excludedMiddle -> impliesToOr
step2 em ito =  orCase (\f -> f) (\f -> Inl (\x -> f (Inr (ito x)))) em

step3 : impliesToOr -> doubleNegation
step3  ito {P} h = orCase {!!} {!!} {!!}

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
