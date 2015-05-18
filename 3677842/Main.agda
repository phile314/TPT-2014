module Main where

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
0 + m = m
Succ k + m = Succ (k + m)

infixl 6 _+_

_*_ : Nat -> Nat -> Nat
0 * n = Zero
(Succ k) * n = n + (k * n)

infixl 7 _*_

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a 0
  Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

head : {a : Set} {n : Nat} -> Vec a (Succ n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a} {A : Set a} (x : A) : A -> Set a where
  Refl : x == x

infix 4 _==_

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
pure {0} _ = Nil
pure {Succ _} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons f fs <*> Cons y ys = Cons (f y) (fs <*> ys)

infixl 10 _<*>_

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap _ Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

-- Infix version of vmap
_<$>_ :  {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
_<$>_ = vmap

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m

-- Vector addition
vadd : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
vadd xs ys = _+_ <$> xs <*> ys

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd xs ys = vadd <$> xs <*> ys
 
-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {0} = Nil
idMatrix {Succ n} = Cons (Cons 1 (pure 0)) (Cons 0 <$> idMatrix)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = pure Nil
transpose (Cons x xs) = vmap Cons x <*> transpose xs

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {0} = Nil
plan {Succ n} = Cons Fz (vmap Fs plan)
 
-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz =  0
forget (Fs n) = Succ (forget n)
 
-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs n) = Fs (embed n)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs n) = cong Succ (correct n)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

cmp' : {n m : Nat} -> Compare n m -> Compare (Succ n) (Succ m)
cmp' (LessThan k) = LessThan k
cmp' Equal = Equal
cmp' (GreaterThan k) = GreaterThan k

-- Show that there is a 'covering function'
cmp : (n m : Nat) -> Compare n m
cmp 0 0 = Equal
cmp 0 (Succ m) = LessThan m
cmp (Succ n) 0 = GreaterThan n
cmp (Succ n) (Succ m) = cmp' (cmp n m)
 
-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m  with cmp n m
difference n .(n + Succ m) | LessThan m = m
difference .n n | Equal = 0
difference .(n + Succ m) n | GreaterThan m = m

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL Refl #-}


sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

plusZero : (n : Nat) -> n + 0 == n
plusZero 0 = Refl
plusZero (Succ n) rewrite plusZero n = Refl

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc 0 m = Refl
plusSucc (Succ n) m rewrite plusSucc n m = Refl

plusCommutes : (n m : Nat) -> n + m == m + n
plusCommutes 0 m rewrite plusZero m = Refl
plusCommutes (Succ n) m rewrite plusCommutes n m = plusSucc m n

plusAssoc : (n m k : Nat) -> n + (m + k) == n + m + k
plusAssoc 0 m k = Refl
plusAssoc (Succ n) m k rewrite plusAssoc n m k = Refl

multZero : (n : Nat) -> (n * 0) == 0
multZero 0 = Refl
multZero (Succ n) rewrite multZero n = Refl

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity 0 m k = Refl
distributivity (Succ x) y z rewrite distributivity x y z
   = {!!}
     
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
SubListRefl {xs = Cons _ _} = Keep SubListRefl

reduce : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList xs ys
reduce (Keep xs) = Drop xs
reduce (Drop xs) = Drop (reduce xs)

isEmpty : {a : Set} {xs ys : List a} {x : a} -> SubList (Cons x xs) ys -> SubList ys xs -> Empty
isEmpty (Keep xs) ys = isEmpty ys xs
isEmpty (Drop xs) ys = isEmpty xs (reduce ys)

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base ys = ys
SubListTrans (Keep xs) (Keep ys) = Keep (SubListTrans xs ys)
SubListTrans xs (Drop ys) = Drop (SubListTrans xs ys)
SubListTrans (Drop xs) (Keep ys) = Drop (SubListTrans xs ys)

SubListAntiSym : {a : Set} {xs ys : List a} -> SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base Base = Refl
SubListAntiSym (Keep xs) (Keep ys) = cong (Cons _) (SubListAntiSym xs ys)
SubListAntiSym (Keep xs) (Drop ys) = magic (isEmpty ys xs)
SubListAntiSym (Drop xs) ys = magic (isEmpty ys xs)

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
data LEQ : Nat -> Nat -> Set where
  Base : {n : Nat} -> LEQ Zero n
  Step : {n m : Nat} -> LEQ n m -> LEQ (Succ n) (Succ m)
 
-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl 0 =  Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base _ = Base
leqTrans (Step leq1) (Step leq2) = Step (leqTrans leq1 leq2)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step p) (Step q) = cong Succ (leqAntiSym p q)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y
-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= Base = Refl
leq<= (Step x) = leq<= x

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq 0  _ _ = Base
<=leq (Succ _) 0 ()
<=leq (Succ n) (Succ m) x = Step (<=leq n m x) 

----------------------
----- Exercise 8 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

_∘_ : {a b c : Set} -> (b -> c) -> (a -> b) -> (a -> c)
f ∘ g = \x -> f (g x)

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
notNotExcludedMiddle p = p (Inr (p ∘ Inl))

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
step1 dn = dn notNotExcludedMiddle

step2 : excludedMiddle -> impliesToOr
step2 em p->q = orCase (Inr ∘ p->q) Inl em

identity : {a : Set} -> a -> a
identity x = x

step3 : impliesToOr -> doubleNegation
step3 ito nnP = orCase (magic ∘ nnP) identity (ito identity)

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

pierces : impliesToOr -> piercesLaw
pierces ito pqp = orCase ({!!}) identity (ito pqp)
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

data RScope : Nat -> Set where
  Lam : {n : Nat} -> RScope (Succ n) -> RScope n
  App : {n : Nat} -> RScope n -> RScope n -> RScope n
  Var : {n : Nat} -> Fin n -> RScope n
