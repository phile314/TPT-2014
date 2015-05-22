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
Zero * n  = 0
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
pure {0} x = Nil
pure {Succ n} x = Cons x (pure {n} x)

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

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd xss yss = vmap (λ xs ys → vmap _+_ xs <*> ys) xss <*> yss

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {0} = Nil
idMatrix {Succ n} = Cons (Cons 1 (pure 0))  (vmap (Cons 0) idMatrix)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = pure Nil
transpose (Cons xs xss) = vmap Cons xs <*> transpose xss
  
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
forget Fz = 0
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

-- Show that there is a 'covering function'
cmp : (n m : Nat) -> Compare n m 
cmp 0 0 = Equal
cmp (Succ n) 0 = GreaterThan n
cmp 0 (Succ n) = LessThan n
cmp (Succ n) (Succ m) = f (cmp n m)
  where
  f :{n m : Nat} ->  Compare n m -> Compare (Succ n) (Succ m)
  f Equal = Equal
  f (LessThan k) = (LessThan k)
  f (GreaterThan k) = (GreaterThan k)

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m = f (cmp n m)
  where
  f :{n m : Nat} ->  Compare n m -> Nat
  f Equal = 0
  f (LessThan k) = Succ k
  f (GreaterThan k) = Succ k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

plusZero : (n : Nat) -> (n + Zero) == n
plusZero 0 = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc 0 m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes 0 0 = Refl
plusCommutes (Succ n) 0 = plusZero (Succ n)
plusCommutes 0 (Succ m) = sym (plusZero (Succ m))
plusCommutes (Succ n) (Succ m) = trans (sym (plusSucc (Succ n) m)) (cong Succ (plusCommutes (Succ n) m))

-- We prove associativity as a lemma for proving distributivity
associativity : (n m k : Nat) -> ((n + m) + k) == (n + (m + k))
associativity Zero m k = Refl
associativity (Succ n) m k = cong Succ (associativity n m k)

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity 0 m k = Refl
distributivity (Succ n) m k = trans (cong (_+_ (m + k)) (distributivity n m k)) (sym (lemma n m k))
  where
  lemma : (n m k : Nat) -> ((Succ n * m) + (Succ n * k)) == ((m + k) + ((n * m) + (n * k)))
  lemma n m k = trans Refl (lemma2 m k (n * m) (n * k))
    where
    lemma2 : (n m i j : Nat) -> ((n + i) + (m + j)) == ((n + m) + (i + j))
    -- Just use commutattivity and distributivity a few times to prove this
    lemma2 n m i j = trans (trans (trans (associativity n i (m + j)) (cong (_+_ n) (cong (_+_ i) (plusCommutes m j)))) (cong (_+_ n) (trans (sym (associativity i j m)) (plusCommutes (i + j) m)))) (sym (associativity n m (i + j)))



----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {a} {Nil} = Base
SubListRefl {a} {Cons x xs} = Keep (SubListRefl)

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans sl Base = sl
SubListTrans (Keep sl1) (Keep sl2) = Keep (SubListTrans sl1 sl2)
SubListTrans (Drop sl1) (Keep sl2) = Drop (SubListTrans sl1 sl2)
SubListTrans sl1 (Drop sl2) = Drop (SubListTrans sl1 sl2)

largerNoSubList : {a : Set} {x : a} {xs : List a} -> SubList (Cons x xs) xs -> Empty
largerNoSubList {a} {x} {Nil} ()
largerNoSubList {a} {.y} {Cons y ys} (Keep sl) = largerNoSubList sl
largerNoSubList {a} {x} {Cons y ys} (Drop sl) = largerNoSubList (destructiveDrop sl)
  where
  -- Drops the first element of the suplist, rather than adding an element to the superlist
  destructiveDrop : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList xs ys
  destructiveDrop (Keep sl) = Drop sl
  destructiveDrop (Drop sl) = Drop (destructiveDrop sl)

-- In the case that one list is longer than the other, we prove a contradiction
contradictionLemma : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList ys xs -> Empty
contradictionLemma sl1 sl2 with SubListTrans sl1 sl2
contradictionLemma sl1 sl2 | sl = largerNoSubList sl

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base sl2 = Refl
SubListAntiSym (Keep {x} sl1) (Keep {.x} sl2) = cong (Cons x) (SubListAntiSym sl1 sl2)
SubListAntiSym (Keep sl1) (Drop sl2) = magic (contradictionLemma sl2 sl1)
SubListAntiSym (Drop sl1) sl2 = magic (contradictionLemma sl2 sl1)

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  LEQBase : forall {n : Nat} -> LEQ 0 n
  LEQStep : forall {n m : Nat} -> LEQ n m -> LEQ (Succ n) (Succ m)

leqRefl : (n : Nat) -> LEQ n n
leqRefl 0 = LEQBase
leqRefl (Succ n) = LEQStep (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans LEQBase leq = LEQBase
leqTrans (LEQStep leq1) (LEQStep leq2) = LEQStep (leqTrans leq1 leq2)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym LEQBase LEQBase = Refl
leqAntiSym (LEQStep leq1) (LEQStep leq2) = cong Succ (leqAntiSym leq1 leq2)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= LEQBase = Refl
leq<= (LEQStep leq) = leq<= leq

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m r = LEQBase
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) r = LEQStep (<=leq n m r)

----------------------
----- Exercise 8 -----
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
notNotExcludedMiddle f = f (Inr (λ x -> f (Inl x)))

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.


doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...

flipOr : {a b : Set} -> Or a b -> Or b a
flipOr (Inl x) = Inr x
flipOr (Inr x) = Inl x

id : {a : Set} -> a -> a
id x = x

mapOr : {a b c d : Set} -> (a -> c) -> (b -> d) -> Or a b -> Or c d
mapOr f g (Inl x) = Inl (f x)
mapOr f g (Inr x) = Inr (g x)

step1 : doubleNegation -> excludedMiddle
step1 dn = dn notNotExcludedMiddle

step2 : excludedMiddle -> impliesToOr
step2 em f = flipOr (mapOr f id em)

step3 : impliesToOr -> doubleNegation
step3 ito h = orCase (λ x -> magic (h x)) id (ito id)

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

--We prove it to be equivalent to doubleNegation, one direction is easy
step4 : piercesLaw -> doubleNegation
step4 pl f = pl (λ x -> magic (f x))

--For the other direction we use a lemma and the fact tha dn is equivalent to em
step5 : doubleNegation -> piercesLaw
step5 dn f = orCase id (lemma f) em
  where
  lemma : {P Q : Set} -> ((P -> Q) -> P) ->  Not P -> P
  lemma f np =  f ((λ p -> magic (np p)))
  em : excludedMiddle
  em = step1 dn

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


-- Some necessary functions:
reduce : Nat -> Nat
reduce 0 = 0
reduce (Succ n) = n

max : Nat -> Nat -> Nat
max n 0 = n
max 0 m = m
max (Succ n) (Succ m) = Succ (max n m)

-- fmap and apply for Maybe
_<$>_ : {a b : Set} -> (a -> b) -> (Maybe a) -> Maybe b
f <$> Just x = Just (f x)
f <$> Nothing = Nothing

_<**>_ : {a b : Set} -> Maybe (a -> b) -> (Maybe a) -> Maybe b
Just f <**> Just x = Just (f x)
mb <**> Nothing = Nothing
Nothing <**> mb = Nothing

-- maybe prove two nats are equal
eq : (n : Nat) -> (m : Nat) -> Maybe (n == m)
eq 0 0 = Just Refl
eq (Succ n) 0 = Nothing
eq 0 (Succ m) = Nothing
eq (Succ n) (Succ m) = cong Succ <$> eq n m

-- We implement well-scoped terms by keeping track of the least scope depth required
data Term : Nat -> Set where
  Lam : {n : Nat} -> Term  n -> Term (reduce n)            -- We may reduce n by one, but if n is zero already that's also good
  App : {n m : Nat} -> Term n -> Term m -> Term (max n m)  -- We need at least n and and least m lambdas, so we take the maximum of n and m
  Var : (n : Nat) -> Term n                                -- At least n more lambdas needed

-- A term is well-scoped if it doesn't need anymore lambdas to bind variables to
WellScoped = Term 0

-- The function that creates WellScoped from Raw if possible
checkScope : Raw -> Maybe WellScoped
checkScope = toTerm
  where
  toTerm : {n : Nat} -> Raw -> Maybe (Term n)
  toTerm (Lam r) = Lam <$> (toTerm r)
  toTerm (App r1 r2) = (App <$> (toTerm r1)) <**> (toTerm r2)
  toTerm {n} (Var m) with eq n m
  toTerm (Var m) | Just Refl = Just (Var m)
  toTerm (Var m) | Nothing = Nothing
