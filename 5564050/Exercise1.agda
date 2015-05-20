module Exercise1 where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits. 

If you have any questions, don't hesitate to email me or ask in class.

Olli Linna - 5564050
Exercises discussed (but not shared) with Rick Klomp
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
{-# BUILTIN ZERO Zero #-}
{-# BUILTIN SUC Succ #-}

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
pure {Zero} o            = Nil
pure {Succ Zero} o       = Cons o Nil
pure {Succ (Succ n)} o   = Cons o (pure o)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> a                = Nil
Cons f xs <*> Cons x xs' = Cons (f x) (xs <*> xs')

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil               = Nil
vmap f (Cons x v)        = Cons (f x) (vmap f v)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m 

-- Define matrix addition 
vadd : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
vadd a b = vmap _+_ a <*> b

madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n                     
-- madd a b = vmap vadd a <*> b -- should be tested
madd Nil b = b
madd (Cons xs xss) (Cons ys yss) = Cons (vadd xs ys) (madd xss yss)

isEq : (a b : Nat) -> Bool
isEq Zero Zero         = True
isEq Zero (Succ b)     = False
isEq (Succ a) Zero     = False
isEq (Succ a) (Succ b) = isEq a b

-- Define the identity matrix
-- idVector returns a vector of length n, where indices are 1 when n == m, otherwise 0
idVector : (n m : Nat) -> Vec Nat n
idVector Zero _             = Nil
idVector (Succ n) m with (isEq (Succ n) m)
idVector (Succ n) m | True  = Cons (Succ Zero) (idVector n m)
idVector (Succ n) m | False = Cons 0 (idVector n m) 

-- auxillary function for defining the identity matrix
idm : (n m : Nat) -> Matrix Nat n m
idm n Zero     = Nil
idm n (Succ m) = Cons (idVector n (Succ m)) (idm n m)

idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero}   = Nil
idMatrix {Succ n} = idm (Succ n) (Succ n)

-- Define matrix transposition
tail : {n : Nat}{a : Set} -> Vec a (Succ n) -> Vec a n
tail (Cons x Nil)                = Nil
tail (Cons x (Cons x' v))        = Cons x' v

transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {Zero}   {m} Nil       = pure {m} Nil
transpose (Cons Nil mas)         = Nil
transpose (Cons (Cons x ma) mas) = Cons (Cons x (vmap head mas)) (transpose (Cons ma (vmap tail mas))) 

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero}   = Nil
plan {Succ n} = Cons (Fz {n}) (pure Fs <*> plan {n})

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz      = Zero
forget (Fs fn) = Succ (forget fn)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed {Zero} ()
embed {Succ n} Fz      = Fz {Succ n}
embed {Succ n} (Fs fn) = Fs {Succ n} (embed fn)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct {Zero} ()
correct {Succ n} Fz     = Refl
correct {Succ n} (Fs i) = cong Succ (correct i)

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
cmp Zero Zero     = Equal
cmp Zero (Succ m) = LessThan {Zero} m
cmp (Succ n) Zero = GreaterThan {Zero} n
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k    = LessThan k
cmp (Succ .m) (Succ m)            | Equal         = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k    = Succ k
difference .m m | Equal                    = 0
difference .(m + Succ k) m | GreaterThan k = Succ k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

-- From Demo
infixr 2 _<_>_
_<_>_ : (x : Nat) -> {y z : Nat} -> (x == y) -> (y == z) -> x == z
x < p > q = trans p q

_■ : forall x -> x == x
_■ x = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero     = Refl
plusZero (Succ n) = Succ (n + 0) < cong Succ (plusZero n) > Refl

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero Zero     = Refl
plusSucc Zero (Succ m) = cong Succ (plusSucc Zero m)
plusSucc (Succ n) m    = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero     = Refl
plusCommutes Zero (Succ m) = cong Succ (plusCommutes Zero m)
plusCommutes (Succ n) m    = Succ n + m < cong Succ (plusCommutes n m) > plusSucc m n

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity = {!!}

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {a} {Nil}       = Base 
SubListRefl {a} {Cons x xs} = Keep SubListRefl 

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans l Base             = l
SubListTrans (Keep l) (Keep l') = Keep (SubListTrans l l')
SubListTrans (Drop l) (Keep l') = Drop (SubListTrans l l')
SubListTrans l (Drop l')        = Drop (SubListTrans l l')                             

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym l Base = Refl
SubListAntiSym (Keep l) (Keep l') with SubListAntiSym l l'
SubListAntiSym (Keep l) (Keep l') | Refl = Refl
SubListAntiSym (Drop l) (Keep l') = _ -- Drop constructors doesn't seem to make sense..
SubListAntiSym l (Drop l') = _

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type  
data LEQ : Nat -> Nat -> Set where
  LeqZero : {n : Nat} -> LEQ Zero n
  LeqSucc : {n m : Nat} -> LEQ n m -> LEQ (Succ n) (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n 
leqRefl Zero     = LeqZero
leqRefl (Succ n) = LeqSucc (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans LeqZero b = LeqZero
leqTrans (LeqSucc a) (LeqSucc b) with leqTrans a b
leqTrans (LeqSucc a) (LeqSucc b) | LeqZero   = LeqSucc LeqZero
leqTrans (LeqSucc a) (LeqSucc b) | LeqSucc p = LeqSucc (LeqSucc p)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym LeqZero LeqZero                          = Refl
leqAntiSym (LeqSucc LeqZero) (LeqSucc LeqZero)      = Refl
leqAntiSym (LeqSucc a) (LeqSucc (LeqSucc b)) with leqAntiSym a (LeqSucc b)
leqAntiSym (LeqSucc n) (LeqSucc (LeqSucc b)) | Refl = Refl

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= {Zero} {m} LeqZero            = Refl
leq<= {Succ n} {Succ m} (LeqSucc a) = leq<= {n} {m} a

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m t            = LeqZero
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) t = LeqSucc (<=leq n m t) 

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP {P} p = λ x → x p

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
notNotExcludedMiddle {P} = λ p → p (Inr (λ np → p (Inl np))) 

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
step1 dn = dn (λ P → P (Inr (λ NP → P (Inl NP))))


step2 : excludedMiddle -> impliesToOr
step2 em = λ f → Inr _

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
