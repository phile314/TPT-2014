module Eexercise1 where

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
pure {Zero} {a} x = Nil
pure {Succ 0} {a} x =  Cons x  Nil  
pure {Succ (Succ _)} {a} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons x x₁ <*> Cons x₂ y = Cons (x  x₂) ( x₁ <*> y)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap x Nil = Nil
vmap x (Cons x₁ y) = Cons (x  x₁) (vmap x y) 

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m 

madd1 : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
madd1 (Cons xs xss) (Cons ys yss) = Cons (xs + ys) (madd1 xss yss)
madd1 Nil Nil = Nil

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons Nil Nil) (Cons Nil Nil) = Cons Nil Nil
madd (Cons xss xss₁) (Cons yss yss₁) = Cons (madd1 xss yss) (madd xss₁ yss₁) 

createZeroes : {n : Nat} -> Vec Nat n
createZeroes {Succ x} = Cons 0 ( createZeroes )
createZeroes {Zero} = Nil

mapInFrontOf : {n m : Nat} -> Matrix Nat n m -> Matrix Nat (Succ n) m
mapInFrontOf Nil =  Nil
mapInFrontOf (Cons xss xss₁) = Cons (Cons 0 xss) (mapInFrontOf xss₁)

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero}= Nil
idMatrix {Succ x} = Cons (Cons 1 createZeroes) (mapInFrontOf idMatrix) -- you add a new layer with 1 trailed by 0's, and add 0's in front of all previous layers

takeHeads : {n m : Nat } {a : Set } -> Matrix a (Succ m) n -> Vec a n 
takeHeads Nil = Nil
takeHeads (Cons (Cons x xs) xs₁) = Cons x (takeHeads xs₁)

takeTails : {n m : Nat } {a : Set } -> Matrix a (Succ m) n -> Matrix a m n 
takeTails Nil = Nil
takeTails (Cons (Cons x xss) xss₁) = Cons xss (takeTails xss₁)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil =  pure Nil 
transpose (Cons Nil x₁) = Nil
transpose (Cons (Cons x xss) xss₁) =  Cons (Cons x (takeHeads xss₁)) (transpose (Cons xss (takeTails xss₁)))
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ x} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget {Succ n} Fz = Zero
forget {Succ n} (Fs y) = Succ (forget y) -- Zero
-- forget {x} (Fs x) = Succ (forget x)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed {Succ n} Fz = Fz
embed {Succ n} (Fs y) = Fs (embed {n} y) -- Fs Fz -- Fs Fz
-- embed (Fs x) =  Fs (embed x) -- Fs (embed x) 

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct {Succ n} Fz = Refl
correct {Succ n} (Fs x) = cong Succ (correct x)
-- correct (Fs x) = {!!} -- {!correct x!}

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
cmp Zero (Succ m) =  LessThan m 
cmp (Succ a) Zero = GreaterThan a
cmp (Succ a) (Succ b) with cmp a b 
cmp (Succ a) (Succ .(a + Succ k)) | LessThan k = LessThan k
cmp (Succ a) (Succ .a) | Equal = Equal
cmp (Succ .(b + Succ k)) (Succ b) | GreaterThan k = GreaterThan k -- case? 

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference a m with cmp a m 
difference a .(a + Succ k) | LessThan k = k
difference a .a | Equal = Zero
difference .(m + Succ k) m | GreaterThan k = k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.


sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

infixr 2 _⟨_⟩_
_⟨_⟩_ : (x : Nat) -> {y z : Nat} -> (x == y) -> (y == z) -> x == z
x ⟨ p ⟩ q = trans p q

_■ : forall (x : Nat) -> x == x
_■ x = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n) 

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero Zero = Refl
plusSucc Zero (Succ b) = Refl
plusSucc (Succ a) Zero = cong Succ (plusSucc a Zero)
plusSucc (Succ a) (Succ b) = cong Succ (plusSucc a (Succ b))  

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero = Refl
plusCommutes Zero (Succ b) = cong Succ (plusCommutes Zero b)
plusCommutes (Succ a) Zero = cong Succ (plusCommutes a Zero)
plusCommutes a (Succ b)  =  
  a + Succ b
  ⟨  sym (plusSucc a b)   ⟩
  Succ (a + b)
  ⟨  cong Succ (plusCommutes a b)   ⟩
  Refl -- (Succ (b + a)) 

timesZero : ( n : Nat ) -> ( n * 0 ) == Zero
timesZero Zero = Refl
timesZero (Succ a) = timesZero a

lemma1 : (a b : Nat) -> (a * b ) == ((a * Zero ) + ( a * b ))
lemma1 Zero Zero = Refl
lemma1 Zero (Succ b) = Refl
lemma1 (Succ a) Zero = lemma1 a Zero
lemma1 a b = {!!}

lemma2 :  ( a b : Nat ) -> (Zero + (a * b)) == ((a * Zero) + (a * b))
lemma2 Zero a = Refl
lemma2 (Succ a) b = {!!} -- lemma2 a

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) Zero Zero = distributivity n Zero Zero
distributivity a Zero b =  
               (a * b) 
               ⟨ Refl ⟩
               ( Zero + (a * b)) 
               ⟨ {! !} ⟩ -- 
               ((a * Zero) + (a * b)) 
               ■
distributivity n m Zero = {!!}
distributivity n m (Succ k) = {!!}

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
SubListRefl {xs = Cons x xs1} =  Keep SubListRefl  

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base Base = Base
SubListTrans Base (Drop x) = (Drop x)
SubListTrans (Keep a) (Keep b) = Keep (SubListTrans a b)
SubListTrans (Keep a) (Drop b) = Drop  (SubListTrans (Keep a) b)
SubListTrans (Drop a) (Drop b) = Drop (SubListTrans (Drop a)  b)
SubListTrans (Drop a) (Keep b) = Drop (SubListTrans a b )

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base Base = Refl
SubListAntiSym (Keep a₁) (Keep b) with SubListAntiSym a₁ b 
SubListAntiSym (Keep a₁) (Keep b) | Refl = Refl
SubListAntiSym {xs = Nil} {Cons x ys} (Drop a) ()
SubListAntiSym {xs = Cons x xs} {Cons .x ys} (Keep a) (Drop b) = cong (Cons x) (SubListAntiSym a (SubListTrans (Drop SubListRefl) b)  )
SubListAntiSym {xs = Cons x xs} {Cons .x ys} (Drop a) (Keep b) = cong (Cons x) (SubListAntiSym (SubListTrans (Drop SubListRefl) a)  b) --SubListAntiSym {!!} (Keep b)
SubListAntiSym {legay} {xs = Cons x xs} {Cons x₁ ys} (Drop a) (Drop b) with  SubListAntiSym  {!!} {!!} -- (Drop a) (Drop b) this should be correct, but i get an error ayy
...| p = p

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  leq-zero : {a : Nat } ->  LEQ Zero a
  leq-suc : {a b : Nat } -> LEQ a b -> LEQ (Succ a) (Succ b) -- LEQ -- Leq : forall b c  -> LEQ b c

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = leq-zero
leqRefl (Succ n) = leq-suc (leqRefl n) --  Base n n  --a = Leq a a

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans leq-zero b = leq-zero
leqTrans (leq-suc a₂) (leq-suc b₁) = leq-suc (leqTrans a₂ b₁) --

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym leq-zero leq-zero = Refl
leqAntiSym (leq-suc a₂) (leq-suc b₁) = cong Succ (leqAntiSym a₂ b₁) 

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= leq-zero = Refl
leq<= (leq-suc a₁) = leq<= a₁

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m x = leq-zero
<=leq (Succ a) Zero ()
<=leq (Succ a) (Succ m) x = leq-suc (<=leq a m x) 

----------------------
----- Exercise 7 ----- --or should this be 8 lmao
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP {a} p = λ z → z p

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
notNotExcludedMiddle = λ {P} z → z (Inr (λ x → z (Inl x))) 

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
step1 dn = λ {P} → dn (λ z → z (Inr (λ x → z (Inl x)))) 

step2 : {P Q  : Set} -> Or P (Not P) -> (P -> Q) -> Or (Not P) Q
step2 (Inl x) x₁ = {!!}
step2 (Inr x) x₁ = {!!}

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

data 360noscope : Set where
  WellScoped : Raw -> 360noscope
  UnWellScoped :  360noscope

-- Scope checking with de bruijn indices means that you cannot acces variables that are deeper nested than the level of lambda you are in right now.
scoobyCheck : Raw -> Nat -> 360noscope
scoobyCheck (Lam x) f with scoobyCheck x (Succ f)
scoobyCheck (Lam x) f | WellScoped x₁ =  WellScoped (Lam x)
scoobyCheck (Lam x) f | UnWellScoped = UnWellScoped
scoobyCheck (App x x₁) f with scoobyCheck x f
scoobyCheck (App x x₂) f | WellScoped x₁ with scoobyCheck x₂ f
scoobyCheck (App x₁ x₂) f | WellScoped x₃ | WellScoped x = WellScoped (App x₁ x₂)
scoobyCheck (App x x₂) f | WellScoped x₁ | UnWellScoped = UnWellScoped
scoobyCheck (App x x₂) f | UnWellScoped = UnWellScoped
scoobyCheck (Var x) f with (Succ x) <= f 
scoobyCheck (Var x) f | True = WellScoped (Var x)
scoobyCheck (Var x) f | False = UnWellScoped

check : Raw -> 360noscope
check r = scoobyCheck r Zero

check1 : Raw -- well scoped : http://i.imgur.com/6XSCj1V.png
check1 = Lam (App (Var 0) (Var 1)) -- Lam (App (Var Zero) (Var Zero))

check2 : 360noscope
check2 = check check1

check3 : Raw -- un well scoped : http://i.imgur.com/wjV9SzE.png
check3 = Lam (Var (Succ( Succ Zero)))

check4 : 360noscope
check4 = check check3
