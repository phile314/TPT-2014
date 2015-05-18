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

_<_ : Nat -> Nat -> Bool
Zero < Zero = False
Zero < Succ b = True
Succ a < Zero = False
Succ a < Succ b = a < b

length : {a : Set} -> List a -> Nat
length Nil = Zero
length (Cons x l) = Succ (length l)

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
Cons x fs <*> Cons x₁ as = Cons (x x₁) (fs <*> as)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.
-- m is the amount of rows
-- n is the amount of columns
Matrix : Set -> Nat -> Nat -> Set
Matrix a m n = Vec (Vec a m) n

-- Helper function: defines vector addition
vadd : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
vadd Nil Nil = Nil
vadd (Cons x xs) (Cons x₁ ys) = Cons (x + x₁) ys

-- Define matrix addition
madd : {m n : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons xss xss₁) (Cons yss yss₁) = Cons (vadd xss yss) (madd xss₁ yss₁)

-- Builds a single column of the id matrix
-- Has to know which column it is, because that's where the 1 is to be put
idMatrixColumn : {n : Nat} -> Fin n -> Vec Nat n
idMatrixColumn {Zero} m = Nil
idMatrixColumn {Succ n} Fz = Cons 1 (pure 0)
idMatrixColumn {Succ n} (Fs m) = Cons 0 (idMatrixColumn m)

-- Given an m x n matrix, it prepends a 0 to every column
-- to create an (m + 1) x n matrix.
-- I mean we're doing agda here, let's not reason about efficiency
addZeroesToM : {m n : Nat} -> Matrix Nat m n -> Matrix Nat (Succ m) n
addZeroesToM Nil = Nil
addZeroesToM (Cons mat mat₁) = Cons (Cons 0 mat) (addZeroesToM mat₁) 

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ n} = Cons (idMatrixColumn Fz) (addZeroesToM idMatrix)

tail : {n : Nat} {a : Set} -> Vec a (Succ n) -> Vec a n
tail (Cons x v) = v

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {Zero} {Zero} Nil = Nil
transpose {Zero} {Succ m} Nil = Cons Nil (transpose Nil) -- Totes makes sense
transpose {Succ n} {Zero} (Cons a₁ a₂) = Nil
transpose {Succ n} {Succ m} (Cons a₁ a₂) = Cons (Cons (head a₁) (vmap head a₂)) (transpose (Cons (tail a₁) (vmap tail a₂))) -- Boom shakalaka

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- toFin : {n : Nat} -> Fin (Succ n)
-- toFin {Zero} = Fz
-- toFin {Succ n} = Fs toFin

-- Grow a vector with Fin
-- Step is needed for plan. Increases the Fin of every element in the list
grow : {n : Nat} -> Vec (Fin n) n -> Vec (Fin (Succ n)) n
grow = vmap Fs

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (grow plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs fn) = Succ (forget fn)

toFin : {n : Nat} -> Fin (Succ n)
toFin {Zero} = Fz
toFin {Succ n} = Fs toFin

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
-- embed Fz = Fz
-- embed (Fs f) = toFin
-- embed {Zero} ()
-- embed {Succ n} f = toFin {Succ n}
embed Fz = Fz
embed (Fs f) = Fs (embed f)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs i) = cong Succ (correct i)

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
cmp Zero Zero = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) = cmp' (cmp n m)

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k = Succ k
difference n .n | Equal = n
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

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero Zero = Refl
plusSucc Zero (Succ m) = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero = Refl
plusCommutes Zero (Succ m) = cong Succ (sym (plusZero m)) 
plusCommutes (Succ n) Zero = cong Succ (plusZero n)
plusCommutes (Succ n) (Succ m) = cong Succ (trans (sym (plusSucc n m)) (plusCommutes (Succ n) m))

distLemma : (n : Nat) -> (n * Zero) == Zero
distLemma Zero = Refl
distLemma (Succ n) = distLemma n

--addOne : (n m : Nat) -> n == m -> (Succ n) == (Succ m)
--addOne n m ev = cong Succ ev

addAnyNumber : (n m k : Nat) -> n == m -> (n + k) == (m + k)
addAnyNumber n m Zero ev = trans (plusZero n) (trans ev (sym (plusZero m)))
addAnyNumber n m (Succ k) ev = trans (sym (plusSucc n k)) (trans (cong Succ (addAnyNumber n m k ev)) (plusSucc m k))

subst : (n l r : Nat) -> l == r -> (l + n) == (r + n)
subst n l r ev = addAnyNumber l r n ev

substr : (n l r : Nat) -> l == r -> (n + l) == (n + r)
substr n l r ev = trans (plusCommutes n l) (trans (subst n l r ev) (plusCommutes r n))

substrMul : (n l r : Nat) -> l == r -> (n * l) == (n * r)
substrMul Zero l r ev = Refl
substrMul (Succ n) l Zero ev = trans (subst (n * l) l Zero ev) (substrMul n l Zero ev)
substrMul (Succ n) l (Succ r) ev = trans (subst (n * l) l (Succ r) ev) (cong Succ (substr r (n * l) (n * (Succ r)) (substrMul n l (Succ r) ev)))

addMultipliedNothing : (n m : Nat) -> ((m * Zero) + n) == (Zero + n)
addMultipliedNothing n m = subst n (m * Zero) Zero (distLemma m)

distribLemma : (n m : Nat) -> n == ((m * Zero) + n) 
distribLemma Zero m = trans (sym (distLemma m)) (sym (plusZero (m * Zero)))
distribLemma (Succ n) m = sym (trans (addMultipliedNothing (Succ n) m) Refl)

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) Zero Zero = distributivity n Zero Zero
distributivity (Succ n) Zero (Succ k) = distribLemma ( Succ (k + (n * Succ k))) n
distributivity (Succ n) (Succ m) Zero = cong Succ (trans (subst (n * Succ (m + Zero)) (m + Zero) m (plusZero m)) (trans (substr m (n * (Succ (m + Zero))) (n * (Succ m)) (substrMul n (Succ (m + Zero)) (Succ m) (cong Succ (plusZero m)))) (sym (trans (substr (m + (n * Succ m)) (n * Zero) Zero (distLemma n)) (plusZero (m + (n * Succ m)))))))
distributivity (Succ n) (Succ m) (Succ k) = cong Succ (trans (substr (m + Succ k) (n * Succ (m + Succ k)) (n * (m + Succ (Succ k))) (substrMul n (Succ (m + Succ k)) (m + Succ (Succ k)) (plusSucc m (Succ k)))) (trans (substr (m + Succ k) (n * (m + Succ (Succ k))) ((n * m) + (n * Succ (Succ k))) (distributivity n m (Succ (Succ k)))) ({!!})))

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
SubListTrans Base (Drop s2) = Drop s2
SubListTrans (Keep s1) (Keep s2) = Keep (SubListTrans s1 s2)
SubListTrans (Keep s1) (Drop s2) = Drop (SubListTrans (Keep s1) s2)
SubListTrans (Drop s1) (Keep s2) = Drop (SubListTrans s1 s2)
SubListTrans (Drop s1) (Drop s2) = Drop (SubListTrans (Drop s1) s2)

SubListLen : {a : Set} {xs ys : List a} -> SubList xs ys -> Nat
SubListLen {xs = Nil} s = Zero
SubListLen {xs = Cons x xs} (Keep s) = Succ (SubListLen s)
SubListLen {xs = Cons x xs} (Drop s) = SubListLen s

AntiSym1 : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x ys) xs -> SubList xs ys -> Empty
AntiSym1 {xs = Nil} {Nil} () s2
AntiSym1 {xs = Nil} {Cons x₁ ys} () s2
AntiSym1 {xs = Cons x₁ xs} {Nil} s1 ()
AntiSym1 {xs = Cons ._ xs} {Cons ._ ys} (Keep s1) (Keep s2) = AntiSym1 s1 s2
AntiSym1 {xs = Cons ._ xs} {Cons x₂ ys} (Keep s1) (Drop s2) = {!!}
AntiSym1 {xs = Cons x₁ xs} {Cons .x₁ ys} (Drop s1) (Keep s2) = {!!}
AntiSym1 {xs = Cons x₁ xs} {Cons x₂ ys} (Drop s1) (Drop s2) = {!!}
{-AntiSym1 {a} {x} {xs} {ys} b s with length xs | length ys
AntiSym1 {a} {x} {Nil} {Nil} () s | Zero | Zero
AntiSym1 {a} {x₁} {Nil} {Cons x ys} () s | Zero | Zero
AntiSym1 {a} {x₁} {Cons x xs} {Nil} b () | Zero | Zero
AntiSym1 {a} {x₂} {Cons x xs} {Cons x₁ ys} b s | Zero | Zero = magic {!!}

AntiSym1 {a} {x} {Nil} {Nil} () s | Zero | Succ q
AntiSym1 {a} {x₁} {Nil} {Cons x ys} () s | Zero | Succ q
AntiSym1 {a} {x₁} {Cons x xs} {Nil} b () | Zero | Succ q
AntiSym1 {a} {x₂} {Cons x xs} {Cons x₁ ys} b s | Zero | Succ q = {!!}

AntiSym1 b s | Succ p | Zero = {!!}
AntiSym1 b s | Succ p | Succ q = {!!}-}



SubListAntiSym : {a : Set} {xs ys : List a} -> SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym {xs = Nil} {Nil} s1 s2 = Refl
SubListAntiSym {xs = Nil} {Cons x ys} (Drop s1) ()
SubListAntiSym {xs = Cons x xs} {Nil} () s2
SubListAntiSym {xs = Cons x xs} {Cons .x ys} (Keep s1) (Keep s2) = cong (Cons x) (SubListAntiSym s1 s2)
SubListAntiSym s1 (Drop s2) = magic (AntiSym1 s1 s2)
SubListAntiSym (Drop s1) (s2) = magic (AntiSym1 s2 s1)


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
data LEQ : Nat -> Nat -> Set where
  LEQBase : {n : Nat} -> LEQ Zero n
  LEQStep : {n m : Nat} -> LEQ m n -> LEQ (Succ m) (Succ n)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = LEQBase
leqRefl (Succ n) = LEQStep (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans LEQBase LEQBase = LEQBase
leqTrans LEQBase (LEQStep r) = LEQBase
leqTrans (LEQStep l) (LEQStep r) = LEQStep (leqTrans l r)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym LEQBase LEQBase = Refl
leqAntiSym (LEQStep l) (LEQStep r) = cong Succ (leqAntiSym l r)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= LEQBase = Refl
leq<= (LEQStep {Zero} {Zero} l) = Refl
leq<= (LEQStep {Zero} {Succ m} l) = leq<= l
leq<= (LEQStep {Succ n} {Zero} l) = Refl
leq<= (LEQStep {Succ n} {Succ m} l) = leq<= l

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero Zero ev = LEQBase
<=leq Zero (Succ m) ev = LEQBase
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) ev = LEQStep (<=leq n m ev)

----------------------
----- Exercise 8 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP P = λ z → z P

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

step2 : excludedMiddle -> impliesToOr
step2 em = λ {P} {Q} → λ z → orCase Inr (λ z₁ → Inl (λ x → z₁ (z x))) em

step3 : {P Q : Set} -> (P -> Q) -> Or (Not P) Q -> doubleNegation
step3 {P} {Q} imp orn = {!!}

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

data WellScoped : Set where
  Good : Raw -> WellScoped
  Bad : WellScoped

isWellScoped : Raw -> Nat -> WellScoped
isWellScoped (Lam r) n with  isWellScoped r (Succ n)
isWellScoped (Lam r) n | Good x = Good (Lam x)
isWellScoped (Lam r) n | Bad = Bad
isWellScoped (App r r₁) n with isWellScoped r n
isWellScoped (App r r₁) n | Good x with isWellScoped r₁ n
isWellScoped (App r r₁) n | Good x₁ | Good x = Good (App r r₁)
isWellScoped (App r r₁) n | Good x | Bad = Bad
isWellScoped (App r r₁) n | Bad = Bad
isWellScoped (Var x) n with x < n
isWellScoped (Var x) n | True = Good (Var x)
isWellScoped (Var x) n | False = Bad

checkWellScoped : Raw -> WellScoped
checkWellScoped r = isWellScoped r Zero

test1 : WellScoped
test1 = checkWellScoped (Var Zero) -- Bad

test2 : WellScoped
test2 = checkWellScoped (Lam (Lam (Var 1))) -- Good

test3 : WellScoped
test3 = checkWellScoped (Lam (Lam (Var 2))) -- Bad

test4 : WellScoped
test4 = checkWellScoped (Lam (App (Var 0) (Var 0))) -- Good

test5 : WellScoped
test5 = checkWellScoped (Lam (App (Var 0) (Var 1))) -- Bad

test6 : WellScoped
test6 = checkWellScoped (Lam (App (Var 1) (Var 0))) -- Bad
