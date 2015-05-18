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
pure {Zero} a = Nil
pure {Succ n} a = Cons a (pure {n} a)

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
vzip : {a b c : Set} {n : Nat} → (a → b → c) → Vec a n → Vec b n → Vec c n 
vzip f Nil Nil = Nil
vzip f (Cons x xs) (Cons y ys) = Cons (f x y) (vzip f xs ys)

madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons xs xss) (Cons ys yss) = Cons (vzip _+_ xs ys) (madd xss yss)

-- Define the identity matrix
vreplicate : {n : Nat} {a : Set} → a → Vec a n
vreplicate {Zero} _ = Nil
vreplicate {Succ n} a = Cons a (vreplicate a)

idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ n} = Cons (Cons 1 (vreplicate 0)) (vmap (\v → Cons 0 v) idMatrix)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {n} {Zero} matrix = Nil
transpose {Zero} {Succ m} Nil = Cons Nil (transpose Nil)
transpose {Succ n} {Succ m} (Cons v vs) = vzip Cons v (transpose vs)

----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.

data _<_ : Nat → Nat → Set where
  Base : ∀{n} → Zero < Succ n
  Step : ∀{n m} → n < m → Succ n < Succ m

plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs f) = Succ (forget f)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed {Succ n} Fz = Fz
embed {Succ n} (Fs f) = Fs (embed f)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct {Succ n} Fz = Refl
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
cmp Zero Zero = Equal
cmp (Succ n) Zero = GreaterThan n
cmp Zero (Succ m) = LessThan m
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k = LessThan k
cmp (Succ .m) (Succ m) | Equal = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k = Succ k
difference .m m | Equal = m
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

infixr 2 _⟨_⟩_
_⟨_⟩_ : (x : Nat) -> {y z : Nat} -> (x == y) -> (y == z) -> x == z
x ⟨ p ⟩ q = trans p q

infixr 3 _□
_□ : ∀ (x : Nat) → x == x
_□ x = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes n Zero = plusZero n
plusCommutes Zero m = sym (plusZero m)
plusCommutes n (Succ m) =
  n + Succ m
  ⟨ sym (plusSucc n m) ⟩
  Succ (n + m)
  ⟨ cong Succ (plusCommutes n m) ⟩
  Succ m + n
  □

plusReflR : {n m₁ m₂ : Nat} → m₁ == m₂ → (n + m₁) == (n + m₂)
plusReflR {Zero} p = p
plusReflR {Succ n} p = cong Succ (plusReflR {n} p)

plusReflL : {m n₁ n₂ : Nat} → n₁ == n₂ → (n₁ + m) == (n₂ + m)
plusReflL {m}{n₁}{n₂} p = 
  n₁ + m
  ⟨ plusCommutes n₁ m ⟩
  m + n₁
  ⟨ plusReflR {m} p ⟩
  m + n₂
  ⟨ plusCommutes m n₂ ⟩
  n₂ + m
  □

plusDistribute : {a b c : Nat} → (a + (b + c)) == ((a + b) + c)
plusDistribute {Zero} = Refl
plusDistribute {Succ a} {Zero} {Zero} = cong Succ (sym (plusZero (a + Zero)))
plusDistribute {Succ a} {Succ b} {c} = cong Succ (plusDistribute {a})
plusDistribute {a} {Zero} {Succ c} = 
  a + Succ c
  ⟨ plusCommutes a (Succ c) ⟩
  Succ c + a
  ⟨ plusReflR {Succ c} (sym (plusZero a)) ⟩
  Succ c + (a + 0)
  ⟨ plusCommutes (Succ c) (a + Zero) ⟩
  (a + 0) + Succ c
  □

timesZero : (n : Nat) → (n * 0) == 0
timesZero Zero = Refl
timesZero (Succ n) = timesZero n

timesSucc : (n m : Nat) → (n * Succ m) == (n + (n * m))
timesSucc Zero m = Refl
timesSucc (Succ n) m = cong Succ (
  m + (n * Succ m)
  ⟨ plusReflR {m} (timesSucc n m) ⟩
  m + (n + (n * m))
  ⟨ plusDistribute {m}⟩
  (m + n) + (n * m)
  ⟨ plusReflL {n * m} (plusCommutes m n) ⟩
  (n + m) + (n * m)
  ⟨ sym (plusDistribute {n}) ⟩
  n + (m + (n * m))
  □)

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity n (Succ m) k = 
  n * Succ (m + k)
  ⟨ timesSucc n (m + k) ⟩
  n + (n * (m + k))
  ⟨ plusReflR {n} (distributivity n m k) ⟩
  n + ((n * m) + (n * k))
  ⟨ plusDistribute {n} ⟩
  ((n + (n * m))) + (n * k)
  ⟨ plusReflL {n * k} (sym (timesSucc n m)) ⟩
  (n * Succ m) + (n * k)
  □
distributivity n Zero (Succ k) =
  n * Succ k
  ⟨ sym (plusZero (n * Succ k)) ⟩
  (n * Succ k) + 0
  ⟨ plusReflR {n * Succ k} (sym (timesZero n)) ⟩
  (n * Succ k) + (n * 0)
  ⟨ plusCommutes (n * Succ k) (n * Zero) ⟩
  (n * 0) + (n * Succ k)
  □
distributivity n Zero Zero = 
  n * 0
  ⟨ sym (plusZero (n * Zero)) ⟩
  (n * 0) + 0
  ⟨ plusReflR {n * 0} (sym (timesZero n)) ⟩
  (n * 0) + (n * 0)
  □

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {_} {Nil} = Base
SubListRefl {_} {Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base m = m
SubListTrans (Keep l) (Keep m) = Keep (SubListTrans l m)
SubListTrans (Drop l) (Keep m) = Drop (SubListTrans l m)
SubListTrans l (Drop m) = Drop (SubListTrans l m)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base m = Refl
SubListAntiSym {a} {Cons x xs} (Keep l) (Keep m) = cong (Cons x) (SubListAntiSym l m)
SubListAntiSym {a} {Cons x xs} {Cons .x ys} (Keep l) (Drop m) = cong (Cons x) (SubListAntiSym l (SubListTrans (Drop SubListRefl) m))
SubListAntiSym {a} {Cons x xs} {Cons .x ys} (Drop l) (Keep m) = cong (Cons x) (SubListAntiSym (SubListTrans (Drop SubListRefl) l) m)
SubListAntiSym {a} {Cons x xs} {Cons y ys} (Drop l) (Drop m) = SubListAntiSym (Drop l) (Drop m)

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Base : ∀{n} → LEQ 0 n
  Step : ∀{n m} → LEQ n m → LEQ (Succ n) (Succ m)


-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base m₁ = Base
leqTrans (Step l) (Step m) = Step (leqTrans l m)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step l) (Step m) = cong Succ (leqAntiSym l m)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type
leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= {Zero} {_} p = Refl
leq<= {Succ n} {Succ m} (Step p) = leq<= p

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m Refl = Base
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) l = Step (<=leq n m l)

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP p z = z p

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
notNotExcludedMiddle n₁ = n₁ (Inr (λ n₂ → n₁ (Inl n₂)))

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
step2 em {P} {Q} pq = orCase Inr (λ z → Inl (λ x → z (pq x))) em

step3 : impliesToOr -> doubleNegation
step3  ito {P} h = orCase {!!} magic (ito h)

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
