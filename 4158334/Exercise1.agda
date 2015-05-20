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

head : {a : Set} {n : Nat} -> Vec a (Succ n) -> a
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

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero}   a = Nil
pure {Succ n} a = Cons a (pure a)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil       <*> _         = Nil
Cons x xs <*> Cons y ys = Cons (x y) (xs <*> ys)

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
vadd : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
vadd xs ys = vmap _+_ xs <*> ys

madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons xs xss) (Cons ys yss) = Cons (vadd xs ys) (madd xss yss)

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ n} = Cons (Cons 1 (pure 0)) (vmap (Cons 0) idMatrix)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {Zero}   {Zero}   _   = Nil
transpose {Zero}   {Succ m} _   = pure Nil
transpose {Succ n} {Zero}   _   = Nil
transpose {Succ n} {Succ m} xss = Cons (vmap head xss) (transpose (vmap tail xss))

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs i) = Succ (forget i)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs x) = Fs (embed x)

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

-- Show that there is a 'covering function'
cmp-succ : {n m : Nat} -> Compare n m -> Compare (Succ n) (Succ m)
cmp-succ (LessThan k) = LessThan k
cmp-succ Equal = Equal
cmp-succ (GreaterThan k) = GreaterThan k

cmp : (n m : Nat) -> Compare n m
cmp Zero     Zero     = Equal
cmp Zero     (Succ m) = LessThan m
cmp (Succ n) Zero     = GreaterThan n
cmp (Succ n) (Succ m) = cmp-succ (cmp n m)

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k    = k
difference n .n            | Equal         = 0
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
infix 3 _■
_■ : {a : Set} (x : a) -> x == x
_■ x = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero m = sym (plusZero m)
plusCommutes (Succ n) m = Succ (n + m) ⟨ cong Succ (plusCommutes n m) ⟩ plusSucc m n

plusAssoc : (n m k : Nat) -> (n + (m + k)) == ((n + m) + k)
plusAssoc Zero m k = Refl
plusAssoc (Succ n) m k = cong Succ (plusAssoc n m k)

aux : (x y x₁ y₁ : Nat) -> ((x + y) + (x₁ + y₁)) == ((x + x₁) + (y + y₁))
aux x y x₁ y₁ =
  (x + y) + (x₁ + y₁)
  ⟨ cong (λ a -> a + (x₁ + y₁)) (plusCommutes x y) ⟩
  (y + x) + (x₁ + y₁)
  ⟨ sym (plusAssoc y x (x₁ + y₁)) ⟩
  y + (x + (x₁ + y₁))
  ⟨ cong (λ a -> y + a) (plusAssoc x x₁ y₁) ⟩
  y + ((x + x₁) + y₁)
  ⟨ cong (λ a -> y + a) (plusCommutes (x + x₁) y₁) ⟩
  y + (y₁ + (x + x₁))
  ⟨ plusAssoc y y₁ (x + x₁) ⟩
  (y + y₁) + (x + x₁)
  ⟨ plusCommutes (y + y₁) (x + x₁) ⟩
  (x + x₁) + (y + y₁)
  ■

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k =
  Succ n * (m + k)
  ⟨ Refl ⟩
  (m + k) + (n * (m + k))
  ⟨ cong (λ x -> (m + k) + x) (distributivity n m k) ⟩
  (m + k) + ((n * m) + (n * k))
  ⟨ aux m k (n * m) (n * k) ⟩
  (m + (n * m)) + (k + (n * k))
  ■

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
SubListTrans Base      Base      = Base
SubListTrans r₁        (Drop r₂) = Drop (SubListTrans r₁ r₂)
SubListTrans (Keep r₁) (Keep r₂) = Keep (SubListTrans r₁ r₂)
SubListTrans (Drop r₁) (Keep r₂) = Drop (SubListTrans r₁ r₂)

SubListReduce : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList xs ys
SubListReduce (Keep r₁) = Drop r₁
SubListReduce (Drop r₁) = Drop (SubListReduce r₁)

SubListAux : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList ys xs -> Empty
SubListAux (Keep r₁) r₂ = SubListAux r₂ r₁
SubListAux (Drop r₁) (Keep r₂) = SubListAux (SubListReduce r₁) r₂
SubListAux (Drop r₁) (Drop r₂) = SubListAux (SubListReduce r₁) (SubListReduce r₂)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base Base = Refl
SubListAntiSym (Keep r₁) (Keep r₂) with SubListAntiSym r₁ r₂
... | Refl = Refl
SubListAntiSym (Keep r₁) (Drop r₂) with SubListAux r₂ r₁
... | ()
SubListAntiSym (Drop r₁) r₂ with SubListAux r₂ r₁
... | ()

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
data LEQ : Nat -> Nat -> Set where
  Base : {n : Nat} -> LEQ 0 n
  Step : {n m : Nat} -> LEQ n m -> LEQ (Succ n) (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base _ = Base
leqTrans (Step r₁) (Step r₂) = Step (leqTrans r₁ r₂)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step r₁) (Step r₂) = cong Succ (leqAntiSym r₁ r₂)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= Base = Refl
leq<= (Step r) = leq<= r

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m x = Base
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) x = Step (<=leq n m x)

----------------------
----- Exercise 8 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP P x = x P

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
notNotExcludedMiddle x = x (Inr (λ x₁ → x (Inl x₁)))

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
step2 x y = orCase Inr (λ x₁ → Inl (λ x₂ → x₁ (y x₂))) x

id : {a : Set} -> a -> a
id a = a

step3 : impliesToOr -> doubleNegation
step3 ito {P} h = orCase (λ x → magic (h x)) id (ito id)

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

And = Pair

fromLeft : {a b : Set} -> Pair a b -> a
fromLeft (x , _) = x

fromRight : {a b : Set} -> Pair a b -> b
fromRight (_ , x) = x

absorption : {P Q : Set} -> Or (And P Q) P -> P
absorption x = orCase (λ x₁ → fromLeft x₁) id x

peirce2ito : piercesLaw -> excludedMiddle
peirce2ito p = {!!}

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
