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

infixl 6 _+_
infixl 7 _*_

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

lappend : {a : Set} -> List a -> List a -> List a
lappend Nil ys = ys
lappend (Cons x xs) ys = Cons x (lappend xs ys)

infixr 5 _++_

_++_ : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
xs ++ ys = append xs ys

infixr 5 _::_

_::_ : {a : Set} {n : Nat} -> a -> Vec a n -> Vec a (Succ n)
x :: ys = Cons x ys

[] : {a : Set} -> Vec a Zero
[] = Nil

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

if_then_else_ : {a : Set} -> Bool -> a -> a -> a
if True  then t else e = t
if False then t else e = e

_≡_ : Nat -> Nat -> Bool
Zero ≡ Zero = True
Zero ≡ Succ y = False
Succ x ≡ Zero = False
Succ x ≡ Succ y = x ≡ y

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero} v = Nil
pure {Succ n} v = Cons v (pure {n} v)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> xs = Nil
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
madd Nil Nil = Nil
madd (Cons xs xss) (Cons ys yss)
  = Cons ((vadd ys) <*> xs) (madd xss yss)
  where vadd : {n : Nat} -> Vec Nat n -> Vec (Nat -> Nat) n
        vadd Nil = Nil
        vadd (Cons x xs) = Cons (_+_ x) (vadd xs)


repeat : {n : Nat} {a : Set} -> a -> (a -> a) -> Vec a n
repeat {Zero} x f = Nil
repeat {Succ n} x f = Cons x (repeat {n} (f x) f)

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix
  = vmap row (repeat 0 (_+_ 1))
  where row : {n : Nat} -> Nat -> Vec Nat n
        row r = vmap (\c -> if r ≡ c then 1 else 0) (repeat 0 (_+_ 1))


replicate : {n : Nat} -> {a : Set} -> a -> Vec a n
replicate {Zero} x = Nil
replicate {Succ i} x = Cons x (replicate {i} x)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = replicate Nil
transpose (Cons Nil xss) = Nil
transpose (Cons (Cons x xs) xss) = Cons (Cons x (vmap head xss)) (transpose (Cons xs (vmap tail xss)))

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

data _<_ : Nat -> Nat -> Set where
  Base : forall {n} -> Zero < Succ n
  Step : forall {n m} -> n < m -> Succ n < Succ m


toFin : {n : Nat} -> (m : Nat) -> Fin (Succ n)
toFin Zero = Fz
toFin {Zero} (Succ m) = Fz
toFin {Succ n} (Succ m) = Fs (toFin m)

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = vmap toFin (repeat 0 (_+_ 1))

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs x) = Succ (forget x)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed {Zero} ()
embed {Succ n} Fz = Fz {Succ n}
embed {Succ n} (Fs x) = Fs {Succ n} (embed x)


correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct {Zero} ()
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
difference n .n | Equal = Zero
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

infixr 2 _<_>_
_<_>_ : {a : Set} -> (x : a) -> {y z : a} -> (x == y) -> (y == z) -> x == z
x < p > q = trans p q

_∎ : forall x -> x == x
_∎ x = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

_∙_ : forall {a b c} -> (b -> c) -> (a -> b) -> a -> c
f ∙ g = λ x -> f (g x)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

-- Reverse of plusSucc
plusSucc' : (n m : Nat) -> (n + Succ m) == Succ (n + m)
plusSucc' Zero m = Refl
plusSucc' (Succ n) m = cong Succ (plusSucc' n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero = Refl
plusCommutes Zero (Succ m) = cong Succ (plusCommutes 0 m)
plusCommutes (Succ n) m =
  Succ (n + m)
  < cong Succ (plusCommutes n m) >
  plusSucc m n


plusAssoc : (x y n : Nat) -> ((x + y) + n) == (x + (y + n))
plusAssoc Zero y n =
  (0 + y) + n
  < Refl >
  y + n
  < Refl >
  ((0 + (y + n)) ∎)
plusAssoc (Succ x) y n = cong Succ (plusAssoc x y n)


axiomA : (n m : Nat) -> (n * (Succ m)) == (n * m + n)
axiomA Zero m = Refl
axiomA (Succ n) m =
  Succ n * Succ m
  < cong Succ' (axiomA n m) >
  1 + (m + (n * m + n))
  < plusCommutes 1 (m + (n * m + n)) >
  (m + (n * m + n)) + 1
  < plusAssoc m (n * m + n) 1 >
  m + (n * m + n + 1)
  < cong (_+_ m) (plusAssoc (n * m) n 1) >
  m + (n * m + (n + 1))
  < plusCommutes m (n * m + (n + 1)) >
  n * m + (n + 1) + m
  < plusAssoc (n * m) (n + 1) m >
  n * m + ((n + 1) + m)
  < plusCommutes (n * m) (n + Succ Zero + m) >
  n + 1 + m + n * m
  < plusAssoc (n + 1) m (n * m) >
  n + 1 + (m + n * m)
  < plusCommutes (n + 1) (m + n * m) >
  m + n * m + (n + 1)
  < cong (_+_ (m + n * m)) (plusCommutes n 1) >
  ((m + n * m + Succ n) ∎)
  where Succ' = _+_ (Succ m)

-- Reverse of axiomA
axiomA' : (n m : Nat) -> (n * m + n) == (n * (Succ m))
axiomA' Zero m = Refl
axiomA' (Succ n) m =
  m + n * m + Succ n
  < plusCommutes (m + n * m) (Succ n) >
  Succ (n + (m + n * m))
  < cong Succ (plusCommutes n (m + n * m)) >
  Succ (m + n * m + n)
  < cong Succ (plusAssoc m (n * m) n) >
  Succ (m + (n * m + n))
  < cong (\ x -> Succ (m + x)) (axiomA' n m) >
  (Succ (m + n * Succ m) ∎)

axiomB : (n : Nat) -> 0 == (n * 0)
axiomB Zero = Refl
axiomB (Succ n) = axiomB n

distributivity : (a b k : Nat) -> (a * (b + k)) == ((a * b) + (a * k))
distributivity a b Zero =
  a * (b + 0)
  < cong (_*_ a) (plusZero b) >
  a * b
  < plusCommutes Zero (a * b) >
  a * b + 0
  < cong (_+_ (a * b)) (axiomB a) >
  ((a * b + a * 0) ∎)
distributivity a b (Succ k) =
  a * (b + Succ k)
  < cong (_*_ a) (plusSucc' b k) >
  a * Succ (b + k)
  < axiomA a (b + k) >
  a * (b + k) + a
  < plusCommutes (a * (b + k)) a >
  a + a * (b + k)
  < cong (_+_ a) (distributivity a b k) >
  a + (a * b + a * k)
  < plusCommutes a (a * b + a * k) >
  a * b + a * k + a
  < plusAssoc (a * b) (a * k) a >
  a * b + (a * k + a)
  < cong (_+_ (a * b)) (axiomA' a k) >
  ((a * b + a * Succ k) ∎)


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
SubListRefl {a} {xs = Cons x xs} = Keep (SubListRefl {a} {xs})

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans xy Base = xy
SubListTrans (Keep xy) (Keep yz) = Keep (SubListTrans xy yz)
SubListTrans (Drop xy) (Keep yz) = Drop (SubListTrans xy yz)
SubListTrans xy (Drop yz) = Drop (SubListTrans xy yz)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base Base = Refl
SubListAntiSym {xs = Cons x xs} (Keep xy) (Keep yx) = cong (Cons x) (SubListAntiSym xy yx)
SubListAntiSym (Keep xy) (Drop yx) = _ -- These 2 cases don't make any sense to me,
SubListAntiSym (Drop xy) yx = _        -- if I'm right, there's no way that these can ever happen

-- Debugging helpers
lista = Cons 5 (Cons 4 (Cons 3 Nil))
lista2 = lappend lista (Cons 6 Nil)
lista3 = lappend lista2 (Cons 7 Nil)

lista' = SubListRefl {Nat} {lista}
lista2' = SubListRefl {Nat} {lista2}


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
data LEQ : Nat -> Nat -> Set where
  Base : forall {y} -> LEQ Zero y
  Step : forall {x y} -> LEQ x y -> LEQ (Succ x) (Succ y)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base mk = Base
leqTrans (Step nm) (Step mk) = Step (leqTrans nm mk)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step nm) (Step mn) with leqAntiSym nm mn
leqAntiSym (Step nm) (Step mn) | Refl = Refl

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= Base = Refl
leq<= (Step nm) = leq<= nm

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m p = Base
<=leq (Succ n) m ()

----------------------
----- Exercise 8 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP p = λ z → z p

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
step2 e = {!!}

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
