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
pure {Zero} a = Nil 
pure {Succ c} a = Cons a (pure {c} a)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons f p <*> Cons x q = Cons (f x) (p <*> q)

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
madd (Cons x xss) (Cons y yss) = Cons (vmap _+_ x <*> y) (madd xss yss)

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ n} = Cons (Cons 1 (pure 0)) (vmap (Cons 0) idMatrix)

tail : {a : Set} {n : Nat}-> Vec a (Succ n) -> Vec a n
tail (Cons x xs) = xs

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {Zero} {Zero} Nil = Nil
transpose {Zero} {Succ m} Nil = pure Nil
transpose (Cons p ps) = vmap Cons p <*> transpose ps

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
forget  Fz = Zero
forget (Fs x) = Succ (forget x)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs x) = Fs (embed x)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct  Fz = Refl
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
cmp : (n m : Nat) -> Compare n m 
cmp Zero Zero = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k = LessThan k
cmp (Succ n) (Succ .n)            | Equal = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k = Succ k
difference n .n            | Equal = 0
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
_⟨_⟩_ : {a : Set} (x : a) -> {y z : a} -> (x == y) -> (y == z) -> x == z
x ⟨ p ⟩ q = trans p q

_qed : forall x -> x == x
x qed = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

-- Some auxillary functions
plusOne : (n : Nat) -> Succ n == (n + 1)
plusOne Zero = Refl
plusOne (Succ n) = cong Succ (plusOne n)

plusSym : (n m : Nat) -> (n + Succ m) == (m + Succ n)
plusSym Zero Zero = Refl
plusSym Zero (Succ m) = cong Succ (plusOne m)
plusSym (Succ n) Zero = cong Succ (sym (plusOne n))
plusSym (Succ n) (Succ m) = cong Succ (trans (plusSym n (Succ m)) (plusSucc m (Succ n)))

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero = Refl
plusCommutes Zero (Succ m) = sym (plusZero (Succ m))
plusCommutes (Succ n) Zero = plusZero (Succ n)
plusCommutes (Succ n) (Succ m) =
  Succ (n + Succ m) 
  ⟨ plusSucc n (Succ m) ⟩ 
  n + Succ (Succ m) 
  ⟨ plusSym n (Succ m) ⟩ 
  Succ (m + Succ n) 
  qed

-- Change the associativity of a sum
plusAssociative : (n m k : Nat) -> (n + (m + k)) == ((n + m) + k)
plusAssociative Zero m k = Refl
plusAssociative (Succ n) m k = cong Succ (plusAssociative n m k)

-- Substitute the left part of the sum to an equal value
plusSubstitutes : {m n' : Nat} -> (n : Nat) -> n == n' -> (n + m) == (n' + m)
plusSubstitutes {Zero} {n'} n x = 
  n + Zero 
  ⟨ plusZero n ⟩ 
  n 
  ⟨ x ⟩
  n' 
  ⟨ sym (plusZero n') ⟩ 
  (n' + Zero) 
  qed
plusSubstitutes {Succ m} {Zero} Zero x = Refl
plusSubstitutes {Succ m} {Succ n'} Zero  x = 
  Succ m
  ⟨ cong Succ (plusSubstitutes 0  x) ⟩ 
  Succ (Succ (n' + m)) 
  ⟨ plusSucc (Succ n') m  ⟩ 
  Succ (n' + Succ m) 
  qed
plusSubstitutes {Succ m} {Zero} (Succ n) x =
  Succ (n + Succ m) 
  ⟨ cong Succ (sym (plusSucc n m)) ⟩ 
  Succ (Succ (n + m)) 
  ⟨ cong Succ (plusSubstitutes (Succ n) x) ⟩ 
  Succ m
  qed
plusSubstitutes {Succ m} {Succ n'} (Succ n) x =
  Succ (n + Succ m)
  ⟨ cong Succ (sym (plusSucc n m)) ⟩
  Succ (Succ (n + m)) 
  ⟨ cong Succ (plusSubstitutes (Succ n)  x) ⟩ 
  Succ (Succ (n' + m)) 
  ⟨ cong Succ (plusSucc n' m) ⟩
  Succ (n' + Succ m) 
  qed

-- Simpler notation of the substitution for the plus operator
+-substitute-left_by_ : {m n' : Nat} -> (n : Nat) ->  n == n' -> (n + m) == (n' + m)
+-substitute-left_by_ = plusSubstitutes

+-substitute-right_by_ : {m n' : Nat} -> (n : Nat) ->  n == n' -> (m + n) == (m + n')
+-substitute-right_by_ = λ {m} {n'} n x → 
  m + n 
  ⟨ plusCommutes m n ⟩
  n + m 
  ⟨ +-substitute-left n by x ⟩
  n' + m 
  ⟨ plusCommutes n' m ⟩
  (m + n') 
  qed

+-substitute_and_ : {m n m' n' : Nat} -> (m == m') -> (n == n') -> (m + n) == (m' + n')
+-substitute_and_ = λ {m} {n} {m'} {n'} x y → 
  m + n 
  ⟨ +-substitute-left m by x ⟩ 
  m' + n 
  ⟨ +-substitute-right n by y ⟩ 
  (m' + n') 
  qed

-- Some lemmas about the times operator
timesZero : (n : Nat) -> (n * Zero) == 0
timesZero Zero = Refl
timesZero (Succ n) = timesZero n

timesCommutes : (n m : Nat) -> (n * m) == (m * n)
timesCommutes Zero Zero = Refl
timesCommutes Zero (Succ m) = sym (timesZero m)
timesCommutes (Succ n) Zero = timesZero n
timesCommutes (Succ n) (Succ m) = 
  Succ (m + (n * Succ m)) 
  ⟨ +-substitute-right n * Succ m by timesCommutes n (Succ m) ⟩ 
  Succ (m + (n + (m * n)))
  ⟨ plusAssociative (Succ m) n (m * n) ⟩
  Succ ((m + n) + (m * n)) 
  ⟨ +-substitute-left Succ m + n by plusSucc m n ⟩ 
  (m + Succ n) + (m * n) 
  ⟨ +-substitute-left m + Succ n by plusCommutes m (Succ n) ⟩ 
  Succ ((n + m) + (m * n)) 
  ⟨ +-substitute-right m * n by timesCommutes m n ⟩ 
  Succ ((n + m) + (n * m))
  ⟨ sym (plusAssociative (Succ n) m (n * m)) ⟩ 
  Succ (n + (Succ n * m)) 
  ⟨ +-substitute-right Succ n * m by timesCommutes (Succ n) m ⟩ 
  (Succ m * Succ n) 
  qed

-- Prove that we can substitute from times too
timesSubstitutes : (n m n' : Nat) -> n == n' -> (n * m) == (n' * m)
timesSubstitutes n Zero n' x = trans (timesZero n) (sym (timesZero n'))
timesSubstitutes Zero (Succ m) Zero x = Refl
timesSubstitutes Zero (Succ m) (Succ n') x =
  Zero * m 
  ⟨ timesSubstitutes Zero m (Succ n') x ⟩ 
  Succ n' * m
  ⟨ timesCommutes (Succ n') m ⟩ 
  m * Succ n' 
  ⟨ +-substitute-left 0 by x ⟩ 
  Succ m * Succ n' 
  ⟨ timesCommutes (Succ m) (Succ n') ⟩
  (Succ n' * Succ m)
  qed 

timesSubstitutes (Succ n) (Succ m) Zero x =
  Succ n * Succ m
  ⟨ timesCommutes (Succ n) (Succ m) ⟩
  Succ m * Succ n 
  ⟨ +-substitute-left Succ n by x ⟩
  m * Succ n
  ⟨ timesCommutes m (Succ n) ⟩ 
  Succ n * m 
  ⟨ timesSubstitutes (Succ n) m 0 x ⟩ 
  Zero
  qed
timesSubstitutes (Succ n) (Succ m) (Succ n') x =
  Succ n * Succ m 
  ⟨ timesCommutes (Succ n) (Succ m) ⟩ 
  Succ m * Succ n 
  ⟨ +-substitute-left Succ n by x ⟩ 
  Succ (n' + (m * Succ n)) 
  ⟨ +-substitute-right m * Succ n by timesCommutes m (Succ n) ⟩ 
  Succ (n' + (Succ n * m))
  ⟨ +-substitute-right Succ n * m by
      timesSubstitutes (Succ n) m (Succ n') x ⟩ 
  Succ (n' + (Succ n' * m))
  ⟨ +-substitute-right Succ n' * m by timesCommutes (Succ n') m ⟩ 
  Succ m * Succ n'
  ⟨ timesCommutes (Succ m) (Succ n') ⟩ 
  (Succ n' * Succ m) 
  qed

-- Again some easier notation for the substitution
*-substitute-left_by_ : {m n' : Nat} -> (n : Nat) ->  n == n' -> (n * m) == (n' * m)
*-substitute-left_by_ = λ {m} {n'} n x → timesSubstitutes n m n' x

*-substitute-right_by_ : {m n' : Nat} -> (n : Nat) ->  n == n' -> (m * n) == (m * n')
*-substitute-right_by_ = λ {m} {n'} n x → 
  m * n 
  ⟨ timesCommutes m n ⟩
  n * m 
  ⟨ *-substitute-left n by x ⟩
  n' * m 
  ⟨ timesCommutes n' m ⟩
  (m * n') 
  qed

*-substitute_and_ : {m n m' n' : Nat} -> (m == m') -> (n == n') -> (m * n) == (m' * n')
*-substitute_and_ = λ {m} {n} {m'} {n'} x y → 
  m * n 
  ⟨ *-substitute-left m by x ⟩ 
  m' * n 
  ⟨ *-substitute-right n by y ⟩ 
  (m' * n') 
  qed

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) Zero Zero =
  n * Zero 
  ⟨ +-substitute-right 0 by (sym (timesZero n)) ⟩ 
  ((n * Zero) + (n * Zero)) 
  qed
distributivity (Succ n) Zero (Succ k) =
  sym (
    (Succ n * Zero) + (Succ n * Succ k) 
    ⟨ +-substitute-left Succ n * Zero by timesZero (Succ n) ⟩ 
    (Succ n * Succ k)
    qed
  )
distributivity (Succ n) (Succ m) Zero =
  Succ ((m + Zero) + (n * Succ (m + Zero)))
  ⟨ +-substitute-left Succ m + Zero by plusZero (Succ m) ⟩ 
  Succ (m + (n * Succ (m + Zero)))
  ⟨ +-substitute-right n * Succ (m + Zero) by
      (*-substitute-right Succ m + Zero by plusZero (Succ m)) ⟩ 
  (Succ n * Succ m) 
  ⟨ +-substitute-right 0 by sym (timesZero n) ⟩ 
  ((Succ n * Succ m) + (n * 0)) qed
distributivity (Succ n) (Succ m) (Succ k) = sym (
  Succ ((m + (n * Succ m)) + Succ (k + (n * Succ k))) 
  ⟨ plusSucc (m + (n * Succ m)) (Succ (k + (n * Succ k))) ⟩ 
  (m + (n * Succ m)) + Succ (Succ (k + (n * Succ k))) 
  ⟨ plusSym (m + (n * Succ m)) (Succ (k + (n * Succ k))) ⟩ 
  Succ (k + (n * Succ k)) + Succ (m + (n * Succ m)) 
  ⟨ plusCommutes (Succ (k + (n * Succ k))) (Succ (m + (n * Succ m))) ⟩ 
  Succ (m + (n * Succ m)) + Succ (k + (n * Succ k))
  ⟨ +-substitute (plusSucc m (n * Succ m)) and (plusSucc k (n * Succ k)) ⟩ 
  (m + Succ (n * Succ m)) + (k + Succ (n * Succ k)) 
  ⟨ +-substitute (plusSym m (n * Succ m)) and (plusSym k (n * Succ k)) ⟩ 
  ((n * Succ m) + Succ m) + ((n * Succ k) + Succ k) 
  ⟨ +-substitute (plusCommutes (n * Succ m) (Succ m)) and (plusCommutes (n * Succ k) (Succ k)) ⟩ 
  (Succ m + (n * Succ m)) + (Succ k + (n * Succ k))
  ⟨ sym (plusAssociative (Succ m) (n * Succ m) (Succ k + (n * Succ k))) ⟩
  Succ (m + ((n * Succ m) + Succ (k + (n * Succ k))))
  ⟨ +-substitute-right ((n * Succ m) + Succ (k + (n * Succ k))) by (plusAssociative (n * Succ m) (Succ k) (n * Succ k)) ⟩
  Succ (m + (((n * Succ m) + Succ k) + (n * Succ k))) 
  ⟨ +-substitute-right (((n * Succ m) + Succ k) + (n * Succ k)) by  (+-substitute-left ((n * Succ m) + Succ k) by (plusCommutes (n * Succ m) (Succ k))) ⟩ 
  Succ (m + Succ ((k + (n * Succ m)) + (n * Succ k))) 
  ⟨ +-substitute-right (Succ ((k + (n * Succ m)) + (n * Succ k))) by (sym (plusAssociative (Succ k) (n * Succ m) (n * Succ k))) ⟩ 
  Succ (m + Succ (k + ((n * Succ m) + (n * Succ k)))) 
  ⟨ plusAssociative (Succ m) (Succ k) ((n * Succ m) + (n * Succ k)) ⟩ 
  Succ ((m + Succ k) + ((n * Succ m) + (n * Succ k))) 
  ⟨ +-substitute-right ((n * Succ m) + (n * Succ k)) by (sym (distributivity n (Succ m) (Succ k))) ⟩
  Succ ((m + Succ k) + (n * Succ (m + Succ k))) 
  qed
  )

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
SubListTrans Base (Drop ys) = Drop ys
SubListTrans (Keep xs) (Keep ys) = Keep (SubListTrans xs ys)
SubListTrans (Drop xs) (Keep ys) = Drop (SubListTrans xs ys)
SubListTrans xs (Drop ys) = Drop (SubListTrans xs ys)

-- Two function to show the contradiction in the anti symmetry proof.
SubListAux : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList xs ys
SubListAux (Keep s) = Drop s
SubListAux (Drop s) = Drop (SubListAux s)

SubListBollocks : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList ys xs -> Empty
SubListBollocks (Keep xs) ys = SubListBollocks ys xs
SubListBollocks (Drop xs) (Keep ys) = SubListBollocks xs (Drop ys)
SubListBollocks (Drop xs) (Drop ys) = SubListBollocks (SubListAux xs) (SubListAux ys)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base Base = Refl
SubListAntiSym (Keep {x} xs) (Keep {.x} ys) = cong (Cons x) (SubListAntiSym xs ys)
SubListAntiSym (Keep xs) (Drop ys) = magic (SubListBollocks ys xs)
SubListAntiSym (Drop xs) ys = magic (SubListBollocks ys xs)

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Base : forall {n} -> LEQ 0 n
  Step : forall {n m} -> LEQ n m -> LEQ (Succ n) (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base y = Base
leqTrans (Step x) (Step y) = Step (leqTrans x y)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step x) (Step y) = cong Succ (leqAntiSym x y)

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
<=leq Zero m _ = Base
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
notNotP p = λ f  → f p

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
notNotExcludedMiddle = λ f → f (Inr (λ x → f (Inl x))) 

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.


doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...


--step1 : doubleNegation -> excludedMiddle
step1 : {P : Set} -> Not (Not P) -> P -> Or P (Not P)
step1 dn p = Inl p

--step2 : excludedMiddle -> impliesToOr
step2 : {P Q : Set} -> Or P (Not P) -> (P -> Q) -> Or (Not P) Q
step2 (Inl x) f = Inr (f x)
step2 (Inr x) f = Inl x

--step3 : impliesToOr -> doubleNegation
step3 : {P Q : Set} -> (P -> Q) -> Or (Not P) Q -> Not (Not P) -> P
step3 f (Inl x) dn = magic (dn x)
step3 f (Inr x) dn =  magic (dn (λ y → {!!}))

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

data Term : Nat -> Set where
  Var : forall {n : Nat} -> (k : Nat) -> LEQ k n -> Term n
  Lam : forall {n : Nat} -> Term (Succ n) -> Term n
  App : forall {n : Nat} -> Term n -> Term n -> Term n

-- Some useful functions for maybe
mapMaybe : {a b : Set} -> (a -> b) -> Maybe a -> Maybe b
mapMaybe f (Just x) = Just (f x)
mapMaybe f Nothing = Nothing

_<m*>_ : {a b : Set} -> Maybe (a -> b) -> Maybe a -> Maybe b
Just f <m*> x = mapMaybe f x
Nothing <m*> x = Nothing

-- Try to prove that n <= m
proveLEQ : (n m : Nat) -> Maybe (LEQ n m)
proveLEQ Zero m = Just Base
proveLEQ (Succ n) Zero = Nothing
proveLEQ (Succ n) (Succ m) = mapMaybe (λ x -> Step x) (proveLEQ n m)


mapRaw : {n : Nat} -> Raw -> Maybe (Term n)
mapRaw (Lam r) = mapMaybe (λ x -> Lam x) (mapRaw r)
mapRaw (App p q) = mapMaybe (λ x y → App x y) (mapRaw p) <m*> mapRaw q
mapRaw {n} (Var x) = mapMaybe (λ y -> Var x y) (proveLEQ x n)

