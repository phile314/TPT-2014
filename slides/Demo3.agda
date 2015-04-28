module Demo3 where

data Bool : Set where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True

if_then_else_ : {a : Set} -> Bool -> a -> a -> a
if True then t else e = t
if False then t else e = e

data ℕ : Set where
  Zero : ℕ
  Succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
Zero + n = n
(Succ m) + n = Succ (m + n)

id : {a : Set} -> a -> a
id {a} x = x

data Either (a b : Set) : Set where
  Inl : a -> Either a b
  Inr : b -> Either a b

foo = id {Bool} True

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

length : {a : Set} -> List a -> ℕ
length Nil = Zero
length (Cons _ xs) = Succ (length xs)

_++_ : ∀ {a : Set} -> List a -> List a -> List a
Nil ++ ys = ys
Cons x xs ++ ys = Cons x (xs ++ ys)

filter : {a : Set} -> (a -> Bool) -> List a -> List a
filter p Nil = Nil
filter p (Cons x xs) with p x
... | True = Cons x (filter p xs)
... | False = filter p xs

data Vector (a : Set) : ℕ -> Set where
  Nil : Vector a Zero
  Cons : {n : ℕ} -> a -> Vector a n -> Vector a (Succ n)

vhead :  {a : Set} -> (n : ℕ) -> Vector a (Succ n) -> a
vhead n (Cons x xs) = x

data Fin : ℕ -> Set where
  FZero : ∀ {n : ℕ} -> Fin (Succ n)
  FSucc : ∀ {n} -> Fin n -> Fin (Succ n)

vlookup : {n : ℕ} {a : Set} -> Vector a n -> Fin n -> a
vlookup (Cons x xs) FZero = x
vlookup (Cons x xs) (FSucc i) = vlookup xs i


data _<_ : ℕ -> ℕ -> Set where
  Base : forall {n} -> Zero < Succ n
  Step : forall {n m} -> n < m -> Succ n < Succ m

vappend : {n m : ℕ} {a : Set} -> Vector a n -> Vector a m -> Vector a (n + m)
vappend {.Zero} Nil ys = ys
vappend {._} (Cons {k} x xs) ys = Cons x (vappend xs ys)

-- _==_ : ℕ -> ℕ -> Bool
-- Zero == Zero = True
-- Zero == Succ y = False
-- Succ x == Zero = False
-- Succ x == Succ y = x == y

data _==_ : ℕ -> ℕ -> Set where
  Refl : forall {n} -> n == n

sym : (x y : ℕ) -> x == y -> y == x
sym x .x Refl = Refl

trans : forall {x y z} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

cong : forall {x y} -> (f : ℕ -> ℕ) -> x == y -> (f x) == (f y)
cong f Refl = Refl

proof : (n : ℕ) -> (n + 0) == n
proof Zero = Refl
proof (Succ n) = cong Succ (proof n)

infixr 2 _⟨_⟩_
_⟨_⟩_ : (x : ℕ) -> {y z : ℕ} -> (x == y) -> (y == z) -> x == z
x ⟨ p ⟩ q = trans p q

_■ : forall x -> x == x
_■ x = Refl

proof' : (n : ℕ) -> (n + 0) == n
proof' Zero = Refl
proof' (Succ n) = 
  (Succ n) + 0
  ⟨ Refl ⟩
  Succ (n + 0)
  ⟨ cong Succ (proof' n) ⟩
  Succ n 
  ■

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

data Empty : Set where

aux : {n m : ℕ} -> Succ n == Succ m -> n == m 
aux Refl = Refl

decideEq : (n m : ℕ) -> Either (n == m) (n == m -> Empty)
decideEq Zero Zero = Inl Refl
decideEq Zero (Succ m) = Inr λ ()
decideEq (Succ n) Zero = Inr λ ()
decideEq (Succ n) (Succ m) = helper n m (decideEq n m)
  where
  helper : (n m : ℕ) -> Either (n == m) (n == m -> Empty) -> 
                      Either (Succ n == Succ m) (Succ n == Succ m -> Empty)
  helper n m p = {!!}

-- with decideEq n m
-- decideEq (Succ n) (Succ .n) | Inl Refl = {!!}
-- ... | Inr diff = Inr (\prf -> diff (aux prf))

data Sublist {a : Set} : List a -> List a -> Set where
  Base : forall {xs} -> Sublist Nil xs  
  Skip : forall {x xs ys } -> Sublist xs ys -> Sublist xs (Cons x ys) 
  Keep : forall {x xs ys } -> Sublist xs ys -> Sublist (Cons x xs) (Cons x ys) 

example : Sublist (Cons 1 Nil) (Cons 2 (Cons 1 (Cons 3 Nil)))
example = Skip (Keep Base)

filter-lemma : {a : Set} -> (xs : List a) -> (p : a -> Bool) -> Sublist (filter p xs) xs
filter-lemma Nil p = Base
filter-lemma (Cons x xs) p with p x
filter-lemma (Cons x xs) p | True = Keep (filter-lemma xs p)
filter-lemma (Cons x xs) p | False = Skip (filter-lemma xs p)

forget : {n : ℕ} -> Fin n -> ℕ
forget i = {!!}

data Check (bound : ℕ) : ℕ -> Set where
  InBounds : ∀ {i : Fin bound} -> Check bound (forget (i))
  OutOfBounds : {k : ℕ} -> Check bound (k + bound)


