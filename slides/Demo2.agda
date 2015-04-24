module Demo2 where

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

_+_ : ℕ → ℕ → ℕ
Zero + n = n
(Succ m) + n = Succ (m + n)

id : {a : Set} -> a -> a
id {a} x = x

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

xs : List Bool
xs = Cons True (Cons False (Cons True Nil))

data Maybe (a : Set) : Set where 
  Nothing : Maybe a
  Just : a -> Maybe a

_!!_ : {a : Set} -> List a -> ℕ -> Maybe a
Nil !! i = Nothing
Cons x xs !! Zero = Just x
Cons x xs !! (Succ i) = xs !! i


filter : {a : Set} -> (a -> Bool) -> List a -> List a
filter p Nil = Nil
filter p (Cons x xs) = if p x then (Cons x (filter p xs)) else filter p xs

head : {a : Set} -> List a -> a
head Nil = {!!}
head (Cons x xs) = x

data Vector (a : Set) : ℕ -> Set where
  Nil : Vector a Zero
  Cons : {n : ℕ} -> a -> Vector a n -> Vector a (Succ n)

xs' : Vector Bool (Succ (Succ (Succ Zero)))
xs' = Cons True (Cons False (Cons False Nil))

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

vlookup' : {n : ℕ} {a : Set} -> Vector a n -> (m : ℕ) -> m < n -> a
vlookup' Nil Zero ()
vlookup' Nil (Succ m) ()
vlookup' (Cons x xs) Zero p = x
vlookup' (Cons x xs) (Succ n₁) (Step p) = vlookup' xs n₁ p

lookup : {a : Set} -> (xs : List a) -> (m : ℕ) -> m < length xs -> a
lookup Nil m ()
lookup (Cons x xs) Zero z = x
lookup (Cons x xs) (Succ n) (Step z) = lookup xs n z

example = lookup (Cons True (Cons False Nil)) (Succ Zero) (Step Base)

vappend : {n m : ℕ} {a : Set} -> Vector a n -> Vector a m -> Vector a (n + m)
vappend Nil ys = ys
vappend (Cons x xs) ys = Cons x (vappend xs ys)

x : Vector Bool (Succ (Succ Zero))
x = Cons True (Cons False Nil)

doubled : Vector Bool (Succ (Succ (Succ (Succ Zero))))
doubled = vappend x x
