module Demo1 where

data Bool : Set where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True

if_then_else_ : Bool -> Bool -> Bool -> Bool
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