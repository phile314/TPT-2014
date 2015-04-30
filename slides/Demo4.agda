module Demo4 where

postulate String : Set

{-# BUILTIN STRING String #-}

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
decideEq (Succ n) (Succ m) with decideEq n m
decideEq (Succ n) (Succ m) | Inl x = Inl (cong Succ x)
decideEq (Succ n) (Succ m) | Inr x = Inr (\p -> x (aux p))

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


-- First exercise set now online

-- Yorick Sijsling in the Colloquium tomorrow

-- Choose your papers!

-- Start thinking about potential projects...



-- Custom induction principles

double : ℕ -> ℕ
double Zero = Zero
double (Succ n) = Succ (Succ (double n))

data Parity : ℕ -> Set where
  IsOdd : (k : ℕ) -> Parity (Succ (double k))
  IsEven : (k : ℕ) -> Parity (double k)

parity? : (n : ℕ) -> Parity n
parity? Zero = IsEven 0
parity? (Succ Zero) = IsOdd 0
parity? (Succ (Succ n)) with parity? n
parity? (Succ (Succ .(Succ (double k)))) | IsOdd k = IsOdd (Succ k)
parity? (Succ (Succ .(double k))) | IsEven k = IsEven (Succ k)

my-function-on-naturals : (x : ℕ) -> ℕ
my-function-on-naturals (x) with parity? x
my-function-on-naturals .(Succ (double k)) | IsOdd k = {!!}
my-function-on-naturals .(double k) | IsEven k = {!!}

my-lemma-on-naturals : {P : ℕ -> Set} -> (x : ℕ) -> P x
my-lemma-on-naturals x with parity? x
my-lemma-on-naturals .(Succ (double k)) | IsOdd k = {!!}
my-lemma-on-naturals .(double k) | IsEven k = {!!}

forget : {n : ℕ} -> Fin n -> ℕ
forget FZero = Zero
forget (FSucc i) = Succ (forget i)

data Bounds (bound : ℕ) : ℕ -> Set where
  InBounds : (i : Fin bound) -> Bounds bound (forget i)
  OutOfBounds : (k : ℕ) -> Bounds bound (k + bound)

checkBound : (bound : ℕ) -> (x : ℕ) -> Bounds bound x
checkBound bound x = {!!}

lookup : forall {bound : ℕ} -> (x : ℕ) -> Vector Bool bound -> Maybe Bool
lookup {bound} n xs with checkBound bound n 
lookup .(forget i) xs | InBounds i = Just (vlookup xs i)
lookup ._ xs | OutOfBounds k = {!...!}

-- Type classes in Agda

data U : Set where
  NAT : U
  BOOL : U
  EITHER : U -> U -> U

-- el : U -> Set
-- el NAT = ℕ
-- el BOOL = Bool
-- el (EITHER u u₁) = Either (el u) (el u₁)

-- show : {u : U} -> el u -> String
-- show {NAT} x = "It's a number!"
-- show {BOOL} True = "True"
-- show {BOOL} False = "False"
-- show {EITHER u u₁} (Inl x) = show {u} x
-- show {EITHER u u₁} (Inr x) = show {u₁} x

-- Statically typed printf

data Unit : Set where
  tt : Unit

postulate Char : Set 
{-# BUILTIN CHAR Char #-}

printfType : List Char -> Set
printfType Nil = Unit
printfType (Cons x Nil) = Unit
printfType (Cons '%' (Cons 's' xs)) = String -> printfType xs
printfType (Cons '%' (Cons 'd' xs)) = ℕ -> printfType xs
printfType (Cons x (Cons x₁ xs)) = printfType (Cons x₁ xs)

-- Lambda calculus in Agda

-- data Raw : Set where 
--   Lam : Raw -> Raw
--   App : Raw -> Raw -> Raw
--   Var : ℕ -> Raw

-- eval : Raw -> {!!}
-- eval r = {!!} 

data Type : Set where
  I : Type
  _=>_ : Type -> Type -> Type

Context = List Type

data Ref : Context -> Type -> Set where
  Top : forall {s G} -> Ref (Cons s G) s
  Pop : forall {s t G} -> Ref G s -> Ref (Cons t G) s 

data Term : Context -> Type -> Set where
  App : ∀ {σ τ Γ} -> Term Γ (σ => τ) -> Term Γ σ -> Term Γ τ
  Lam : forall {s t G} -> Term (Cons s G) t -> Term G (s => t)
  Var : forall {s G} -> Ref G s -> Term G s

el : Type -> Set
el I = Unit
el (t => t₁) = el t -> el t₁

data Env : Context -> Set where
  ENil : Env Nil
  ECons : forall {s ctx} -> el s -> Env ctx -> Env (Cons s ctx)

envLookup : forall {s G} -> Env G -> Ref G s -> el s
envLookup (ECons x env) Top = x
envLookup (ECons x env) (Pop r) = envLookup env r

eval : forall {s G} -> Env G -> Term G s -> el s
eval env (App t t₁) = (eval env t) (eval env t₁)
eval env (Lam t₁) = \x -> eval (ECons x env) t₁
eval env (Var x) = envLookup env x

