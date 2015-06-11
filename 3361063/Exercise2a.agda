
module Exercise2a where
--open import Agda.Primitive
--------------------------------------------------------------------------------
--Instructions--
{-
Fill in the holes below

Extend the language with tuples, fst, and snd

Complete the proofs again

You may want to check Chapter 11.7 of Pierce's book to see how he defines
the syntax, semantics and types for tuples.

Hint: in many of the lemmas, I have made all arguments
explicit. This way I don't give away too much information about how
to do your induction. In many cases, you can make many of these
arguments implicit. It's a good idea to do so -- it'll make your
lemmas much more readable.
-}
--------------------------------------------------------------------------------

-------------------------------------------------------------------------------
----------------------                 Prelude             --------------------
-------------------------------------------------------------------------------

-- Equality.
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
  
cong : {a b : Set} {x y : a} (f : a -> b) -> x == y -> f x == f y
cong f refl = refl

_∎ : {X : Set} (x : X) -> x == x
x ∎ = refl
_=⟨_⟩_ : {X : Set} -> (x : X) -> ∀ {y z} -> x == y -> y == z -> x == z
x =⟨ refl ⟩ q   = q
_=⟨_]_ : {X : Set} -> (x : X) -> ∀ {y z} -> y == x -> y == z -> x == z
x =⟨ refl ] q   = q
infixr 2 _=⟨_⟩_

-- Contradiction type.
data Empty : Set where

-- Reducto ab absurdum.
contradiction : {A : Set} → Empty → A
contradiction ()

-- Negation
Not : Set → Set
Not A = A → Empty

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b


-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

data Type : Set where
  NAT : Type
  BOOL : Type
  PAIR : Type -> Type -> Type

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT
  vpair : ∀{tₗ tᵣ} (l : Value tₗ) (r : Value tᵣ) -> Value (PAIR tₗ tᵣ)

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL 
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  pair          : ∀ {tₗ tᵣ} (l : Term tₗ)(r : Term tᵣ) -> Term (PAIR tₗ tᵣ)
  projₗ         : ∀ {tₗ tᵣ} -> Term (PAIR tₗ tᵣ) -> Term tₗ
  projᵣ         : ∀ {tₗ tᵣ} -> Term (PAIR tₗ tᵣ) -> Term tᵣ


natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
⌜ vpair l r ⌝ = pair ⌜ l ⌝ ⌜ r ⌝

-- Example term.
ex : Term NAT -> Term BOOL 
ex t = if iszero t then false else true

------------------------------------------------------------------------
-- Denotational semantics.
--------------------------------------------------------------------------------

-- Evaluation of if-then-else expressions applied to values.
cond : forall {ty} -> Value BOOL → Value ty → Value ty → Value ty
cond vtrue v2 v3 = v2
cond vfalse v2 v3 = v3

vsucc : Value NAT -> Value NAT
vsucc (vnat x) = vnat (Succ x)

viszero : Value NAT -> Value BOOL
viszero (vnat Zero) = vtrue
viszero (vnat (Succ x)) = vfalse

vprojₗ : ∀{l r} -> Value (PAIR l r) -> Value l
vprojₗ (vpair l r) = l

vprojᵣ : ∀{l r} -> Value (PAIR l r) -> Value r
vprojᵣ (vpair l r) = r

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ pair l r ⟧ = vpair ⟦ l ⟧ ⟦ r ⟧
⟦ projₗ p ⟧ = vprojₗ ⟦ p ⟧
⟦ projᵣ p ⟧ = vprojᵣ ⟦ p ⟧

-- What can we do to define a denotational semantics?
--   Add types!

-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

-- Evidence type that shows a certain term represents a value.
data Is-value {ty : Type} : Term ty → Set where
  is-value : ∀ v → Is-value ⌜ v ⌝

toVal : forall {ty} -> (t : Term ty) -> Is-value t -> Value ty
toVal .(⌜ v ⌝) (is-value v) = v

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ       : forall {t t' : Term NAT} -> Step {NAT} t t' -> Step {NAT} (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) (true)
  E-IsZeroSucc : {v : Value NAT} -> Step (iszero (succ ⌜ v ⌝)) false
  E-IsZero     : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  E-Left       : ∀{tₗ tᵣ}{l l' : Term tₗ}{r : Term tᵣ} -> Step {tₗ} l l' ->  Step {PAIR tₗ tᵣ} (pair l r) (pair l' r)
  E-Right      : ∀{tₗ tᵣ}{l : Term tₗ}{r r' : Term tᵣ} -> {v : Is-value {tₗ} l} -> Step {tᵣ} r r' ->  Step {PAIR tₗ tᵣ} (pair l r) (pair l r')
  E-Projₗ      : ∀{tₗ tᵣ}{l : Term tₗ}{r : Term tᵣ}{v : Is-value (pair l r)} -> Step (projₗ (pair l r)) l
  E-Projₗ'     : ∀{tₗ tᵣ}{t t' : Term (PAIR tₗ tᵣ)} -> Step t t' -> Step (projₗ t) (projₗ t')
  E-Projᵣ      : ∀{tₗ tᵣ}{l : Term tₗ}{r : Term tᵣ}{v : Is-value (pair l r)} -> Step (projᵣ (pair l r)) r
  E-Projᵣ'     : ∀{tₗ tᵣ}{t t' : Term (PAIR tₗ tᵣ)} -> Step t t' -> Step (projᵣ t) (projᵣ t')

-- So we can add *types* to our term language. 
--
-- But when is a type system 'good'?
-- What would we like to prove about the relation between our semantics and well-typed terms?


-- A term is reducible when some evaluation step can be applied to it.
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : {t' : Term ty} -> Step t t' -> Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} -> Term ty → Set
NF t = Red t -> Empty

valuesDoNotStep : forall {ty} -> (v : Value ty) {t : Term ty} -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue ()
valuesDoNotStep vfalse ()
valuesDoNotStep (vnat Zero) ()
valuesDoNotStep (vnat (Succ x)) (E-Succ step) = valuesDoNotStep (vnat x) step
valuesDoNotStep (vpair l r) (E-Left step) = valuesDoNotStep l step
valuesDoNotStep (vpair l r) (E-Right step) = valuesDoNotStep r step

values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces x) = valuesDoNotStep v x

--------------------------------------------------------------------------------
-- Type safety (sometimes called type soundness)
--
--  * progress -- a well-typed term is a value or is reducible --
--    'well-typed terms are never stuck'
--
--  * preservation -- if a well-typed term performs an evaluation
--    step, the result is still well-typed
-- 
-- Together these two properties guarantee that 'well-typed programs
-- don't go wrong'
--------------------------------------------------------------------------------

preservation : forall {ty : Type} -> (t1 t2 : Term ty) ->
  Step t1 t2 -> ty == ty
preservation t1 t2 step = refl


mutual
  -- If-then-else terms are reducible.
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3 
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t) t4 t5 with iszero-reduces t
  if-reduces (iszero t) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (projₗ x) t4 t5 with projₗ-reduces x 
  if-reduces (projₗ x) t4 t5 | Reduces x₁ = Reduces (E-If-If x₁)
  if-reduces (projᵣ x) t4 t5 with projᵣ-reduces x
  if-reduces (projᵣ x) t4 t5 | Reduces x₁ = Reduces (E-If-If x₁)

  projₗ-reduces : ∀{tₗ tᵣ}(t : Term (PAIR tₗ tᵣ)) -> Red (projₗ t)
  projₗ-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂ 
  projₗ-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Projₗ' x)
  projₗ-reduces (pair t t₁) with progress t 
  projₗ-reduces (pair t t₁) | Left x with normal-forms-are-values t x
  projₗ-reduces (pair .(⌜ v ⌝) t₁) | Left x | is-value v with progress t₁
  projₗ-reduces (pair .(⌜ v ⌝) t₁) | Left v | is-value x₁ | Left x with normal-forms-are-values t₁ x
  projₗ-reduces (pair .(⌜ x₁ ⌝) .(⌜ v ⌝)) | Left x₁ | is-value v₁ | Left x | is-value v = Reduces (E-Projₗ {v = is-value (vpair v₁ v)})
  projₗ-reduces (pair .(⌜ x₁ ⌝) t₁) | Left x₁ | is-value v | Right (Reduces x) = Reduces (E-Projₗ' (E-Right x))
  projₗ-reduces (pair t t₁) | Right (Reduces x) = Reduces (E-Projₗ' (E-Left x))
  projₗ-reduces (projₗ t) with projₗ-reduces t 
  projₗ-reduces (projₗ t) | Reduces x = Reduces (E-Projₗ' x)
  projₗ-reduces (projᵣ t) with projᵣ-reduces t
  projₗ-reduces (projᵣ t) | Reduces x = Reduces (E-Projₗ' x)

  projᵣ-reduces : ∀{tₗ tᵣ}(t : Term (PAIR tₗ tᵣ)) -> Red (projᵣ t)
  projᵣ-reduces t = {!the same!}

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (projₗ t) with projₗ-reduces t
  iszero-reduces (projₗ t) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces (projᵣ t) with projᵣ-reduces t 
  iszero-reduces (projᵣ t) | Reduces x = Reduces (E-IsZero x)
  
  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k succ-nf
    where   succ-nf : NF k
            succ-nf (Reduces x) = nf (Reduces (E-Succ x))
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (pair {tᵣ = tᵣ} l r) nf₁ with normal-forms-are-values l left-nf , normal-forms-are-values r right-nf
    where   left-nf : NF l
            left-nf (Reduces x) = nf₁ (Reduces (E-Left x))
            right-nf : NF r
            right-nf (Reduces x) = nf₁ (Reduces (E-Right {v = normal-forms-are-values l (left-nf)} x))
  normal-forms-are-values (pair .(⌜ v ⌝) ._) nf | is-value v , is-value vᵣ = is-value (vpair v vᵣ)
  normal-forms-are-values (projₗ x) nf = contradiction (nf (projₗ-reduces x))
  normal-forms-are-values (projᵣ x) nf = contradiction (nf (projᵣ-reduces x))

-- Steps are deterministic: the same term can not be evaluated in more than one manner.
  deterministic : ∀ {ty} {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
  deterministic E-If-True E-If-True = refl
  deterministic E-If-True (E-If-If ())
  deterministic E-If-False E-If-False = refl
  deterministic E-If-False (E-If-If ())
  deterministic (E-If-If ()) E-If-True
  deterministic (E-If-If ()) E-If-False
  deterministic (E-If-If step1) (E-If-If step2) = cong (\x -> if x then _ else _) (deterministic step1 step2)
  deterministic (E-Succ step1) (E-Succ step2) = cong succ (deterministic step1 step2)
  deterministic E-IsZeroZero E-IsZeroZero = refl
  deterministic E-IsZeroZero (E-IsZero ())
  deterministic (E-IsZeroSucc {v}) steps2 = lemma v _ steps2
    where lemma : (v : Value NAT) (t : Term BOOL) -> Step (iszero (succ ⌜ v ⌝)) t -> false == t
          lemma v true ()
          lemma v false steps = refl
          lemma v (if t then t₁ else t₂) ()
          lemma v (iszero ._) (E-IsZero (E-Succ step)) = contradiction (valuesDoNotStep v step)
          lemma v₁ (projₗ t) ()
          lemma v₁ (projᵣ t) ()
  deterministic (E-IsZero ()) E-IsZeroZero
  deterministic (E-IsZero (E-Succ step1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v step1)
  deterministic (E-IsZero step1) (E-IsZero step2) = cong iszero (deterministic step1 step2)
  deterministic (E-Left step1) (E-Left step2) = cong (\l -> pair l _) (deterministic step1 step2)
  deterministic (E-Left step1) (E-Right {v = x} step2) = contradiction (values-are-normal-forms _ x (Reduces step1))
  deterministic (E-Right {v = x} step1) (E-Left step2) = contradiction (values-are-normal-forms _ x (Reduces step2))
  deterministic (E-Right step1) (E-Right step2) = cong (\r -> pair _ r) (deterministic step1 step2)
  deterministic E-Projₗ E-Projₗ = refl
  deterministic E-Projᵣ E-Projᵣ = refl
  deterministic (E-Projₗ {v = v}) (E-Projₗ' y) = contradiction (values-are-normal-forms (pair _ _) v (Reduces y))
  deterministic (E-Projₗ' x) (E-Projₗ {v = v}) = contradiction (values-are-normal-forms (pair _ _) v (Reduces x))
  deterministic (E-Projₗ' x) (E-Projₗ' y) = cong projₗ (deterministic x y)
  deterministic (E-Projᵣ {v = v}) (E-Projᵣ' y) = contradiction (values-are-normal-forms (pair _ _) v (Reduces y))
  deterministic (E-Projᵣ' x) (E-Projᵣ {v = v}) = contradiction (values-are-normal-forms (pair _ _) v (Reduces x))
  deterministic (E-Projᵣ' x) (E-Projᵣ' y) = cong projᵣ (deterministic x y)

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true = Left (values-are-normal-forms true (is-value vtrue))
  progress false = Left (values-are-normal-forms false (is-value vfalse))
  progress (if t then t₁ else t₂) = Right (if-reduces t _ _)
  progress zero = Left (values-are-normal-forms zero (is-value (vnat (Zero))))
  progress (succ t) with progress t 
  progress (succ t) | Left nf = Left lemma
    where lemma : Red (succ t) -> Empty
          lemma (Reduces (E-Succ x)) = nf (Reduces x)
  progress (succ t) | Right (Reduces step) = Right (Reduces (E-Succ step))
  progress (iszero t) with progress t
  progress (iszero t) | Left x with normal-forms-are-values t x
  progress (iszero .zero) | Left x₁ | is-value (vnat Zero) = Right (Reduces E-IsZeroZero)
  progress (iszero .(succ (natTerm x))) | Left x₁ | is-value (vnat (Succ x)) = 
    Right (Reduces (E-IsZeroSucc {vnat x}))
  progress (iszero t) | Right (Reduces step) = Right (Reduces (E-IsZero step))
  progress (pair l r) with progress l
  progress (pair l r) | Right (Reduces step) = Right (Reduces (E-Left step))
  progress (pair l r) | Left nf with progress r
  progress (pair l r) | Left nf | Right (Reduces step) = Right (Reduces (E-Right {v = normal-forms-are-values l nf} step))
  progress (pair l r) | Left nfₗ | Left nfᵣ = Left lemma
    where lemma : Red (pair l r) -> Empty
          lemma (Reduces (E-Left stepₗ)) = nfₗ (Reduces stepₗ)
          lemma (Reduces (E-Right stepᵣ)) = nfᵣ (Reduces stepᵣ)
  progress (projₗ x) with progress x
  progress (projₗ x) | Left x₁ with normal-forms-are-values x x₁ 
  progress (projₗ .(pair ⌜ v ⌝ ⌜ v₁ ⌝)) | Left x₁ | is-value (vpair v v₁) = Right (Reduces (E-Projₗ {v = is-value (vpair v v₁)}))
  progress (projₗ x) | Right (Reduces x₁) = Right (Reduces (E-Projₗ' x₁))
  progress (projᵣ x) with progress x
  progress (projᵣ x) | Left x₁ with normal-forms-are-values x x₁
  progress (projᵣ .(pair ⌜ v ⌝ ⌜ v₁ ⌝)) | Left x₁ | is-value (vpair v v₁) = Right (Reduces (E-Projᵣ {v = is-value (vpair v v₁)}))
  progress (projᵣ x) | Right (Reduces x₁) = Right (Reduces (E-Projᵣ' x₁))

--------------------------------------------------------------------------------
-- Sequences of small steps.
--------------------------------------------------------------------------------

-- A sequence of steps that can be applied in succession.
data Steps {ty : Type} : Term ty → Term ty → Set where
  Nil : forall {t} -> Steps t t
  Cons : forall {t1 t2 t3} -> Step t1 t2 -> Steps t2 t3 -> Steps t1 t3

-- Single-step sequence.
[_] : ∀ {ty} {t₁ t₂ : Term ty} -> Step t₁ t₂ -> Steps t₁ t₂
[_] x = Cons x Nil
  
-- Concatenation.
_++_ : ∀ {ty} {t₁ t₂ t₃ : Term ty} → Steps t₁ t₂ → Steps t₂ t₃ → Steps t₁ t₃
Nil ++ stps' = stps'
Cons x stps ++ stps' = Cons x (stps ++ stps')

infixr 5 _++_

-- Applying steps inside steps
-- φ wraps terms, like x ↦ if x then t else e
-- f wraps steps, like E-If-If
cong-map : forall {tyq tyr} -> { q q' : Term tyq } ->
          {φ : Term tyq -> Term tyr} ->
          (f : { a a' : Term tyq } -> Step a a' -> Step (φ a) (φ a')) ->
          Steps q q' -> Steps (φ q) (φ q')
cong-map f Nil = Nil
cong-map f (Cons x ss) = Cons (f x) (cong-map f ss)

uniqueness-of-normal-forms :
  ∀ {ty} {t t₁ t₂ : Term ty} →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ == t₂
uniqueness-of-normal-forms Nil Nil nf1 nf2 = refl
uniqueness-of-normal-forms Nil (Cons x s2) nf1 nf2 = contradiction (nf1 (Reduces x))
uniqueness-of-normal-forms (Cons x s1) Nil nf1 nf2 = contradiction (nf2 (Reduces x))
uniqueness-of-normal-forms (Cons x xs) (Cons y ys) nf1 nf2 with deterministic x y 
uniqueness-of-normal-forms (Cons x xs) (Cons y ys) nf1 nf2 | refl = uniqueness-of-normal-forms xs ys nf1 nf2


            
------------------------------------------------------------------------
-- Expressing and proving termination.

-- The execution of a term terminates when there exists a step
-- sequence that evaluates this term to a value.
data _⇓ {ty : Type} (t : Term ty) : Set where
  terminates : ∀ v → Steps t (⌜ v ⌝) → t ⇓

-- If t₁ evaluates to t₂, and t₂ terminates, then t₁ terminates as
-- well.
prepend-steps : ∀ {ty} {t₁ t₂ : Term ty} →  Steps t₁ t₂  → t₂ ⇓  → t₁ ⇓
prepend-steps steps (terminates v x₁) = terminates v (steps ++ x₁)

{-
E-If-Steps : ∀ {ty} {t t'} {t1 t2 : Term ty} →
        Steps t t' →
        Steps (if t then t1 else t2) (if t' then t1 else t2)
E-If-Steps Nil = Nil
E-If-Steps (Cons x steps) = Cons (E-If-If x) (E-If-Steps steps)

E-Succ-Steps : ∀ {t t' : Term NAT} -> 
        Steps t t' →
        Steps (succ t) (succ t')
E-Succ-Steps Nil = Nil
E-Succ-Steps (Cons x steps) = Cons (E-Succ x) (E-Succ-Steps steps)

E-IsZero-Steps : ∀ {t t' : Term NAT} -> 
        Steps t t' →
        Steps (iszero t) (iszero t')
E-IsZero-Steps Nil = Nil
E-IsZero-Steps (Cons x steps) = Cons (E-IsZero x) (E-IsZero-Steps steps)
-- -}

-- All steps terminate.
termination : ∀ {ty} (t : Term ty) → t ⇓
termination true = terminates vtrue Nil
termination false = terminates vfalse Nil
termination (if t then t₁ else t₂) with termination t
termination (if t then t₁ else t₂) | terminates vtrue x with termination t₁ 
termination (if t then t₁ else t₂) | terminates vtrue x₁ | terminates v x = 
  terminates v (cong-map E-If-If x₁  ++ [ E-If-True ] ++ x)
termination (if t then t₁ else t₂) | terminates vfalse x with termination t₂
termination (if t then t₁ else t₂) | terminates vfalse x₁ | terminates v x = 
  terminates v (cong-map E-If-If x₁ ++ [ E-If-False ] ++ x)
termination zero = terminates (vnat Zero) Nil
termination (succ t) with termination t
termination (succ t) | terminates (vnat x) q = terminates (vnat (Succ x)) (cong-map E-Succ q)
termination (iszero t) with termination t
termination (iszero t) | terminates (vnat Zero) s = terminates vtrue (cong-map E-IsZero s ++ [ E-IsZeroZero ])
termination (iszero t) | terminates (vnat (Succ x)) s = terminates vfalse (cong-map E-IsZero s ++ [ E-IsZeroSucc {vnat x} ])
termination (pair l r) with termination l ; ... | tₗ with termination r
termination (pair l r) | terminates vₗ sₗ | terminates vᵣ sᵣ = terminates (vpair vₗ vᵣ) (cong-map E-Left sₗ ++ cong-map (E-Right {v = is-value vₗ}) sᵣ) 
termination (projₗ x) with termination x
termination (projₗ x) | terminates (vpair v v₁) x₁ = terminates (vprojₗ (vpair v v₁)) (cong-map E-Projₗ' x₁ ++ [ E-Projₗ {v = is-value (vpair v v₁)} ])
termination (projᵣ x) with termination x
termination (projᵣ x) | terminates (vpair v v₁) x₁ = terminates (vprojᵣ (vpair v₁ v₁)) (cong-map E-Projᵣ' x₁ ++ [ E-Projᵣ {v = is-value (vpair v v₁)} ])

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalZero : zero ⇓ vnat (Zero)
  EvalSucc : forall {n c} -> c ⇓ vnat n -> succ c ⇓ vnat (Succ n)
  EvalIfTrue  : {ty : Type} {t e : Term ty} -> forall {c v} -> c ⇓ vtrue  -> t ⇓ v -> if c then t else e  ⇓ v
  EvalIfFalse : {ty : Type} {t e : Term ty} -> forall {c v} -> c ⇓ vfalse -> e ⇓ v -> if c then t else e  ⇓ v
  EvalIsZeroZero : forall {c} -> c ⇓ vnat Zero -> iszero c ⇓ vtrue
  EvalIsZeroSucc : forall {c n} -> c ⇓ vnat (Succ n) -> iszero c ⇓ vfalse
  EvalPair : {tₗ tᵣ : Type} {l : Term tₗ} {r : Term tᵣ} -> ∀ { vₗ vᵣ} -> l ⇓ vₗ -> r ⇓ vᵣ -> pair l r ⇓ vpair vₗ vᵣ
  EvalProjL : {tₗ tᵣ : Type} {p : Term (PAIR tₗ tᵣ)} {vₗ : Value tₗ} {vᵣ : Value tᵣ} -> p ⇓ vpair vₗ vᵣ -> projₗ p ⇓ vₗ
  EvalProjR : {tₗ tᵣ : Type} {p : Term (PAIR tₗ tᵣ)} {vₗ : Value tₗ} {vᵣ : Value tᵣ} -> p ⇓ vpair vₗ vᵣ -> projᵣ p ⇓ vᵣ

-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
--big-to-small (EvalValue (is-value v)) = Nil
big-to-small (EvalTrue) = Nil
big-to-small (EvalFalse) = Nil
big-to-small (EvalZero) = Nil
big-to-small (EvalSucc n) = cong-map E-Succ (big-to-small n)
big-to-small (EvalIfTrue c t) = cong-map E-If-If (big-to-small c) ++ [ E-If-True ] ++ (big-to-small t)
big-to-small (EvalIfFalse c t) = cong-map E-If-If (big-to-small c) ++ [ E-If-False ] ++ (big-to-small t)
big-to-small (EvalIsZeroZero x) = cong-map E-IsZero (big-to-small x) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroSucc x) = cong-map E-IsZero (big-to-small x) ++ [ (E-IsZeroSucc {vnat _}) ]
big-to-small (EvalPair {vₗ = vₗ} l r) = cong-map E-Left (big-to-small l) ++ cong-map (E-Right {v = is-value vₗ}) (big-to-small r)
big-to-small (EvalProjL {vₗ = vₗ}{vᵣ = vᵣ} x) = cong-map E-Projₗ' (big-to-small x) ++ [ (E-Projₗ {v = is-value (vpair vₗ vᵣ)}) ] 
big-to-small (EvalProjR {vₗ = vₗ}{vᵣ = vᵣ} x) = cong-map E-Projᵣ' (big-to-small x) ++ [ (E-Projᵣ {v = is-value (vpair vₗ vᵣ)}) ]

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = EvalTrue
value-to-value vfalse = EvalFalse
value-to-value (vnat Zero) = EvalZero
value-to-value (vnat (Succ n)) = EvalSucc (value-to-value (vnat n))
value-to-value (vpair l r) = EvalPair (value-to-value l) (value-to-value r)

steps-for-nat : (n : Nat) -> natTerm n ⇓ vnat n
steps-for-nat Zero = EvalZero
steps-for-nat (Succ n) = EvalSucc (steps-for-nat n)

prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True x₁ = EvalIfTrue (EvalTrue) x₁
prepend-step E-If-False x₁ = EvalIfFalse (EvalFalse) x₁
prepend-step (E-If-If d) (EvalIfTrue e e₁) = EvalIfTrue (prepend-step d e) e₁
prepend-step (E-If-If d) (EvalIfFalse e e₁) = EvalIfFalse (prepend-step d e) e₁
prepend-step (E-Succ s) (EvalSucc e) = EvalSucc (prepend-step s e)
prepend-step E-IsZeroZero EvalTrue = EvalIsZeroZero EvalZero
prepend-step (E-IsZeroSucc {vnat n}) EvalFalse = EvalIsZeroSucc (EvalSucc (steps-for-nat n))
prepend-step (E-IsZero s) (EvalIsZeroZero e) = EvalIsZeroZero (prepend-step s e)
prepend-step (E-IsZero s) (EvalIsZeroSucc e) = EvalIsZeroSucc (prepend-step s e)
prepend-step (E-Left step) (EvalPair l r) = EvalPair (prepend-step step l) r
prepend-step (E-Right step) (EvalPair l r) = EvalPair l (prepend-step step r)
prepend-step E-Projₗ y = {!!}
prepend-step E-Projᵣ y = {!!}
prepend-step (E-Projₗ' s) (EvalProjL y) = EvalProjL (prepend-step s y)
prepend-step (E-Projᵣ' s) (EvalProjR y) = EvalProjR (prepend-step s y)

small-to-big : {ty : Type} -> {t : Term ty} -> {v : Value ty} → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big Nil                   = value-to-value _
small-to-big (Cons E-If-True s)    = prepend-step E-If-True (small-to-big s)
small-to-big (Cons E-If-False s)   = prepend-step E-If-False (small-to-big s)
small-to-big (Cons (E-If-If x) s)  = prepend-step ((E-If-If x)) (small-to-big s)
small-to-big (Cons (E-Succ x₁) s)  = prepend-step (E-Succ x₁) (small-to-big s)
small-to-big (Cons E-IsZeroZero s) = prepend-step E-IsZeroZero (small-to-big s)
small-to-big (Cons (E-IsZeroSucc {v2}) s) = prepend-step (E-IsZeroSucc {v2}) (small-to-big s)
small-to-big (Cons (E-IsZero n) s) = prepend-step (E-IsZero n) (small-to-big s)
small-to-big (Cons (E-Left step) s) = prepend-step (E-Left step) (small-to-big s)
small-to-big (Cons (E-Right {v = v} step) s) = prepend-step ((E-Right {v = v}) step) (small-to-big s)
small-to-big (Cons (E-Projₗ {v = v}) s) = prepend-step (E-Projₗ {v = v}) (small-to-big s)
small-to-big (Cons (E-Projᵣ {v = v}) s) = prepend-step (E-Projᵣ {v = v}) (small-to-big s)
small-to-big (Cons (E-Projₗ' step) s) = prepend-step (E-Projₗ' step) (small-to-big s)
small-to-big (Cons (E-Projᵣ' step) s) = prepend-step (E-Projᵣ' step) (small-to-big s)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete zero = EvalZero
⇓-complete (if c then t₁ else t₂) with ⇓-complete c
⇓-complete (if c then t₁ else t₂) | _ with ⟦ c ⟧
⇓-complete (if c then t₁ else t₂) | d | vtrue  = EvalIfTrue d (⇓-complete t₁)
⇓-complete (if c then t₁ else t₂) | d | vfalse = EvalIfFalse d (⇓-complete t₂)
⇓-complete (succ t) with ⇓-complete t
⇓-complete (succ t) | c with ⟦ t ⟧
⇓-complete (succ t) | c | vnat x = EvalSucc c
⇓-complete (iszero n) with ⇓-complete n
⇓-complete (iszero n) | ⇓n with ⟦ n ⟧
⇓-complete (iszero n) | ⇓n | vnat Zero = EvalIsZeroZero ⇓n
⇓-complete (iszero n) | ⇓n | vnat (Succ x) = EvalIsZeroSucc ⇓n
⇓-complete (pair l r) with ⇓-complete l
⇓-complete (pair l r) | _ with ⇓-complete r
⇓-complete (pair l r) | ⇓l | ⇓r = EvalPair ⇓l ⇓r
⇓-complete (projₗ t) with ⇓-complete t 
... | ⇓t with ⟦ t ⟧ 
⇓-complete (projₗ t) | ⇓t | vpair vt vt₁ = EvalProjL ⇓t
⇓-complete (projᵣ t) with ⇓-complete t
... | ⇓t with ⟦ t ⟧ 
⇓-complete (projᵣ t) | ⇓t | vpair vt vt₁ = EvalProjR ⇓t


-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) {v : Value ty} → t ⇓ v → v == ⟦ t ⟧
⇓-sound true EvalTrue = refl
⇓-sound false EvalFalse = refl
⇓-sound zero EvalZero = refl
⇓-sound (succ n) (EvalSucc x) = cong vsucc (⇓-sound n x)
⇓-sound (if c then t else e) {v} (EvalIfTrue p p₁)  = v                      =⟨ ⇓-sound t p₁ ⟩
                                                      ⟦ t ⟧                  =⟨ cong (\x -> cond x ⟦ t ⟧ ⟦ e ⟧) (⇓-sound c p) ⟩
                                                      cond ⟦ c ⟧ ⟦ t ⟧ ⟦ e ⟧ ∎
⇓-sound (if c then t else e) {v} (EvalIfFalse p p₁) = v                      =⟨ ⇓-sound e p₁ ⟩
                                                      ⟦ e ⟧                  =⟨ cong (\x -> cond x ⟦ t ⟧ ⟦ e ⟧) (⇓-sound c p) ⟩
                                                      cond ⟦ c ⟧ ⟦ t ⟧ ⟦ e ⟧ ∎
⇓-sound (iszero c) (EvalIsZeroZero p) = cong viszero (⇓-sound c p)
⇓-sound (iszero c) (EvalIsZeroSucc p) = cong viszero (⇓-sound c p)
⇓-sound (pair l r) (EvalPair {vₗ = vₗ} {vᵣ = vᵣ} e e₁) = vpair vₗ vᵣ       =⟨ cong (\x -> vpair x vᵣ) (⇓-sound l e) ⟩
                                                         vpair ⟦ l ⟧ vᵣ    =⟨ cong (vpair ⟦ l ⟧) (⇓-sound r e₁) ⟩
                                                         vpair ⟦ l ⟧ ⟦ r ⟧ ∎
⇓-sound (projₗ x) (EvalProjL {vₗ = vₗ}{vᵣ = vᵣ} s) = cong vprojₗ (⇓-sound x s)
⇓-sound (projᵣ x) (EvalProjR {vₗ = vₗ}{vᵣ = vᵣ} s) = cong vprojᵣ (⇓-sound x s)

-- Retrospective
-- * Three styles of semantics: denotational, small step and big step
-- * All three can be shown to be equivalent
-- * To avoid handling 'stuck' terms, we introduced a typing discipline
-- * And proved type soundness -- 'well-typed terms can't go wrong'
--
--   (the proof was easy using Agda - because we only considered well-typed 
--   terms to begin with; usually we would need to do induction over the typing
--   derivation)
-- 
-- * All proofs are by easy induction -- finding the right definitions is hard!
