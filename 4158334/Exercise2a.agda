
module Exercise2a where

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

-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

data Type : Set where
  NAT : Type
  BOOL : Type
  _×_ : Type -> Type -> Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL 
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- Let's add tuples
  _,_           : {ty₁ ty₂ : Type} → (a : Term ty₁) → (b : Term ty₂) → Term (ty₁ × ty₂)
  fst           : {ty₁ ty₂ : Type} → (t : Term (ty₁ × ty₂)) → Term ty₁
  snd           : {ty₁ ty₂ : Type} → (t : Term (ty₁ × ty₂)) → Term ty₂

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT
  -- ...
  vpair : {ty₁ ty₂ : Type} → Value ty₁ → Value ty₂ → Value (ty₁ × ty₂)

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
⌜ vpair a b ⌝ = ⌜ a ⌝ , ⌜ b ⌝

-- Evidence type that shows a certain term represents a value.
data Is-value {ty : Type} : Term ty → Set where
  is-value : ∀ v → Is-value ⌜ v ⌝

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

vfst : {ty₁ ty₂ : Type} → Value (ty₁ × ty₂) → Value ty₁
vfst (vpair a b) = a

vsnd : {ty₁ ty₂ : Type} → Value (ty₁ × ty₂) → Value ty₂
vsnd (vpair a b) = b

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ t₁ , t₂ ⟧ = vpair ⟦ t₁ ⟧ ⟦ t₂ ⟧ 
⟦ fst t ⟧ = vfst ⟦ t ⟧
⟦ snd t ⟧ = vsnd ⟦ t ⟧

-- What can we do to define a denotational semantics?
--   Add types!

-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True    : ∀ {ty} {t1 t2 : Term ty} → Step (if true then t1 else t2) t1
  E-If-False   : ∀ {ty} {t1 t2 : Term ty} → Step (if false then t1 else t2) t2
  E-If-If      : ∀ {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty}
               → Step t1 t1' → Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ       : ∀ {t t' : Term NAT}
               → Step {NAT} t t' → Step {NAT} (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) (true)
  E-IsZeroSucc : {v : Value NAT} → Step (iszero (succ ⌜ v ⌝)) false
  E-IsZero     : ∀ {t t' : Term NAT} → Step t t' → Step (iszero t) (iszero t')
  E-PairBeta1  : ∀ {ty₁ ty₂} {t₁ : Term ty₁} {t₂ : Term ty₂} {v₁ : Value ty₁} {v₂ : Value ty₂}
               → ⌜ v₁ ⌝ == t₁ → ⌜ v₂ ⌝ == t₂ → Step (fst (t₁ , t₂)) t₁
  E-PairBeta2  : ∀ {ty₁ ty₂} {t₁ : Term ty₁} {t₂ : Term ty₂} {v₁ : Value ty₁} {v₂ : Value ty₂}
               → ⌜ v₁ ⌝ == t₁ → ⌜ v₂ ⌝ == t₂ → Step (snd (t₁ , t₂)) t₂
  E-Proj1      : ∀ {ty₁ ty₂} {t t' : Term (ty₁ × ty₂)}
               → Step t t' → Step (fst t) (fst t')
  E-Proj2      : ∀ {ty₁ ty₂} {t t' : Term (ty₁ × ty₂)}
               → Step t t' → Step (snd t) (snd t')
  E-Pair1      : ∀ {ty₁ ty₂} {t₁ t₁' : Term ty₁} {t₂ : Term ty₂}
               → Step t₁ t₁' → Step (t₁ , t₂) (t₁' , t₂)
  E-Pair2      : ∀ {ty₁ ty₂} {v₁ : Value ty₁} {t₁ : Term ty₁} {t₂ t₂' : Term ty₂}
               → ⌜ v₁ ⌝ == t₁ → Step t₂ t₂' → Step (t₁ , t₂) (t₁ , t₂')

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep (vpair a b) ._ (E-Pair1 step) = valuesDoNotStep a _ step
valuesDoNotStep (vpair a b) ._ (E-Pair2 x step) = valuesDoNotStep b _ step

-- Steps are deterministic: the same term can not be evaluated in more than one manner.
deterministic : ∀ {ty} {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic E-If-True E-If-True = refl
deterministic E-If-True (E-If-If ())
deterministic E-If-False E-If-False = refl
deterministic E-If-False (E-If-If ())
deterministic (E-If-If ()) E-If-True
deterministic (E-If-If ()) E-If-False
deterministic (E-If-If steps1) (E-If-If steps2) = cong (\x -> if x then _ else _) (deterministic steps1 steps2)
deterministic (E-Succ steps1) (E-Succ steps2) = cong succ (deterministic steps1 steps2)
deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())
deterministic (E-IsZeroSucc {v}) steps2 = lemma v _ steps2
  where
  lemma : (v : Value NAT) (t : Term BOOL) -> Step (iszero (succ ⌜ v ⌝)) t -> false == t
  lemma (vnat x) true ()
  lemma (vnat x) false steps = refl
  lemma (vnat x) (if t then t₁ else t₂) ()
  lemma (vnat x) (iszero ._) (E-IsZero (E-Succ steps)) = contradiction (valuesDoNotStep (vnat x) _ steps)
  lemma (vnat x) (fst t) ()
  lemma (vnat x) (snd t) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ steps1)
deterministic (E-IsZero steps1) (E-IsZero steps2) = cong iszero (deterministic steps1 steps2)
deterministic (E-PairBeta1 r₁ r₂) (E-PairBeta1 r₁' r₂') = refl
deterministic (E-PairBeta1 {v₁} refl refl) (E-Proj1 s) = {!!}
deterministic (E-PairBeta2 r₁ r₂) (E-PairBeta2 r₁' r₂') = refl
deterministic (E-PairBeta2 refl refl) (E-Proj2 s) = {!!}
deterministic (E-Proj1 s) (E-PairBeta1 refl refl) = {!!}
deterministic (E-Proj1 s) (E-Proj1 s') = cong fst (deterministic s s')
deterministic (E-Proj2 s) (E-PairBeta2 refl refl) = {!!}
deterministic (E-Proj2 s) (E-Proj2 s') = cong snd (deterministic s s')
deterministic (E-Pair1 x) (E-Pair1 x') = cong (λ z → z , _) (deterministic x x')
deterministic (E-Pair1 x) (E-Pair2 {v₁ = v} refl x') = contradiction (valuesDoNotStep v _ x)
deterministic (E-Pair2 {v₁ = v} refl x) (E-Pair1 x') = contradiction (valuesDoNotStep v _ x')
deterministic (E-Pair2 r x) (E-Pair2 r' x') = cong (_,_ _) (deterministic x x')

-- So we can add *types* to our term language. 
--
-- But when is a type system 'good'?
-- What would we like to prove about the relation between our semantics and well-typed terms?

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

-- A term is reducible when some evaluation step can be applied to it.
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : {t' : Term ty} -> Step t t' -> Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} -> Term ty → Set
NF t = Red t -> Empty

toVal : forall {ty} -> (t : Term ty) -> Is-value t -> Value ty
toVal .(⌜ v ⌝) (is-value v) = v

mutual
  -- If-then-else terms are reducible.
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3 
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t) t4 t5 with iszero-reduces t
  if-reduces (iszero t) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (fst t) t2 t3 with fst-reduces t
  if-reduces (fst t) t2 t3 | Reduces x = Reduces (E-If-If x)
  if-reduces (snd t) t2 t3 with snd-reduces t
  if-reduces (snd t) t2 t3 | Reduces x = Reduces (E-If-If x)

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst t) with fst-reduces t
  iszero-reduces (fst t) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces (snd t) with snd-reduces t
  iszero-reduces (snd t) | Reduces x = Reduces (E-IsZero x)

  fst-reduces : {ty₁ ty₂ : Type} → (t : Term (ty₁ × ty₂)) → Red (fst t)
  fst-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  fst-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Proj1 x)
  fst-reduces (t₁ , t₂) = {!!}
  fst-reduces (fst t) with fst-reduces t
  fst-reduces (fst t) | Reduces x = Reduces (E-Proj1 x)
  fst-reduces (snd t) with snd-reduces t
  fst-reduces (snd t) | Reduces x = Reduces (E-Proj1 x)

  snd-reduces : {ty₁ ty₂ : Type} → (t : Term (ty₁ × ty₂)) → Red (snd t)
  snd-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  snd-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Proj2 x)
  snd-reduces (t₁ , t₂) = {!!}
  snd-reduces (fst t) with fst-reduces t
  snd-reduces (fst t) | Reduces x = Reduces (E-Proj2 x)
  snd-reduces (snd t) with snd-reduces t
  snd-reduces (snd t) | Reduces x = Reduces (E-Proj2 x)

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (fst k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (snd k) nf (Reduces x) = nf (Reduces (E-Succ x))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (t₁ , t₂) nf = {!!}
  normal-forms-are-values (fst t) nf = contradiction (nf (fst-reduces t))
  normal-forms-are-values (snd t) nf = contradiction (nf (snd-reduces t))

  values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
  values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

  value-pairs-are-normal-forms : ∀ {ty₁ ty₂} (t₁ : Term ty₁) → (t₂ : Term ty₂) → Is-value t₁ → Is-value t₂ → NF (t₁ , t₂)
  value-pairs-are-normal-forms .(⌜ v₁ ⌝) .(⌜ v₂ ⌝) (is-value v₁) (is-value v₂) (Reduces x) = valuesDoNotStep (vpair v₁ v₂) _ x

  lemma : (t : Term NAT) -> (Red t -> Empty) -> Red (succ t) -> Empty
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true = Left (values-are-normal-forms true (is-value vtrue))
  progress false = Left (values-are-normal-forms false (is-value vfalse))
  progress (if t then t₁ else t₂) = Right (if-reduces t _ _)
  progress zero = Left (values-are-normal-forms zero (is-value (vnat (Zero))))
  progress (succ t) with progress t 
  progress (succ t) | Left x = Left (lemma t x)
  progress (succ t) | Right (Reduces step) = Right (Reduces (E-Succ step))
  progress (iszero t) with progress t
  progress (iszero t) | Left x with normal-forms-are-values t x
  progress (iszero .zero) | Left x₁ | is-value (vnat Zero) = Right (Reduces E-IsZeroZero)
  progress (iszero .(succ (natTerm x))) | Left x₁ | is-value (vnat (Succ x)) = 
    Right (Reduces (E-IsZeroSucc {vnat x}))
  progress (iszero t) | Right (Reduces step) = Right (Reduces (E-IsZero step))
  progress (t₁ , t₂) with progress t₁
  progress (t₁ , t₂) | Left x with progress t₂
  progress (t₁ , t₂) | Left x | Left y = Left (value-pairs-are-normal-forms t₁ t₂ (normal-forms-are-values t₁ x) (normal-forms-are-values t₂ y))
  progress (t₁ , t₂) | Left x | Right (Reduces y) = Right (Reduces (E-Pair2 {!!} y))
  progress (t₁ , t₂) | Right (Reduces x) = Right (Reduces (E-Pair1 x))
  progress (fst t) = Right (fst-reduces t)
  progress (snd t) = Right (snd-reduces t)


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

-- All steps terminate.
termination : ∀ {ty} (t : Term ty) → t ⇓
termination true = terminates vtrue Nil
termination false = terminates vfalse Nil
termination (if t then t₁ else t₂) with termination t
termination (if t then t₁ else t₂) | terminates vtrue x with termination t₁ 
termination (if t then t₁ else t₂) | terminates vtrue x₁ | terminates v x = 
  terminates v (E-If-Steps x₁  ++ [ E-If-True ] ++ x)
termination (if t then t₁ else t₂) | terminates vfalse x with termination t₂
termination (if t then t₁ else t₂) | terminates vfalse x₁ | terminates v x = 
  terminates v (E-If-Steps x₁ ++ [ E-If-False ] ++ x)
termination zero = terminates (vnat Zero) Nil
termination (succ t) with termination t
termination (succ t) | terminates (vnat x) q = terminates (vnat (Succ x)) (E-Succ-Steps q)
termination (iszero (if t then t₁ else t₂)) with termination t
termination (iszero (if t then t₁ else t₂)) | terminates vtrue x with termination t₁
termination (iszero (if t then t₁ else t₂)) | terminates vtrue x₂ | terminates (vnat Zero) x₁ = 
  terminates vtrue 
    (E-IsZero-Steps (E-If-Steps x₂ ++ [ E-If-True ]) ++ E-IsZero-Steps x₁ ++ [ E-IsZeroZero ])
termination (iszero (if t then t₁ else t₂)) | terminates vtrue x₂ | terminates (vnat (Succ x)) x₁ = 
  terminates vfalse 
    (E-IsZero-Steps (E-If-Steps x₂ ++ [ E-If-True ]) ++ E-IsZero-Steps x₁ ++ [ E-IsZeroSucc {vnat x} ])
termination (iszero (if t then t₁ else t₂)) | terminates vfalse x with termination t₂
termination (iszero (if t then t₁ else t₂)) | terminates vfalse x₂ | terminates (vnat Zero) x₁ = 
  terminates vtrue 
    (E-IsZero-Steps (E-If-Steps x₂ ++ [ E-If-False ] ++ x₁) ++ [ E-IsZeroZero ])
termination (iszero (if t then t₁ else t₂)) | terminates vfalse x₂ | terminates (vnat (Succ x)) x₁ =
  terminates vfalse 
     (E-IsZero-Steps (E-If-Steps x₂ ++ [ E-If-False ] ++ x₁) ++ [ E-IsZeroSucc {vnat x} ])
termination (iszero zero) = terminates vtrue (Cons E-IsZeroZero Nil)
termination (iszero (succ t)) with termination t
termination (iszero (succ t)) | terminates v x =
   terminates vfalse (E-IsZero-Steps (E-Succ-Steps x) ++ [ E-IsZeroSucc {v} ])
termination (iszero (fst t)) with termination t
termination (iszero (fst t)) | terminates v x = {!!}
termination (iszero (snd t)) = {!!}
termination (t₁ , t₂) with termination t₁
termination (t₁ , t₂) | terminates v x with termination t₂
termination (t₁ , t₂) | terminates v₁ x₁ | terminates v x = terminates (vpair v₁ v) {!!}
termination (fst t) = {!!}
termination (snd t) = {!!}

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue       : true ⇓ vtrue
  EvalFalse      : false ⇓ vfalse
  EvalIfTrue     : {ty : Type} {e₁ : Term BOOL} {e₂ e₃ : Term ty} {v : Value ty}
                 → e₁ ⇓ vtrue → e₂ ⇓ v → (if e₁ then e₂ else e₃) ⇓ v
  EvalIfFalse    : {ty : Type} {e₁ : Term BOOL} {e₂ e₃ : Term ty} {v : Value ty}
                 → e₁ ⇓ vfalse → e₃ ⇓ v → (if e₁ then e₂ else e₃) ⇓ v
  EvalZero       : zero ⇓ vnat Zero
  EvalSucc       : {n : Term NAT} {k : Nat}
                 → n ⇓ vnat k → succ n ⇓ vnat (Succ k)
  EvalIsZeroZero : {e₁ : Term NAT}
                 → e₁ ⇓ vnat Zero → iszero e₁ ⇓ vtrue
  EvalIsZeroSucc : {e₁ : Term NAT} {k : Nat}
                 → e₁ ⇓ vnat (Succ k) → iszero e₁ ⇓ vfalse
  

-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue           = Nil
big-to-small EvalFalse          = Nil
big-to-small (EvalIfTrue p p₁)  = E-If-Steps (big-to-small p) ++ [ E-If-True ] ++ big-to-small p₁
big-to-small (EvalIfFalse p p₁) = E-If-Steps (big-to-small p) ++ [ E-If-False ] ++ big-to-small p₁
big-to-small EvalZero           = Nil
big-to-small (EvalSucc p)       = E-Succ-Steps (big-to-small p)
big-to-small (EvalIsZeroZero p) = {!!} ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroSucc p) = {!!}

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) → ⌜ v ⌝ ⇓ v
value-to-value vtrue           = EvalTrue
value-to-value vfalse          = EvalFalse
value-to-value (vnat Zero)     = EvalZero
value-to-value (vnat (Succ x)) = EvalSucc (value-to-value (vnat x))
value-to-value (vpair v₁ v₂)   = {!!}

iszerosucc-lemma : ∀ {n} → iszero (succ n) ⇓ vfalse
iszerosucc-lemma {n} = EvalIsZeroSucc (EvalSucc {!!}) -- Surely this should be provable?

prepend-step : {ty : Type} {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True bs = EvalIfTrue EvalTrue bs
prepend-step E-If-False bs = EvalIfFalse EvalFalse bs
prepend-step (E-If-If ss) (EvalIfTrue e₁t e₂v) = EvalIfTrue (prepend-step ss e₁t) e₂v
prepend-step (E-If-If ss) (EvalIfFalse e₁f e₃v) = EvalIfFalse (prepend-step ss e₁f) e₃v
prepend-step (E-Succ ss) (EvalSucc bs) = EvalSucc (prepend-step ss bs)
prepend-step E-IsZeroZero EvalTrue = EvalIsZeroZero EvalZero
prepend-step E-IsZeroSucc EvalFalse = iszerosucc-lemma
prepend-step (E-IsZero ss) (EvalIsZeroZero bs) = EvalIsZeroZero (prepend-step ss bs)
prepend-step (E-IsZero ss) (EvalIsZeroSucc bs) = EvalIsZeroSucc (prepend-step ss bs)
prepend-step (E-PairBeta1 r₁ r₂) bigstep = {!!}
prepend-step (E-PairBeta2 r₁ r₂) bigstep = {!!}
prepend-step (E-Proj1 e) bigstep = {!!}
prepend-step (E-Proj2 e) bigstep = {!!}
prepend-step (E-Pair1 e) bigstep = {!!}
prepend-step (E-Pair2 x e) bigstep = {!!}

small-to-big : {ty : Type} {t : Term ty} → (v : Value ty) → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big v Nil = value-to-value v
small-to-big v (Cons step steps) = prepend-step step (small-to-big v steps)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t₁ else t₂) with ⇓-complete t
... | y = {!!}
⇓-complete zero = {!!}
⇓-complete (succ t) = {!!}
⇓-complete (iszero t) = {!!}
⇓-complete (t₁ , t₂) = {!!}
⇓-complete (fst t) = {!!}
⇓-complete (snd t) = {!!}

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound t v p = {!!}



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
