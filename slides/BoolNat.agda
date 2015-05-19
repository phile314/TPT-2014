
module BoolNat where

-------------------------------------------------------------------------------
----------------------                 Prelude             --------------------
-------------------------------------------------------------------------------

-- Equality.
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
  
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

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL 
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL


-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
  where
  natTerm : Nat -> Term NAT
  natTerm Zero = zero
  natTerm (Succ k) = succ (natTerm k)


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

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ with ⟦ k ⟧
⟦ succ k ⟧ | vnat x = vnat (Succ x)
⟦ iszero t ⟧ with ⟦ t ⟧
⟦ iszero t ⟧ | vnat Zero = vtrue
⟦ iszero t ⟧ | vnat (Succ x) = vfalse


-- What can we do to define a denotational semantics?
--   Add types!

-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ       : forall {t t' : Term NAT} -> Step {NAT} t t' -> Step {NAT} (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) (true)
  E-IsZeroSucc : {t : Term NAT} -> Step (iszero (succ t)) false
  E-IsZero     : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')

-- Steps are deterministic: the same term can not be evaluated in more than one manner.
deterministic : ∀ {ty} {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic steps1 steps2 = {!!}

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

-- Evidence type that shows a certain term represents a value.
data Is-value {ty : Type} : Term ty → Set where
  is-value : ∀ v → Is-value ⌜ v ⌝

mutual
  -- If-then-else terms are reducible.
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  -- if-reduces true t2 t3 = Reduces E-If-True
  -- if-reduces false t2 t3 = Reduces E-If-False
  -- if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  -- if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 = {!!}
  if-reduces (iszero t) t4 t5 with iszero-reduces t
  if-reduces (iszero t) t4 t5 | Reduces x = Reduces (E-If-If x)


  iszero-reduces : (t : Term NAT) -> Red (iszero t) -- Red (iszero t)
  iszero-reduces t = {!!}

-- A normal form must be a value.
normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
normal-forms-are-values true nf = is-value vtrue
normal-forms-are-values false nf = is-value vfalse
normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
normal-forms-are-values zero nf  = is-value (vnat (Zero))
normal-forms-are-values (succ k) nf with normal-forms-are-values k {!!}
normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
normal-forms-are-values v _  = {!!}

values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
values-are-normal-forms t v = {!!}

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
progress (iszero t) = {!!}

-- TODO
--   * prove uniqueness of normal forms
--   * prove termination
--   * define a big step semantics
--   * prove various semantics equivalent




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
