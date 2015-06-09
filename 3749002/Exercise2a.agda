
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

-- Reductio ab absurdum.
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
  TUPLE : Type -> Type -> Type

-- Our Term language
data Term : Type -> Set where
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- Tuple
  tuple         : ∀ {ty₁ ty₂ : Type} -> Term ty₁ -> Term ty₂ -> Term (TUPLE ty₁ ty₂)
  fst           : ∀ {ty₁ ty₂ : Type} -> Term (TUPLE ty₁ ty₂) -> Term ty₁
  snd           : ∀ {ty₁ ty₂ : Type} -> Term (TUPLE ty₁ ty₂) -> Term ty₂


-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT
  -- Tuple
  vtup : ∀ {ty₁ ty₂ : Type} -> Value ty₁ -> Value ty₂ -> Value (TUPLE ty₁ ty₂)

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
⌜ vtup l r ⌝ = tuple ⌜ l ⌝ ⌜ r ⌝


-- Example term.
ex : Term NAT -> Term BOOL
ex t = if iszero t then false else true

-- Another example
ex2 : Term NAT -> Term BOOL
ex2 t = iszero t

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

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ tuple l r ⟧ = vtup ⟦ l ⟧ ⟦ r ⟧
⟦ fst t ⟧ with ⟦ t ⟧
⟦ fst t ⟧ | vtup p p₁ = p
⟦ snd t ⟧ with ⟦ t ⟧
⟦ snd t ⟧ | vtup p p₁ = p₁

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
  E-Succ       : ∀ {t t' : Term NAT} -> Step {NAT} t t' -> Step {NAT} (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) (true)
  E-IsZeroSucc : {v : Value NAT} -> Step (iszero (succ ⌜ v ⌝)) false
  E-IsZero     : ∀ {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  E-TupL       : ∀ {tyₗ tyᵣ : Type} {t t' : Term tyₗ} {r : Term tyᵣ} -> Step t t' -> Step (tuple t r) (tuple t' r)
  E-TupR       : ∀ {tyₗ tyᵣ : Type} {t t' : Term tyᵣ} {l : Value tyₗ} -> Step t t' -> Step (tuple ⌜ l ⌝ t) (tuple ⌜ l ⌝ t')
  E-Fst-Eval   : ∀ {tyₗ tyᵣ : Type} {t t' : Term (TUPLE tyₗ tyᵣ)} -> Step t t' -> Step (fst t) (fst t')
  E-Snd-Eval   : ∀ {tyₗ tyᵣ : Type} {t t' : Term (TUPLE tyₗ tyᵣ)} -> Step t t' -> Step (snd t) (snd t')
  E-Fst        : ∀ {tyₗ tyᵣ : Type} {l : Value tyₗ} {r : Value tyᵣ} -> Step (fst (tuple ⌜ l ⌝ ⌜ r ⌝)) ⌜ l ⌝
  E-Snd        : ∀ {tyₗ tyᵣ : Type} {l : Value tyₗ} {r : Value tyᵣ} -> Step (snd (tuple ⌜ l ⌝ ⌜ r ⌝ )) ⌜ r ⌝

coerce : forall {ty} {a a' b : Term ty} -> a == a' -> Step a b -> Step a' b
coerce refl st = st

mutual
  valuesStepLemma : forall {ty ty'} {l : Term ty} {r : Term ty'} {v : Value ty} {v' : Value ty'} {t : Term (TUPLE ty ty')} ->
    l == ⌜ v ⌝ -> r == ⌜ v' ⌝ -> Step (tuple l r) t -> Empty
  valuesStepLemma lv rv' (E-TupL step) with coerce lv step
  valuesStepLemma {.BOOL} {ty'} {.true} {r} {vtrue} refl rv' (E-TupL {.BOOL} {.ty'} {.true} {true} step) | p = valuesDoNotStep vtrue true step
  valuesStepLemma {.BOOL} {ty'} {.false} {r} {vfalse} refl rv' (E-TupL {.BOOL} {.ty'} {.false} {true} step) | ()
  valuesStepLemma {.BOOL} {ty'} {.true} {r} {vtrue} refl rv' (E-TupL {.BOOL} {.ty'} {.true} {false} step) | ()
  valuesStepLemma {.BOOL} {ty'} {.false} {r} {vfalse} refl rv' (E-TupL {.BOOL} {.ty'} {.false} {false} step) | ()
  valuesStepLemma {.BOOL} {ty'} {.true} {r} {vtrue} refl rv' (E-TupL {.BOOL} {.ty'} {.true} {if t' then t'' else t'''} step) | ()
  valuesStepLemma {.BOOL} {ty'} {.false} {r} {vfalse} refl rv' (E-TupL {.BOOL} {.ty'} {.false} {if t' then t'' else t'''} step) | ()
  valuesStepLemma {.NAT} {ty'} {.(natTerm x)} {r} {vnat x} refl rv' (E-TupL {.NAT} {.ty'} {.(natTerm x)} {if t' then t'' else t'''} step) | p = valuesDoNotStep (vnat x) (if t' then t'' else t''') step
  valuesStepLemma {._} {ty'} {.(tuple ⌜ v ⌝ ⌜ v₁ ⌝)} {r} {vtup v v₁} refl rv' (E-TupL {._} {.ty'} {.(tuple ⌜ v ⌝ ⌜ v₁ ⌝)} {if t' then t'' else t'''} step) | ()
  valuesStepLemma {.NAT} {ty'} {.(natTerm x)} {r} {vnat x} refl rv' (E-TupL {.NAT} {.ty'} {.(natTerm x)} {zero} step) | p = valuesDoNotStep (vnat x) zero step
  valuesStepLemma {.NAT} {ty'} {.(natTerm x)} {r} {vnat x} refl rv' (E-TupL {.NAT} {.ty'} {.(natTerm x)} {succ t'} step) | p = valuesDoNotStep (vnat x) (succ t') step
  valuesStepLemma {.BOOL} {ty'} {.true} {r} {vtrue} refl rv' (E-TupL {.BOOL} {.ty'} {.true} {iszero t'} step) | ()
  valuesStepLemma {.BOOL} {ty'} {.false} {r} {vfalse} refl rv' (E-TupL {.BOOL} {.ty'} {.false} {iszero t'} step) | ()
  valuesStepLemma {._} {ty'} {.(tuple ⌜ v ⌝ ⌜ v₁ ⌝)} {r} {vtup v v₁} refl rv' (E-TupL {._} {.ty'} {.(tuple ⌜ v ⌝ ⌜ v₁ ⌝)} {tuple t' t''} step) | p = valuesDoNotStep (vtup v v₁) (tuple t' t'') step
  valuesStepLemma {.BOOL} {ty'} {.true} {r} {vtrue} refl rv' (E-TupL {.BOOL} {.ty'} {.true} {fst t'} step) | ()
  valuesStepLemma {.BOOL} {ty'} {.false} {r} {vfalse} refl rv' (E-TupL {.BOOL} {.ty'} {.false} {fst t'} step) | ()
  valuesStepLemma {.NAT} {ty'} {.(natTerm x)} {r} {vnat x} refl rv' (E-TupL {.NAT} {.ty'} {.(natTerm x)} {fst t'} step) | p = valuesDoNotStep (vnat x) (fst t') step
  valuesStepLemma {._} {ty'} {.(tuple ⌜ v ⌝ ⌜ v₁ ⌝)} {r} {vtup v v₁} refl rv' (E-TupL {._} {.ty'} {.(tuple ⌜ v ⌝ ⌜ v₁ ⌝)} {fst t'} step) | ()
  valuesStepLemma {.BOOL} {ty'} {.true} {r} {vtrue} refl rv' (E-TupL {.BOOL} {.ty'} {.true} {snd t'} step) | ()
  valuesStepLemma {.BOOL} {ty'} {.false} {r} {vfalse} refl rv' (E-TupL {.BOOL} {.ty'} {.false} {snd t'} step) | ()
  valuesStepLemma {.NAT} {ty'} {.(natTerm x)} {r} {vnat x} refl rv' (E-TupL {.NAT} {.ty'} {.(natTerm x)} {snd t'} step) | p = valuesDoNotStep (vnat x) (snd t') step
  valuesStepLemma {._} {ty'} {.(tuple ⌜ v ⌝ ⌜ v₁ ⌝)} {r} {vtup v v₁} refl rv' (E-TupL {._} {.ty'} {.(tuple ⌜ v ⌝ ⌜ v₁ ⌝)} {snd t'} step) | () --valuesDoNotStep {!!} _ p
  valuesStepLemma lv rv' (E-TupR step) with coerce rv' step
  valuesStepLemma {ty} {.BOOL} {._} {.true} {v} {vtrue} lv refl (E-TupR step) | ()
  valuesStepLemma {ty} {.BOOL} {._} {.false} {v} {vfalse} lv refl (E-TupR step) | ()
  valuesStepLemma {ty} {.NAT} {._} {.(natTerm x)} {v} {vnat x} lv refl (E-TupR {.ty} {.NAT} {.(natTerm x)} {if t' then t'' else t'''} step) | p = valuesDoNotStep (vnat x) (if t' then t'' else t''') step
  valuesStepLemma {ty} {.NAT} {._} {.(natTerm x)} {v} {vnat x} lv refl (E-TupR {.ty} {.NAT} {.(natTerm x)} {zero} step) | p = valuesDoNotStep (vnat x) zero step
  valuesStepLemma {ty} {.NAT} {._} {.(natTerm x)} {v} {vnat x} lv refl (E-TupR {.ty} {.NAT} {.(natTerm x)} {succ t'} step) | p = valuesDoNotStep (vnat x) (succ t') step
  valuesStepLemma {ty} {.NAT} {._} {.(natTerm x)} {v} {vnat x} lv refl (E-TupR {.ty} {.NAT} {.(natTerm x)} {fst t'} step) | p = valuesDoNotStep (vnat x) (fst t') step
  valuesStepLemma {ty} {.NAT} {._} {.(natTerm x)} {v} {vnat x} lv refl (E-TupR {.ty} {.NAT} {.(natTerm x)} {snd t'} step) | p = valuesDoNotStep (vnat x) (snd t') step
  valuesStepLemma {ty} {._} {._} {.(tuple ⌜ v' ⌝ ⌜ v'' ⌝)} {v} {vtup v' v''} lv refl (E-TupR {.ty} {._} {.(tuple ⌜ v' ⌝ ⌜ v'' ⌝)} {if t' then t'' else t'''} step) | ()
  valuesStepLemma {ty} {._} {._} {.(tuple ⌜ v' ⌝ ⌜ v'' ⌝)} {v} {vtup v' v''} lv refl (E-TupR {.ty} {._} {.(tuple ⌜ v' ⌝ ⌜ v'' ⌝)} {tuple t' t''} step) | p = valuesDoNotStep (vtup v' v'') (tuple t' t'') step
  valuesStepLemma {ty} {._} {._} {.(tuple ⌜ v' ⌝ ⌜ v'' ⌝)} {v} {vtup v' v''} lv refl (E-TupR {.ty} {._} {.(tuple ⌜ v' ⌝ ⌜ v'' ⌝)} {fst t'} step) | ()
  valuesStepLemma {ty} {._} {._} {.(tuple ⌜ v' ⌝ ⌜ v'' ⌝)} {v} {vtup v' v''} lv refl (E-TupR {.ty} {._} {.(tuple ⌜ v' ⌝ ⌜ v'' ⌝)} {snd t'} step) | ()


  valueIsTerm : ∀ {ty} -> (v : Value ty) -> ⌜ v ⌝ == ⌜ v ⌝
  valueIsTerm v = refl

  valuesDoNotStep : forall {ty} -> (v : Value ty) -> (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
  valuesDoNotStep vtrue t ()
  valuesDoNotStep vfalse t ()
  valuesDoNotStep (vnat x) t step = lemma x t step
    where
    lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
    lemma Zero t ()
    lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
  valuesDoNotStep (vtup l r) (if t then t₁ else t₂) ()
  valuesDoNotStep (vtup l r) (fst tup) ()
  valuesDoNotStep (vtup l r) (snd tup) ()
  valuesDoNotStep (vtup l r) (tuple t t₁) step = valuesStepLemma {_} {_} {⌜ l ⌝} {⌜ r ⌝} {l} {r} (valueIsTerm l) (valueIsTerm r) step


-- Steps are deterministic: the same term can not be evaluated in more than one manner.
deterministic : ∀ {ty} {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic E-If-True E-If-True = refl
deterministic E-If-True (E-If-If ())
deterministic E-If-False E-If-False = refl
deterministic E-If-False (E-If-If ())
deterministic (E-If-If ()) E-If-True
deterministic (E-If-If ()) E-If-False
deterministic (E-If-If s1) (E-If-If s2) = cong (\x -> if x then _ else _) (deterministic s1 s2)
deterministic (E-Succ s1) (E-Succ s2) = cong succ (deterministic s1 s2)
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
deterministic (E-TupL {_} {_} {_} {_} {r} s1) (E-TupL s2) = cong (λ z → tuple z r) (deterministic s1 s2)
deterministic (E-TupL s1) (E-TupR s2) = {!!}
deterministic (E-TupR {tyₗ} {tyᵣ} {tᵣ} {tᵣ'} {vₗ} s1) s2 with ⌜ vₗ ⌝ | ⟦ tᵣ ⟧
deterministic (E-TupR s1) (E-TupL s2) | p | q = {!!}
deterministic (E-TupR s1) (E-TupR s2) | ._ | q = {!!}
deterministic (E-Fst-Eval s1) (E-Fst-Eval s2) = cong fst (deterministic s1 s2)
deterministic (E-Fst-Eval {t' = if t' then t'' else t'''} s1) (E-Fst {a} {b} {l} {r}) = contradiction (valuesDoNotStep (vtup l r) (if t' then t'' else t''') s1)
deterministic (E-Fst-Eval {t' = tuple t' t''} s1) (E-Fst {a} {b} {l} {r}) = contradiction (valuesDoNotStep (vtup l r) (tuple t' t'') s1)
deterministic (E-Fst-Eval {t' = fst t'} s1) (E-Fst {a} {b} {l} {r}) = contradiction (valuesDoNotStep (vtup l r) (fst t') s1)
deterministic (E-Fst-Eval {t' = snd t'} s1) (E-Fst {a} {b} {l} {r}) = contradiction (valuesDoNotStep (vtup l r) (snd t') s1)
deterministic (E-Snd-Eval s1) (E-Snd-Eval s2) = cong snd (deterministic s1 s2)
deterministic (E-Snd-Eval {t' = if t' then t'' else t'''} s1) (E-Snd {a} {b} {l} {r}) = contradiction (valuesDoNotStep (vtup l r) (if t' then t'' else t''') s1)
deterministic (E-Snd-Eval {t' = tuple t' t''} s1) (E-Snd {a} {b} {l} {r}) = contradiction (valuesDoNotStep (vtup l r) (tuple t' t'') s1)
deterministic (E-Snd-Eval {t' = fst t'} s1) (E-Snd {a} {b} {l} {r}) = contradiction (valuesDoNotStep (vtup l r) (fst t') s1)
deterministic (E-Snd-Eval {t' = snd t'} s1) (E-Snd {a} {b} {l} {r}) = contradiction (valuesDoNotStep (vtup l r) (snd t') s1)
deterministic (E-Fst {ty1} {ty2} {l} {r}) s2 with ⌜ l ⌝ | ⌜ r ⌝
deterministic E-Fst (E-Fst-Eval s2) | p | q = {!!}
deterministic E-Fst E-Fst | ._ | ._ = refl
deterministic (E-Snd {ty1} {ty2} {l} {r}) s2 with ⌜ l ⌝ | ⌜ r ⌝
deterministic E-Snd (E-Snd-Eval s2) | p | q = {!!}
deterministic E-Snd E-Snd | ._ | ._ = refl

{-
deterministic (E-TupL {l} {r} {b} {c} {d} x) (E-TupL x₁) = let a = deterministic x x₁ in cong (λ z → tuple z d) a
deterministic (E-TupL {ty} {ty2} x) (E-TupR {.ty} {.ty2} {r1} {r2} {l} x₁) = contradiction (valuesDoNotStep l _ x)
deterministic (E-TupR {tyₗ} {tyᵣ} {r₁} {r₂} {l} x) x₁ with ⌜ l ⌝
deterministic (E-TupR {.ty} {.ty2} {r1} {r2} {l} x) (E-TupL {ty} {ty2} x₁) | p = contradiction (valuesDoNotStep {!l!} _ x₁)
deterministic (E-TupR x) (E-TupR {tyₗ} {tyᵣ} {r₁} {r₂} {l} x₁) | ._ = cong (tuple ⌜ l ⌝) (deterministic x x₁)
 -}


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

toVal : forall {ty} -> (t : Term ty) -> Is-value t -> Value ty
toVal .(⌜ v ⌝) (is-value v) = v

mutual
  fst-reduces : ∀ {tyₗ tyᵣ : Type} (t : Term (TUPLE tyₗ tyᵣ)) -> Red (fst t)
  fst-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  fst-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Fst-Eval x)
  fst-reduces (tuple t t₁) with progress t | progress t₁
  fst-reduces (tuple t t₁) | Left x | Left x₁ with normal-forms-are-values t x | normal-forms-are-values t₁ x₁
  fst-reduces (tuple .(⌜ v ⌝) .(⌜ v₁ ⌝)) | Left x | Left x₁ | is-value v | is-value v₁ = Reduces (E-Fst {_} {_} {v} {v₁})
  fst-reduces {tyₗ} {tyᵣ} (tuple t t₁) | Left x | Right (Reduces x₁) with normal-forms-are-values t x
  fst-reduces (tuple .(⌜ v ⌝) t₁) | Left x | Right (Reduces x₁) | is-value v = Reduces (E-Fst-Eval (E-TupR {_} {_} {_} {_} {v} x₁))
  fst-reduces (tuple t t₁) | Right (Reduces x) | q = Reduces (E-Fst-Eval (E-TupL x))
  fst-reduces (fst t) with fst-reduces t
  fst-reduces (fst t) | Reduces x = Reduces (E-Fst-Eval x)
  fst-reduces (snd t) with snd-reduces t
  fst-reduces (snd t) | Reduces x = Reduces (E-Fst-Eval x)

  snd-reduces : ∀ {tyₗ tyᵣ : Type} (t : Term (TUPLE tyₗ tyᵣ)) -> Red (snd t)
  snd-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  snd-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Snd-Eval x)
  snd-reduces (tuple t t₁) with progress t | progress t₁
  snd-reduces (tuple t t₁) | Left x | Left x₁ with normal-forms-are-values t x | normal-forms-are-values t₁ x₁
  snd-reduces (tuple .(⌜ v ⌝) .(⌜ v₁ ⌝)) | Left x | Left x₁ | is-value v | is-value v₁ = Reduces (E-Snd {_} {_} {v} {v₁})
  snd-reduces (tuple t t₁) | Left x | Right (Reduces x₁) with normal-forms-are-values t x
  snd-reduces (tuple .(⌜ v ⌝) t₁) | Left x | Right (Reduces x₁) | is-value v = Reduces (E-Snd-Eval (E-TupR {_} {_} {_} {_} {v} x₁))
  snd-reduces (tuple t t₁) | Right (Reduces x) | q = Reduces (E-Snd-Eval (E-TupL x))
  snd-reduces (fst t) with fst-reduces t
  snd-reduces (fst t) | Reduces x = Reduces (E-Snd-Eval x)
  snd-reduces (snd t) with snd-reduces t
  snd-reduces (snd t) | Reduces x = Reduces (E-Snd-Eval x)

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

  tupleR-Reduces : ∀ {tyₗ tyᵣ : Type} {r : Term tyᵣ} -> (l : Value tyₗ) -> Red r -> Red (tuple ⌜ l ⌝ r)
  tupleR-Reduces {_} {_} l (Reduces x) = Reduces (E-TupR {_} {_} {_} {_} {l} x)

  iszero-reduces : (t : Term NAT) -> Red (iszero t)
  iszero-reduces (fst t) with fst-reduces t
  iszero-reduces (fst t) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces (snd t) with snd-reduces t
  iszero-reduces (snd t) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (fst t) nf x with fst-reduces t
  succ-nf (fst t) nf x₁ | Reduces x = nf (Reduces (E-Succ x))
  succ-nf (snd t) nf x with snd-reduces t
  succ-nf (snd t) nf x₁ | Reduces x = nf (Reduces (E-Succ x))
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))

  tupleL-nf : {tyₗ tyᵣ : Type} {l : Term tyₗ} {r : Term tyᵣ} -> NF (tuple l r) -> NF l
  tupleL-nf nf (Reduces x) = nf (Reduces (E-TupL x))

  lemmading : {v : Value NAT} -> ⌜ vsucc v ⌝ == succ ⌜ v ⌝
  lemmading {vnat x} = refl

  -- STOP WHINING ABOUT THIS LOOKING UGLY
  -- IT WORKS DAMNIT
  tupleL-Succ-nf : {tyᵣ : Type} {r : Term tyᵣ} -> (l : Value NAT) -> NF (tuple (succ ⌜ l ⌝) r) -> NF r
  tupleL-Succ-nf (vnat x) nf (Reduces x₁) = nf (Reduces (E-TupR {_} {_} {_} {_} {vnat (Succ x)} x₁))


  tupleR-nf : {tyₗ tyᵣ : Type} {r : Term tyᵣ} -> (l : Value tyₗ) -> NF (tuple ⌜ l ⌝ r) -> NF r
  tupleR-nf l nf (Reduces x) = nf (Reduces (E-TupR {_} {_} {_} {_} {l} x))

  fstNf : {tyₗ tyᵣ : Type} {t : Term (TUPLE tyₗ tyᵣ)} -> NF (fst t) -> NF t
  fstNf nf (Reduces x) = nf (Reduces (E-Fst-Eval x))

  sndNf : {tyₗ tyᵣ : Type} {t : Term (TUPLE tyₗ tyᵣ)} -> NF (snd t) -> NF t
  sndNf nf (Reduces x) = nf (Reduces (E-Snd-Eval x))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat Zero)
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (tuple true r) nf with normal-forms-are-values r (tupleR-nf vtrue nf)
  normal-forms-are-values (tuple true .(⌜ v ⌝)) nf | is-value v = is-value (vtup vtrue v)
  normal-forms-are-values (tuple false r) nf with normal-forms-are-values r (tupleR-nf vfalse nf)
  normal-forms-are-values (tuple false .(⌜ v ⌝)) nf | is-value v = is-value (vtup vfalse v)
  normal-forms-are-values (tuple (if l then l₁ else l₂) r) nf = contradiction (tupleL-nf nf (if-reduces l l₁ l₂))
  normal-forms-are-values (tuple zero r) nf with normal-forms-are-values r (tupleR-nf (vnat Zero) nf)
  normal-forms-are-values (tuple zero .(⌜ v ⌝)) nf | is-value v = is-value (vtup (vnat Zero) v)
  normal-forms-are-values (tuple (succ l) r) nf with normal-forms-are-values l (succ-nf l (tupleL-nf nf))
  normal-forms-are-values (tuple (succ .(⌜ v ⌝)) r) nf | is-value v with normal-forms-are-values r (tupleL-Succ-nf v nf)
  normal-forms-are-values (tuple (succ .(⌜ vnat x ⌝)) .(⌜ v₁ ⌝)) nf | is-value (vnat x) | is-value v₁ = is-value (vtup (vnat (Succ x)) v₁) -- WOULD YOU LOOK AT THE FACT THAT THIS TYPE CHECKS
  normal-forms-are-values (tuple (iszero l) r) nf = contradiction (tupleL-nf nf (iszero-reduces l))
  normal-forms-are-values (tuple (tuple l l₁) r) nf with normal-forms-are-values l (tupleL-nf (tupleL-nf nf))
  normal-forms-are-values (tuple (tuple .(⌜ v ⌝) l₁) r) nf | is-value v with normal-forms-are-values l₁ (tupleR-nf v (tupleL-nf nf))
  normal-forms-are-values (tuple (tuple .(⌜ v ⌝) .(⌜ v₁ ⌝)) r) nf | is-value v | is-value v₁ with normal-forms-are-values r (tupleR-nf (vtup v v₁) nf)
  normal-forms-are-values (tuple (tuple .(⌜ v ⌝) .(⌜ v₁ ⌝)) .(⌜ v₂ ⌝)) nf | is-value v | is-value v₁ | is-value v₂ = is-value (vtup (vtup v v₁) v₂) -- OR THIS EVEN, HOLY SHIT
  normal-forms-are-values (tuple (fst t) r) nf = contradiction (tupleL-nf nf (fst-reduces t))
  normal-forms-are-values (tuple (snd t) r) nf = contradiction (tupleL-nf nf (snd-reduces t))
  normal-forms-are-values (fst t) nf = contradiction (nf (fst-reduces t))
  normal-forms-are-values (snd t) nf = contradiction (nf (snd-reduces t))

  values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
  values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

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
  progress (tuple l r) with progress l | progress r
  progress (tuple l r) | Left x | Left x₁ with normal-forms-are-values l x | normal-forms-are-values r x₁
  progress (tuple .(⌜ v ⌝) .(⌜ v₁ ⌝)) | Left x | Left x₁ | is-value v | is-value v₁ = Left (values-are-normal-forms (tuple ⌜ v ⌝ ⌜ v₁ ⌝) (is-value (vtup v v₁)))
  progress (tuple l r) | Left x | Right (Reduces x₁) with normal-forms-are-values l x
  progress (tuple .(⌜ v ⌝) r) | Left x | Right (Reduces x₁) | is-value v = Right (Reduces (E-TupR {_} {_} {_} {_} {v} x₁))
  progress (tuple l r) | Right (Reduces x) | q = Right (Reduces (E-TupL x))
  progress (fst t) = Right (fst-reduces t)
  progress (snd t) = Right (snd-reduces t)



--------------------------------------------------------------------------------
-- Sequences of small steps.
--------------------------------------------------------------------------------

-- A sequence of steps that can be applied in succession.
data Steps {ty : Type} : Term ty → Term ty → Set where
  Nil : forall {t} -> Steps t t
  Cons : forall {t1 t2 t3 : Term ty} -> Step t1 t2 -> Steps t2 t3 -> Steps t1 t3

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

E-If-Step : ∀ {ty} {t t'} {t1 t2 : Term ty} →
        Step t t' → Step (if t then t1 else t2) (if t' then t1 else t2)
E-If-Step step = E-If-If step

E-If-Steps : ∀ {ty} {t t'} {t1 t2 : Term ty} →
        Steps t t' →
        Steps (if t then t1 else t2) (if t' then t1 else t2)
E-If-Steps Nil = Nil
E-If-Steps (Cons x steps) = Cons (E-If-If x) (E-If-Steps steps)

E-Succ-Step : ∀ {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t')
E-Succ-Step = E-Succ

E-Succ-Steps : ∀ {t t' : Term NAT} -> Steps t t' → Steps (succ t) (succ t')
E-Succ-Steps Nil = Nil
E-Succ-Steps (Cons x steps) = Cons (E-Succ x) (E-Succ-Steps steps)

E-IsZero-Steps : ∀ {t t' : Term NAT} -> Steps t t' → Steps (iszero t) (iszero t')
E-IsZero-Steps Nil = Nil
E-IsZero-Steps (Cons x steps) = Cons (E-IsZero x) (E-IsZero-Steps steps)

E-TupleL-Steps : ∀ {tyₗ tyᵣ : Type} {l l' : Term tyₗ} {r : Term tyᵣ} -> Steps l l' -> Steps (tuple l r) (tuple l' r)
E-TupleL-Steps Nil = Nil
E-TupleL-Steps (Cons x steps) = Cons (E-TupL x) (E-TupleL-Steps steps)

E-TupleR-Steps : ∀ {tyₗ tyᵣ : Type} {r r' : Term tyᵣ} {l : Value tyₗ} -> Steps r r' -> Steps (tuple ⌜ l ⌝ r) (tuple ⌜ l ⌝ r')
E-TupleR-Steps Nil = Nil -- Implicit arguments are made explicit because Agda whines in yellow otherwise
E-TupleR-Steps {tyₗ} {tyᵣ} {r} {r'} {l} (Cons {.r} {oi} x steps) = Cons (E-TupR {tyₗ} {tyᵣ} {r} {oi} {l} x) (E-TupleR-Steps {tyₗ} {tyᵣ} {oi} {r'} {l} steps)

E-Fst-Steps : ∀ {tyₗ tyᵣ : Type} {t t' : Term (TUPLE tyₗ tyᵣ)} ->  Steps t t' -> Steps (fst t) (fst t')
E-Fst-Steps Nil = Nil
E-Fst-Steps (Cons x st) = Cons (E-Fst-Eval x) (E-Fst-Steps st)

E-Snd-Steps : ∀ {tyₗ tyᵣ : Type} {t t' : Term (TUPLE tyₗ tyᵣ)} ->  Steps t t' -> Steps (snd t) (snd t')
E-Snd-Steps Nil = Nil
E-Snd-Steps (Cons x st) = Cons (E-Snd-Eval x) (E-Snd-Steps st)

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
termination (iszero (succ t)) | terminates v x = terminates vfalse (E-IsZero-Steps (E-Succ-Steps x) ++ [ E-IsZeroSucc {v} ])
termination (iszero (fst t)) with termination (fst t)
termination (iszero (fst t)) | terminates (vnat Zero) x₁ = terminates vtrue (E-IsZero-Steps x₁ ++ [ E-IsZeroZero ])
termination (iszero (fst t)) | terminates (vnat (Succ x)) x₁ = terminates vfalse (E-IsZero-Steps x₁ ++ [ E-IsZeroSucc {vnat x} ])
termination (iszero (snd t)) with termination (snd t)
termination (iszero (snd t)) | terminates (vnat Zero) x₁ = terminates vtrue (E-IsZero-Steps x₁ ++ Cons E-IsZeroZero Nil)
termination (iszero (snd t)) | terminates (vnat (Succ x)) x₁ = terminates vfalse (E-IsZero-Steps x₁ ++ [ E-IsZeroSucc {vnat x} ])
termination (tuple l r) with termination l | termination r
termination (tuple l r) | terminates v x | terminates v₁ x₁ = terminates (vtup v v₁) (E-TupleL-Steps x ++ E-TupleR-Steps {_} {_} {_} {_} {v} x₁)
termination (fst t) with termination t
termination (fst t) | terminates (vtup v v₁) x = terminates v (E-Fst-Steps x ++ [ E-Fst {_} {_} {v} {v₁} ])
termination (snd t) with termination t
termination (snd t) | terminates (vtup v v₁) x = terminates v₁ (E-Snd-Steps x ++ [ E-Snd {_} {_} {v} {v₁} ])

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
    EvalTrue    : true ⇓ vtrue
    EvalFalse   : false ⇓ vfalse
    EvalIfTrue  : forall {c : Term BOOL} {ty} {t e : Term ty} {v} -> c ⇓ vtrue -> t ⇓ v -> ((if c then t else e) ⇓ v)
    EvalIfFalse : forall {c : Term BOOL} {ty} {t e : Term ty} {v} -> c ⇓ vfalse -> e ⇓ v -> ((if c then t else e) ⇓ v)
    EvalZero    : zero ⇓ (vnat Zero)
    EvalSucc    : forall {n : Term NAT} {v : Nat} -> n ⇓ vnat v -> (succ n) ⇓ (vnat (Succ v))
    EvalIsZeroZ : forall {x : Term NAT} -> x ⇓ (vnat Zero) ->  iszero x ⇓ vtrue
    EvalIsZeroS : forall {x : Term NAT} {y : Nat} -> x ⇓ (vnat (Succ y)) ->  iszero x ⇓ vfalse
    EvalTuple   : forall {tyₗ tyᵣ : Type} {l : Term tyₗ} {r : Term tyᵣ} {vₗ : Value tyₗ} {vᵣ : Value tyᵣ} -> l ⇓ vₗ -> r ⇓ vᵣ -> tuple l r ⇓ vtup vₗ vᵣ
    -- EvalTupleL  : forall {tyₗ tyᵣ : Type} {l : Term tyₗ} {r : Term tyᵣ} {vₗ : Value tyₗ} {vᵣ : Value tyᵣ} -> l ⇓ vₗ -> r ⇓ vᵣ -> tuple l r ⇓ vtup vₗ vᵣ
    EvalFst     : forall {tyₗ tyᵣ : Type} {t : Term (TUPLE tyₗ tyᵣ)} {vₗ : Value tyₗ} {vᵣ : Value tyᵣ} -> t ⇓ vtup vₗ vᵣ -> fst t ⇓ vₗ
    EvalSnd     : forall {tyₗ tyᵣ : Type} {t : Term (TUPLE tyₗ tyᵣ)} {vₗ : Value tyₗ} {vᵣ : Value tyᵣ} -> t ⇓ vtup vₗ vᵣ -> snd t ⇓ vᵣ


-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small (EvalIfTrue p p₁) = E-If-Steps (big-to-small p) ++ Cons E-If-True (big-to-small p₁)
big-to-small (EvalIfFalse p p₁) = E-If-Steps (big-to-small p) ++ Cons E-If-False (big-to-small p₁)
big-to-small (EvalSucc n) = let rec = big-to-small n in (E-Succ-Steps rec) 
big-to-small (EvalZero) = Nil
big-to-small (EvalIsZeroZ p) = E-IsZero-Steps (big-to-small p) ++ Cons E-IsZeroZero Nil
big-to-small (EvalIsZeroS {x} {n} p) = E-IsZero-Steps (big-to-small p) ++ Cons (E-IsZeroSucc {vnat n}) Nil
big-to-small (EvalTuple {tyₗ} {tyᵣ} {l} {r} {vl} el er) = let left = big-to-small el in (E-TupleL-Steps left) ++ (E-TupleR-Steps {_} {_} {_} {_} {vl} (big-to-small er))
big-to-small (EvalFst {tyₗ} {tyᵣ} {tup} {vₗ} {vᵣ} t) = let tup = big-to-small t in E-Fst-Steps tup ++ [ E-Fst {tyₗ} {tyᵣ} {vₗ} {vᵣ} ]
big-to-small (EvalSnd {tyₗ} {tyᵣ} {tup} {vₗ} {vᵣ} t) = E-Snd-Steps (big-to-small t) ++ [ E-Snd {tyₗ} {tyᵣ} {vₗ} {vᵣ} ]

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = EvalTrue
value-to-value vfalse = EvalFalse
value-to-value (vnat Zero) = EvalZero
value-to-value (vnat (Succ x)) = EvalSucc (value-to-value (vnat x))
value-to-value (vtup l r) = EvalTuple (value-to-value l) (value-to-value r)

prepend-step : {ty : Type} {t t' : Term ty} {v : Value ty} → Step t t' → t' ⇓ v → t ⇓ v
prepend-step E-If-True p = EvalIfTrue EvalTrue p
prepend-step E-If-False p = EvalIfFalse EvalFalse p
prepend-step (E-If-If s) (EvalIfTrue p p₁) = EvalIfTrue (prepend-step s p) p₁
prepend-step (E-If-If s) (EvalIfFalse p p₁) = EvalIfFalse (prepend-step s p) p₁
prepend-step (E-Succ s) (EvalSucc p) = EvalSucc (prepend-step s p)
prepend-step E-IsZeroZero EvalTrue = EvalIsZeroZ EvalZero
prepend-step (E-IsZeroSucc {vnat x}) EvalFalse = EvalIsZeroS (value-to-value (vnat (Succ x)))
prepend-step (E-IsZero s) (EvalIsZeroZ p) = EvalIsZeroZ (prepend-step s p)
prepend-step (E-IsZero s) (EvalIsZeroS p) = EvalIsZeroS (prepend-step s p)
prepend-step (E-TupL x) (EvalTuple x₁ x₂) = EvalTuple (prepend-step x x₁) x₂
prepend-step (E-TupR x) (EvalTuple x₁ x₂) = EvalTuple x₁ (prepend-step x x₂)
prepend-step (E-Fst {tyₗ} {tyᵣ} {l} {r}) b = {!!} {-with ⌜ l ⌝ | ⌜ r ⌝
prepend-step E-Fst EvalTrue | .true | q = EvalFst {!!}
prepend-step E-Fst EvalFalse | .false | q = {!!}
prepend-step E-Fst (EvalIfTrue b b₁) | ._ | q = {!!}
prepend-step E-Fst (EvalIfFalse b b₁) | ._ | q = {!!}
prepend-step E-Fst EvalZero | .zero | q = {!!}
prepend-step E-Fst (EvalSucc b) | ._ | q = {!!}
prepend-step E-Fst (EvalIsZeroZ b) | ._ | q = {!!}
prepend-step E-Fst (EvalIsZeroS b) | ._ | q = {!!}
prepend-step E-Fst (EvalTuple b b₁) | ._ | q = {!!}
prepend-step E-Fst (EvalFst b) | ._ | q = {!!}
prepend-step E-Fst (EvalSnd b) | ._ | q = {!!} -}
{- prepend-step (E-Fst {l = vtrue} {vtrue}) b = EvalFst (EvalTuple b b)
prepend-step (E-Fst {l = vtrue} {vfalse}) b = EvalFst (EvalTuple b EvalFalse)
prepend-step (E-Fst {l = vtrue} {vnat x}) b = {!E!}
prepend-step (E-Fst {l = vtrue} {vtup r r₁}) b = {!!}
prepend-step (E-Fst {l = vfalse}) b = {!!}
prepend-step (E-Fst {l = vnat x}) b = {!!}
prepend-step (E-Fst {l = vtup l l₁}) b = {!!} -}
{-prepend-step (E-Fst {l = vtrue}) EvalTrue = {!!}
prepend-step (E-Fst {l = vfalse}) EvalFalse = {!!}
prepend-step (E-Fst {l = vnat x}) b = {!b!}
prepend-step (E-Fst {l = vtup l l₁}) (EvalTuple b b₁) = {!!} -}
prepend-step (E-Snd) b = {!b!}
prepend-step (E-Fst-Eval s) (EvalFst b) = EvalFst (prepend-step s b)
prepend-step (E-Snd-Eval s) (EvalSnd b) = EvalSnd (prepend-step s b)

small-to-big : {ty : Type} {t : Term ty} → (v : Value ty) → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big v Nil = value-to-value v
small-to-big v (Cons x steps) = prepend-step x (small-to-big v steps)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans refl refl = refl
infixr 2 _⟨_⟩_

sym : {a : Set} {x y : a} -> x == y -> y == x
sym refl = refl

_⟨_⟩_ : (x : Nat) -> {y z : Nat} -> (x == y) -> (y == z) -> x == z
x ⟨ p ⟩ q = trans p q

_■ : forall (x : Nat) -> x == x
_■ x = refl

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t₁ else t₂) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t₁ else t₂) | vtrue | p = EvalIfTrue p (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | vfalse | p = EvalIfFalse p (⇓-complete t₂)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ ._) | vnat x | EvalIfTrue p p₁ = EvalSucc (EvalIfTrue p p₁)
⇓-complete (succ ._) | vnat x | EvalIfFalse p p₁ = EvalSucc (EvalIfFalse p p₁)
⇓-complete (succ .zero) | vnat .Zero | EvalZero = EvalSucc EvalZero
⇓-complete (succ ._) | vnat ._ | EvalSucc p = EvalSucc (EvalSucc p)
⇓-complete (succ ._) | vnat x | EvalFst p = EvalSucc (EvalFst p)
⇓-complete (succ ._) | vnat x | EvalSnd p = EvalSucc (EvalSnd p)
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | p = EvalIsZeroZ p
⇓-complete (iszero t) | vnat (Succ x) | p = EvalIsZeroS p
⇓-complete (tuple l r) = EvalTuple (⇓-complete l) (⇓-complete r)
⇓-complete (fst t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (fst t) | vtup p p₁ | q = EvalFst q
⇓-complete (snd t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (snd t) | vtup p p₁ | q = EvalSnd q


trueNotFalse : vtrue == vfalse -> Empty
trueNotFalse ()

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → v == ⟦ t ⟧
⇓-sound EvalTrue = refl
⇓-sound EvalFalse = refl
⇓-sound (EvalIfTrue {c} {ty} {t} {e} {v} cnd thn) with ⟦ c ⟧ | ⇓-sound cnd
⇓-sound (EvalIfTrue {c} {ty} {t} {e} {v} cnd thn) | vtrue | q = ⇓-sound thn
⇓-sound (EvalIfTrue cnd thn) | vfalse | ()
⇓-sound (EvalIfFalse {c} {ty} {t} {e} {v} cnd thn) with ⟦ c ⟧ | ⇓-sound cnd
⇓-sound (EvalIfFalse cnd thn) | vtrue | ()
⇓-sound (EvalIfFalse cnd thn) | vfalse | q = ⇓-sound thn
⇓-sound EvalZero = refl
⇓-sound (EvalSucc {x} {v} p) = cong vsucc (⇓-sound p)
⇓-sound (EvalIsZeroZ {x} p) with ⟦ x ⟧ | ⇓-sound p
⇓-sound (EvalIsZeroZ p) | .(vnat Zero) | refl = refl
⇓-sound (EvalIsZeroS {x} {y} p) with ⟦ x ⟧ | ⇓-sound p
⇓-sound (EvalIsZeroS p) | ._ | refl = refl
⇓-sound (EvalTuple {tyₗ} {tyᵣ} {l} {r} el er) with ⟦ l ⟧ | ⇓-sound el | ⟦ r ⟧ | ⇓-sound er
⇓-sound (EvalTuple el er) | vₗ | refl | vᵣ | refl = refl
⇓-sound (EvalFst {tyₗ} {tyᵣ} {t} p) with ⟦ t ⟧ | ⇓-sound p
⇓-sound (EvalFst p) | vtup v vᵣ | refl = refl
⇓-sound (EvalSnd {tyₗ} {tyᵣ} {t} p) with ⟦ t ⟧ | ⇓-sound p
⇓-sound (EvalSnd p) | vtup vₗ v | refl = refl


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
