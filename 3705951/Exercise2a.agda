
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
  NAT  : Type
  BOOL : Type
  _,_  : Type -> Type -> Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL 
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- Tuples 
  _,_           : {t1 t2 : Type} -> Term t1 -> Term t2 -> Term (t1 , t2)
  fst           : {t1 t2 : Type} -> Term (t1 , t2) -> Term t1
  snd           : {t1 t2 : Type} -> Term (t1 , t2) -> Term t2


-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT
  -- Tuples of values are values
  _,_ : {t1 t2 : Type} -> Value t1 -> Value t2 -> Value (t1 , t2)

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
⌜ (x , y) ⌝ = (⌜ x ⌝ , ⌜ y ⌝)


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

vfst : {t1 t2 : Type} -> Value (t1 , t2) -> Value t1
vfst (x , y) = x

vsnd : {t1 t2 : Type} -> Value (t1 , t2) -> Value t2
vsnd (x , y) = y

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ (x , y) ⟧ = (⟦ x ⟧ , ⟦ y ⟧)
⟦ fst tup ⟧ = vfst ⟦ tup ⟧
⟦ snd tup ⟧ = vsnd ⟦ tup ⟧

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
  E-IsZeroSucc : {v : Value NAT} -> Step (iszero (succ ⌜ v ⌝)) false
  E-IsZero     : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  -- Evaluating the elements of a tuple, evaluate the first argument if possible:
  E-EvalFst    : forall {t1 t2} {x x' : Term t1} {y : Term t2} -> Step x x' -> Step (x , y) (x' , y)
  E-EvalSnd    : forall {t1 t2} {x : Term t1} {y y' : Term t2} {vx : Value t1} -> ⌜ vx ⌝ == x -> Step y y' -> Step (x , y) (x , y')
  -- Evaluating fst and snd applied to a tuple:
  E-GetFst     : forall {t1 t2} {x : Term t1} {y : Term t2} -> Step (fst (x , y)) x
  E-GetSnd     : forall {t1 t2} {x : Term t1} {y : Term t2} -> Step (snd (x , y)) y
  -- Delaying fst and snd
  E-Fst        : forall {t1 t2 : Type} {t t' : Term (t1 , t2)} -> Step t t' -> Step (fst t) (fst t')
  E-Snd        : forall {t1 t2 : Type} {t t' : Term (t1 , t2)} -> Step t t' -> Step (snd t) (snd t')

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep (_,_ {t1} {t2} x y) .(x' , ⌜ y ⌝) (E-EvalFst {.t1} {.t2} {.(⌜ x ⌝)} {x'} step) = valuesDoNotStep x x' step
valuesDoNotStep (_,_ {t1} {t2} x y) .(⌜ x ⌝ , y') (E-EvalSnd {.t1} {.t2} {.(⌜ x ⌝)} {.(⌜ y ⌝)} {y'} eq step) = valuesDoNotStep y y' step


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
  lemma (vnat x) (fst tup) ()
  lemma (vnat x) (snd tup) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ steps1)
deterministic (E-IsZero steps1) (E-IsZero steps2) = cong iszero (deterministic steps1 steps2)
deterministic (E-EvalFst y) (E-EvalFst y') = cong ((λ x -> (x , _))) (deterministic y y')
deterministic (E-EvalFst y0) (E-EvalSnd {_} {_} {.(⌜ vx ⌝)} {_} {_} {vx} refl y1) = contradiction (valuesDoNotStep vx _ y0)
deterministic (E-EvalSnd {_} {_} {.(⌜ vx ⌝)} {_} {_} {vx} refl x) (E-EvalFst y0) = contradiction (valuesDoNotStep vx _ y0)
deterministic (E-EvalSnd refl x) (E-EvalSnd r y) with deterministic x y
deterministic (E-EvalSnd refl x) (E-EvalSnd r y) | refl = refl
deterministic E-GetFst E-GetFst = refl
deterministic E-GetFst (E-Fst y) = contradiction (valuesDoNotStep _ _ y)
deterministic E-GetSnd E-GetSnd = refl
deterministic E-GetSnd (E-Snd y) = contradiction (valuesDoNotStep _ _ y)
deterministic (E-Fst y) E-GetFst = contradiction (valuesDoNotStep _ _ y)
deterministic (E-Fst y) (E-Fst y') = cong fst (deterministic y y')
deterministic (E-Snd y) E-GetSnd = contradiction (valuesDoNotStep _ _ y)
deterministic (E-Snd y) (E-Snd y') = cong snd (deterministic y y')

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
  -- If-then-else terms are reducible.
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3 
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t) t4 t5 with iszero-reduces t
  if-reduces (iszero t) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (fst t) t4 t5 with fst-reduces t
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (snd t) t4 t5 with snd-reduces t
  ... | Reduces x = Reduces (E-If-If x)

  fst-reduces : {t1 t2 : Type} -> (t : Term (t1 , t2)) -> Red (fst t)
  fst-reduces (if c then t else e) with if-reduces c t e
  ... | Reduces x = Reduces (E-Fst x)
  fst-reduces (y , y') = Reduces E-GetFst
  fst-reduces (fst y) with fst-reduces y
  fst-reduces (fst y) | Reduces y' = Reduces (E-Fst y')
  fst-reduces (snd y) with snd-reduces y
  fst-reduces (snd y) | Reduces y' = Reduces (E-Fst y')

  snd-reduces : {t1 t2 : Type} -> (t : Term (t1 , t2)) -> Red (snd t)
  snd-reduces (if c then t else e) with if-reduces c t e
  ... | Reduces x = Reduces (E-Snd x)
  snd-reduces (y , y') = Reduces E-GetSnd
  snd-reduces (fst y) with fst-reduces y
  snd-reduces (fst y) | Reduces y' = Reduces (E-Snd y')
  snd-reduces (snd y) with snd-reduces y
  snd-reduces (snd y) | Reduces y' = Reduces (E-Snd y')

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst y) with fst-reduces y
  iszero-reduces (fst y) | Reduces y' = Reduces (E-IsZero y')
  iszero-reduces (snd y) with snd-reduces y
  iszero-reduces (snd y) | Reduces y' = Reduces (E-IsZero y')

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (fst y) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (snd y) nf (Reduces x) = nf (Reduces (E-Succ x))

  fst-nf : ∀ {ty1 ty2} {t1 : Term ty1} {t2 : Term ty2} -> NF (t1 , t2) -> NF t1
  fst-nf nf (Reduces y) = nf (Reduces (E-EvalFst y))

  snd-nf : ∀ {ty1 ty2} {t1 : Term ty1} {t2 : Term ty2} -> NF (t1 , t2) -> NF t2
  snd-nf nf (Reduces y) = nf (Reduces (E-EvalSnd refl y))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (x , y) nf with normal-forms-are-values x (fst-nf nf) | normal-forms-are-values y (snd-nf nf)
  normal-forms-are-values (.(⌜ v ⌝) , .(⌜ v' ⌝)) nf | is-value v | is-value v' = is-value ((v , v'))
  normal-forms-are-values (fst y) nf = contradiction (nf (fst-reduces y))
  normal-forms-are-values (snd y) nf = contradiction (nf (snd-reduces y))

  values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
  values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

  lemma : (t : Term NAT) -> (Red t -> Empty) -> Red (succ t) -> Empty
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  lemma2 : forall {ty1 ty2} -> (t1 : Term ty1) -> (t2 : Term ty2) -> (Red t1 -> Empty) -> (Red t2 -> Empty) -> Red (t1 , t2) -> Empty
  lemma2 t1 t2 nf1 nf2 (Reduces (E-EvalFst y)) = nf1 (Reduces y)
  lemma2 t1 t2 nf1 nf2 (Reduces (E-EvalSnd y y0)) = nf2 (Reduces y0)

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
  progress (x , y) with progress x
  progress (x , y) | Left n with progress y
  progress (x , y) | Left n | Left y' = Left (lemma2 x y n y')
  progress (x , y) | Left n | Right (Reduces y') = Right (Reduces (E-EvalSnd refl y'))
  progress (x , y) | Right (Reduces y') = Right (Reduces (E-EvalFst y'))
  progress (fst t) with progress t
  progress (fst t) | Left x with normal-forms-are-values t x
  progress (fst .(⌜ y ⌝ , ⌜ y' ⌝)) | Left x | is-value (y , y') = Right (Reduces E-GetFst)
  progress (fst t) | Right (Reduces y) = Right (Reduces (E-Fst y))
  progress (snd t) with progress t
  progress (snd t) | Left x with normal-forms-are-values t x
  progress (snd .(⌜ y ⌝ , ⌜ y' ⌝)) | Left x | is-value (y , y') = Right (Reduces E-GetSnd)
  progress (snd t) | Right (Reduces y) = Right (Reduces (E-Snd y))



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

-- zero steps using equality
trivialSteps : ∀ {ty} {t1 t2 : Term ty} -> t1 == t2 -> Steps t1 t2
trivialSteps refl = Nil
  
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

E-Fst-Steps : ∀ {ty1 ty2} {t1 t1' : Term ty1} {t2 : Term ty2} -> 
        Steps t1 t1' →
        Steps (t1 , t2) (t1' , t2)
E-Fst-Steps Nil = Nil
E-Fst-Steps (Cons x steps) = Cons (E-EvalFst x) (E-Fst-Steps steps)

E-Snd-Steps : ∀ {ty1 ty2} {t1 : Term ty1} {t2 t2' : Term ty2} -> 
        Steps t2 t2' →
        Steps (t1 , t2) (t1 , t2')
E-Snd-Steps Nil = Nil
E-Snd-Steps (Cons x steps) = Cons (E-EvalSnd refl x) (E-Snd-Steps steps)

E-Fst'-Steps : ∀ {ty1 ty2 : Type} {t1 t2 : Term (ty1 , ty2)} -> 
        Steps t1 t2 →
        Steps (fst t1) (fst t2)
E-Fst'-Steps Nil = Nil
E-Fst'-Steps (Cons x steps) = Cons (E-Fst x) (E-Fst'-Steps steps)

E-Snd'-Steps : ∀ {ty1 ty2 : Type} {t1 t2 : Term (ty1 , ty2)} -> 
        Steps t1 t2 →
        Steps (snd t1) (snd t2)
E-Snd'-Steps Nil = Nil
E-Snd'-Steps (Cons x steps) = Cons (E-Snd x) (E-Snd'-Steps steps)

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
termination (iszero t) with termination t
termination (iszero t) | terminates (vnat Zero) y' = terminates vtrue (E-IsZero-Steps y' ++ [ E-IsZeroZero ])
termination (iszero t) | terminates (vnat (Succ y)) y' = terminates vfalse (E-IsZero-Steps y' ++ [ E-IsZeroSucc {vnat y} ])
termination (x , y) with termination x | termination y
termination (x , y) | terminates v y' | terminates v' y0 = terminates (v , v') (E-Fst-Steps y' ++ E-Snd-Steps y0)
termination (fst y) with termination y
termination (fst y) | terminates (y' , y0) y1 = terminates y' (E-Fst'-Steps y1 ++ [ E-GetFst ])
termination (snd y) with termination y
termination (snd y) | terminates (y' , y0) y1 = terminates y0 (E-Snd'-Steps y1 ++ [ E-GetSnd ])

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue       : true ⇓ vtrue
  EvalFalse      : false ⇓ vfalse
  EvalIfTrue     : {ty : Type} {b : Term BOOL} {t1 t2 : Term ty} {v : Value ty} -> b ⇓ vtrue  -> t1 ⇓ v -> if b then t1 else t2 ⇓ v
  EvalIfFalse    : {ty : Type} {b : Term BOOL} {t1 t2 : Term ty} {v : Value ty} -> b ⇓ vfalse -> t2 ⇓ v -> if b then t1 else t2 ⇓ v
  EvalZero       : zero ⇓ vnat Zero
  EvalSucc       : {n : Term NAT} {v : Value NAT} -> n ⇓ v -> succ n ⇓ vsucc v
  EvalIszero     : {n : Term NAT} {v : Value NAT} -> n ⇓ v -> iszero n ⇓ viszero v
  EvalTuple      : {t1 t2 : Type} -> {x : Term t1} -> {y : Term t2} -> {vx : Value t1} -> {vy : Value t2} -> x ⇓ vx -> y ⇓ vy -> (x , y) ⇓ (vx , vy)
  EvalFst        : {t1 t2 : Type} -> {tup : Term (t1 , t2)} -> {vx : Value t1} -> {vy : Value t2} -> tup ⇓ (vx , vy) -> fst tup ⇓ vx
  EvalSnd        : {t1 t2 : Type} -> {tup : Term (t1 , t2)} -> {vx : Value t1} -> {vy : Value t2} -> tup ⇓ (vx , vy) -> snd tup ⇓ vy


-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue  = Nil
big-to-small EvalFalse = Nil
big-to-small (EvalIfTrue b t1) = E-If-Steps (big-to-small b) ++ [ E-If-True ] ++ big-to-small t1
big-to-small (EvalIfFalse b t2) = E-If-Steps (big-to-small b) ++ [ E-If-False ] ++ big-to-small t2
big-to-small EvalZero = Nil
big-to-small (EvalSucc {n} {v} red) = (E-Succ-Steps (big-to-small red)) ++ trivialSteps (lemma1 {v})
  where
  lemma1 : {n : Value NAT} -> succ ⌜ n ⌝ == ⌜ vsucc n ⌝
  lemma1 {vnat Zero} = refl
  lemma1 {vnat (Succ n)} = cong succ (lemma1 {vnat n})
big-to-small (EvalIszero {n} {v} red) =  E-IsZero-Steps (big-to-small red) ++ [ isZeroStep {v} ]
  where
  isZeroStep : {n : Value NAT} -> Step (iszero ⌜ n ⌝) (⌜ viszero n ⌝)
  isZeroStep {vnat Zero} = E-IsZeroZero
  isZeroStep {vnat (Succ n)} = E-IsZeroSucc {vnat n}
big-to-small {._} {._} {._} (EvalTuple x y) = E-Fst-Steps (big-to-small x) ++ E-Snd-Steps (big-to-small y)
big-to-small {_} {._} {_} (EvalFst x) =  E-Fst'-Steps (big-to-small x) ++ [ E-GetFst ]
big-to-small {_} {._} {_} (EvalSnd x) =  E-Snd'-Steps (big-to-small x) ++ [ E-GetSnd ]

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = EvalTrue
value-to-value vfalse = EvalFalse
value-to-value (vnat Zero) = EvalZero
value-to-value (vnat (Succ n)) = EvalSucc (value-to-value (vnat n))
value-to-value (x , y) = EvalTuple (value-to-value x) (value-to-value y)


-- Completeness moved, so it can be used in prepend-step
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if c then t else e) with ⟦ c ⟧ | ⇓-complete c
⇓-complete (if c then t else e) | vtrue | x = EvalIfTrue x (⇓-complete t)
⇓-complete (if c then t else e) | vfalse | x = EvalIfFalse x (⇓-complete e)
⇓-complete zero = EvalZero
⇓-complete (succ n) = EvalSucc (⇓-complete n)
⇓-complete (iszero n) = EvalIszero (⇓-complete n)
⇓-complete (y , y') = EvalTuple (⇓-complete y) (⇓-complete y')
⇓-complete (fst y) with ⟦ y ⟧ | ⇓-complete y
⇓-complete (fst y) | (y' , y0) | z = EvalFst z
⇓-complete (snd y) with ⟦ y ⟧ | ⇓-complete y
⇓-complete (snd y) | (y' , y0) | z = EvalSnd z

prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step {ty} .(if true then t2 else t3) t2 v (E-If-True {.ty} {.t2} {t3}) red = EvalIfTrue EvalTrue red
prepend-step {ty} .(if false then t1 else t2) t2 v (E-If-False {.ty} {t1}) red = EvalIfFalse EvalFalse red
prepend-step {ty} .(if t1 then t2 else t3) .(if t1' then t2 else t3) v (E-If-If {.ty} {t1} {t1'} {t2} {t3} y) (EvalIfTrue y' y0) = EvalIfTrue (prepend-step t1 t1'  vtrue y y') y0
prepend-step {ty} .(if t1 then t2 else t3) .(if t1' then t2 else t3) v (E-If-If {.ty} {t1} {t1'} {t2} {t3} y) (EvalIfFalse y' y0) = EvalIfFalse (prepend-step t1 t1' vfalse y y') y0
prepend-step .(succ t) .(succ t') .(vsucc v) (E-Succ {t} {t'} n) (EvalSucc {.t'} {v} y) = EvalSucc (prepend-step t t' v n y)
prepend-step .(iszero zero) .true .vtrue E-IsZeroZero EvalTrue = EvalIszero EvalZero
prepend-step .(iszero (succ (natTerm y))) .false .vfalse (E-IsZeroSucc {vnat y}) EvalFalse = EvalIszero (EvalSucc (value-to-value (vnat y)))
prepend-step .(iszero t) .(iszero t') .(viszero v) (E-IsZero {t} {t'} y) (EvalIszero {.t'} {v} y') =  EvalIszero (prepend-step t t' v y y')
prepend-step .(x , y) .(x' , y) .(vx , vy) (E-EvalFst {t1} {t2} {x} {x'} {y} y') (EvalTuple {.t1} {.t2} {.x'} {.y} {vx} {vy} y0 y1) = EvalTuple (prepend-step x x' vx y' y0) y1
prepend-step .(x , y) .(x , y') .(vx' , vy) (E-EvalSnd {t1} {t2} {x} {y} {y'} y0 y1) (EvalTuple {.t1} {.t2} {.x} {.y'} {vx'} {vy} y2 y3) = EvalTuple y2 (prepend-step y y' vy y1 y3)
prepend-step (fst (y , y')) .y v (E-GetFst) r = EvalFst (EvalTuple r (⇓-complete y'))
prepend-step (snd (y , y')) .y' v (E-GetSnd) r = EvalSnd (EvalTuple ((⇓-complete y)) r)
prepend-step .(fst t) .(fst t') v (E-Fst {._} {t2} {t} {t'} y) (EvalFst y') = EvalFst (prepend-step t t' ((v , _)) y y')
prepend-step .(snd t) .(snd t') v (E-Snd {t1} {._} {t} {t'} y) (EvalSnd y') = EvalSnd (prepend-step t t' (_ , v) y y')

small-to-big : {ty : Type} -> (t : Term ty) -> (v : Value ty) → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big .true vtrue Nil = EvalTrue
small-to-big .false vfalse Nil = EvalFalse
small-to-big .zero (vnat Zero) Nil = EvalZero
small-to-big .(succ (natTerm y)) (vnat (Succ y)) Nil = EvalSucc (small-to-big (natTerm y) (vnat y) Nil)
small-to-big .(⌜ y ⌝ , ⌜ y' ⌝) (y , y') Nil = EvalTuple (small-to-big ⌜ y ⌝ y Nil) (small-to-big ⌜ y' ⌝ y' Nil)
small-to-big t v (Cons y y') = prepend-step t _ v y (small-to-big _ v y')

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.





--------------------------------------------------------------------
--------------------------------------------------------------------
--                                                                --
-- Completeness proof moved up so it can be used in prepend-step! --
--                                                                --
--------------------------------------------------------------------
--------------------------------------------------------------------


⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound true vtrue p = refl
⇓-sound true vfalse ()
⇓-sound false vtrue ()
⇓-sound false vfalse p = refl
⇓-sound (if c then t else e) v (EvalIfTrue y y') with ⇓-sound c vtrue y
⇓-sound (if c then t else e) v (EvalIfTrue y y') | x with ⟦ c ⟧
⇓-sound (if c then t else e) v (EvalIfTrue y y') | refl | vtrue = ⇓-sound t v y'
⇓-sound (if c then t else e) v (EvalIfTrue y y') | () | vfalse
⇓-sound (if c then t else e) v (EvalIfFalse y y') with ⇓-sound c vfalse y
⇓-sound (if c then t else e) v (EvalIfFalse y y') | x with ⟦ c ⟧
⇓-sound (if c then t else e) v (EvalIfFalse y y') | refl | vfalse = ⇓-sound e v y'
⇓-sound (if c then t else e) v (EvalIfFalse y y') | () | vtrue
⇓-sound zero (vnat Zero) p = refl
⇓-sound zero (vnat (Succ y)) ()
⇓-sound .(succ n) .(vsucc v) (EvalSucc {n} {v} y)  with ⇓-sound n v y
⇓-sound .(succ n) .(vsucc ⟦ n ⟧) (EvalSucc {n} y) | refl = refl
⇓-sound .(iszero n) .(viszero v) (EvalIszero {n} {v} y)  with ⇓-sound n v y
⇓-sound .(iszero n) .(viszero ⟦ n ⟧) (EvalIszero {n} y) | refl = refl
⇓-sound .(x , y) .(vx , vy) (EvalTuple {t1} {t2} {x} {y} {vx} {vy} y' y0) with ⇓-sound x vx y' | ⇓-sound y vy y0
⇓-sound .(x , y) .(⟦ x ⟧ , ⟦ y ⟧) (EvalTuple {t1} {t2} {x} {y} y' y0) | refl | refl = refl
⇓-sound (fst tup) y (EvalFst y') with ⇓-sound tup (y , _) y'
... | p = cong vfst p
⇓-sound (snd tup) y (EvalSnd y') with ⇓-sound tup (_ , y) y'
... | p = cong vsnd p

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