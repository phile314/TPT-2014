
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

sym : {a : Set} {x y : a} -> x == y -> y == x
sym refl = refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans refl refl = refl

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
  tuple         : {a b : Type} -> Term a -> Term b -> Term (TUPLE a b)
  fst           : {a b : Type} -> Term (TUPLE a b) -> Term a
  snd           : {a b : Type} -> Term (TUPLE a b) -> Term b


-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT
  vtuple : {a b : Type} -> Value a -> Value b -> Value (TUPLE a b)

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
⌜ vtuple a b ⌝ = tuple ⌜ a ⌝ ⌜ b ⌝


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

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ tuple x y ⟧ = vtuple ⟦ x ⟧ ⟦ y ⟧
⟦ fst x ⟧ with ⟦ x ⟧
⟦ fst x ⟧ | vtuple p q = p
⟦ snd x ⟧ with ⟦ x ⟧
⟦ snd x ⟧ | vtuple p q = q

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
  E-TupleFst   : forall {ty ty'} -> { t t' : Term ty} -> {p : Term ty'} -> Step t t' -> Step (tuple t p) (tuple t' p)
  E-TupleSnd   : forall {ty ty'} -> { t t' : Term ty} -> {p : Value ty'} -> Step t t' -> Step (tuple ⌜ p ⌝ t) (tuple ⌜ p ⌝ t')
  E-FstTuple   : forall {ty ty'} -> { t : Term ty} -> {t' : Term ty'} -> Step (fst (tuple t t')) t
  E-SndTuple   : forall {ty ty'} -> { t : Term ty} -> {t' : Term ty'} -> Step (snd (tuple t t')) t'
  E-Fst        : forall {ty ty'} -> { tup tup' : Term (TUPLE ty ty') } -> Step tup tup' ->  Step (fst tup) (fst tup')
  E-Snd        : forall {ty ty'} -> { tup tup' : Term (TUPLE ty ty') } -> Step tup tup' ->  Step (snd tup) (snd tup')

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep (vtuple x y) t step = lem t ⌜ x ⌝ ⌜ y ⌝ step
  where
  lem : forall {a b : Type} -> (t : Term (TUPLE a b)) (v : Term a) -> (w : Term b) -> Step (tuple v w) t -> Empty
  lem (if t₁ then t₂ else t₃) v w ()
  lem (tuple p q) v .q (E-TupleFst stp) = {!!}
  lem (tuple ._ q) ._ w (E-TupleSnd stp) = {!!}
  lem (fst t₁) v w ()
  lem (snd t₁) v w ()

flip : forall {a b c : Set} -> (a -> b -> c) -> b -> a -> c
flip f b a = f a b

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
  lemma (vnat x) (fst y) ()
  lemma (vnat x) (snd y) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ steps1)
deterministic (E-IsZero steps1) (E-IsZero steps2) = cong iszero (deterministic steps1 steps2)
deterministic (E-TupleFst { p = p } x) (E-TupleFst y) = cong (flip tuple p) (deterministic x y)
deterministic (E-TupleFst x) (E-TupleSnd { p = p} y) = contradiction (valuesDoNotStep p _ x)
deterministic (E-TupleSnd { p = p } x) y = contradiction (valuesDoNotStep {!!} _ x)
deterministic E-FstTuple E-FstTuple = refl
deterministic E-FstTuple (E-Fst y) = {!!}
deterministic E-SndTuple E-SndTuple = refl
deterministic E-SndTuple (E-Snd y) = {!!}
deterministic (E-Fst x) E-FstTuple = {!!}
deterministic (E-Fst x) (E-Fst y) = cong fst (deterministic x y)
deterministic (E-Snd x) E-SndTuple = {!!}
deterministic (E-Snd x) (E-Snd y) = cong snd (deterministic x y)

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
  if-reduces (fst x) y z with fst-reduces x
  if-reduces (fst x) y z | Reduces p = Reduces (E-If-If p)
  if-reduces (snd x) y z with snd-reduces x
  if-reduces (snd x) y z | Reduces p = Reduces (E-If-If p)


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

  fst-reduces : forall {a b : Type} (t : Term (TUPLE a b)) -> Red (fst t)
  fst-reduces (if c then t else e) with if-reduces c t e
  fst-reduces (if c then t else e) | Reduces x = Reduces (E-Fst x)
  fst-reduces (tuple p q) = Reduces E-FstTuple
  fst-reduces (fst t) with fst-reduces t
  fst-reduces (fst t) | Reduces x = Reduces (E-Fst x)
  fst-reduces (snd t) with snd-reduces t
  fst-reduces (snd t) | Reduces x = Reduces (E-Fst x)

  snd-reduces : forall {a b : Type} (t : Term (TUPLE a b)) -> Red (snd t)
  snd-reduces (if c then t else e) with if-reduces c t e
  snd-reduces (if c then t else e) | Reduces x = Reduces (E-Snd x)
  snd-reduces (tuple t t₁) = Reduces E-SndTuple
  snd-reduces (fst t) with fst-reduces t
  snd-reduces (fst t) | Reduces x = Reduces (E-Snd x)
  snd-reduces (snd t) with snd-reduces t
  snd-reduces (snd t) | Reduces x = Reduces (E-Snd x)

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (fst y) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (snd y) nf (Reduces x) = nf (Reduces (E-Succ x))

  fst-nf : forall {a b} -> (t : Term a) -> (t' : Term b) -> NF (tuple t t') -> NF t
  fst-nf t t' nf (Reduces x) = nf (Reduces (E-TupleFst x))

  snd-nf : forall {a b} -> (t : Value a) -> (t' : Term b) -> NF (tuple ⌜ t ⌝ t') -> NF t'
  snd-nf t t' nf (Reduces x) = nf (Reduces (E-TupleSnd { p = t } x))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (tuple x y) nf with normal-forms-are-values x (fst-nf x y nf)
  normal-forms-are-values (tuple .(⌜ v ⌝) y) nf | is-value v with normal-forms-are-values y (snd-nf v y nf)
  normal-forms-are-values (tuple .(⌜ v ⌝) .(⌜ w ⌝)) nf | is-value v | is-value w = is-value (vtuple v w)
  normal-forms-are-values (fst x) nf = contradiction (nf (fst-reduces x))
  normal-forms-are-values (snd x) nf = contradiction (nf (snd-reduces x))

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
  progress (tuple x y) with progress x
  progress (tuple x y) | Left p with progress y
  progress (tuple x y) | Left p | Left q with normal-forms-are-values x p | normal-forms-are-values y q
  progress (tuple .(⌜ u ⌝) .(⌜ v ⌝)) | Left p | Left q | is-value u | is-value v = Left (values-are-normal-forms (tuple _ _) (is-value (vtuple u v)))
  progress (tuple x y) | Left p | Right (Reduces q) with normal-forms-are-values x p
  progress (tuple .(⌜ v ⌝) y) | Left p | Right (Reduces q) | is-value v = Right (Reduces (E-TupleSnd { p = v } q))
  progress (tuple x y) | Right (Reduces p) = Right (Reduces (E-TupleFst p))
  progress (fst x) = Right (fst-reduces x)
  progress (snd x) = Right (snd-reduces x)

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

E-Fst-Steps : forall {a b} {t t' : Term (TUPLE a b)} -> Steps t t' -> Steps (fst t) (fst t')
E-Fst-Steps Nil = Nil
E-Fst-Steps (Cons x steps) = Cons (E-Fst x) (E-Fst-Steps steps)

E-Snd-Steps : forall {a b} {t t' : Term (TUPLE a b)} -> Steps t t' -> Steps (snd t) (snd t')
E-Snd-Steps Nil = Nil
E-Snd-Steps (Cons x steps) = Cons (E-Snd x) (E-Snd-Steps steps)

E-TupleFst-Steps : forall {a b} {t t' : Term a} -> {s : Term b} -> Steps t t' -> Steps (tuple t s) (tuple t' s)
E-TupleFst-Steps Nil = Nil
E-TupleFst-Steps (Cons x steps) = Cons (E-TupleFst x) (E-TupleFst-Steps steps)

E-TupleSnd-Steps : forall {a b} {t t' : Term a} -> {s : Value b} -> Steps t t' -> Steps (tuple ⌜ s ⌝ t) (tuple ⌜ s ⌝ t')
E-TupleSnd-Steps Nil = Nil
E-TupleSnd-Steps {a} {b} {t} {t'} {s} (Cons x steps) = Cons  (E-TupleSnd {p = s} x) (E-TupleSnd-Steps {s = s} steps)

E-FstTuple-Steps : forall {a b} {p : Term a} {q : Term b} {tup : Term (TUPLE a b)} -> Steps tup (tuple p q) -> Steps (fst tup) p
E-FstTuple-Steps Nil = [ E-FstTuple ]
E-FstTuple-Steps (Cons x s) = Cons (E-Fst x) (E-FstTuple-Steps s)

E-SndTuple-Steps : forall {a b} {p : Term a} {q : Term b} {tup : Term (TUPLE a b)} -> Steps tup (tuple p q) -> Steps (snd tup) q
E-SndTuple-Steps Nil = [ E-SndTuple ]
E-SndTuple-Steps (Cons x s) = Cons (E-Snd x) (E-SndTuple-Steps s)

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
termination (iszero (fst x)) with termination x
termination (iszero (fst x)) | terminates (vtuple (vnat Zero) v) w = terminates vtrue (E-IsZero-Steps (E-Fst-Steps w) ++ [ E-IsZero E-FstTuple ] ++ [ E-IsZeroZero ])
termination (iszero (fst x)) | terminates (vtuple (vnat (Succ n)) v) w = terminates vfalse (E-IsZero-Steps (E-Fst-Steps w) ++ [ E-IsZero E-FstTuple ] ++ [ E-IsZeroSucc {vnat n} ])
termination (iszero (snd x)) with termination x
termination (iszero (snd x)) | terminates (vtuple v (vnat Zero)) w = terminates vtrue (E-IsZero-Steps (E-Snd-Steps w) ++ [ E-IsZero E-SndTuple ] ++ [ E-IsZeroZero ])
termination (iszero (snd x)) | terminates (vtuple v (vnat (Succ n))) w = terminates vfalse (E-IsZero-Steps (E-Snd-Steps w) ++ [ E-IsZero E-SndTuple ] ++ [ E-IsZeroSucc {vnat n} ])
termination (tuple x y) with termination x | termination y
termination (tuple x y) | terminates u p | terminates v q = terminates (vtuple u v) (E-TupleFst-Steps p ++ E-TupleSnd-Steps {s = u} q)
termination (fst x) with termination x
termination (fst x) | terminates (vtuple t t') q = terminates t (E-Fst-Steps q ++ [ E-FstTuple ])
termination (snd x) with termination x
termination (snd x) | terminates (vtuple t t') q = terminates t' (E-Snd-Steps q ++ [ E-SndTuple ])

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalIfTrue : forall {ty} {c : Term BOOL} {t e : Term ty} {v} -> c ⇓ vtrue -> t ⇓ v -> if c then t else e ⇓ v
  EvalIfFalse : forall {ty} {c : Term BOOL} {t e : Term ty} {v} -> c ⇓ vfalse -> e ⇓ v -> if c then t else e ⇓ v
  EvalZero : zero ⇓ vnat Zero
  EvalSucc : forall {x : Term NAT} {y : Nat} -> x ⇓ vnat y -> succ x ⇓ vnat (Succ y)
  EvalIsZeroZero : forall {x : Term NAT} -> x ⇓ vnat Zero -> iszero x ⇓ vtrue
  EvalIsZeroSucc : forall {x : Term NAT} {y : Nat} -> x ⇓ vnat (Succ y)  -> iszero x ⇓ vfalse
  EvalTuple : forall {a b} {p : Term a} {q : Term b} {u : Value a} {v : Value b} -> p ⇓ u -> q ⇓ v -> tuple p q ⇓ vtuple u v
  EvalFst : forall {a b} {p : Value a} {q : Value b} {v} -> v ⇓ vtuple p q -> fst v ⇓ p
  EvalSnd : forall {a b} {p : Value a} {q : Value b} {v} -> v ⇓ vtuple p q -> snd v ⇓ q

-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small (EvalIfTrue p q) = E-If-Steps (big-to-small p) ++ [ E-If-True ] ++ big-to-small q
big-to-small (EvalIfFalse p q) = E-If-Steps (big-to-small p) ++ [ E-If-False ] ++ big-to-small q
big-to-small EvalZero = Nil
big-to-small (EvalSucc p) = E-Succ-Steps (big-to-small p)
big-to-small (EvalIsZeroZero p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroSucc {x} {y} p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroSucc { vnat y } ]
big-to-small (EvalTuple {u = u} x y) = E-TupleFst-Steps (big-to-small x) ++ E-TupleSnd-Steps { s = u } (big-to-small y)
big-to-small (EvalFst x) = E-FstTuple-Steps (big-to-small x)
big-to-small (EvalSnd x) = E-SndTuple-Steps (big-to-small x)

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = EvalTrue
value-to-value vfalse = EvalFalse
value-to-value (vnat Zero) = EvalZero
value-to-value (vnat (Succ x)) = EvalSucc (value-to-value (vnat x))
value-to-value (vtuple x y) = EvalTuple (value-to-value x) (value-to-value y)

prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True p = EvalIfTrue EvalTrue p
prepend-step E-If-False t = EvalIfFalse EvalFalse t
prepend-step (E-If-If s) (EvalIfTrue p q) = EvalIfTrue (prepend-step s p) q
prepend-step (E-If-If s) (EvalIfFalse p q) = EvalIfFalse (prepend-step s p) q
prepend-step (E-Succ s) (EvalSucc x) = EvalSucc (prepend-step s x)
prepend-step E-IsZeroZero EvalTrue = EvalIsZeroZero EvalZero
prepend-step (E-IsZeroSucc {vnat x}) EvalFalse = EvalIsZeroSucc (value-to-value (vnat (Succ x)))
prepend-step (E-IsZero s) (EvalIsZeroZero p) = EvalIsZeroZero (prepend-step s p)
prepend-step (E-IsZero s) (EvalIsZeroSucc p) = EvalIsZeroSucc (prepend-step s p)
prepend-step (E-TupleFst x) (EvalTuple y z) = EvalTuple (prepend-step x y) z
prepend-step (E-TupleSnd x) (EvalTuple y z) = EvalTuple y (prepend-step x z)
prepend-step (E-FstTuple {t' = t'}) y = EvalFst (EvalTuple y _)
prepend-step E-SndTuple y = EvalSnd (EvalTuple _ y)
prepend-step (E-Fst x) (EvalFst y) = EvalFst (prepend-step x y)
prepend-step (E-Snd x) (EvalSnd y) = EvalSnd (prepend-step x y)

small-to-big : {ty : Type} -> {t : Term ty} -> (v : Value ty) → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big v Nil = value-to-value v
small-to-big v (Cons x steps) = prepend-step x (small-to-big v steps)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then x else y) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then x else y) | vtrue | q = EvalIfTrue q (⇓-complete x)
⇓-complete (if t then x else y) | vfalse | q = EvalIfFalse q (⇓-complete y)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | q = EvalSucc q
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | q = EvalIsZeroZero q
⇓-complete (iszero t) | vnat (Succ x) | q = EvalIsZeroSucc { y = x } q
⇓-complete (tuple x y) with ⟦ x ⟧ | ⟦ y ⟧ | ⇓-complete x | ⇓-complete y
... | x' | y' | p | q = EvalTuple p q
⇓-complete (fst x) with ⟦ x ⟧ | ⇓-complete x
⇓-complete (fst x) | vtuple p q | e = EvalFst e
⇓-complete (snd x) with ⟦ x ⟧ | ⇓-complete x
⇓-complete (snd x) | vtuple p q | e = EvalSnd e

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} {v : Value ty} -> (t : Term ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound true EvalTrue = refl
⇓-sound false EvalFalse = refl
⇓-sound (if c then t else e) (EvalIfTrue { v = v } x y) = trans (⇓-sound t y) (lem t e (⇓-sound c x))
  where
  lem : forall {ty : Type} {c : Value BOOL} (t e : Term ty) -> vtrue == c -> ⟦ t ⟧ == cond c ⟦ t ⟧ ⟦ e ⟧
  lem t e refl = refl
⇓-sound (if c then t else e) (EvalIfFalse x y) = trans (⇓-sound e y) (lem t e (⇓-sound c x))
  where
  lem : forall {ty : Type} {c : Value BOOL} (t e : Term ty) -> vfalse == c -> ⟦ e ⟧ == cond c ⟦ t ⟧ ⟦ e ⟧
  lem t e refl = refl
⇓-sound zero EvalZero = refl
⇓-sound (succ x) (EvalSucc y) = cong vsucc (⇓-sound x y)
⇓-sound (iszero x) (EvalIsZeroZero y) = cong viszero (⇓-sound x y)
⇓-sound (iszero x) (EvalIsZeroSucc y) = cong viszero (⇓-sound x y)
⇓-sound (tuple p q) (EvalTuple x y) with ⇓-sound p x | ⇓-sound q y
⇓-sound (tuple p q) (EvalTuple x y) | refl | refl = refl
⇓-sound (fst x) (EvalFst y) with ⟦ x ⟧ | ⇓-sound x y
⇓-sound (fst x) (EvalFst y) | vtuple v w | refl = refl
⇓-sound (snd x) (EvalSnd y) with ⟦ x ⟧ | ⇓-sound x y
⇓-sound (snd x) (EvalSnd y) | vtuple p v | refl = refl

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
