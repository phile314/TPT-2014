
module Exercise2a where

-------------------------------------------------------------------------------
-- I'm sorry if the Agda is unreadable in some places - especially in
-- deterministic. In deterministic and the soundness and completeness proofs,
-- I've used the following three tricks (or survival techniques):
--
-- 1. If Agda gets stuck on a unification problem, it has to do with a term
-- that is presented to it as a function value, say ⌜ v ⌝. This situation can
-- be solved by *removing* that information and passing something of the
-- correct type, say t, to a lemma, while sneakily preserving the information
-- that t is actually ⌜ v ⌝ by passing the proof t == ⌜ v ⌝. See also this
-- answer to a similar question: http://stackoverflow.com/a/27066945.
-- You can also change the data type itself, but that doesn't seem pretty.

-- 2. Argument order matters! This is because I as a programmer know which of
-- two arguments I've case split first on, but once it's just program text,
-- Agda can only assume - it (most likely) assumes that it's the first one,
-- and that doesn't work out. Someone has suggested syntax to fix this.
-- https://code.google.com/p/agda/issues/detail?id=408

-- 3. withs with two arguments are (apparently) fundamentally different from
-- two withs with one argument each (i.e. the former cannot be expressed in
-- terms of the latter). This is probably because substitutions are only
-- applied to the current goal and then forgotten. Such two-argument withs
-- were necessary in ⇓-complete and ⇓-sound.
-------------------------------------------------------------------------------

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

data Both (a b : Set) : Set where
  both : a -> b -> Both a b

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
  -- And let's add tuples
  <_,_>         : {ty1 ty2 : Type} -> Term ty1 -> Term ty2 -> Term (TUPLE ty1 ty2)
  fst           : {ty1 ty2 : Type} -> Term (TUPLE ty1 ty2) -> Term ty1
  snd           : {ty1 ty2 : Type} -> Term (TUPLE ty1 ty2) -> Term ty2

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And a new value, for natural numbers
  vnat : Nat -> Value NAT
  -- One more, for tuples
  <<_,_>> : {ty1 ty2 : Type} -> Value ty1 -> Value ty2 -> Value (TUPLE ty1 ty2)

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat k ⌝ = natTerm k
⌜ << v1 , v2 >> ⌝ = < ⌜ v1 ⌝ , ⌜ v2 ⌝ >

-- Example term.
ex : Term NAT -> Term BOOL 
ex t = if iszero t then false else true

-------------------------------------------------------------------------------
-- Denotational semantics.
-------------------------------------------------------------------------------

-- Evaluation of a variety of expressions applied to values.

cond : forall {ty} -> Value BOOL → Value ty → Value ty → Value ty
cond vtrue v2 v3 = v2
cond vfalse v2 v3 = v3

vsucc : Value NAT -> Value NAT
vsucc (vnat x) = vnat (Succ x)

viszero : Value NAT -> Value BOOL
viszero (vnat Zero) = vtrue
viszero (vnat (Succ x)) = vfalse

vfst : {ty1 ty2 : Type} -> Value (TUPLE ty1 ty2) -> Value ty1
vfst << v₁ , v₂ >> = v₁

vsnd : {ty1 ty2 : Type} -> Value (TUPLE ty1 ty2) -> Value ty2
vsnd << v₁ , v₂ >> = v₂

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ < t₁ , t₂ > ⟧ = << ⟦ t₁ ⟧ , ⟦ t₂ ⟧ >>
⟦ fst t ⟧ = vfst ⟦ t ⟧
⟦ snd t ⟧ = vsnd ⟦ t ⟧

-- What can we do to define a denotational semantics?
--   Add types!

-------------------------------------------------------------------------------
-- Small-step semantics.
-------------------------------------------------------------------------------

-- For tuples, we need a rule to evaluate the first and the second parts:
-- E-Tuple-Fst and E-Tuple-Snd.
-- For fst and snd, we need rules to evaluate under them (cf. E-IsZero):
-- E-Fst and E-Snd, as well as rules to eliminate them (cf. E-IsZeroSucc):
-- E-Fst-Fst and E-Snd-Snd.
-- Note that in order to keep the evaluation deterministic, we need to keep
-- a rule from becoming applicable as long as any other rules is still
-- applicable. This is done by requiring that the ‟previous” parts of the
-- terms are values. For example, E-Tuple-Snd only works when the first
-- part of the tuple is a value.

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ       : forall {t t' : Term NAT} -> Step {NAT} t t' -> Step {NAT} (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) (true)
  E-IsZeroSucc : {v : Value NAT} -> Step (iszero (succ ⌜ v ⌝)) false
  E-IsZero     : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  E-Tuple-Fst : forall {ty1 ty2} {t1 t1' : Term ty1} {t2 : Term ty2} ->
              Step t1 t1' -> Step < t1 , t2 > < t1' , t2 >
  E-Tuple-Snd : {ty1 ty2 : Type} {v1 : Value ty1} {t2 t2' : Term ty2} ->
              Step t2 t2' -> Step < ⌜ v1 ⌝ , t2 > < ⌜ v1 ⌝ , t2' >
  E-Fst-Fst : forall {ty1 ty2} {v1 : Value ty1} {v2 : Value ty2} -> Step (fst < ⌜ v1 ⌝ , ⌜ v2 ⌝ >) ⌜ v1 ⌝
  E-Fst : forall {ty1 ty2} {t t' : Term (TUPLE ty1 ty2)} -> Step t t' -> Step (fst t) (fst t')
  E-Snd-Snd : forall {ty1 ty2} {v1 : Value ty1} {v2 : Value ty2} -> Step (snd < ⌜ v1 ⌝ , ⌜ v2 ⌝ >) ⌜ v2 ⌝
  E-Snd : forall {ty1 ty2} {t t' : Term (TUPLE ty1 ty2)} -> Step t t' -> Step (snd t) (snd t')

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep << v1 , v2 >> (if t then t₁ else t₂) ()
valuesDoNotStep << v1 , v2 >> < t1 , t2 > step with lemma step
  where
  lemma : forall {ty1 ty2} {t1 t1' : Term ty1} {t2 t2' : Term ty2} -> Step < t1 , t2 > < t1' , t2' > -> Either (Step t1 t1') (Step t2 t2')
  lemma (E-Tuple-Fst step) = Left step
  lemma (E-Tuple-Snd step) = Right step
valuesDoNotStep << v1 , v2 >> < t1 , t2 > step | Left x = valuesDoNotStep v1 t1 x
valuesDoNotStep << v1 , v2 >> < t1 , t2 > step | Right x = valuesDoNotStep v2 t2 x
valuesDoNotStep << v1 , v2 >> (fst t) ()
valuesDoNotStep << v1 , v2 >> (snd t) ()

-- Steps are deterministic: the same term can not be evaluated in more than one manner.
-- Note: the lemmas that take equality proofs as arguments and then pattern-match on
-- refl might seem superfluous, but they're not - see point 1 in the header.
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
deterministic (E-Tuple-Fst {t2 = t2} steps1) (E-Tuple-Fst steps2) = cong (λ t1 → < t1 , t2 >) (deterministic steps1 steps2)
deterministic (E-Tuple-Fst {t1' = t1'} steps1) (E-Tuple-Snd {v1 = v1} steps2) = contradiction (valuesDoNotStep v1 t1' steps1)
deterministic {t₂ = fst t} (E-Tuple-Snd steps1) ()
deterministic {t₂ = snd t} (E-Tuple-Snd steps1) ()
deterministic {t₂ = if t₂ then t₃ else t₄} (E-Tuple-Snd steps1) ()
deterministic {t₂ = < _ , _ >} (E-Tuple-Snd {ty1} {ty2} {v1} {t2} steps1) steps2 with lemma steps2 refl
  where
  lemma : forall {t1 t1' : Term ty1} {t2 t2' : Term ty2} -> Step < t1 , t2 > < t1' , t2' > -> t1 == ⌜ v1 ⌝ -> Both (t1' == ⌜ v1 ⌝) (Step t2 t2')
  lemma {t1' = t1'} (E-Tuple-Fst step) refl = contradiction (valuesDoNotStep v1 t1' step)
  lemma (E-Tuple-Snd step) p = both p step
deterministic {t₂ = < ._ , _ >} (E-Tuple-Snd steps1) steps2 | both refl x₁ with deterministic steps1 x₁
deterministic {t₂ = < ._ , _ >} (E-Tuple-Snd steps1) steps2 | both refl x₁ | refl = refl
deterministic (E-Fst-Fst {ty1} {ty2} {v1} {v2}) steps2 = sym (lemma steps2 refl refl)
  where
  lemma : forall {t1 t1' : Term ty1} {t2 : Term ty2} -> Step (fst < t1 , t2 >) t1' -> t1 == ⌜ v1 ⌝ -> t2 == ⌜ v2 ⌝ -> t1' == ⌜ v1 ⌝
  lemma E-Fst-Fst p1 p2 = p1
  lemma (E-Fst {t' = t'} step) refl refl = contradiction (valuesDoNotStep << v1 , v2 >> t' step)
deterministic (E-Fst {t' = t'} steps1) (E-Fst-Fst {v1 = v1} {v2 = v2}) = contradiction (valuesDoNotStep << v1 , v2 >> t' steps1)
deterministic (E-Fst steps1) (E-Fst steps2) = cong fst (deterministic steps1 steps2)
deterministic (E-Snd-Snd {ty1} {ty2} {v1} {v2}) steps2 = sym (lemma steps2 refl refl)
  where
  lemma : forall {t1 : Term ty1} {t2 t2' : Term ty2} -> Step (snd < t1 , t2 >) t2' -> t1 == ⌜ v1 ⌝ -> t2 == ⌜ v2 ⌝ -> t2' == ⌜ v2 ⌝
  lemma E-Snd-Snd p1 p2 = p2
  lemma (E-Snd {t' = t'} step) refl refl = contradiction (valuesDoNotStep << v1 , v2 >> t' step)
deterministic (E-Snd {t' = t'} steps1) (E-Snd-Snd {v1 = v1} {v2 = v2}) = contradiction (valuesDoNotStep << v1 , v2 >> t' steps1)
deterministic (E-Snd steps1) (E-Snd steps2) = cong snd (deterministic steps1 steps2)

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
  if-reduces (fst t) t2 t3 with fst-reduces t
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (snd t) t2 t3 with snd-reduces t
  ... | Reduces x = Reduces (E-If-If x)

  -- Iszero-terms are reducible.
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

  -- Fst-terms are reducible.
  fst-reduces : ∀ {ty1 ty2} (t : Term (TUPLE ty1 ty2)) -> Red (fst t)
  fst-reduces (if t1 then t2 else t3) with if-reduces t1 t2 t3
  fst-reduces (if t1 then t2 else t3) | Reduces x = Reduces (E-Fst x)
  fst-reduces < t1 , t2 > with progress t1
  fst-reduces < t1 , t2 > | Left x with normal-forms-are-values t1 x
  fst-reduces < .(⌜ v1 ⌝) , t2 > | Left x | is-value v1 with progress t2
  fst-reduces < .(⌜ v1 ⌝) , t2 > | Left x₁ | is-value v1 | Left x with normal-forms-are-values t2 x
  fst-reduces < .(⌜ v1 ⌝) , .(⌜ v2 ⌝) > | Left x₁ | is-value v1 | Left x | is-value v2 = Reduces (E-Fst-Fst {v1 = v1} {v2 = v2})
  fst-reduces < .(⌜ v1 ⌝) , t2 > | Left x₁ | is-value v1 | Right (Reduces x) = Reduces (E-Fst (E-Tuple-Snd {v1 = v1} x))
  fst-reduces < t1 , t2 > | Right (Reduces x) = Reduces (E-Fst (E-Tuple-Fst x))
  fst-reduces (fst t) with fst-reduces t
  fst-reduces (fst t) | Reduces x = Reduces (E-Fst x)
  fst-reduces (snd t) with snd-reduces t
  fst-reduces (snd t) | Reduces x = Reduces (E-Fst x)

  -- Snd-terms are reducible.
  snd-reduces : ∀ {ty1 ty2} (t : Term (TUPLE ty1 ty2)) -> Red (snd t)
  snd-reduces (if t1 then t2 else t3) with if-reduces t1 t2 t3
  snd-reduces (if t1 then t2 else t3) | Reduces x = Reduces (E-Snd x)
  snd-reduces < t1 , t2 > with progress t1
  snd-reduces < t1 , t2 > | Left x with normal-forms-are-values t1 x
  snd-reduces < .(⌜ v1 ⌝) , t2 > | Left x | is-value v1 with progress t2
  snd-reduces < .(⌜ v1 ⌝) , t2 > | Left x₁ | is-value v1 | Left x with normal-forms-are-values t2 x
  snd-reduces < .(⌜ v1 ⌝) , .(⌜ v2 ⌝) > | Left x₁ | is-value v1 | Left x | is-value v2 = Reduces (E-Snd-Snd {v1 = v1} {v2 = v2})
  snd-reduces < .(⌜ v1 ⌝) , t2 > | Left x₁ | is-value v1 | Right (Reduces x) = Reduces (E-Snd (E-Tuple-Snd {v1 = v1} x))
  snd-reduces < t1 , t2 > | Right (Reduces x) = Reduces (E-Snd (E-Tuple-Fst x))
  snd-reduces (fst t) with fst-reduces t
  snd-reduces (fst t) | Reduces x = Reduces (E-Snd x)
  snd-reduces (snd t) with snd-reduces t
  snd-reduces (snd t) | Reduces x = Reduces (E-Snd x)

  -- A successor that is a normal form contains a normal form.
  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (fst t) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (snd t) nf (Reduces x) = nf (Reduces (E-Succ x))

  -- A tuple that is a normal form contains a normal form (as fst).
  tuple-nf-fst : {ty1 ty2 : Type} -> {t2 : Term ty2} -> (t1 : Term ty1) -> NF < t1 , t2 > -> NF t1
  tuple-nf-fst t1 nf (Reduces x) = nf (Reduces (E-Tuple-Fst x))

  -- A tuple that is a normal form contains a normal form (as snd).
  tuple-nf-snd : {ty1 ty2 : Type} -> {t1 : Term ty1} -> (t2 : Term ty2) -> NF < t1 , t2 > -> NF t2
  tuple-nf-snd {t1 = t1} t2 nf (Reduces x) with normal-forms-are-values t1 (tuple-nf-fst t1 nf)
  tuple-nf-snd t2 nf (Reduces x) | is-value v1 = nf (Reduces (E-Tuple-Snd {v1 = v1} x))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values < t₁ , t₂ > nf with normal-forms-are-values t₁ (tuple-nf-fst t₁ nf) | normal-forms-are-values t₂ (tuple-nf-snd t₂ nf)
  normal-forms-are-values < .(⌜ v₁ ⌝) , .(⌜ v₂ ⌝) > nf | is-value v₁ | is-value v₂ = is-value << v₁ , v₂ >>
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
  progress < t1 , t2 > with progress t1
  progress < t1 , t2 > | Left x with normal-forms-are-values t1 x
  progress < .(⌜ v₁ ⌝) , t2 > | Left x | is-value v₁ with progress t2
  progress < .(⌜ v₁ ⌝) , t2 > | Left x₁ | is-value v₁ | Left x with normal-forms-are-values t2 x
  progress < .(⌜ v₁ ⌝) , .(⌜ v₂ ⌝) > | Left x₁ | is-value v₁ | Left x | is-value v₂ = Left (values-are-normal-forms < ⌜ v₁ ⌝ , ⌜ v₂ ⌝ > (is-value << v₁ , v₂ >>))
  progress < .(⌜ v₁ ⌝) , t2 > | Left x₁ | is-value v₁ | Right (Reduces x) = Right (Reduces (E-Tuple-Snd {v1 = v₁} x))
  progress < t1 , t2 > | Right (Reduces x) = Right (Reduces (E-Tuple-Fst x))
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

-- List-operating (mapped) versions of the various
-- ‟evaluation under ...” evaluation steps

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

E-Tuple-Fst-Steps : ∀ {ty1 ty2} {t1 t1' : Term ty1} {t2 : Term ty2} ->
        Steps t1 t1' →
        Steps < t1 , t2 > < t1' , t2 >
E-Tuple-Fst-Steps Nil = Nil
E-Tuple-Fst-Steps (Cons x steps) = Cons (E-Tuple-Fst x) (E-Tuple-Fst-Steps steps)

E-Tuple-Snd-Steps : ∀ {ty1 ty2} {v1 : Value ty1} {t2 t2' : Term ty2} ->
        Steps t2 t2' →
        Steps < ⌜ v1 ⌝ , t2 > < ⌜ v1 ⌝ , t2' >
E-Tuple-Snd-Steps Nil = Nil
E-Tuple-Snd-Steps {v1 = v1} (Cons x steps) = Cons (E-Tuple-Snd {v1 = v1} x) (E-Tuple-Snd-Steps {v1 = v1} steps)

E-Fst-Steps : ∀ {ty1 ty2} {t t' : Term (TUPLE ty1 ty2)} ->
        Steps t t' →
        Steps (fst t) (fst t')
E-Fst-Steps Nil = Nil
E-Fst-Steps (Cons x steps) = Cons (E-Fst x) (E-Fst-Steps steps)

E-Snd-Steps : ∀ {ty1 ty2} {t t' : Term (TUPLE ty1 ty2)} ->
        Steps t t' →
        Steps (snd t) (snd t')
E-Snd-Steps Nil = Nil
E-Snd-Steps (Cons x steps) = Cons (E-Snd x) (E-Snd-Steps steps)

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
termination (iszero (fst t)) | terminates << vnat Zero , v2 >> x₁ =
  terminates vtrue
    ((E-IsZero-Steps (E-Fst-Steps x₁ ++ [ E-Fst-Fst {v1 = vnat Zero} {v2 = v2} ])) ++ [ E-IsZeroZero ])
termination (iszero (fst t)) | terminates << vnat (Succ x) , v2 >> x₁ =
  terminates vfalse
    ((E-IsZero-Steps (E-Fst-Steps x₁ ++ [ E-Fst-Fst {v1 = vnat (Succ x)} {v2 = v2} ])) ++ [ E-IsZeroSucc {v = vnat x} ])
termination (iszero (snd t)) with termination t
termination (iszero (snd t)) | terminates << v1 , vnat Zero >> x₁ =
  terminates vtrue
    ((E-IsZero-Steps (E-Snd-Steps x₁ ++ [ E-Snd-Snd {v1 = v1} {v2 = vnat Zero} ])) ++ [ E-IsZeroZero ])
termination (iszero (snd t)) | terminates << v1 , vnat (Succ x) >> x₁ =
  terminates vfalse
    ((E-IsZero-Steps (E-Snd-Steps x₁ ++ [ E-Snd-Snd {v1 = v1} {v2 = vnat (Succ x)} ])) ++ [ E-IsZeroSucc {v = vnat x} ])
termination < t1 , t2 > with termination t1 | termination t2
termination < t1 , t2 > | terminates v₁ x₁ | terminates v₂ x₂ =
  terminates << v₁ , v₂ >> (E-Tuple-Fst-Steps x₁ ++ E-Tuple-Snd-Steps {v1 = v₁} x₂)
termination (fst t) with termination t
termination (fst t) | terminates << v1 , v2 >> x =
  terminates v1 (E-Fst-Steps x ++ [ E-Fst-Fst {v1 = v1} {v2 = v2} ])
termination (snd t) with termination t
termination (snd t) | terminates << v1 , v2 >> x =
  terminates v2 (E-Snd-Steps x ++ [ E-Snd-Snd {v1 = v1} {v2 = v2} ])

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
-- These have been chosen in a way that matches the Bool big-step
-- semantics.
data _⇓_ : {ty : Type} → Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalZero : zero ⇓ vnat Zero
  EvalSucc : forall {t} {n} -> t ⇓ vnat n -> succ t ⇓ vnat (Succ n)
  EvalIsZeroZero : forall {t} -> t ⇓ vnat Zero -> iszero t ⇓ vtrue
  EvalIsZeroSucc : forall {t} {n} -> t ⇓ vnat (Succ n) -> iszero t ⇓ vfalse
  EvalIfTrue : forall {ty} {c} {t : Term ty} {e : Term ty} {v : Value ty} -> c ⇓ vtrue -> t ⇓ v -> if c then t else e ⇓ v
  EvalIfFalse : forall {ty} {c} {t : Term ty} {e : Term ty} {v : Value ty} -> c ⇓ vfalse -> e ⇓ v -> if c then t else e ⇓ v
  EvalTuple : forall {ty1 ty2} {t1 : Term ty1} {t2 : Term ty2} {v1 : Value ty1} {v2 : Value ty2} -> t1 ⇓ v1 -> t2 ⇓ v2 -> < t1 , t2 > ⇓ << v1 , v2 >>
  EvalFst : forall {ty1 ty2} {t : Term (TUPLE ty1 ty2)} {v1 : Value ty1} {v2 : Value ty2} -> t ⇓ << v1 , v2 >> -> fst t ⇓ v1
  EvalSnd : forall {ty1 ty2} {t : Term (TUPLE ty1 ty2)} {v1 : Value ty1} {v2 : Value ty2} -> t ⇓ << v1 , v2 >> -> snd t ⇓ v2

-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small EvalZero = Nil
big-to-small (EvalSucc r) = E-Succ-Steps (big-to-small r)
big-to-small (EvalIsZeroZero r) = E-IsZero-Steps (big-to-small r) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroSucc {n = n} r) = E-IsZero-Steps (big-to-small r) ++ [ E-IsZeroSucc {vnat n} ]
big-to-small (EvalIfTrue rc rt) = E-If-Steps (big-to-small rc) ++ [ E-If-True ] ++ big-to-small rt
big-to-small (EvalIfFalse rc re) = E-If-Steps (big-to-small rc) ++ [ E-If-False ] ++ big-to-small re
big-to-small {v = << v1 , v2 >>} (EvalTuple r1 r2) = E-Tuple-Fst-Steps (big-to-small r1) ++ E-Tuple-Snd-Steps {v1 = v1} (big-to-small r2)
big-to-small (EvalFst {v1 = v1} {v2 = v2} p) = E-Fst-Steps (big-to-small p) ++ [ E-Fst-Fst {v1 = v1} {v2 = v2}]
big-to-small (EvalSnd {v1 = v1} {v2 = v2} p) = E-Snd-Steps (big-to-small p) ++ [ E-Snd-Snd {v1 = v1} {v2 = v2}]

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = EvalTrue
value-to-value vfalse = EvalFalse
value-to-value (vnat Zero) = EvalZero
value-to-value (vnat (Succ x)) = EvalSucc (value-to-value (vnat x))
value-to-value << v1 , v2 >> = EvalTuple (value-to-value v1) (value-to-value v2)

prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True r = EvalIfTrue EvalTrue r
prepend-step E-If-False r = EvalIfFalse EvalFalse r
prepend-step (E-If-If step) (EvalIfTrue rc rt) = EvalIfTrue (prepend-step step rc) rt
prepend-step (E-If-If step) (EvalIfFalse rc re) = EvalIfFalse (prepend-step step rc) re
prepend-step (E-Succ step) (EvalSucc r) = EvalSucc (prepend-step step r)
prepend-step E-IsZeroZero EvalTrue = EvalIsZeroZero EvalZero
prepend-step (E-IsZeroSucc {vnat x}) EvalFalse = EvalIsZeroSucc (EvalSucc (value-to-value (vnat x)))
prepend-step (E-IsZero step) (EvalIsZeroZero r) = EvalIsZeroZero (prepend-step step r)
prepend-step (E-IsZero step) (EvalIsZeroSucc r) = EvalIsZeroSucc (prepend-step step r)
prepend-step (E-Tuple-Fst step) (EvalTuple r1 r2) = EvalTuple (prepend-step step r1) r2
prepend-step (E-Tuple-Snd step) (EvalTuple r1 r2) = EvalTuple r1 (prepend-step step r2)
prepend-step (E-Fst-Fst {v1 = v1} {v2 = v2}) r = EvalFst (EvalTuple r (value-to-value v2))
prepend-step (E-Fst step) (EvalFst r) = EvalFst (prepend-step step r)
prepend-step (E-Snd-Snd {v1 = v1} {v2 = v2}) r = EvalSnd (EvalTuple (value-to-value v1) r)
prepend-step (E-Snd step) (EvalSnd r) = EvalSnd (prepend-step step r)

small-to-big : {ty : Type} -> {t : Term ty} -> {v : Value ty} → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big {v = v} Nil = value-to-value v
small-to-big (Cons x steps) = prepend-step x (small-to-big steps)
--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t₁ else t₂) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t₁ else t₂) | vtrue | c = EvalIfTrue c (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | vfalse | c = EvalIfFalse c (⇓-complete t₂)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | c = EvalSucc c
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | c = EvalIsZeroZero c
⇓-complete (iszero t) | vnat (Succ x) | c = EvalIsZeroSucc c
⇓-complete < t1 , t2 > = EvalTuple (⇓-complete t1) (⇓-complete t2)
⇓-complete (fst t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (fst t) | << v1 , v2 >> | c = EvalFst c
⇓-complete (snd t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (snd t) | << v1 , v2 >> | c = EvalSnd c

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → v == ⟦ t ⟧
⇓-sound EvalTrue = refl
⇓-sound EvalFalse = refl
⇓-sound EvalZero = refl
⇓-sound (EvalSucc {t} {n} r) with ⟦ t ⟧ | ⇓-sound r
⇓-sound (EvalSucc r) | ._ | refl = refl
⇓-sound (EvalIsZeroZero {t} r) with ⟦ t ⟧ | ⇓-sound r
⇓-sound (EvalIsZeroZero r) | ._ | refl = refl
⇓-sound (EvalIsZeroSucc {t} {n} r) with ⟦ t ⟧ | ⇓-sound r
⇓-sound (EvalIsZeroSucc r) | ._ | refl = refl
⇓-sound (EvalIfTrue {c = c} rc rt) with ⟦ c ⟧ | ⇓-sound rc
⇓-sound (EvalIfTrue rc rt) | .vtrue | refl = ⇓-sound rt
⇓-sound (EvalIfFalse {c = c} rc re) with ⟦ c ⟧ | ⇓-sound rc
⇓-sound (EvalIfFalse rc re) | .vfalse | refl = ⇓-sound re
⇓-sound (EvalTuple {t1 = t1} {t2 = t2} r1 r2)
  with ⟦ t1 ⟧ | ⇓-sound r1 | ⟦ t2 ⟧ | ⇓-sound r2
⇓-sound (EvalTuple r1 r2) | ._ | refl | ._ | refl = refl
⇓-sound (EvalFst {t = t} r) with ⟦ t ⟧ | ⇓-sound r
⇓-sound (EvalFst r) | ._ | refl = refl
⇓-sound (EvalSnd {t = t} r) with ⟦ t ⟧ | ⇓-sound r
⇓-sound (EvalSnd r) | ._ | refl = refl

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
