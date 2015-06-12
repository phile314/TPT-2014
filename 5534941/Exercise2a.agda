
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
  TUP2 : Type -> Type -> Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL 
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- And tuples!
  _,_            : {t t' : Type} → (x : Term t) → (y : Term t') → Term (TUP2 t t')
  fst              : {t t' : Type} → (x : Term (TUP2 t t')) → Term t
  snd            : {t t' : Type} → (x : Term (TUP2 t t')) → Term t'


-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  vnat : Nat -> Value NAT
  vtup2 : {t t' : Type} → Value t → Value t' → Value (TUP2 t t')

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat k ⌝ = natTerm k
⌜ vtup2 x y ⌝ = (⌜ x ⌝ , ⌜ y ⌝)


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

vfst : {t t' : Type} → Value (TUP2 t t') → Value t
vfst (vtup2 x _) = x

vsnd : {t t' : Type} → Value (TUP2 t t') → Value t'
vsnd (vtup2 _ y) = y

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ (x , y) ⟧ = vtup2 ⟦ x ⟧ ⟦ y ⟧
⟦ fst x ⟧ = vfst ⟦ x ⟧
⟦ snd x ⟧ = vsnd ⟦ x ⟧

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
  -- Tuples; evaluated from left to right! TODO: Use is-value declared below instead of ⌜ v1 ⌝ == t1 ??
  E-Tup2-1 :  forall {ty1 ty2} {t1 t1' : Term ty1}{t2 : Term ty2} → Step t1 t1' → Step (t1 , t2) (t1' , t2)
  E-Tup2-2 :  forall {ty1 ty2} {t1 : Term ty1}{v1 : Value ty1}{t2 t2'  : Term ty2} → ⌜ v1 ⌝ == t1 → Step t2 t2' → Step (t1 , t2) (t1 , t2')
  E-Fst : forall {ty1 ty2} {t t' : Term (TUP2 ty1 ty2)} → Step t t' → Step (fst t) (fst t')       -- To fst / snd
  E-Snd : forall {ty1 ty2} {t t' : Term (TUP2 ty1 ty2)} → Step t t' → Step (snd t) (snd t')
  -- Extracts from fst / snd; only when both branches are fully evaluated
  E-Fst-Extract : forall {ty1 ty2} {t1 : Term ty1} {v1 : Value ty1} {t2 : Term ty2} {v2 : Value ty2} → 
    ⌜ v1 ⌝ == t1 → ⌜ v2 ⌝ == t2 → Step (fst (t1 , t2)) t1
  E-Snd-Extract : forall {ty1 ty2} {t1 : Term ty1} {v1 : Value ty1} {t2 : Term ty2} {v2 : Value ty2} → 
    ⌜ v1 ⌝ == t1 → ⌜ v2 ⌝ == t2 → Step (snd (t1 , t2)) t2

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep (vtup2 x _) ._ (E-Tup2-1 step) = valuesDoNotStep x _ step
valuesDoNotStep (vtup2 _ y) ._ (E-Tup2-2 _ step) = valuesDoNotStep y _ step


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
  lemma (vnat x) (fst z) ()
  lemma (vnat x) (snd z) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ steps1)
deterministic (E-IsZero steps1) (E-IsZero steps2) = cong iszero (deterministic steps1 steps2)
deterministic (E-Tup2-1 a) (E-Tup2-1 b) = cong (λ z → (z , _)) (deterministic a b)
deterministic (E-Tup2-1 a) (E-Tup2-2 {v1 = v1} refl b) =  contradiction (valuesDoNotStep v1 _ a)
deterministic (E-Tup2-2 {v1 = v1} refl a) (E-Tup2-1 b) = contradiction (valuesDoNotStep v1 _ b)
deterministic (E-Tup2-2 p a) (E-Tup2-2 x b) = cong (λ z → (_ , z)) (deterministic a b) -- \z -> (_ , z) is clearer than (_,_ _)
deterministic (E-Fst a) (E-Fst b) = cong fst (deterministic a b)
deterministic (E-Fst a) (E-Fst-Extract {v1 = v1} {v2 = v2} refl refl) = contradiction (valuesDoNotStep (vtup2 v1 v2) _ a)
deterministic (E-Snd a) (E-Snd b) = cong snd (deterministic a b)
deterministic (E-Snd a) (E-Snd-Extract {v1 = v1} {v2 = v2} refl refl) = contradiction (valuesDoNotStep (vtup2 v1 v2) _ a)
deterministic (E-Fst-Extract {v1 = v1} {v2 = v2} refl refl) (E-Fst b) = contradiction (valuesDoNotStep (vtup2 v1 v2) _ b)
deterministic (E-Fst-Extract p q) (E-Fst-Extract x y) = refl
deterministic (E-Snd-Extract {v1 = v1} {v2 = v2} refl refl) (E-Snd b) = contradiction (valuesDoNotStep (vtup2 v1 v2) _ b)
deterministic (E-Snd-Extract p q) (E-Snd-Extract x y) = refl

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
  if-reduces (fst t) _ _ with fst-reduces t
  if-reduces (fst t) _ _ | Reduces x = Reduces (E-If-If x)
  if-reduces (snd t) _ _ with snd-reduces t
  if-reduces (snd t) _ _ | Reduces x = Reduces (E-If-If x)


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

  fst-reduces : ∀ {ty ty1} (x : Term (TUP2 ty ty1)) → Red (fst x)
  fst-reduces (if t then t₁ else t₂)  with if-reduces t t₁ t₂
  fst-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Fst x)
  fst-reduces (x , x₁) with progress x
  fst-reduces (x , x₂) | Left x₁ with normal-forms-are-values x x₁ 
  fst-reduces (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v with progress x₂ 
  fst-reduces (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v | Left x with normal-forms-are-values x₂ x
  fst-reduces (.(⌜ v ⌝) , .(⌜ v₁ ⌝)) | Left x₁ | is-value v | Left x | is-value v₁ = Reduces (E-Fst-Extract {v1 = v} {v2 = v₁} refl refl)
  fst-reduces (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v | Right (Reduces x) = Reduces (E-Fst (E-Tup2-2 {v1 = v} refl x))
  fst-reduces (x , x₂) | Right (Reduces x₁) = Reduces (E-Fst (E-Tup2-1 x₁))
  fst-reduces (fst t) with fst-reduces t
  fst-reduces (fst t) | Reduces x = Reduces (E-Fst x)
  fst-reduces (snd t) with snd-reduces t
  fst-reduces (snd t₁) | Reduces x = Reduces (E-Fst x)

  snd-reduces : ∀ {ty ty1} (x : Term (TUP2 ty ty1)) → Red (snd x)
  snd-reduces (if t then t₁ else t₂)  with if-reduces t t₁ t₂
  snd-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Snd x)
  snd-reduces (x , x₁) with progress x
  snd-reduces (x , x₂) | Left x₁ with normal-forms-are-values x x₁ 
  snd-reduces (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v with progress x₂
  snd-reduces (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v | Left x with normal-forms-are-values x₂ x 
  snd-reduces (.(⌜ v₁ ⌝) , .(⌜ v ⌝)) | Left x₁ | is-value v₁ | Left x | is-value v = Reduces (E-Snd-Extract {v1 = v₁} {v2 = v} refl refl)
  snd-reduces (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v | Right (Reduces x) = Reduces (E-Snd (E-Tup2-2 {v1 = v} refl x))
  snd-reduces (x , x₂) | Right (Reduces x₁) = Reduces (E-Snd (E-Tup2-1 x₁))
  snd-reduces (fst t) with fst-reduces t
  snd-reduces (fst t) | Reduces x = Reduces (E-Snd x)
  snd-reduces (snd t) with snd-reduces t
  snd-reduces (snd t₁) | Reduces x = Reduces (E-Snd x)

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (fst t) nf x with fst-reduces t
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf (snd t) nf x with snd-reduces t
  ... | Reduces step = nf (Reduces (E-Succ step))

  fst-nf : ∀ {ty ty1} → (x : Term ty) →  {y : Term ty1} →  NF (x , y) → NF x
  fst-nf true nf (Reduces ())
  fst-nf false nf (Reduces ())
  fst-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Tup2-1 step))
  fst-nf zero nf (Reduces ())
  fst-nf (succ k) nf (Reduces x) = nf (Reduces (E-Tup2-1 x))
  fst-nf (iszero k) nf x with iszero-reduces k
  ... | Reduces step = nf (Reduces (E-Tup2-1 step))
  fst-nf (x , x₁) nf (Reduces x₂) = nf (Reduces (E-Tup2-1 x₂))
  fst-nf (fst x) nf (Reduces x₁) = nf (Reduces (E-Tup2-1 x₁))
  fst-nf (snd x) nf (Reduces x₁) = nf (Reduces (E-Tup2-1 x₁))

  snd-nf : ∀ {ty ty1} → {x : Value ty} →  (y : Term ty1) →  NF (⌜ x ⌝ , y) → NF y
  snd-nf true nf (Reduces ())
  snd-nf false nf (Reduces ())
  snd-nf {x = v} (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Tup2-2 {v1 = v} refl step))
  snd-nf zero nf (Reduces ())
  snd-nf {x = v} (succ k) nf (Reduces x) = nf (Reduces (E-Tup2-2 {v1 = v} refl x))
  snd-nf {x = v} (iszero k) nf x with iszero-reduces k
  ... | Reduces step = nf (Reduces (E-Tup2-2 {v1 = v} refl step))
  snd-nf {x = v} (x , x₁) nf (Reduces x₂) = nf (Reduces (E-Tup2-2 {v1 = v} refl x₂))
  snd-nf {x = v} (fst x) nf (Reduces x₁) = nf (Reduces (E-Tup2-2 {v1 = v} refl x₁))
  snd-nf {x = v} (snd x) nf (Reduces x₁) = nf (Reduces (E-Tup2-2 {v1 = v} refl x₁))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (x , y) nf with normal-forms-are-values x (fst-nf x nf)
  normal-forms-are-values (.(⌜ v ⌝) , y) nf | is-value v with normal-forms-are-values y (snd-nf {x = v} y nf)
  normal-forms-are-values (.(⌜ v ⌝) , .(⌜ v₁ ⌝)) nf | is-value v | is-value v₁ = is-value (vtup2 v v₁)
  normal-forms-are-values (fst t) nf = contradiction (nf (fst-reduces t))
  normal-forms-are-values (snd t) nf = contradiction (nf (snd-reduces t))

  -- Made t implicit; is-value forces it to be ⌜ v ⌝ already..
  values-are-normal-forms : forall {ty} {t : Term ty} -> Is-value t -> NF t
  values-are-normal-forms  (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

  lemma : (t : Term NAT) -> (Red t -> Empty) -> Red (succ t) -> Empty
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true = Left (values-are-normal-forms (is-value vtrue))
  progress false = Left (values-are-normal-forms (is-value vfalse))
  progress (if t then t₁ else t₂) = Right (if-reduces t _ _)
  progress zero = Left (values-are-normal-forms (is-value (vnat (Zero))))
  progress (succ t) with progress t 
  progress (succ t) | Left x = Left (lemma t x)
  progress (succ t) | Right (Reduces step) = Right (Reduces (E-Succ step))
  progress (iszero t) with progress t
  progress (iszero t) | Left x with normal-forms-are-values t x
  progress (iszero .zero) | Left x₁ | is-value (vnat Zero) = Right (Reduces E-IsZeroZero)
  progress (iszero .(succ (natTerm x))) | Left x₁ | is-value (vnat (Succ x)) = 
    Right (Reduces (E-IsZeroSucc {vnat x}))
  progress (iszero t) | Right (Reduces step) = Right (Reduces (E-IsZero step))
  progress (x , x₁) with progress x
  progress (x , x₂) | Left x₁ with normal-forms-are-values x x₁ 
  progress (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v with progress x₂
  progress (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v | Left x with normal-forms-are-values x₂ x
  progress (.(⌜ v₁ ⌝) , .(⌜ v ⌝)) | Left x₁ | is-value v₁ | Left x | is-value v = Left (lemp  x₁ x)
    where
    lemp : ∀ {ty ty1} → {t : Term ty} → {t1 : Term ty1} → (Red t → Empty) → (Red t1 → Empty) → Red (t , t1) → Empty
    lemp nf1 nf2 (Reduces (E-Tup2-1 x₂)) = nf1 (Reduces x₂)
    lemp nf1 nf2 (Reduces (E-Tup2-2 x₂ x₃)) = nf2 (Reduces x₃)
  progress (.(⌜ v ⌝) , x₂) | Left x₁ | is-value v | Right (Reduces x) = Right (Reduces (E-Tup2-2 {v1 = v} refl x))
  progress (x , x₂) | Right (Reduces x₁) = Right (Reduces (E-Tup2-1 x₁))
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

E-Fst-Steps : ∀ {ty ty'} → {t t' : Term (TUP2 ty ty')} →
        Steps t t' → 
        Steps (fst t) (fst t')
E-Fst-Steps Nil = Nil
E-Fst-Steps (Cons x a) = Cons (E-Fst x) (E-Fst-Steps a)

E-Snd-Steps : ∀ {ty ty'} → {t t' : Term (TUP2 ty ty')} →
        Steps t t' → 
        Steps (snd t) (snd t')
E-Snd-Steps Nil = Nil
E-Snd-Steps (Cons x a) = Cons (E-Snd x) (E-Snd-Steps a)

E-Tup2-1-Steps : ∀ {ty1 ty2} → {t1 t1' : Term ty1} → {t2 : Term ty2} →
        Steps t1 t1' → 
        Steps (t1 , t2) (t1' , t2)
E-Tup2-1-Steps Nil = Nil
E-Tup2-1-Steps (Cons x a) = Cons (E-Tup2-1 x) (E-Tup2-1-Steps a)

E-Tup2-2-Steps : ∀ {ty1 ty2} → {t1 : Term ty1} → {v1 : Value ty1} → {t2 t2' : Term ty2} → (⌜ v1 ⌝ == t1) →
        Steps t2 t2' → 
        Steps (t1 , t2) (t1 , t2')
E-Tup2-2-Steps _ Nil = Nil
E-Tup2-2-Steps {v1 = v1} p (Cons x a) = Cons (E-Tup2-2 {v1 = v1} p x) (E-Tup2-2-Steps {v1 = v1} p a)

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
termination (iszero (fst x)) | terminates (vtup2 (vnat Zero) v₁) x₂ = 
   terminates vtrue (E-IsZero-Steps (E-Fst-Steps x₂ ++ [ E-Fst-Extract {v1 = vnat Zero} {v2 = v₁} refl refl ]) ++  [ E-IsZeroZero ])
termination (iszero (fst x)) | terminates (vtup2 (vnat (Succ x₁)) v₁) x₂ = 
   terminates vfalse (E-IsZero-Steps (E-Fst-Steps x₂ ++ [ E-Fst-Extract {v1 = vnat (Succ x₁)} {v2 = v₁} refl refl ]) ++ [ E-IsZeroSucc {vnat x₁} ])
termination (iszero (snd x)) with termination x
termination (iszero (snd x)) | terminates (vtup2 v (vnat Zero)) x₂ = 
   terminates vtrue (E-IsZero-Steps (E-Snd-Steps x₂ ++ [ E-Snd-Extract {v1 = v} {v2 = vnat Zero} refl refl ]) ++ [ E-IsZeroZero ])
termination (iszero (snd x)) | terminates (vtup2 v (vnat (Succ x₁))) x₂ = 
   terminates vfalse (E-IsZero-Steps (E-Snd-Steps x₂ ++ [ E-Snd-Extract {v1 = v} {v2 = vnat (Succ x₁)} refl refl ]) ++ [ E-IsZeroSucc {vnat x₁} ])
termination (x , y) with termination x
termination (x , y) | terminates v x₁ with termination y
termination (x₁ , y) | terminates v₁ x₂ | terminates v x = terminates (vtup2 v₁ v) (E-Tup2-1-Steps x₂ ++ E-Tup2-2-Steps {v1 = v₁} refl x)
termination (fst x) with termination x
termination (fst x) | terminates (vtup2 v v₁) x₁ = terminates v (E-Fst-Steps x₁ ++ [ E-Fst-Extract {v1 = v} {v2 = v₁} refl refl ])
termination (snd x) with termination x
termination (snd x) | terminates (vtup2 v v₁) x₁ = terminates v₁ (E-Snd-Steps x₁ ++ [ E-Snd-Extract {v1 = v} {v2 = v₁} refl refl ])

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  E-True : true ⇓ vtrue
  E-False : false ⇓ vfalse
  E-If-True : {ty : Type}{c : Term BOOL}{t e : Term ty}{v : Value ty} → c ⇓ vtrue  → t ⇓ v → if c then t else e ⇓ v
  E-If-False : {ty : Type}{c : Term BOOL}{t e : Term ty}{v : Value ty} → c ⇓ vfalse → e ⇓ v → if c then t else e ⇓ v
  E-Zero : zero ⇓ vnat Zero
  E-Succ :  {t : Term NAT}{t'  : Nat} → t ⇓ vnat t' → succ t ⇓ vnat (Succ t')
  E-IsZero-Zero : {k : Term NAT} → k ⇓ vnat Zero → iszero k ⇓ vtrue
  E-IsZero-Succ : {k : Term NAT}{l : Nat} → k ⇓ vnat (Succ l) → iszero k ⇓ vfalse
  E-Tup2 : {ty ty1 : Type} {x : Term ty} {y : Term ty1} {x' : Value ty} {y' : Value ty1} → x ⇓ x' → y ⇓ y'  → (x , y) ⇓ vtup2 x' y'
-- Can't get this notation to work, so using the ones below instead
--  E-Fst : {ty ty1 : Type} {x : Term ty} {y : Term ty1} {v : Value ty} → x ⇓ v → fst (x , y) ⇓ v
--  E-Snd : {ty ty1 : Type} {x : Term ty} {y : Term ty1} {v : Value ty1} → y ⇓ v → snd (x , y) ⇓ v
  E-Fst : {ty ty1 : Type} {t : Term (TUP2 ty ty1)} {v : Value ty} {v1 : Value ty1} → t ⇓ vtup2 v v1 → fst t ⇓ v
  E-Snd : {ty ty1 : Type} {t : Term (TUP2 ty ty1)} {v : Value ty} {v1 : Value ty1} → t ⇓ vtup2 v v1 → snd t ⇓ v1


-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small E-True = Nil
big-to-small E-False = Nil
big-to-small (E-If-True c t) = E-If-Steps (big-to-small c) ++ Cons E-If-True (big-to-small t)
big-to-small (E-If-False c t) = E-If-Steps (big-to-small c) ++ Cons E-If-False (big-to-small t)
big-to-small E-Zero = Nil
big-to-small (E-Succ p) = E-Succ-Steps (big-to-small p)
big-to-small (E-IsZero-Zero p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small (E-IsZero-Succ {l = l} p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroSucc {vnat l} ] -- Annoying one -.-
big-to-small (E-Tup2 {x' = x' } x y) = E-Tup2-1-Steps (big-to-small x) ++ E-Tup2-2-Steps {v1 = x'} refl (big-to-small y)
-- big-to-small (E-Fst {y = y} {v = v₁} a) with termination y -- Even more annoying...
-- big-to-small (E-Fst {v = v₁} a) | terminates v₂ ys = E-Fst-Steps (E-Tup2-1-Steps (big-to-small a) ++ E-Tup2-2-Steps {v1 = v₁} refl ys) ++ [ E-Fst-Extract {v1 = v₁} {v2 = v₂} refl refl ]
big-to-small (E-Fst {v = v₁} {v1 = v₂} x) = E-Fst-Steps (big-to-small x) ++ [ E-Fst-Extract {v1 = v₁} {v2 = v₂} refl refl ]
--big-to-small (E-Snd {x = x} {v = v₂}a) with termination x
--big-to-small (E-Snd {v = v₂} a) | terminates v₁ xs = E-Snd-Steps (E-Tup2-1-Steps xs ++ E-Tup2-2-Steps {v1 = v₁} refl (big-to-small a)) ++ [ E-Snd-Extract {v1 = v₁} {v2 = v₂} refl refl ]
big-to-small (E-Snd {v = v₁} {v1 = v₂} x) = E-Snd-Steps (big-to-small x) ++ [ E-Snd-Extract {v1 = v₁} {v2 = v₂} refl refl ]



-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = E-True
value-to-value vfalse = E-False
value-to-value (vnat Zero) = E-Zero
value-to-value (vnat (Succ x)) = E-Succ (value-to-value (vnat x))
value-to-value (vtup2 x y) = E-Tup2 (value-to-value x) (value-to-value y)

-- Made some terms implicit
prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True b = E-If-True E-True b
prepend-step E-If-False b = E-If-False E-False b
prepend-step (E-If-If s) (E-If-True b bs) = E-If-True (prepend-step s b) bs
prepend-step (E-If-If s) (E-If-False b bs) = E-If-False (prepend-step s b) bs
prepend-step (E-Succ s) (E-Succ b) = E-Succ (prepend-step s b)
prepend-step E-IsZeroZero E-True = E-IsZero-Zero E-Zero
prepend-step (E-IsZeroSucc {vnat x}) E-False = E-IsZero-Succ (E-Succ (value-to-value (vnat x)))
prepend-step (E-IsZero s) (E-IsZero-Zero b) = E-IsZero-Zero (prepend-step s b)
prepend-step (E-IsZero s) (E-IsZero-Succ b) = E-IsZero-Succ (prepend-step s b)
prepend-step (E-Tup2-1 a) (E-Tup2 b b₁) = E-Tup2 (prepend-step a b) b₁
prepend-step (E-Tup2-2 x a) (E-Tup2 b b₁) = E-Tup2 b (prepend-step a b₁)
prepend-step (E-Fst a) (E-Fst b) = E-Fst (prepend-step a b)
prepend-step (E-Snd a) (E-Snd b) = E-Snd (prepend-step a b)
prepend-step {v = v} (E-Fst-Extract {v1 = v1} {v2 = v2} refl refl) b = {!!} -- Can't get it to proof v and v1 are equal
prepend-step (E-Snd-Extract x x₁) b = {!!} -- E-Snd b -- (same here)

-- Made some terms imlicit
small-to-big : {ty : Type} -> {t : Term ty} -> {v : Value ty} → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big {t = .true} {v = vtrue} Nil = E-True
small-to-big {t = .false} {v = vfalse} Nil = E-False
small-to-big {t = .zero} {v = vnat Zero} Nil = E-Zero
small-to-big {t = .(succ (natTerm x))} {v = vnat (Succ x)} Nil = E-Succ (value-to-value (vnat x))
small-to-big {t = .(⌜ x ⌝ ,  ⌜ y ⌝)} {v = vtup2 x y} Nil = E-Tup2 (value-to-value x) (value-to-value y)
small-to-big (Cons x s) = prepend-step x  (small-to-big s)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = E-True
⇓-complete false = E-False
⇓-complete (if c then t else e) with ⇓-complete c 
⇓-complete (if c then t else e) | x with ⟦ c ⟧ -- can't do at once on previous line sadly
⇓-complete (if c then t else e) | x | vtrue = E-If-True x (⇓-complete t)
⇓-complete (if c then t else e) | x | vfalse = E-If-False x (⇓-complete e)
⇓-complete zero = E-Zero
⇓-complete (succ t) with ⇓-complete t
⇓-complete (succ t) | x with ⟦ t ⟧
⇓-complete (succ t) | x | vnat _ = E-Succ x
⇓-complete (iszero t) with ⇓-complete t
⇓-complete (iszero t) | x with ⟦ t ⟧
⇓-complete (iszero t) | x | vnat Zero = E-IsZero-Zero x
⇓-complete (iszero t) | x | vnat (Succ _) = E-IsZero-Succ x
⇓-complete (x , y) with ⇓-complete x | ⇓-complete y
⇓-complete (x , y) | x₁ | y₁ = E-Tup2 x₁ y₁
⇓-complete (fst t) with ⇓-complete t
⇓-complete (fst t) | x with ⟦ t ⟧
⇓-complete (fst t) | x | vtup2 l _ = E-Fst x
⇓-complete (snd t) with ⇓-complete t
⇓-complete (snd t) | x with ⟦ t ⟧ 
⇓-complete (snd t) | x | vtup2 _ l = E-Snd x

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound true .vtrue E-True = refl
⇓-sound false .vfalse E-False = refl
⇓-sound (if c then t else e) v (E-If-True p p₁) with ⇓-sound c vtrue p           -- soundness of condition
⇓-sound (if c then t else e) v (E-If-True p p₁) | y with  ⟦ c ⟧ | ⇓-sound t v p₁ -- value of condition  soundness of t
⇓-sound (if c then t else e) .(⟦ t ⟧) (E-If-True p p₁) | refl | .vtrue | refl = refl
⇓-sound (if c then t else e) v (E-If-False p p₁) with ⇓-sound c vfalse p
⇓-sound (if c then t else e) v (E-If-False p p₁) | y with ⟦ c ⟧ | ⇓-sound e v p₁
⇓-sound (if c then t else e) .(⟦ e ⟧) (E-If-False p p₁) | refl | .vfalse | refl = refl
⇓-sound zero .(vnat Zero) E-Zero = refl
⇓-sound (succ t) ._ (E-Succ p) with ⇓-sound t _ p
⇓-sound (succ t) ._ (E-Succ p) | x with ⟦ t ⟧ 
⇓-sound (succ t) ._ (E-Succ p) | refl | ._ = refl
⇓-sound (iszero t) .vtrue (E-IsZero-Zero p) with ⇓-sound t _ p
⇓-sound (iszero t) .vtrue (E-IsZero-Zero p) | x with ⟦ t ⟧  
⇓-sound (iszero t) .vtrue (E-IsZero-Zero p) | refl | .(vnat Zero) = refl
⇓-sound (iszero t) .vfalse (E-IsZero-Succ p) with ⇓-sound t _ p 
⇓-sound (iszero t) .vfalse (E-IsZero-Succ p) | x with ⟦ t ⟧ 
⇓-sound (iszero t) .vfalse (E-IsZero-Succ p) | refl | ._ = refl
⇓-sound (a , b) ._ (E-Tup2 x y) with ⇓-sound a _ x | ⇓-sound b _ y
⇓-sound (a , b) ._ (E-Tup2 x y) | l | m with ⟦ a ⟧ | ⟦ b ⟧
⇓-sound (a , b) .(vtup2 q r) (E-Tup2 x y) | refl | refl | q | r = refl
⇓-sound (fst a) b (E-Fst x) with ⇓-sound a _ x
⇓-sound (fst a) b (E-Fst x) | l with ⟦ a ⟧
⇓-sound (fst a) b (E-Fst x) | refl | ._ = refl
⇓-sound (snd a) b (E-Snd x) with ⇓-sound a _ x
⇓-sound (snd a) b (E-Snd x) | l with ⟦ a ⟧
⇓-sound (snd a) b (E-Snd x) | refl | ._ = refl



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
