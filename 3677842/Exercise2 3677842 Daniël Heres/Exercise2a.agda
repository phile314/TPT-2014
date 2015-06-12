
module Exercise2a where

--------------------------------------------------------------------------------

-- Daniel Heres 3677842
--Instructions--
{-
Fill in the holes below

Extend the language with tuples, fst, and snd

Complete the proofs again

You may want to check Chapter ₁₁.7 of Pierce's book to see how he defines
the syntax, semantics and Types for tuples.

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
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : {a b : Set} {x y : a} (f : a → b) → x ≡ y → f x ≡ f y
cong f refl = refl

-- Contradiction Type.
data Ø : Set where

-- Reducto ab absurdum.
contradiction : {A : Set} → Ø → A
contradiction ()

-- Negation
Not : Set → Set
Not A = A → Ø

data Nat : Set where
  Zero : Nat
  Succ : Nat → Nat

data Either (a b : Set) : Set where
  Left : a → Either a b
  Right : b → Either a b

-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

data Type : Set where
  NAT : Type
  BOOL : Type
  -- Product Type
  _×_ : Type → Type → Type

-- Our Term language
data Term : Type → Set where
  false         : Term BOOL
  true          : Term BOOL
  if_then_else_ : {τ : Type} → (c : Term BOOL) → (t e : Term τ) → Term τ

  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) → Term NAT
  iszero        : (n : Term NAT) → Term BOOL

  _,_ : ∀ {τ₁ τ₂} → Term τ₁ → Term τ₂ → Term (τ₁ × τ₂)
  fst : ∀ {τ₁ τ₂} → Term (τ₁ × τ₂) → Term τ₁
  snd : ∀ {τ₁ τ₂} → Term (τ₁ × τ₂) → Term τ₂

-- The set of atomic values within the language.
data Value : Type → Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat → Value NAT
  vpair  : ∀ {τ₁ τ₂} → Value τ₁ → Value τ₂ → Value (τ₁ × τ₂)
natTerm : Nat → Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : ∀ {τ} → Value τ → Term τ
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
⌜ vpair a b ⌝ = ⌜ a ⌝ , ⌜ b ⌝

-- Example term.
ex : Term NAT → Term BOOL
ex t = if iszero t then false else true

------------------------------------------------------------------------
-- Denotational semantics.
--------------------------------------------------------------------------------

-- Evaluation of if-then-else expressions applied to values.
cond : ∀ {τ} → Value BOOL → Value τ → Value τ → Value τ
cond vtrue v₂ v3 = v₂
cond vfalse v₂ v3 = v3

vsucc : Value NAT → Value NAT
vsucc (vnat x) = vnat (Succ x)

viszero : Value NAT → Value BOOL
viszero (vnat Zero) = vtrue
viszero (vnat (Succ x)) = vfalse

-- Evaluation function.
⟦_⟧ : ∀ {τ} → Term τ  → Value τ
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧

⟦ ( a , b)  ⟧ = vpair ⟦ a ⟧  ⟦ b ⟧

⟦ fst a ⟧ with ⟦ a ⟧
⟦ fst  a ⟧ | vpair x _ = x

⟦ snd a ⟧ with ⟦ a ⟧
⟦ snd  a ⟧ | vpair _ y = y


-- What can we do to define a denotational semantics?
--   Add Types!

-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

-- Evidence Type that shows a certain term represents a value.
data Is-value {τ : Type} : Term τ → Set where
  is-value : ∀ v → Is-value ⌜ v ⌝
data Step  : {τ : Type} → Term τ → Term τ → Set where
  E-If-True : ∀  {τ} {t₁ t₂ : Term τ} → Step (if true then t₁ else t₂) t₁
  E-If-False : ∀ {τ} {t₁ t₂ : Term τ} → Step (if false then t₁ else t₂) t₂
  E-If-If : ∀ {τ} {t₁ t₁' : Term BOOL} {t₂ t3 : Term τ} → Step t₁ t₁' →
    Step (if t₁ then t₂ else t3) (if t₁' then t₂ else t3)
  E-Succ       : ∀ {t t' : Term NAT} → Step {NAT} t t' → Step {NAT} (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) (true)
  E-IsZeroSucc : {v : Value NAT} → Step (iszero (succ ⌜ v ⌝)) false
  E-IsZero     : ∀ {t t' : Term NAT} → Step t t' → Step (iszero t) (iszero t')

  E-Pair₁ : ∀ {τ τ₂} {t₁ t₁' : Term τ} → {t₂ : Term τ₂} → Step t₁ t₁' → Step (t₁ , t₂) (t₁' , t₂)
  E-Pair₂ : ∀ {τ τ₂} {t₁ : Term τ} {t₂ t₂' : Term τ₂} {v₁ : Value τ} → t₁ ≡ ⌜ v₁ ⌝ → Step t₂ t₂' → Step (t₁ , t₂) (t₁ , t₂')

  E-PairBeta₁ : ∀ {τ τ₂} {t₁ : Term τ} {v₁ : Value τ} {t₂ : Term τ₂} {v₂ : Value τ₂} → t₁ ≡ ⌜ v₁ ⌝ → t₂  ≡ ⌜ v₂ ⌝ → Step (fst (t₁ , t₂)) t₁
  E-PairBeta₂ : ∀ {τ τ₂} {t₁ : Term τ} {t₂ : Term τ₂} {v₁ : Value τ} {v₂ : Value τ₂} → t₁ ≡ ⌜ v₁ ⌝ → t₂  ≡ ⌜ v₂ ⌝ → Step (snd (t₁ , t₂)) t₂

  E-Proj₁ :  ∀ {τ τ₂} {t₁ t₁' : Term (τ × τ₂)} → Step t₁ t₁' → Step (fst t₁) (fst t₁')
  E-Proj₂ :  ∀ {τ τ₂} {t₁ t₁' : Term (τ × τ₂)} → Step t₁ t₁' → Step (snd t₁) (snd t₁')

valuesDoNotStep : ∀ {τ} → (v : Value τ) (t : Term τ) →  Step (⌜ v ⌝) t → Ø
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) → (t : Term NAT) → Step (natTerm n) t → Ø
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep (vpair a b) ._ (E-Pair₁ x) = valuesDoNotStep a _ x
valuesDoNotStep (vpair a b) ._ (E-Pair₂ x y) = valuesDoNotStep b _ y

-- Steps are deterministic: the same term can not be evaluated in more than one manner.


toVal : ∀ {τ} → {t : Term τ} → Is-value t → Value τ
toVal {_} (is-value v) = v
deterministic : ∀ {τ} {t t₁ t₂ : Term τ} → Step t t₁ → Step t t₂ → t₁ ≡ t₂
deterministic E-If-True E-If-True = refl
deterministic E-If-True (E-If-If ())
deterministic E-If-False E-If-False = refl
deterministic E-If-False (E-If-If ())
deterministic (E-If-If ()) E-If-True
deterministic (E-If-If ()) E-If-False
deterministic (E-If-If steps₁) (E-If-If steps₂) = cong (\b → if b then _ else _) (deterministic steps₁ steps₂)
deterministic (E-Succ steps₁) (E-Succ steps₂) = cong succ (deterministic steps₁ steps₂)
deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps₁)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ steps₁)
deterministic (E-IsZero steps₁) (E-IsZero steps₂) = cong iszero (deterministic steps₁ steps₂)
deterministic (E-IsZeroSucc {v}) steps₂ = lemma v _ steps₂
  where
  lemma : (v : Value NAT) (t : Term BOOL) → Step (iszero (succ ⌜ v ⌝)) t → false ≡ t
  lemma (vnat x) false s = refl
  lemma (vnat x) true ()
  lemma (vnat x) (if t then t₁ else t₂) ()
  lemma (vnat x) (iszero ._) (E-IsZero (E-Succ s)) = contradiction (valuesDoNotStep (vnat x) _ s)
  lemma (vnat x) (fst t) ()
  lemma (vnat x) (snd t) ()
deterministic (E-PairBeta₁ a b) (E-PairBeta₁ x y) = refl
deterministic (E-PairBeta₂ x y) (E-PairBeta₂ a b) = refl
deterministic (E-Pair₁ x) (E-Pair₁ x₁) = cong (λ z → z , _) (deterministic x x₁)
deterministic (E-Proj₂ x) (E-Proj₂ y) = cong snd (deterministic x y)
deterministic (E-Pair₁ x) (E-Pair₂ y z) = contradiction {!!}
deterministic (E-Pair₂ x x2) (E-Pair₁ y) = contradiction {!!}
deterministic (E-Pair₂ x x2) (E-Pair₂ y y2) = cong (_,_ _) (deterministic x2 y2)
deterministic (E-Proj₁ x) (E-Proj₁ y) = cong fst (deterministic x y)
deterministic (E-PairBeta₁ x y) (E-Proj₁ z) = contradiction {!!}
deterministic (E-PairBeta₂ a b) (E-Proj₂ y) = contradiction {!!}
deterministic (E-Proj₁ x) (E-PairBeta₁ y z) = contradiction {!!}
deterministic (E-Proj₂ x) (E-PairBeta₂ a b) = contradiction {!!}

-- So we can add *Types* to our term language.
--
-- But when is a Type system 'good'?
-- What would we like to prove about the relation between our semantics and well-Typed terms?

--------------------------------------------------------------------------------
-- Type safety (sometimes called Type soundness)
--
--  * progress -- a well-Typed term is a value or is reducible --
--    'well-Typed terms are never stuck'
--
--  * preservation -- if a well-Typed term performs an evaluation
--    step, the result is still well-Typed
--
-- Together these two properties guarantee that 'well-Typed programs
-- don't go wrong'
--------------------------------------------------------------------------------

preservation : ∀ {τ : Type} → (t₁ t₂ : Term τ) → Step t₁ t₂ → τ ≡ τ
preservation t₁ t₂ step = refl

-- A term is reducible when some evaluation step can be applied to it.
data Red {τ : Type} (t : Term τ) : Set where
  Reduces : {t' : Term τ} → Step t t' → Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {τ} → Term τ → Set
NF t = Red t → Ø


mutual
  -- If-then-else terms are reducible.
  if-reduces : ∀ {τ} (T₁ : Term BOOL) (T₂ : Term τ) (T₃ : Term τ) → Red (if T₁ then T₂ else T₃)
  if-reduces true t₂ t3 = Reduces E-If-True
  if-reduces false t₂ t3 = Reduces E-If-False
  if-reduces (if t₁ then t₂ else t3) t4 t5 with if-reduces t₁ t₂ t3
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (fst a) t₁ t₂ with fst-reduces a
  if-reduces (fst a) t₁ t₂ | Reduces v = Reduces (E-If-If v)
  if-reduces (snd a) t₁ t₂ with snd-reduces a
  if-reduces (snd a) t₁ t₂ | Reduces v = Reduces (E-If-If v)
  if-reduces (iszero t) t4 t5 with iszero-reduces t
  if-reduces (iszero t) t4 t5 | Reduces x = Reduces (E-If-If x)

  fst-reduces : {τ₁ τ₂ : Type} → (T : Term (τ₁ × τ₂)) → Red (fst T)
  fst-reduces (if x then x₁ else x₂) with if-reduces x x₁ x₂
  fst-reduces (if x then x₁ else x₂) | Reduces v = Reduces (E-Proj₁ v)
  fst-reduces (x , x₁) with pair-reduces x x₁
  fst-reduces (x , x₁) | Reduces x₂ = Reduces (E-Proj₁ x₂)
  fst-reduces (fst x) with fst-reduces x
  fst-reduces (fst x) | Reduces v = Reduces (E-Proj₁ v)
  fst-reduces (snd x) with snd-reduces x
  fst-reduces (snd x) | Reduces v = Reduces (E-Proj₁ v)


  pair-reduces : {τ τ₂ : Type} → (T : Term τ) → (T₂ : Term τ₂) → Red (T , T₂)
  pair-reduces true t = Reduces {!!}
  pair-reduces false t = {!!}
  pair-reduces (if s then s₁ else s₂) t with if-reduces s s₁ s₂
  pair-reduces (if s then s₁ else s₂) t | Reduces x = Reduces (E-Pair₁ x)
  pair-reduces zero t with progress t
  pair-reduces zero t | Left x = {!  !}
  pair-reduces zero t | Right (Reduces x) = Reduces (E-Pair₂ refl x)
  pair-reduces (succ s) t with progress s
  pair-reduces (succ s) t | Left x = {! !}
  pair-reduces (succ s) t | Right (Reduces x) = Reduces (E-Pair₁ (E-Succ x))
  pair-reduces (iszero s) t with iszero-reduces s
  pair-reduces (iszero s) t | Reduces x = Reduces (E-Pair₁ x)
  pair-reduces (s , s₁) t with pair-reduces s s₁
  pair-reduces (s , s₁) t | Reduces x = Reduces (E-Pair₁ x)
  pair-reduces (fst s) t with fst-reduces s
  pair-reduces (fst s) t | Reduces x = Reduces (E-Pair₁ x)
  pair-reduces (snd s) t with snd-reduces s
  pair-reduces (snd s) t | Reduces x = Reduces (E-Pair₁ x)

  snd-reduces : {τ₁ τ₂ : Type} → (te : Term (τ₁ × τ₂)) → Red (snd te)
  snd-reduces (if x then x₁ else x₂) with if-reduces x x₁ x₂
  snd-reduces (if x then x₁ else x₂) | Reduces v = Reduces (E-Proj₂ v)
  snd-reduces (x , x₁) with pair-reduces x x₁
  snd-reduces (s , s₁) | Reduces x = Reduces (E-Proj₂ x)
  snd-reduces (fst x) with fst-reduces x
  snd-reduces (fst x) | Reduces v = Reduces (E-Proj₂ v)
  snd-reduces (snd x) with snd-reduces x
  snd-reduces (snd x) | Reduces v = Reduces (E-Proj₂ v)

  iszero-reduces : (t : Term NAT) → Red (iszero t)
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (fst a) with fst-reduces a
  iszero-reduces (fst a) | Reduces v =  Reduces (E-IsZero v)
  iszero-reduces (snd a) with snd-reduces a
  iszero-reduces (snd a) | Reduces v = Reduces (E-IsZero v)
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))

  succ-nf : (k : Term NAT) → NF (succ k) → NF k
  succ-nf (if t₁ then t₂ else t3) nf x with if-reduces t₁ t₂ t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (fst a) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (snd a) nf (Reduces x) = nf (Reduces (E-Succ x))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {τ} (t : Term τ) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (a , b) nf = contradiction (nf (pair-reduces a b))
  normal-forms-are-values (fst a) nf = contradiction (nf (fst-reduces a))
  normal-forms-are-values (snd a) nf = contradiction (nf (snd-reduces a))

  values-are-normal-forms : ∀ {τ} (t : Term τ) → Is-value t → NF t
  values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

  lemma : (t : Term NAT) → (Red t → Ø) → Red (succ t) → Ø
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  progress : {τ : Type} → (t : Term τ) → Either (NF t) (Red t)
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
  progress (a , b) = Right (pair-reduces a b)
  progress (fst t) = Right (fst-reduces t)
  progress (snd t) = Right (snd-reduces t)


--------------------------------------------------------------------------------
-- Sequences of small steps.
--------------------------------------------------------------------------------

-- A sequence of steps that can be applied in succession.
data Steps {τ : Type} : Term τ → Term τ → Set where
  Nil : ∀ {t} → Steps t t
  Cons : ∀ {t₁ t₂ t3} → Step t₁ t₂ → Steps t₂ t3 → Steps t₁ t3

-- Single-step sequence.
[_] : ∀ {τ} {t₁ t₂ : Term τ} → Step t₁ t₂ → Steps t₁ t₂
[_] x = Cons x Nil

-- Concatenation.
_++_ : ∀ {τ} {t₁ t₂ t₃ : Term τ} → Steps t₁ t₂ → Steps t₂ t₃ → Steps t₁ t₃
Nil ++ stps' = stps'
Cons x stps ++ stps' = Cons x (stps ++ stps')

infixr 5 _++_

uniqueness-of-normal-forms :
  ∀ {τ} {t t₁ t₂ : Term τ} →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ ≡ t₂
uniqueness-of-normal-forms Nil Nil nf₁ nf₂ = refl
uniqueness-of-normal-forms Nil (Cons x s₂) nf₁ nf₂ = contradiction (nf₁ (Reduces x))
uniqueness-of-normal-forms (Cons x s₁) Nil nf₁ nf₂ = contradiction (nf₂ (Reduces x))
uniqueness-of-normal-forms (Cons x xs) (Cons y ys) nf₁ nf₂ with deterministic x y
uniqueness-of-normal-forms (Cons x xs) (Cons y ys) nf₁ nf₂ | refl = uniqueness-of-normal-forms xs ys nf₁ nf₂

------------------------------------------------------------------------
-- Expressing and proving termination.

-- The execution of a term terminates when there exists a step
-- sequence that evaluates this term to a value.
data _⇓ {τ : Type} (t : Term τ) : Set where
  terminates : ∀ v → Steps t (⌜ v ⌝) → t ⇓

-- If t₁ evaluates to t₂, and t₂ terminates, then t₁ terminates as
-- well.
prepend-steps : ∀ {τ} {t₁ t₂ : Term τ} →  Steps t₁ t₂  → t₂ ⇓  → t₁ ⇓
prepend-steps steps (terminates v x₁) = terminates v (steps ++ x₁)

E-If-Steps : ∀ {τ} {t t'} {t₁ t₂ : Term τ} →
        Steps t t' →
        Steps (if t then t₁ else t₂) (if t' then t₁ else t₂)
E-If-Steps Nil = Nil
E-If-Steps (Cons x steps) = Cons (E-If-If x) (E-If-Steps steps)

E-Succ-Steps : ∀ {t t' : Term NAT} →
        Steps t t' →
        Steps (succ t) (succ t')
E-Succ-Steps Nil = Nil
E-Succ-Steps (Cons x steps) = Cons (E-Succ x) (E-Succ-Steps steps)

E-IsZero-Steps : ∀ {t t' : Term NAT} →
        Steps t t' →
        Steps (iszero t) (iszero t')
E-IsZero-Steps Nil = Nil
E-IsZero-Steps (Cons x steps) = Cons (E-IsZero x) (E-IsZero-Steps steps)

E-Fst-Steps : ∀ {t τ} → {t₁ t₂ : Term (t × τ)} → Steps t₁ t₂ → Steps (fst t₁) (fst t₂)
E-Fst-Steps Nil = Nil
E-Fst-Steps (Cons x x₁) = Cons (E-Proj₁ x) (E-Fst-Steps x₁)

terminate-pair : ∀ {τ τ₂} (s : Term τ) (t : Term τ₂) → s ⇓ → t ⇓ → (s , t) ⇓
terminate-pair s t (terminates v x) (terminates v₁ x₁) = terminates (vpair v v₁){!    !}
-- All steps terminate.
termination : ∀ {τ} (t : Term τ) → t ⇓
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
termination (a , b) = terminate-pair a b (termination a) (termination b)
termination (iszero (fst x)) with termination x
termination (iszero (fst x)) | terminates v x₁ = terminates vtrue {!    !}
termination (iszero (snd x)) with termination x
termination (iszero (snd x)) | terminates v x₁ = {!    !}
termination (fst a) with termination a
termination (fst a) | terminates v x = terminates {!    !} (E-Fst-Steps x ++ {! [E-Fst ]   !} )
termination (snd a) with termination a
termination (snd a) | terminates v x = terminates {!    !} {!    !}
------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {τ : Type} → Term τ → Value τ → Set where
  ⇓-True : true ⇓ vtrue
  ⇓-False : false ⇓ vfalse

  ⇓-If-True :  {τ : Type} {tb : Term BOOL} {t₁ t₂ : Term τ} {v : Value τ} → tb ⇓ vtrue  → t₁ ⇓ v → if tb then t₁ else t₂ ⇓ v
  ⇓-If-False : {τ : Type} {tb : Term BOOL} {t₁ t₂ : Term τ} {v : Value τ} → tb ⇓ vfalse → t₂ ⇓ v → if tb then t₁ else t₂ ⇓ v

  ⇓-Zero : zero ⇓ vnat Zero
  ⇓-Succ : {t : Term NAT} {v : Nat} → t ⇓ vnat v → succ t ⇓ vsucc (vnat v)
  ⇓-IsZero : {t : Term NAT} {v : Value NAT} → t ⇓ v → iszero t ⇓ viszero v
  ⇓-IsZeroSucc : {t : Term NAT} {v : Nat} → t ⇓ vnat v → iszero (succ t) ⇓ vfalse

  ⇓-Pair : {τ τ₂ : Type} {t₁ : Term τ} {t₂ : Term τ₂} {v₁ : Value τ} {v₂ : Value τ₂} → t₁ ⇓ v₁ → t₂ ⇓ v₂ → (t₁ , t₂) ⇓ (vpair v₁ v₂)
  ⇓-Proj₁ : {τ τ₂ : Type} {t₁ : Term τ} {t₂ : Term τ₂} {v : Value τ} → t₁ ⇓ v → fst (t₁ , t₂) ⇓ v
  ⇓-Proj₂ : {τ τ₂ : Type} {t₁ : Term τ} {t₂ : Term τ₂} {v : Value τ₂} → t₂ ⇓ v → snd (t₁ , t₂) ⇓ v


big-to-small : ∀ {τ} {t : Term τ} {v : Value τ} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small ⇓-True = Nil
big-to-small ⇓-False = Nil
big-to-small ⇓-Zero = Nil
big-to-small (⇓-If-True x x₁) = E-If-Steps (big-to-small x) ++ Cons E-If-True (big-to-small x₁)
big-to-small (⇓-If-False x x₁) = E-If-Steps (big-to-small x) ++ Cons E-If-False (big-to-small x₁)
big-to-small (⇓-IsZero x) = {!    !}
big-to-small (⇓-Proj₁ x) = Cons {!E-PairBeta₁!} (big-to-small x) -- Cons E-PairBeta₁ (big-to-small x)
big-to-small (⇓-Proj₂ {v} {w} x) = {!!} -- Cons (E-PairBeta₂) (big-to-small x)
big-to-small (⇓-Succ a) = E-Succ-Steps (big-to-small a)
big-to-small (⇓-Pair a b) = {!    !}
big-to-small (⇓-IsZeroSucc x) = {! E-ZeroSucc-Steps (big-to-small x)   !}

-- Conversion from small- to big-step representations.
value-to-value : ∀ {τ} (v : Value τ) → ⌜ v ⌝ ⇓ v
value-to-value vtrue = ⇓-True
value-to-value vfalse = ⇓-False
value-to-value (vnat x) with ⟦ natTerm x ⟧
value-to-value (vnat Zero) | y = ⇓-Zero
value-to-value (vnat (Succ x)) | y = ⇓-Succ (value-to-value (vnat x))
value-to-value (vpair _ _) = ⇓-Pair (value-to-value _) (value-to-value _)

prepend-step : ∀ {τ} {t t' : Term τ} {v : Value τ} → Step t t' → t' ⇓ v → t ⇓ v
prepend-step E-If-True x = ⇓-If-True ⇓-True x
prepend-step E-If-False x = ⇓-If-False ⇓-False x
prepend-step (E-If-If x) (⇓-If-True x₁ x₂) = ⇓-If-True (prepend-step x x₁) x₂
prepend-step (E-If-If x) (⇓-If-False x₁ x₂) = ⇓-If-False (prepend-step x x₁) x₂
prepend-step (E-Succ x) (⇓-Succ x₁) = ⇓-Succ (prepend-step x x₁)
prepend-step E-IsZeroZero ⇓-True = ⇓-IsZero ⇓-Zero
prepend-step {v = vtrue} E-IsZeroSucc ()
prepend-step {v = vfalse} E-IsZeroSucc ⇓-False = {!!} --⇓-IsZeroSucc ⇓-Zero
prepend-step (E-IsZero x) (⇓-IsZero y) = ⇓-IsZero (prepend-step x y)
prepend-step (E-Pair₁ x) (⇓-Pair x₁ x₂) = ⇓-Pair (prepend-step x x₁) x₂
prepend-step (E-Pair₂ x y) (⇓-Pair x₂ x₃) = ⇓-Pair x₂ (prepend-step y x₃)
prepend-step (E-PairBeta₁ a b) y = ⇓-Proj₁ y
prepend-step (E-PairBeta₂ a b) y = ⇓-Proj₂ y
prepend-step (E-IsZero x) (⇓-IsZeroSucc y) = ⇓-IsZero (prepend-step x (⇓-Succ y))
prepend-step (E-Proj₁ x) (⇓-Proj₁ y) = {! ?!}
prepend-step (E-Proj₂ x) (⇓-Proj₂ y) = {!!}
small-to-big : {τ : Type} → {t : Term τ} {v : Value τ} → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big Nil = value-to-value _
small-to-big (Cons x xs) = prepend-step x (small-to-big xs)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {τ} (t : Term τ) → t ⇓ ⟦ t ⟧
⇓-complete true = ⇓-True
⇓-complete false = ⇓-False
⇓-complete (if t then t₁ else t₂) with ⇓-complete t
...| c with ⟦ t ⟧
⇓-complete (if t then t₁ else t₂) | c | vtrue = ⇓-If-True c (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | c | vfalse = ⇓-If-False c (⇓-complete t₂)
⇓-complete zero = ⇓-Zero
⇓-complete (succ t) with ⇓-complete t
...| c with ⟦ t ⟧
⇓-complete (succ x) | c | vnat x₁ = ⇓-Succ c
⇓-complete (iszero x) with ⇓-complete x
...| c with ⟦ x ⟧
⇓-complete (iszero x) | c | vzero = ⇓-IsZero c
⇓-complete (_,_ _ _) = ⇓-Pair (⇓-complete _) (⇓-complete _)
⇓-complete (fst a) = {!!} (⇓-complete a)
⇓-complete (snd a) = {!!} (⇓-complete a)


-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {τ} (t : Term τ) (v : Value τ) → t ⇓ v → v ≡ ⟦ t ⟧
⇓-sound true vtrue ⇓-True = refl
⇓-sound true vfalse ()
⇓-sound false vtrue ()
⇓-sound false vfalse x = refl
⇓-sound (if t then t₁ else t₂) v (⇓-If-True x x₁) with  ⟦ t ⟧ | ⇓-sound _ _ x
⇓-sound (if t then t₁ else t₂) v  (⇓-If-True x y) | vfalse | ()
⇓-sound (if t then t₁ else t₂) v  (⇓-If-True a b) | vtrue  | x = ⇓-sound _ _ b
⇓-sound (if t then t₁ else t₂) v (⇓-If-False x x₁) with  ⟦ t ⟧ | ⇓-sound _ _ x
⇓-sound (if t then t₁ else t₂) v  (⇓-If-False x y) | vtrue | ()
⇓-sound (if t then t₁ else t₂) v  (⇓-If-False a b) | vfalse  | x = ⇓-sound _ _ b
⇓-sound zero (vnat .Zero) ⇓-Zero = refl
⇓-sound (succ t) (vnat ._) (⇓-Succ y) = {!!}
⇓-sound (iszero v) vtrue x with ⟦ v ⟧
⇓-sound (iszero t) vtrue x₁ | vnat x = {! !}
⇓-sound (iszero t) vfalse x with ⟦ t ⟧
⇓-sound (iszero t) vfalse x₁ | vnat x = {!!}

⇓-sound (fst ._) v (⇓-Proj₁ x) = ⇓-sound _ v x
⇓-sound (snd ._) v (⇓-Proj₂ x) = ⇓-sound _ v x
⇓-sound (t , t₁) (vpair v v₁) (⇓-Pair x x₁) = {!!}

-- Retrospective
-- × Three sτles of semantics: denotational, small step and big step
-- × All three can be shown to be equivalent
-- × To avoid handling 'stuck' terms, we introduced a τping discipline
-- × And proved Type soundness -- 'well-Typed terms can't go wrong'
--
--   (the proof was easy using Agda - because we only considered well-Typed
--   terms to begin with; usually we would need to do induction over the τping
--   derivation)
--
-- × All proofs are by easy induction -- finding the right definitions is hard!
