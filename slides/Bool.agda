
module Bool where

-------------------------------------------------------------------------------
----------------------                 Prelude             --------------------
-------------------------------------------------------------------------------
-- Equality.
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
  
-- Contradiction type.
data Empty : Set where

-- Reducto ab absurdum.
contradiction : {A : Set} → Empty → A
contradiction ()

-- Negation.
Not : Set → Set
Not A = A → Empty

-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

-- Grammar of terms.
data Term : Set where 
  true          : Term
  false         : Term
  if_then_else_ : (t₁ t₂ t₃ : Term) → Term

-- The set of atomic values within the language. In this case the booleans true and false.
data Value : Set where
  vtrue : Value
  vfalse : Value

-- Associate each value with a term.
⌜_⌝ : Value → Term
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false

-- Example term.
ex : Term
ex = if true then false else true

------------------------------------------------------------------------
-- Denotational semantics.

-- Evaluation of if-then-else expressions applied to values.
cond : Value → Value → Value → Value
cond vtrue v2 v3 = v2
cond vfalse v2 v3 = v3

-- Evaluation function.
⟦_⟧ : Term → Value
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧

-------------------------------------------------------------------------------
-- Small-step semantics.
--------------------------------------------------------------------------------

data Step : Term → Term → Set where
  E-If-True : forall {t1 t2} -> Step (if true then t1 else t2) t1
  E-If-False : forall {t1 t2} -> Step (if false then t1 else t2) t2
  E-If-If : forall {t1 t2 t3 t1'} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)


-- The previous example term evaluates to false.
exStep : Step ex false
exStep = E-If-True

-- Steps are deterministic: the same term can not be evaluated in more than one manner.
deterministic : ∀ {t t₁ t₂} → Step t t₁ → Step t t₂ → t₁ ≡ t₂
deterministic E-If-True E-If-True = refl
deterministic E-If-True (E-If-If ())
deterministic E-If-False E-If-False = refl
deterministic E-If-False (E-If-If ())
deterministic (E-If-If ()) E-If-True
deterministic (E-If-If ()) E-If-False
deterministic (E-If-If s1) (E-If-If s2) with deterministic s1 s2
deterministic (E-If-If s1) (E-If-If s2) | refl = refl

-- A term is reducible when some evaluation step can be applied to it.
data Red (t : Term) : Set where
  Reduces : {t' : Term} -> Step t t' -> Red t

-- A term is considered a normal form whenever it is not reducible.
NF : Term → Set
NF t = Red t -> Empty

-- Evidence type that shows a certain term represents a value.
data Is-value : Term → Set where
  is-value : ∀ v → Is-value ⌜ v ⌝

-- If-then-else terms are reducible.
if-reduces : ∀ t₁ t₂ t₃ → Red (if t₁ then t₂ else t₃)
if-reduces true t2 t3 = Reduces E-If-True
if-reduces false t2 t3 = Reduces E-If-False
if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)

-- A normal form must be a value.
normal-forms-are-values : ∀ t → NF t → Is-value t
normal-forms-are-values true nf = is-value vtrue
normal-forms-are-values false nf = is-value vfalse
normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))

anotherExample : Term
anotherExample = if ex then ex else ex

evalAnotherExample : Step anotherExample false
evalAnotherExample = {!!}

------------------------------------------------------------------------
-- Sequences of small steps.

-- A sequence of steps that can be applied in succession.
data Steps : Term → Term → Set where
  Nil : forall {t} -> Steps t t
  Cons : forall {t1 t2 t3} -> Step t1 t2 -> Steps t2 t3 -> Steps t1 t3

-- Single-step sequence.
[_] : ∀ {t₁ t₂} -> Step t₁ t₂ -> Steps t₁ t₂
[_] x = Cons x Nil
  
-- Concatenation.
_++_ : ∀ {t₁ t₂ t₃} → Steps t₁ t₂ → Steps t₂ t₃ → Steps t₁ t₃
Nil ++ stps' = stps'
Cons x stps ++ stps' = Cons x (stps ++ stps')

infixr 5 _++_

-- An extension of the E-If rule, for multiple steps.
E-If-Steps : ∀ {t₁ t₁′ t₂ t₃} →
        Steps t₁ t₁′ →
        Steps (if t₁ then t₂ else t₃) (if t₁′ then t₂ else t₃)
E-If-Steps Nil = Nil
E-If-Steps (Cons x steps) = Cons (E-If-If x) (E-If-Steps steps)

-- A term can not evaluate to more than one normal form.
uniqueness-of-normal-forms :
  ∀ {t t₁ t₂} →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ ≡ t₂
uniqueness-of-normal-forms s1 s2 nf1 nf2 = {!!}


-- Example: if ex then ex else ex evaluates to false.
exSteps : Steps (if ex then ex else ex) false
exSteps = Cons (E-If-If E-If-True) (Cons E-If-False (Cons E-If-True Nil))
            
------------------------------------------------------------------------
-- Expressing and proving termination.

-- The execution of a term terminates when there exists a step
-- sequence that evaluates this term to a value.
data _⇓ (t : Term) : Set where
  terminates : ∀ v → Steps t (⌜ v ⌝) → t ⇓

-- If t₁ evaluates to t₂, and t₂ terminates, then t₁ terminates as
-- well.
prepend-steps : ∀ {t₁ t₂} →  Steps t₁ t₂  → t₂ ⇓  → t₁ ⇓
prepend-steps steps (terminates v x₁) = terminates v (steps ++ x₁)

-- All steps terminate.
termination : ∀ t → t ⇓
termination true = terminates vtrue Nil
termination false = terminates vfalse Nil
termination (if t then t₁ else t₂) with termination t
termination (if t then t₁ else t₂) | terminates vtrue x with termination t₁
termination (if t then t₁ else t₂) | terminates vtrue steps1 | terminates v steps2 = 
  terminates v (E-If-Steps steps1 ++ Cons E-If-True steps2)
termination (if t then t₁ else t₂) | terminates vfalse x with termination t₂
termination (if t then t₁ else t₂) | terminates vfalse steps1 | terminates v steps2 = 
  terminates v (E-If-Steps steps1 ++ Cons E-If-False steps2)


------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b' denotes that a will evaluate to value b after a 
-- complete execution of the term.
data _⇓_ : Term → Value → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalIfTrue : forall {c t e v} -> c ⇓ vtrue -> t ⇓ v -> if c then t else e ⇓ v
  EvalIfFalse : forall {c t e v} -> c ⇓ vfalse -> e ⇓ v -> if c then t else e ⇓ v


-- Example: if ex then ex else ex evaluates to false (using big-step notation).
ex⇓ : if ex then ex else ex ⇓ vfalse
ex⇓ = EvalIfFalse (EvalIfTrue EvalTrue EvalFalse) (EvalIfTrue EvalTrue EvalFalse)

-- Converstion from big- to small-step representations.
big-to-small : ∀ {t v} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small (EvalIfTrue p p₁) = E-If-Steps (big-to-small p) ++ [ E-If-True ] ++ big-to-small p₁
big-to-small (EvalIfFalse p p₁) = E-If-Steps (big-to-small p) ++ [ E-If-False ] ++ big-to-small p₁


lemma : (v : Value) -> ⌜ v ⌝ ⇓ v
lemma vtrue = EvalTrue
lemma vfalse = EvalFalse

-- Conversion from small- to big-step representations.
small-to-big : (t : Term) -> (v : Value) → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big .(⌜ v ⌝) v Nil = lemma v
small-to-big ._ v (Cons E-If-True p) = EvalIfTrue EvalTrue (small-to-big _ _ p)
small-to-big ._ v (Cons E-If-False p) = EvalIfFalse EvalFalse (small-to-big _ _ p)
small-to-big ._ v (Cons (E-If-If x) p) = {!!}

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics


-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ t → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t₁ else t₂) with ⇓-complete t
⇓-complete (if .true then t₁ else t₂) | EvalTrue = EvalIfTrue EvalTrue {!!}
⇓-complete (if .false then t₁ else t₂) | EvalFalse = {!!}
⇓-complete (if ._ then t₁ else t₂) | EvalIfTrue p p₁ = {!!}
⇓-complete (if ._ then t₁ else t₂) | EvalIfFalse p p₁ = {!!}

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ t v → t ⇓ v → v ≡ ⟦ t ⟧
⇓-sound .true .vtrue EvalTrue = refl
⇓-sound .false .vfalse EvalFalse = refl
⇓-sound ._ v (EvalIfTrue p p₁) = {!!}
⇓-sound ._ v (EvalIfFalse p p₁) = {!!}
