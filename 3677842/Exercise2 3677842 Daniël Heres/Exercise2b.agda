
module Exercise2b where

--------------------------------------------------------------------------------
-- Instructions
{-
Complete the holes in the proof below

The trick is to choose the right argument on which to do induction.
You may want to consult Pierce's book (Chapter 12) or the Coquand note
on the website.
-}
--------------------------------------------------------------------------------

------------------------------------------------------------------------
-- Prelude.
--------------------------------------------------------------------------------

-- Equality, and laws.
data _≡_ {a : Set} (x : a) : a → Set where
 Refl : x ≡ x

cong : ∀ {a b x y} → (f : a → b) → x ≡ y → f x ≡ f y
cong f Refl = Refl

symmetry : {a : Set} → {x y : a} → x ≡ y → y ≡ x
symmetry Refl = Refl

transitivity : {a : Set} → {x y z : a} → x ≡ y → y ≡ z → x ≡ z
transitivity Refl Refl = Refl

-- Lists.
data List (a : Set) : Set where
 []   : List a
 _::_ : a → List a → List a

-- Pairs.
data Pair (a b : Set) : Set where
  _,_ : a → b → Pair a b

fst : ∀ {a b} → Pair a b → a
fst (x , _) = x

snd : ∀ {a b} → Pair a b → b
snd (_ , x) = x

-- Unit type.
data Unit : Set where
 U : Unit

-- The empty type and negation.
data Absurd : Set where

Not : Set → Set
Not x = x → Absurd

contradiction : {a : Set} → Absurd → a
contradiction ()

------------------------------------------------------------------------
-- Types and terms.
--------------------------------------------------------------------------------

-- Unit and function types are supported.
data Type : Set where
 O    : Type
 _=>_ : Type → Type → Type

el : Type → Set
el O = Unit
el (s => t) = el s → el t

-- Type context: the top of this list is the type of the innermost
-- abstraction variable, the next element is the type of the next
-- variable, and so on.
Context : Set
Context = List Type

-- Reference to a variable, bound during some abstraction.
data Ref : Context → Type → Set where
 Top : ∀ {G u} → Ref (u :: G) u
 Pop : ∀ {G u v} → Ref G u → Ref (v :: G) u



-- A term in the lambda calculus. The language solely consists of
-- abstractions, applications and variable references.
mutual
  data Term : Context → Type → Set where
   Abs : ∀ {G u v} → (body : Term (u :: G) v) → Term G (u => v)
   App : ∀ {G u v} → (f : Term G (u => v)) → (x : Term G u) → Term G v
   Var : ∀ {G u} → Ref G u → Term G u


  data Env : List Type → Set where
    Nil  : Env []
    Cons : ∀ {ctx τ} → Closed τ → Env ctx → Env (τ :: ctx)

  data Closed : Type → Set where
    Closure : ∀ {ctx τ} → (t : Term ctx τ) → (env : Env ctx) → Closed τ
    Clapp : ∀ {τ τ'} → (f : Closed (τ => τ')) (x : Closed τ) →
               Closed τ'


IsValue : ∀ {τ} → Closed τ → Set
IsValue (Closure (Abs t) env) = Unit
IsValue (Closure (App t t₁) env) = Absurd
IsValue (Closure (Var x) env) = Absurd
IsValue (Clapp t t₁) = Absurd

------------------------------------------------------------------------
-- Step-by-step evaluation of terms.

lookup : ∀ {ctx τ} → Ref ctx τ → Env ctx → Closed τ
lookup Top (Cons x env) = x
lookup (Pop i) (Cons x env) = lookup i env

data Step : ∀ {τ} → Closed τ → Closed τ → Set where
  AppL : {τ τ' : Type} (f f' : Closed (τ => τ')) (x : Closed τ) →
    Step f f' → Step (Clapp f x) (Clapp f' x)
  Beta : {τ τ' : Type} {ctx : Context} (body : Term (τ :: ctx) τ') (v : Closed τ)
    {env : Env ctx} →
    Step (Clapp (Closure (Abs body) env) v) (Closure body (Cons v env))
  Lookup : {ctx : List Type} {τ : Type} {i : Ref ctx τ} {env : Env ctx} →
          Step (Closure (Var i) env) (lookup i env)
  Dist : {τ τ' : Type} {ctx : List Type} {env : Env ctx} {f : Term ctx (τ => τ')} {x : Term ctx τ} →
         Step (Closure (App f x) env) (Clapp (Closure f env) (Closure x env))


-- Reducibility.
data Reducible : ∀ {τ} → Closed τ → Set where
 Red : ∀ {τ} → {c1 c2 : Closed τ} → Step c1 c2 → Reducible c1

-- Non-reducable terms are considered normal forms.
NF : ∀ {τ} → Closed τ → Set
NF c = Not (Reducible c)

-- A sequence of steps that can be applied in succession.
data Steps : ∀ {τ} → Closed τ → Closed τ → Set where
 Nil  : ∀ {τ} → {c : Closed τ} → Steps c c
 Cons : ∀ {τ} → {c1 c2 c3 : Closed τ} → Step c1 c2 → Steps c2 c3 → Steps c1 c3

--------------------------------------------------------------------------------
-- Termination
--------------------------------------------------------------------------------

-- Definition of termination: a sequence of steps exist that ends up in a normal form.
data Terminates : ∀ {τ} → Closed τ → Set where
  Halts : ∀ {τ} → {c nf : Closed τ} → NF nf → Steps c nf → Terminates c

Normalizable : (τ : Type) → Closed τ → Set
Normalizable O c = Terminates c
Normalizable (τ => τ₁) f =
  Pair (Terminates f)
       ((x : Closed τ) → Normalizable τ x → Normalizable τ₁ (Clapp f x))

-- Structure that maintains normalization proofs for all elements in the environment.
NormalizableEnv : ∀ {ctx} → Env ctx → Set
NormalizableEnv Nil = Unit
NormalizableEnv (Cons {ctx} {τ} x env) = Pair (Normalizable τ x) (NormalizableEnv env)

-- Normalization implies termination.
normalizable-terminates : ∀ {τ c} → Normalizable τ c → Terminates c
normalizable-terminates {O} (Halts x x₁) = Halts x x₁
normalizable-terminates {τ => τ₁} (x , x₁) = x

-- Helper lemma's for normalization proof.
normalizableStep : ∀ {τ} → {c1 c2 : Closed τ} → Step c1 c2 →
   Normalizable τ c2 → Normalizable τ c1
normalizableStep {O} s (Halts x x₁) = Halts x (Cons s x₁)
normalizableStep {τ => τ₁} s (Halts x x₁ , x₂) = (Halts x (Cons s x₁), (\a b → normalizableStep (AppL _ _ a s) (x₂ a b) ))

normalizableSteps : ∀ {τ} → {c1 c2 : Closed τ} → Steps c1 c2 → Normalizable τ c2 → Normalizable τ c1
normalizableSteps Nil n = n
normalizableSteps (Cons x steps) n = normalizableStep x (normalizableSteps steps n)

-- The following three lemmas may use mutual recursion. This is done
-- in Agda by separating the type signature and the function
-- definition.

-- Closed applications of the form 'f x' are normalizable when both f and x are normalizable.
clapp-normalization : ∀ {A B} → {c1 : Closed (A => B)} → {c2 : Closed A} →
                       Normalizable (A => B) c1  → Normalizable A c2 → Normalizable B (Clapp c1 c2)
clapp-normalization (x , x₁) x₂ = x₁ _ x₂

-- Lookups are normalizable
lookup-normalization : ∀ {ctx} {τ : Type} (env : Env ctx) (r : Ref ctx τ) → NormalizableEnv env → Normalizable τ (lookup r env)
lookup-normalization (Cons x env) Top (x₁ , x₂) = x₁
lookup-normalization (Cons x env) (Pop y) (x₁ , x₂) = lookup-normalization env y x₂

to-NF : {τ : Type} → {c : Closed τ} → IsValue c → NF c
to-NF {c = Closure ._ _} x (Red Lookup) = x
to-NF {c = Closure ._ _} x (Red Dist)   = x
to-NF {c = Clapp _ _} x _ = x

-- All closure terms are normalizable.
closure-normalization : ∀ {ctx} → {τ : Type} → (t : Term ctx τ) → (env : Env ctx) →
 NormalizableEnv env → Normalizable τ (Closure t env)
closure-normalization (Abs x) e e2 = (Halts (to-NF U) Nil , ((\a b → normalizableStep (Beta x a) ( (closure-normalization x (Cons a e) (b , e2))))) )
closure-normalization (App x x₁) e e2 = normalizableStep Dist (clapp-normalization (closure-normalization x e e2) (closure-normalization x₁ e e2))
closure-normalization (Var x) e e2 = normalizableStep Lookup (lookup-normalization e x e2)

mutual
  -- An environment is always normalizable
  normalizable-env : ∀ {ctx : Context} (env : Env ctx) → NormalizableEnv env
  normalizable-env Nil = U
  normalizable-env (Cons x env) = normalization x , normalizable-env env

  -- All terms are normalizable.
  normalization : {τ : Type} → (c : Closed τ) → Normalizable τ c
  normalization  (Closure t x) = closure-normalization t x (normalizable-env x)
  normalization (Clapp c c₁) = clapp-normalization (normalization c) (normalization c₁)

termination : {τ : Type} → (c : Closed τ) → Terminates c
termination c = normalizable-terminates (normalization c)
