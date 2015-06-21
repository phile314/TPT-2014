
module Exercise2b where

{-

F142001

-}

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
data _==_ {a : Set} (x : a) : a -> Set where
 Refl : x == x

cong : forall {a b x y} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

symmetry : {a : Set} -> {x y : a} -> x == y -> y == x
symmetry Refl = Refl

transitivity : {a : Set} -> {x y z : a} -> x == y -> y == z -> x == z
transitivity Refl Refl = Refl

-- Lists.
data List (a : Set) : Set where
 []   : List a
 _::_ : a -> List a -> List a

-- Pairs.
data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

fst : forall {a b} -> Pair a b -> a
fst (x , _) = x

snd : forall {a b} -> Pair a b -> b
snd (_ , x) = x

-- Unit type.
data Unit : Set where
 U : Unit

-- The empty type and negation.
data Absurd : Set where

Not : Set -> Set
Not x = x -> Absurd

contradiction : {a : Set} -> Absurd -> a
contradiction ()

------------------------------------------------------------------------
-- Types and terms.
--------------------------------------------------------------------------------

-- Unit and function types are supported.
data Type : Set where
 O    : Type
 _=>_ : Type -> Type -> Type

el : Type -> Set
el O = Unit
el (s => t) = el s -> el t

-- Type context: the top of this list is the type of the innermost
-- abstraction variable, the next element is the type of the next
-- variable, and so on.
Context : Set
Context = List Type

-- Reference to a variable, bound during some abstraction.
data Ref : Context -> Type -> Set where
 Top : forall {G u} -> Ref (u :: G) u
 Pop : forall {G u v} -> Ref G u -> Ref (v :: G) u

-- A term in the lambda calculus. The language solely consists of
-- abstractions, applications and variable references.
mutual
  data Term : Context -> Type -> Set where
   Abs : forall {G u v} -> (body : Term (u :: G) v) -> Term G (u => v)
   App : forall {G u v} -> (f : Term G (u => v)) -> (x : Term G u) -> Term G v
   Var : forall {G u} -> Ref G u -> Term G u


  data Env : List Type -> Set where
    Nil  : Env []
    Cons : forall {ctx ty} -> Closed ty -> Env ctx -> Env (ty :: ctx)

  data Closed : Type -> Set where
    Closure : forall {ctx ty} -> (t : Term ctx ty) -> (env : Env ctx) -> Closed ty
    Clapp : forall {ty ty'} -> (f : Closed (ty => ty')) (x : Closed ty) ->
               Closed ty'


IsValue : forall {ty} -> Closed ty -> Set
IsValue (Closure (Abs t) env) = Unit
IsValue (Closure (App t t₁) env) = Absurd
IsValue (Closure (Var x) env) = Absurd
IsValue (Clapp t t₁) = Absurd

------------------------------------------------------------------------
-- Step-by-step evaluation of terms.

lookup : forall {ctx ty} -> Ref ctx ty -> Env ctx -> Closed ty
lookup Top (Cons x env) = x
lookup (Pop i) (Cons x env) = lookup i env



data Step : forall {ty} -> Closed ty -> Closed ty -> Set where 
  AppL : {ty ty' : Type} (f f' : Closed (ty => ty')) (x : Closed ty) ->
    Step f f' -> Step (Clapp f x) (Clapp f' x)
  Beta : {ty ty' : Type} {ctx : Context} (body : Term (ty :: ctx) ty') (v : Closed ty)
    {env : Env ctx} ->
    Step (Clapp (Closure (Abs body) env) v) (Closure body (Cons v env))
  Lookup : {ctx : List Type} {ty : Type} {i : Ref ctx ty} {env : Env ctx} ->
          Step (Closure (Var i) env) (lookup i env)
  Dist : {ty ty' : Type} {ctx : List Type} {env : Env ctx} {f : Term ctx (ty => ty')} {x : Term ctx ty} ->
         Step (Closure (App f x) env) (Clapp (Closure f env) (Closure x env))


-- Reducibility.
data Reducible : forall {ty} -> Closed ty -> Set where
 Red : forall {ty} -> {c1 c2 : Closed ty} -> Step c1 c2 -> Reducible c1

-- Non-reducable terms are considered normal forms.
NF : forall {ty} -> Closed ty -> Set
NF c = Not (Reducible c)

-- A sequence of steps that can be applied in succession.
data Steps : forall {ty} -> Closed ty -> Closed ty -> Set where
 Nil  : forall {ty} -> {c : Closed ty} -> Steps c c
 Cons : forall {ty} -> {c1 c2 c3 : Closed ty} -> Step c1 c2 -> Steps c2 c3 -> Steps c1 c3

--------------------------------------------------------------------------------
-- Termination
--------------------------------------------------------------------------------

-- Definition of termination: a sequence of steps exist that ends up in a normal form.
data Terminates : forall {ty} -> Closed ty -> Set where
  Halts : forall {ty} -> {c nf : Closed ty} -> NF nf -> Steps c nf -> Terminates c

Normalizable : (ty : Type) -> Closed ty -> Set
Normalizable O c = Terminates c
Normalizable (ty => ty₁) f = 
  Pair (Terminates f) 
       ((x : Closed ty) -> Normalizable ty x -> Normalizable ty₁ (Clapp f x))

-- Structure that maintains normalization proofs for all elements in the environment.
NormalizableEnv : forall {ctx} -> Env ctx -> Set
NormalizableEnv Nil = Unit
NormalizableEnv (Cons {ctx} {ty} x env) = Pair (Normalizable ty x) (NormalizableEnv env) 

-- Normalization implies termination.
normalizable-terminates : forall {ty c} -> Normalizable ty c -> Terminates c
normalizable-terminates {O}          x      = x
normalizable-terminates {ty => ty₁} (x , _) = x

-- Helper lemma's for normalization proof.

-- We can always add a single step in front of the normalization proof.
-- We pattern match on the implicit type.
-- For the termination proof, we can simply add the step "c1 -> c2" to the front.
-- For the second half of the pair, we use a sublemma to condition further on the subtype of the target,
-- because this again determines whether we need to provide only a termination proof or a complete normalization pair.
normalizableStep : forall {ty} -> {c1 c2 : Closed ty} -> Step c1 c2 ->
   Normalizable ty c2 -> Normalizable ty c1
normalizableStep {O}         step (Halts x steps)      = Halts x (Cons step steps)
normalizableStep {ty => ty₁} step (Halts x steps , x₂) = ( Halts x (Cons step steps) , (\y → \norm → sublemma step y norm (x₂ y norm)) )
   where
   sublemma : ∀ {ty ty₁} {c₁ c₂ : Closed (ty => ty₁)} → Step c₁ c₂ → (y : Closed ty) → Normalizable ty y → Normalizable ty₁ (Clapp c₂ y) →  Normalizable ty₁ (Clapp c₁ y)
   sublemma {ty₁ = O}          step y norm (Halts x steps)      =   Halts x (Cons (AppL _ _ y step) steps)
   sublemma {ty₁ = ty₂ => ty₃} step y norm (Halts x steps , x₁) = ( Halts x (Cons (AppL _ _ y step) steps) ,
                                                                    (\x' → \norm' → sublemma (AppL _ _ y step) x' norm' (x₁ x' norm')) )

-- Generalization: we can add several steps in front of the normalization proof.
normalizableSteps : forall {ty} -> {c1 c2 : Closed ty} -> Steps c1 c2 -> Normalizable ty c2 -> Normalizable ty c1
normalizableSteps Nil               norm = norm
normalizableSteps (Cons step steps) norm = normalizableStep step (normalizableSteps steps norm)




-- An environment is always normalizable
normalizable-env : forall {ctx : Context} {env : Env ctx} -> NormalizableEnv env

-- Closed applications of the form 'f x' are normalizable when both f and x are normalizable.
clapp-normalization : forall {A B} -> {c1 : Closed (A => B)} -> {c2 : Closed A} -> 
                       Normalizable (A => B) c1  -> Normalizable A c2 -> Normalizable B (Clapp c1 c2)

-- All closure terms are normalizable.
closure-normalization : forall {ctx} -> (ty : Type) -> (t : Term ctx ty) -> (env : Env ctx) -> 
 NormalizableEnv env -> Normalizable ty (Closure t env)

-- All terms are normalizable.
normalization : (ty : Type) -> (c : Closed ty) -> Normalizable ty c

-- An environment is always normalizable: we simply provide normalization proofs for each element in the list
normalizable-env {env = Nil} = U
normalizable-env {env = Cons y env} = ( normalization _ y , normalizable-env {_} {env} )

-- Closure normalization: pattern match primarily on the structure of the term
-- CASE 1: abstraction
-- For termination, we need a sublemma to show that a term of the form "Closure (Abs t) env" is never reducible.
-- The second half is provided by first doing a beta reduction, and then recursing
closure-normalization ._ (Abs t)    env norm = ( Halts sublemma  Nil , (\t₁ → \norm₁ → normalizableStep (Beta t t₁) (closure-normalization _ t (Cons t₁ env) (norm₁ , norm)) ))
  where
  sublemma : ∀ {ty ty' ctx} {t : Term (ty' :: ctx) ty} {env : Env ctx} → Reducible (Closure (Abs t) env) → Absurd
  sublemma (Red ())

-- CASE 2: application
-- simply recursion, plus our helper lemma clapp-normalization (see below)
closure-normalization ty          (App t t₁) env norm = normalizableStep Dist (clapp-normalization
                                                             (closure-normalization _ t env norm)
                                                             (closure-normalization _ t₁ env norm))
-- CASE 3: variable
-- the normalizable environment already carries the normalization proof. The trick is to look it up
-- (I needed an extra lemma for this, lookup2, but I'm not sure this is strictly necessary
closure-normalization ty (Var x) env norm = normalizableStep Lookup (lookup2 x env norm)
  where
  lookup2 : forall {ctx ty} -> (ref : Ref ctx ty) -> (env : Env ctx) -> NormalizableEnv env -> Normalizable ty (lookup ref env)
  lookup2 Top (Cons x env) (x₁ , x₂) = x₁
  lookup2 (Pop ref) (Cons x env) (x₁ , x₂) = lookup2 ref env x₂

-- Clapp normalization: a one-liner. Observe that the normalization proof of the first term is always a pair, because the first term has a complex type
clapp-normalization (x , x₁) norm₂ = x₁ _ norm₂


-- Once we got all the helper lemma's out of the way, the definition of normalization is quite easy.
normalization ty (Closure t env) = closure-normalization ty t env normalizable-env
normalization ty (Clapp c c₁) = clapp-normalization (normalization _ c) (normalization _ c₁)

-- All that remains is to strip away the extra information from the normalization proofs in order to turn them into termination proofs.
termination : (ty : Type) -> (c : Closed ty) -> Terminates c
termination ty c = normalizable-terminates (normalization ty c)
