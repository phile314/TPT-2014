
module Exercise2b where

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
normalizable-terminates {O} (Halts x x₁) = Halts x x₁
normalizable-terminates {ty => ty₁} (x , x₁) = x

-- Helper lemmas for normalization proof.
normalizableStep : forall {ty} -> {c1 c2 : Closed ty} -> Step c1 c2 ->
   Normalizable ty c2 -> Normalizable ty c1
normalizableStep {O} step (Halts x x₁) = Halts x (Cons step x₁)
normalizableStep {ty => ty₁} {c1} {c2} step (Halts x x₁ , x₂) =
  (Halts x (Cons step x₁)) , (λ x₃ x₄ → normalizableStep (AppL c1 c2 x₃ step) (x₂ x₃ x₄))

normalizableSteps : forall {ty} -> {c1 c2 : Closed ty} -> Steps c1 c2 -> Normalizable ty c2 -> Normalizable ty c1
normalizableSteps Nil n = n
normalizableSteps (Cons x steps) n = normalizableStep x (normalizableSteps steps n)

-- The following three lemmas may use mutual recursion. This is done
-- in Agda by separating the type signature and the function
-- definition.

mutual
  -- Closed applications of the form 'f x' are normalizable when both f and x are normalizable.
  clapp-normalization : forall {A B} -> {c1 : Closed (A => B)} -> {c2 : Closed A} -> Normalizable (A => B) c1  -> Normalizable A c2 -> Normalizable B (Clapp c1 c2)
  clapp-normalization {c2 = c2} (x , x₁) n2 = x₁ c2 n2

  -- All closure terms are normalizable.
  closure-normalization : forall {ctx} -> (ty : Type) -> (t : Term ctx ty) -> (env : Env ctx) -> NormalizableEnv env -> Normalizable ty (Closure t env)
  closure-normalization ._ (Abs {v = v} t) env nenv = (Halts lemma Nil) , (λ x x₁ → normalizableStep (Beta t x) (closure-normalization v t (Cons x env) (x₁ , nenv)))
    where
    lemma : NF (Closure (Abs t) env)
    lemma (Red ())
  closure-normalization ty (App {u = u} t t₁) env nenv = normalizableStep Dist (clapp-normalization (closure-normalization (u => ty) t env nenv) (closure-normalization u t₁ env nenv))
  closure-normalization ty (Var x) env nenv = normalizableStep Lookup (lookup' x env nenv)
    where
    -- A lookup function that additionally retrieves the normalizability proof from
    -- the normalizable environment.
    lookup' : forall {ctx ty} -> (x : Ref ctx ty) -> (env : Env ctx) -> NormalizableEnv env -> Normalizable ty (lookup x env)
    lookup' Top (Cons x env) (x₁ , x₂) = x₁
    lookup' (Pop ref) (Cons x env) (x₁ , x₂) = lookup' ref env x₂

  -- An environment is always normalizable.
  normalizable-env : forall {ctx : Context} {env : Env ctx} -> NormalizableEnv env
  normalizable-env {[]} {Nil} = U
  normalizable-env {ty :: ctx} {Cons x env} = normalization ty x , normalizable-env

  -- All terms are normalizable.
  normalization : (ty : Type) -> (c : Closed ty) -> Normalizable ty c
  normalization ty (Closure t env) = closure-normalization ty t env normalizable-env
  normalization ty (Clapp c c₁) = clapp-normalization (normalization _ c) (normalization _ c₁)

termination : (ty : Type) -> (c : Closed ty) -> Terminates c
termination ty c = normalizable-terminates (normalization ty c)
