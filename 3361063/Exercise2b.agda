
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

-- Helper lemma's for normalization proof.
normalizableStep : forall {ty} -> {c1 c2 : Closed ty} -> Step c1 c2 ->
   Normalizable ty c2 -> Normalizable ty c1
normalizableStep {O} s (Halts x x₁) = Halts x (Cons s x₁)
normalizableStep {ty => ty₁} s (Halts h Nil , x₂) = (Halts h (Cons s Nil)) , (λ x₁ x₃ → normalizableStep (AppL _ _ x₁ s) (x₂ x₁ x₃))
normalizableStep {ty => ty₁} s (Halts h (Cons (AppL f f' x₁ x₂) x₃) , ns) = (Halts h (Cons s (Cons (AppL f f' x₁ x₂) x₃))) , (λ x₅ x₆ → normalizableStep (AppL _ (Clapp f x₁) x₅ s) (ns x₅ x₆))
normalizableStep {ty => ty₁} s (Halts h (Cons (Beta body v) x₂) , ns) = (Halts h (Cons s (Cons (Beta body v) x₂))) , (λ x₁ x₄ → normalizableStep (AppL _ (Clapp (Closure (Abs body) _) v) x₁ s) (ns x₁ x₄))
normalizableStep {ty => ty₁} s (Halts h (Cons Lookup x₂) , ns) = (Halts h (Cons s (Cons Lookup x₂))) , (λ x₁ x₃ → normalizableStep (AppL _ (Closure (Var _) _) x₁ s) (ns x₁ x₃))
normalizableStep {ty => ty₁} s (Halts h (Cons Dist x₂) , ns) = (Halts h (Cons s (Cons Dist x₂))) , (λ x₁ x₃ → normalizableStep (AppL _ (Closure (App _ _) _) x₁ s) (ns x₁ x₃))

normalizableSteps : forall {ty} -> {c1 c2 : Closed ty} -> Steps c1 c2 -> Normalizable ty c2 -> Normalizable ty c1
normalizableSteps Nil n = n
normalizableSteps {ty} (Cons s steps) n  with normalizableSteps steps n
normalizableSteps {O} (Cons s steps) n | Halts h ss = Halts h (Cons s ss)
normalizableSteps {ty => ty₁} (Cons s steps) n | Halts h ss , ns = normalizableStep s (Halts h ss , ns)

lookup' : ∀ {ty ctx} -> (ref : Ref ctx ty) -> (env : Env ctx) -> NormalizableEnv env -> Normalizable ty (lookup ref env)
lookup' Top (Cons x G₁) (x₁ , x₂) = x₁
lookup' (Pop r) (Cons x G₁) (x₁ , x₂) = lookup' r G₁ x₂

abs-nf : ∀ {ty G u} {g : Env G} {tm : Term (u :: G) ty} -> Not (Reducible (Closure {G} {u => ty} (Abs {G} {u} {ty} tm) g))
abs-nf (Red ())

-- The following three lemmas may use mutual recursion. This is done
-- in Agda by separating the type signature and the function
-- definition.
mutual
  -- Closed applications of the form 'f x' are normalizable when both f and x are normalizable.
  clapp-normalization : forall {A B} -> {c1 : Closed (A => B)} -> {c2 : Closed A} -> 
                         Normalizable (A => B) c1  -> Normalizable A c2 -> Normalizable B (Clapp c1 c2)
  clapp-normalization (x , x₁) nc2 = x₁ _ nc2
  -- All closure terms are normalizable.
  closure-normalization : forall {ctx} -> (ty : Type) -> (t : Term ctx ty) -> (env : Env ctx) -> 
   NormalizableEnv env -> Normalizable ty (Closure t env)
  closure-normalization _ (Var x) G nG = normalizableStep Lookup (lookup' x G nG)
  closure-normalization _ (App tm tm₁) G nG = let ntm₁ = closure-normalization _ tm₁ G nG
                                                  ntm = closure-normalization _ tm G nG
                                              in normalizableStep Dist (clapp-normalization ntm ntm₁)
  closure-normalization (ty => ty₁) (Abs tm) G nG = (Halts abs-nf Nil) , (λ x x₁ → normalizableStep (Beta tm x) (closure-normalization ty₁ tm (Cons x G) (x₁ , nG)))

  -- An environment is always normalizable
  normalizable-env : forall {ctx : Context} {env : Env ctx} -> NormalizableEnv env
  normalizable-env {[]} {Nil} = U
  normalizable-env {x :: ctx} {Cons x₁ env} = (normalization x x₁) , (normalizable-env {ctx} {env})

  -- All terms are normalizable.
  normalization : (ty : Type) -> (c : Closed ty) -> Normalizable ty c
  normalization ty (Closure t env) = closure-normalization ty t env normalizable-env
  normalization ty (Clapp c c₁) with normalization _ c , normalization _ c₁
  normalization ty (Clapp c c₁) | n , n₁ = clapp-normalization n n₁


termination : (ty : Type) -> (c : Closed ty) -> Terminates c
termination ty c = normalizable-terminates (normalization ty c)

-- I did not need this, feel free to skip
{-
-- If Reducible were replaced by a Step, this could be made to work
isValue' : ∀ {ty ty'} (c : Closed (ty => ty')) (d : Closed ty) -> Reducible (Clapp c d) -- IsValue (Clapp {ty } {ty' } c d)
isValue' (Closure (Abs t) env) c₁ =  (Red (Beta _ _))
isValue' (Closure (App t t₁) env) c₁  =  (Red (AppL _ _ _ Dist))
isValue' (Closure (Var x) env) c₁  =  (Red (AppL _ _ _ Lookup))
isValue' (Clapp a b) c₁  = {!Red ( AppL _ _ _ {!isValue' ? ?   stuck here because we need to know the result of the step!} )!}

isValue : ∀ {ty} (c : Closed ty) -> (nf : NF c) -> IsValue c
isValue (Closure (App t t₁) env) nf = nf (Red Dist)
isValue (Closure (Var x) env) nf = nf (Red Lookup)
isValue (Closure (Abs t) env) nf = U
isValue (Clapp a b) nf = nf (isValue' a b)
-- -}
