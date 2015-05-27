
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
data _==_ {a}{A : Set a} (x : A) : A → Set a where
  refl : x == x

-- The two following pragmas are here so I can use the 'rewrite' keyword
-- when I have some (p : x == y).

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}  

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

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    p1 : A
    p2 : B p1

open Σ {{...}}

-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

data Type : Set where
  NAT : Type
  BOOL : Type
  _×_  : Type → Type → Type

mutual
  -- Our Term language
  data Term : Type -> Set where 
    true          : Term BOOL 
    false         : Term BOOL
    if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
    -- Let's add natural numbers
    zero          : Term NAT
    succ          : (n : Term NAT) -> Term NAT
    iszero        : (n : Term NAT) -> Term BOOL
    -- Let's add tuples
    π₁            : ∀{A B}(n : Term (A × B)) → Term A
    π₂            : ∀{A B}(n : Term (A × B)) → Term B
    <_,_>         : ∀{A B} → Term A → Term B → Term (A × B)


  -- The set of atomic values within the language.
  data Value : Type -> Set where
    vtrue : Value BOOL 
    vfalse : Value BOOL
    -- And a new value
    vnat : Nat -> Value NAT
    vpair : ∀{A B} → Value A → Value B → Value (A × B) 

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝     = true
⌜ vfalse ⌝    = false
⌜ vnat k ⌝    = natTerm k
⌜ vpair a b ⌝ = < ⌜ a ⌝ , ⌜ b ⌝ >


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

vPi1 : ∀{A B} → Value (A × B) → Value A
vPi1 (vpair va _) = va

vPi2 : ∀{A B} → Value (A × B) → Value B
vPi2 (vpair _ vb) = vb

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ π₁ t ⟧ = vPi1 ⟦ t ⟧
⟦ π₂ t ⟧ = vPi2 ⟦ t ⟧
⟦ < ta , tb > ⟧ = vpair ⟦ ta ⟧ ⟦ tb ⟧

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
  -- Here we add the rules for evaluating types. Note that
  -- a projection is only 'eliminated' when the pair has been fully evaluated,
  -- that is, both its components are values.
  --
  -- This is given as an argument in the two following constructors,
  -- mainly to 'make Agda happy'. If we index a datatype by a function,
  -- we might run into some nasty unification problems.
  --
  E-Pi1        : ∀{A B}{t : Term A}{vt : Value A}{u : Term B}{vu : Value B}
               → t == ⌜ vt ⌝ → u == ⌜ vu ⌝ → Step (π₁ < t  , u >) t
  E-Pi2        : ∀{A B}{t : Term A}{vt : Value A}{u : Term B}{vu : Value B}
               → t == ⌜ vt ⌝ → u == ⌜ vu ⌝ → Step (π₂ < t , u >) u
  E-Pi1-tr     : ∀ {A B}{t t' : Term (A × B)}
               → Step t t'  → Step (π₁ t) (π₁ t')
  E-Pi2-tr     : ∀ {A B}{t t' : Term (A × B)} 
               → Step t t' → Step (π₂ t) (π₂ t')
  E-Pair1      : ∀ {A B}{t t' : Term A}{u : Term B}
               → Step t t' → Step < t , u > < t' , u >
  -- Also, note how we fix the evaluation order of pairs here,
  -- This is required to prove determinism.
  E-Pair2      : ∀{A B}{t : Term A}{vt : Value A}{u u' : Term B}
               → t == ⌜ vt ⌝ → Step u u' → Step < t , u > < t , u' >

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vpair va vb) (if t then t₁ else t₂) ()
valuesDoNotStep (vpair va vb) (π₁ t) ()
valuesDoNotStep (vpair va vb) (π₂ t) ()
valuesDoNotStep (vpair va vb) < t , .(⌜ vb ⌝) > (E-Pair1 s) = valuesDoNotStep va _ s
valuesDoNotStep (vpair va vb) < .(⌜ va ⌝) , b > (E-Pair2 x s) = valuesDoNotStep vb _ s
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step

valuesDoNotStep-imp : ∀{ty}{v : Value ty}{t : Term ty} → Step (⌜ v ⌝) t → Empty
valuesDoNotStep-imp {v = v} {t = t} = valuesDoNotStep v t


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
  lemma (vnat x) (π₁ t) ()
  lemma (vnat x) (π₂ t) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ steps1)
deterministic (E-IsZero steps1) (E-IsZero steps2) = cong iszero (deterministic steps1 steps2)
deterministic (E-Pi1 x y) (E-Pi1 x1 y1) = refl
deterministic (E-Pi1 {vt = vt} x y) (E-Pi1-tr (E-Pair1 z)) rewrite x 
  = contradiction (valuesDoNotStep vt _ z)
deterministic (E-Pi1 {vu = vu} x y) (E-Pi1-tr (E-Pair2 _ z)) rewrite y
  = contradiction (valuesDoNotStep vu _ z)
deterministic (E-Pi2 x y) (E-Pi2 x₁ x₂) = refl
deterministic (E-Pi2 {vt = vt} x y) (E-Pi2-tr (E-Pair1 z)) rewrite x 
  = contradiction (valuesDoNotStep vt _ z)
deterministic (E-Pi2 {vu = vu} x y) (E-Pi2-tr (E-Pair2 _ z)) rewrite y
  = contradiction (valuesDoNotStep vu _ z)
deterministic (E-Pi1-tr (E-Pair1 z)) (E-Pi1 {vt = vt} x y) rewrite x 
  = contradiction (valuesDoNotStep vt _ z)
deterministic (E-Pi1-tr (E-Pair2 _ z)) (E-Pi1 {vu = vu} x y) rewrite y
  = contradiction (valuesDoNotStep vu _ z)
deterministic (E-Pi1-tr s) (E-Pi1-tr y) with deterministic s y
...| refl = refl
deterministic (E-Pi2-tr (E-Pair1 z)) (E-Pi2 {vt = vt} x y) rewrite x 
  = contradiction (valuesDoNotStep vt _ z)
deterministic (E-Pi2-tr (E-Pair2 _ z)) (E-Pi2 {vu = vu} x y) rewrite y
  = contradiction (valuesDoNotStep vu _ z)
deterministic (E-Pi2-tr s) (E-Pi2-tr y) with deterministic s y
...| refl = refl
deterministic (E-Pair1 s) (E-Pair1 y) with deterministic s y
...| refl = refl
deterministic (E-Pair1 {t' = t'} s) (E-Pair2 {vt = vt} prf y) 
  rewrite prf = contradiction (valuesDoNotStep vt t' s)
deterministic (E-Pair2 {vt = vt} p s) (E-Pair1 {t' = t'} y) 
  rewrite p  = contradiction (valuesDoNotStep vt t' y)
deterministic (E-Pair2 p s) (E-Pair2 x y) with deterministic s y
...| refl = refl

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

unStep : ∀{ty}{t : Term ty} → Red t → Σ (Term ty) (Step t)
unStep (Reduces {t'} step) = t' , step

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} -> Term ty → Set
NF t = Red t -> Empty

-- Evidence type that shows a certain term represents a value.
data Is-value {ty : Type} : Term ty → Set where
  is-value : ∀ v → Is-value ⌜ v ⌝

toVal : forall {ty} -> (t : Term ty) -> Is-value t -> Value ty
toVal .(⌜ v ⌝) (is-value v) = v

mutual
  -- This is pretty close to Is-Value, I just prefer working on Σ's.
  nf⇒val : ∀{ty}(t : Term ty)(nf : NF t) → Σ (Value ty) (λ v → t == ⌜ v ⌝)
  nf⇒val true nf = vtrue , refl
  nf⇒val false nf = vfalse , refl
  nf⇒val (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  nf⇒val zero nf = vnat Zero , refl
  nf⇒val (succ t) nf with nf⇒val t (succ-nf t nf)
  ...| vnat rv , prf = vnat (Succ rv) , cong succ prf
  nf⇒val (iszero t) nf = contradiction (nf (iszero-reduces t))
  nf⇒val (π₁ t) nf = contradiction (nf (pi1-reduces t))
  nf⇒val (π₂ t) nf = contradiction (nf (pi2-reduces t))
  nf⇒val < t , u > nf 
    with nf⇒val t (pair-nf-1 nf)
       | nf⇒val u (pair-nf-2 nf)
  ...| rt , prft | ru , prfu 
    rewrite prft | prfu = vpair rt ru , refl

  -- If-then-else terms are reducible.
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3 
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t) t4 t5 with iszero-reduces t
  if-reduces (iszero t) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (π₁ t) t4 t5 with pi1-reduces t
  ...| Reduces x = Reduces (E-If-If x)
  if-reduces (π₂ t) t4 t5 with pi2-reduces t
  ...| Reduces x = Reduces (E-If-If x)

  pi1-reduces : ∀{ty ty'} (t : Term (ty × ty')) → Red (π₁ t)
  pi1-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  ...| Reduces x = Reduces (E-Pi1-tr x)
  pi1-reduces (π₁ t) with pi1-reduces t
  ...| Reduces x = Reduces (E-Pi1-tr x)
  pi1-reduces (π₂ t) with pi2-reduces t
  ...| Reduces x = Reduces (E-Pi1-tr x)
  pi1-reduces < t , t₁ > with progress t
  ...| Right (Reduces x) = Reduces (E-Pi1-tr (E-Pair1 x))
  ...| Left x with nf⇒val t x | progress t₁
  ...| nf-t , prf | Right (Reduces y) = Reduces (E-Pi1-tr (E-Pair2 {vt = nf-t} prf y))
  ...| nf-t , prf | Left y with nf⇒val t₁ y
  ...| nf-t₁ , prf2 = Reduces (E-Pi1 {vt = nf-t} {vu = nf-t₁} prf prf2)
  

  pi2-reduces : ∀{ty ty'} (t : Term (ty × ty')) → Red (π₂ t)
  pi2-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  ...| Reduces x = Reduces (E-Pi2-tr x)
  pi2-reduces (π₁ t) with pi1-reduces t
  ...| Reduces x = Reduces (E-Pi2-tr x)
  pi2-reduces (π₂ t) with pi2-reduces t
  ...| Reduces x = Reduces (E-Pi2-tr x)
  pi2-reduces < t , t₁ > with progress t
  ...| Right (Reduces x) = Reduces (E-Pi2-tr (E-Pair1 x))
  ...| Left x with nf⇒val t x | progress t₁
  ...| nf-t , prf | Right (Reduces y) = Reduces (E-Pi2-tr (E-Pair2 {vt = nf-t} prf y))
  ...| nf-t , prf | Left y with nf⇒val t₁ y
  ...| nf-t₁ , prf2 = Reduces (E-Pi2 {vt = nf-t} {vu = nf-t₁} prf prf2)


  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (π₁ t) with pi1-reduces t
  ...| Reduces x = Reduces (E-IsZero x)
  iszero-reduces (π₂ t) with pi2-reduces t
  ...| Reduces x = Reduces (E-IsZero x)

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (π₁ t) with pi1-reduces t
  ...| Reduces x = λ x₁ x₂ → x₁ (Reduces (E-Succ x))
  succ-nf (π₂ t) with pi2-reduces t
  ...| Reduces x = λ x₁ x₂ → x₁ (Reduces (E-Succ x))

  pair-nf-1 : ∀{A B}{ta : Term A}{tb : Term B}
            → NF < ta , tb > → NF ta
  pair-nf-1 nf (Reduces x) = nf (Reduces (E-Pair1 x))

  pair-nf-2 : ∀{A B}{ta : Term A}{tb : Term B}
            → NF < ta , tb > → NF tb
  pair-nf-2 {ta = ta} nf (Reduces x) with pair-nf-1 nf
  ...| nf-ta with nf⇒val ta nf-ta
  ...| v , prf = nf (Reduces (E-Pair2 {vt = v} prf x))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (π₁ t) nf = contradiction (nf (pi1-reduces t))
  normal-forms-are-values (π₂ t) nf = contradiction (nf (pi2-reduces t))
  normal-forms-are-values < a , b > nf
    with normal-forms-are-values a (pair-nf-1 nf)
       | normal-forms-are-values b (pair-nf-2 nf)
  normal-forms-are-values < .(⌜ a ⌝) , .(⌜ b ⌝) > nf | is-value a | is-value b 
    = is-value (vpair a b)
  

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
  progress (π₁ t) = Right (pi1-reduces t)
  progress (π₂ t) = Right (pi2-reduces t)
  progress < a , b > with progress a
  ...| Right (Reduces x) = Right (Reduces (E-Pair1 x))
  ...| Left x with nf⇒val a x | progress b
  ...| nf-a , prf-a | Right (Reduces y) = Right (Reduces (E-Pair2 {vt = nf-a} prf-a y))
  ...| nf-a , prf-a | Left  y with nf⇒val b y
  ...| nf-b , prf-b 
    rewrite prf-a 
          | prf-b 
          = Left (values-are-normal-forms < ⌜ nf-a ⌝ , ⌜ nf-b ⌝ > (is-value (vpair nf-a nf-b))) 


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

-- Auxiliar lemma to map a function over steps.
-- Very usefull for converting big-step to small-step.
map-steps : ∀{ty ty' t t'}{F : Term ty → Term ty'} 
          → ({a b : Term ty} → Step a b → Step (F a) (F b)) 
          → Steps t t' → Steps (F t) (F t')
map-steps f Nil = Nil
map-steps f (Cons {t1} {t2} x xs) = Cons (f x) (map-steps f xs)

append : ∀{ty}{t t' t'' : Term ty}
       → Step t' t''
       → Steps t t'
       → Steps t t''
append s Nil = Cons s Nil
append s (Cons x xs) = Cons x (append s xs)

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
E-If-Steps = map-steps E-If-If

E-Succ-Steps : ∀ {t t' : Term NAT} -> 
        Steps t t' →
        Steps (succ t) (succ t')
E-Succ-Steps = map-steps E-Succ

E-IsZero-Steps : ∀ {t t' : Term NAT} -> 
        Steps t t' →
        Steps (iszero t) (iszero t')
E-IsZero-Steps = map-steps E-IsZero

E-Pi1-Steps : {a b : Type}{t : Term (a × b)}{ta : Value a}{tb : Value b}
            → Steps t < ⌜ ta ⌝ , ⌜ tb ⌝ >
            → Steps (π₁ t) (⌜ ta ⌝)
E-Pi1-Steps {ta = ta} {tb = tb} s
  = map-steps E-Pi1-tr s ++ [ E-Pi1 {vt = ta} {vu = tb} refl refl ]

E-Pi2-Steps : {a b : Type}{t : Term (a × b)}{ta : Value a}{tb : Value b}
            → Steps t < ⌜ ta ⌝ , ⌜ tb ⌝ >
            → Steps (π₂ t) (⌜ tb ⌝)
E-Pi2-Steps {ta = ta} {tb = tb} s
  = map-steps E-Pi2-tr s ++ [ E-Pi2 {vt = ta} {vu = tb} refl refl ]

E-Pair-Steps : {a b : Type}{ta : Term a}{va : Value a}{tb tb' : Term b}
             → Steps ta (⌜ va ⌝) → Steps tb tb'
             → Steps < ta , tb > < ⌜ va ⌝ , tb' >
E-Pair-Steps Nil Nil = Nil
E-Pair-Steps {va = va} Nil (Cons x tbtb')  = Cons (E-Pair2 {vt = va} refl x) (E-Pair-Steps {va = va} Nil tbtb')
E-Pair-Steps {va = va} (Cons x tava) tbtb' = Cons (E-Pair1 x) (E-Pair-Steps {va = va} tava tbtb')

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
termination (iszero (π₁ t)) with termination t
...| terminates (vpair (vnat Zero)     v₁) x 
   = terminates vtrue  (E-IsZero-Steps (E-Pi1-Steps {ta = vnat Zero} {tb = v₁} x) ++ Cons E-IsZeroZero Nil)
...| terminates (vpair (vnat (Succ v)) v₁) x 
   = terminates vfalse (E-IsZero-Steps (E-Pi1-Steps {ta = vnat (Succ v)} {tb = v₁} x) ++ Cons (E-IsZeroSucc {v = vnat v})  Nil)
termination (iszero (π₂ t)) with termination t
...| terminates (vpair v₁ (vnat Zero))     x 
   = terminates vtrue  (E-IsZero-Steps (E-Pi2-Steps {ta = v₁} {tb = vnat Zero} x) ++ Cons E-IsZeroZero Nil)
...| terminates (vpair v₁ (vnat (Succ v))) x 
   = terminates vfalse (E-IsZero-Steps (E-Pi2-Steps {ta = v₁} {tb = vnat (Succ v)} x) ++ Cons (E-IsZeroSucc {v = vnat v}) Nil)
termination (π₁ t) with termination t
...| terminates (vpair vta vtb) x = terminates vta (E-Pi1-Steps {ta = vta} {tb = vtb} x)
termination (π₂ t) with termination t
...| terminates (vpair vta vtb) x = terminates vtb (E-Pi2-Steps {ta = vta} {tb = vtb} x)
termination < ta , tb > with termination ta | termination tb
...| terminates vta xa | terminates vtb xb = terminates (vpair vta vtb) (E-Pair-Steps {ta = ta} {va = vta} {tb = tb} xa xb)

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} → Term ty → Value ty → Set where
  B-True    : true ⇓ vtrue
  B-False   : false ⇓ vfalse
  B-Zero    : zero  ⇓ (vnat Zero)
  B-IfTrue  : ∀{ty c t e v} → c ⇓ vtrue  → _⇓_ {ty} t v → _⇓_ {ty} (if c then t else e) v
  B-IfFalse : ∀{ty c t e v} → c ⇓ vfalse → _⇓_ {ty} e v → _⇓_ {ty} (if c then t else e) v
  B-IsZeroZero  : ∀{t} → t ⇓ (vnat Zero) → (iszero t) ⇓ vtrue
  B-IsZeroFalse : ∀{t n} → t ⇓ (vnat (Succ n)) → (iszero t) ⇓ vfalse
  B-Succ : ∀{t n} → t ⇓ (vnat n) → (succ t) ⇓ (vnat (Succ n))
  B-Pair : ∀{T U t u vt vu} → _⇓_ {T} t vt → _⇓_ {U} u vu → < t , u > ⇓ (vpair vt vu)
  B-Pi1  : ∀{A B t a b} → _⇓_ {A × B} t (vpair a b) → (π₁ t) ⇓ a
  B-Pi2  : ∀{A B t a b} → _⇓_ {A × B} t (vpair a b) → (π₂ t) ⇓ b

-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small B-True  = Nil
big-to-small B-False = Nil
big-to-small B-Zero  = Nil
big-to-small (B-IfTrue p p₁)   = map-steps E-If-If (big-to-small p) ++ [ E-If-True ] ++ big-to-small p₁
big-to-small (B-IfFalse p p₁)  = map-steps E-If-If (big-to-small p) ++ [ E-If-False ] ++ big-to-small p₁
big-to-small (B-IsZeroZero p)  = map-steps E-IsZero (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small (B-IsZeroFalse {n = n} p) = map-steps E-IsZero (big-to-small p) ++ [ E-IsZeroSucc {v = vnat n} ]
big-to-small (B-Succ p)        = map-steps E-Succ (big-to-small p)
big-to-small {v = vpair va vb} (B-Pair p p₁)     
  = map-steps E-Pair1 (big-to-small p) 
    ++ map-steps (E-Pair2 {vt = va} refl) (big-to-small p₁)
big-to-small {v = v} (B-Pi1 {b = b} p) = map-steps E-Pi1-tr (big-to-small p) ++ [ E-Pi1 {vt = v} {vu = b} refl refl ]
big-to-small {v = v} (B-Pi2 {a = a} p) = map-steps E-Pi2-tr (big-to-small p) ++ [ E-Pi2 {vt = a} {vu = v} refl refl ]

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = B-True
value-to-value vfalse = B-False
value-to-value (vnat Zero) = B-Zero
value-to-value (vnat (Succ x)) = B-Succ (value-to-value (vnat x))
value-to-value (vpair v v₁) = B-Pair (value-to-value v) (value-to-value v₁)


if-is-not-value : {ty : Type}{t e : Term ty}{c : Term BOOL}{v : Value ty}
                → (if c then t else e) == ⌜ v ⌝ → Empty
if-is-not-value {v = vtrue} ()
if-is-not-value {v = vfalse} ()
if-is-not-value {v = vnat Zero} ()
if-is-not-value {v = vnat (Succ x)} ()
if-is-not-value {v = vpair v v₁} ()

-- This function looks horrible. Yet, I don't know if there is a more elegant approach to it.
-- After all, we need to show that regardless of the step we took, it can be pre-prended
-- to a big-step.
prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step ._ .true .vtrue E-If-True B-True = B-IfTrue B-True B-True
prepend-step ._ .true .vtrue E-If-False B-True = B-IfFalse B-False B-True
prepend-step .(iszero zero) .true .vtrue E-IsZeroZero B-True = B-IsZeroZero B-Zero
prepend-step ._ .true .vtrue (E-Pi1 {vu = vu} x x₁) B-True 
  rewrite x₁ = B-Pi1 (B-Pair B-True (value-to-value vu))
prepend-step ._ .true .vtrue (E-Pi2 {vt = vt} x x₁) B-True 
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) B-True)
prepend-step ._ .false .vfalse E-If-True B-False = B-IfTrue B-True B-False
prepend-step ._ .false .vfalse E-If-False B-False = B-IfFalse B-False B-False
prepend-step ._ .false .vfalse (E-IsZeroSucc {v = vnat n}) B-False = B-IsZeroFalse (B-Succ (value-to-value (vnat n)))
prepend-step ._ .false .vfalse (E-Pi1 {vu = vu} x x₁) B-False 
  rewrite x₁ = B-Pi1 (B-Pair B-False (value-to-value vu))
prepend-step ._ .false .vfalse (E-Pi2 {vt = vt} x x₁) B-False
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) B-False)
prepend-step ._ .zero .(vnat Zero) E-If-True B-Zero = B-IfTrue B-True B-Zero
prepend-step ._ .zero .(vnat Zero) E-If-False B-Zero = B-IfFalse B-False B-Zero
prepend-step ._ .zero .(vnat Zero) (E-Pi1 {vu = vu} x x₁) B-Zero
  rewrite x₁ = B-Pi1 (B-Pair B-Zero (value-to-value vu))
prepend-step ._ .zero .(vnat Zero) (E-Pi2 {vt = vt} x x₁) B-Zero 
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) B-Zero)
prepend-step ._ ._ v E-If-True (B-IfTrue r r₁) = B-IfTrue B-True (B-IfTrue r r₁)
prepend-step ._ ._ v E-If-False (B-IfTrue r r₁) = B-IfFalse B-False (B-IfTrue r r₁)
prepend-step ._ ._ v (E-If-If {t1 = t1} {t1' = t1'} s) (B-IfTrue r r₁) = B-IfTrue (prepend-step t1 t1' vtrue s r) r₁
prepend-step ._ ._ v (E-Pi1 {vu = vu} x x₁) (B-IfTrue r r₁) 
  rewrite x₁ = B-Pi1 (B-Pair (B-IfTrue r r₁) (value-to-value vu))
prepend-step ._ ._ v (E-Pi2 {vt = vt} x x₁) (B-IfTrue r r₁) 
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) (B-IfTrue r r₁))
prepend-step ._ ._ v E-If-True (B-IfFalse r r₁) = B-IfTrue B-True (B-IfFalse r r₁)
prepend-step ._ ._ v E-If-False (B-IfFalse r r₁) = B-IfFalse B-False (B-IfFalse r r₁)
prepend-step ._ ._ v (E-If-If {t1 = t1} {t1' = t1'} s) (B-IfFalse r r₁) = B-IfFalse (prepend-step t1 t1' vfalse s r) r₁
prepend-step ._ ._ v (E-Pi1 {vt = vt} x x₁) (B-IfFalse r r₁) 
  rewrite x₁ = contradiction (if-is-not-value {v = vt} x)
prepend-step ._ ._ v (E-Pi2 {vu = vu} x x₁) (B-IfFalse r r₁) 
  rewrite x = contradiction (if-is-not-value {v = vu} x₁)
prepend-step ._ ._ .vtrue E-If-True (B-IsZeroZero r) = B-IfTrue B-True (B-IsZeroZero r)
prepend-step ._ ._ .vtrue E-If-False (B-IsZeroZero r) = B-IfFalse B-False (B-IsZeroZero r)
prepend-step ._ ._ .vtrue (E-IsZero {t = t} {t' = t'} s) (B-IsZeroZero r) = B-IsZeroZero (prepend-step t t' (vnat Zero) s r)
prepend-step ._ ._ .vtrue (E-Pi1 {vu = vu} x x₁) (B-IsZeroZero r) 
  rewrite x₁ = B-Pi1 (B-Pair (B-IsZeroZero r) (value-to-value vu))
prepend-step ._ ._ .vtrue (E-Pi2 {vt = vt} x x₁) (B-IsZeroZero r) 
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) (B-IsZeroZero r))
prepend-step ._ ._ .vfalse E-If-True (B-IsZeroFalse r) = B-IfTrue B-True (B-IsZeroFalse r)
prepend-step ._ ._ .vfalse E-If-False (B-IsZeroFalse r) = B-IfFalse B-False (B-IsZeroFalse r)
prepend-step ._ ._ .vfalse (E-IsZero {t = t} {t' = t'} s) (B-IsZeroFalse {n = n} r) 
  = B-IsZeroFalse (prepend-step t t' (vnat (Succ n)) s r)
prepend-step ._ ._ .vfalse (E-Pi1 {vu = vu} x x₁) (B-IsZeroFalse r) 
  rewrite x₁ = B-Pi1 (B-Pair (B-IsZeroFalse r) (value-to-value vu))
prepend-step ._ ._ .vfalse (E-Pi2 {vt = vt}  x x₁) (B-IsZeroFalse r) 
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) (B-IsZeroFalse r))
prepend-step ._ ._ ._ E-If-True (B-Succ r) = B-IfTrue B-True (B-Succ r)
prepend-step ._ ._ ._ E-If-False (B-Succ r) = B-IfFalse B-False (B-Succ r)
prepend-step ._ ._ ._ (E-Succ {t = t} {t' = t'} s) (B-Succ {n = n} r) = B-Succ (prepend-step t t' (vnat n) s r)
prepend-step ._ ._ ._ (E-Pi1 {vu = vu} x x₁) (B-Succ r) 
  rewrite x₁ = B-Pi1 (B-Pair (B-Succ r) (value-to-value vu))
prepend-step ._ ._ ._ (E-Pi2 {vt = vt} x x₁) (B-Succ r)
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) (B-Succ r))
prepend-step ._ ._ ._ E-If-True (B-Pair r r₁) = B-IfTrue B-True (B-Pair r r₁)
prepend-step ._ ._ ._ E-If-False (B-Pair r r₁) = B-IfFalse B-False (B-Pair r r₁)
prepend-step ._ ._ ._ (E-Pi1 {vu = vu} x x₁) (B-Pair r r₁) 
  rewrite x₁ = B-Pi1 (B-Pair (B-Pair r r₁) (value-to-value vu))
prepend-step ._ ._ ._ (E-Pi2 {vt = vt} x x₁) (B-Pair r r₁)
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) (B-Pair r r₁))
prepend-step ._ ._ ._ (E-Pair1 {t = t} {t' = t'} s) (B-Pair {vt = vt} r r₁) = B-Pair (prepend-step t t' vt s r) r₁
prepend-step ._ ._ ._ (E-Pair2 {u = u} {u' = u'} x s) (B-Pair {vu = vu} r r₁) = B-Pair r (prepend-step u u' vu s r₁)
prepend-step ._ ._ v E-If-True (B-Pi1 r) = B-IfTrue B-True (B-Pi1 r)
prepend-step ._ ._ v E-If-False (B-Pi1 r) = B-IfFalse B-False (B-Pi1 r)
prepend-step ._ ._ v (E-Pi1 {vu = vu} x x₁) (B-Pi1 r) 
  rewrite x₁ = B-Pi1 (B-Pair (B-Pi1 r) (value-to-value vu))
prepend-step ._ ._ v (E-Pi2 {vt = vt} x x₁) (B-Pi1 r) 
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) (B-Pi1 r))
prepend-step ._ ._ v (E-Pi1-tr {t = t} {t' = t'} s) (B-Pi1 {b = b} r) = B-Pi1 (prepend-step t t' (vpair v b) s r)
prepend-step ._ ._ v E-If-True (B-Pi2 r) = B-IfTrue B-True (B-Pi2 r)
prepend-step ._ ._ v E-If-False (B-Pi2 r) = B-IfFalse B-False (B-Pi2 r)
prepend-step ._ ._ v (E-Pi1 {vu = vu} x x₁) (B-Pi2 r) 
  rewrite x₁ = B-Pi1 (B-Pair (B-Pi2 r) (value-to-value vu))
prepend-step ._ ._ v (E-Pi2 {vt = vt} x x₁) (B-Pi2 r) 
  rewrite x = B-Pi2 (B-Pair (value-to-value vt) (B-Pi2 r))
prepend-step ._ ._ v (E-Pi2-tr {t = t} {t' = t'} s) (B-Pi2 {a = a} r) = B-Pi2 (prepend-step t t' (vpair a v) s r)

small-to-big : {ty : Type} -> (t : Term ty) -> (v : Value ty) → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big .(⌜ v ⌝) v Nil = value-to-value v
small-to-big t v (Cons {t2 = t2} x steps) = prepend-step t t2 v x (small-to-big t2 v steps)


--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

subst : {A : Set}(P : A → Set){a₁ a₂ : A} → a₁ == a₂ → P a₁ → P a₂
subst P refl pa = pa

eval : {ty : Type}(t : Term ty) → Σ (Value ty) (λ v → ⟦ t ⟧ == v)
eval t = ⟦ t ⟧ , refl

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = B-True
⇓-complete false = B-False
⇓-complete (if t then t₁ else t₂) with ⇓-complete t | eval t
...| r | vtrue , prf  rewrite prf = B-IfTrue r (⇓-complete t₁)
...| r | vfalse , prf rewrite prf = B-IfFalse r (⇓-complete t₂)
⇓-complete zero = B-Zero
⇓-complete (succ t) with ⇓-complete t | eval t
...| r | vnat x , prf rewrite prf = B-Succ r
⇓-complete (iszero t) with ⇓-complete t | eval t
...| r | vnat Zero     , prf rewrite prf = B-IsZeroZero r
...| r | vnat (Succ n) , prf rewrite prf = B-IsZeroFalse r
⇓-complete (π₁ t) with ⇓-complete t | eval t
...| r | vpair va vb , prf rewrite prf = B-Pi1 r
⇓-complete (π₂ t) with ⇓-complete t | eval t
...| r | vpair va vb , prf rewrite prf = B-Pi2 r
⇓-complete < t , u > with ⇓-complete t | eval t
...| rt | vt , tprf with ⇓-complete u | eval u
...| ru | vu , uprf rewrite tprf | uprf = B-Pair rt ru

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → ⟦ t ⟧ == v
⇓-sound true .vtrue B-True = refl
⇓-sound false .vfalse B-False = refl
⇓-sound (if t then t₁ else t₂) v (B-IfTrue p p₁)
  rewrite (⇓-sound t vtrue p) = ⇓-sound t₁ v p₁
⇓-sound (if t then t₁ else t₂) v (B-IfFalse p p₁)
  rewrite (⇓-sound t vfalse p) = ⇓-sound t₂ v p₁
⇓-sound zero .(vnat Zero) B-Zero = refl
⇓-sound (succ t) .(vnat (Succ n)) (B-Succ {n = n} p) 
  rewrite (⇓-sound t (vnat n) p) = refl
⇓-sound (iszero t) .vtrue (B-IsZeroZero p) 
  rewrite (⇓-sound t (vnat Zero) p) = refl
⇓-sound (iszero t) .vfalse (B-IsZeroFalse {n = n} p) 
  rewrite (⇓-sound t (vnat (Succ n)) p) = refl
⇓-sound (π₁ t) v (B-Pi1 {b = b} p) 
  rewrite (⇓-sound t (vpair v b) p) = refl
⇓-sound (π₂ t) v (B-Pi2 {a = a} p)
  rewrite (⇓-sound t (vpair a v) p) = refl
⇓-sound < t , u > ._ (B-Pair {vt = vt} {vu = vu} pt pu) 
  rewrite (⇓-sound t vt pt)
        | (⇓-sound u vu pu) = refl

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
