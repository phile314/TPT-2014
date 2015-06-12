
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
  PAIR : Type -> Type -> Type

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b


-- Our Term language
data Term : Type -> Set where
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  pair          : {ty ty' : Type} -> (a : Term ty) -> (b : Term ty') -> Term (PAIR ty ty')
  fst           : {ty ty' : Type} -> Term (PAIR ty ty') -> Term ty
  snd           : {ty ty' : Type} -> Term (PAIR ty ty') -> Term ty'



-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT
  vpair : {ty ty' : Type} -> (a : Value ty) -> (b : Value ty') -> Value (PAIR ty ty')


natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
⌜ vpair a b ⌝ = pair ⌜ a ⌝ ⌜ b ⌝


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
⟦ pair a b ⟧ = vpair ⟦ a ⟧ ⟦ b ⟧
⟦ fst p ⟧ with ⟦ p ⟧
⟦ fst p ⟧ | vpair a b = a
⟦ snd p ⟧ with ⟦ p ⟧
⟦ snd p ⟧ | vpair a b = b

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
  E-Fst : forall {ty ty' : Type} {t : Term (PAIR ty ty')} {t' : Term ty} -> Step (fst t) t'
  E-Snd : forall {ty ty' : Type} {t : Term (PAIR ty ty')} {t' : Term ty'} -> Step (snd t) t'
  E-Pair-Fst : forall {ty ty' : Type} {a a' : Term ty} {b : Term ty'} -> Step a a' -> Step (pair a b) (pair a' b)
  E-Pair-Snd : forall {ty ty' : Type} {a : Term ty} {b b' : Term ty'} -> Step b b' -> Step (pair a b) (pair a b')

-- I'm quite confident that the tuple related Step constructors are incorrect, as I have been
-- unable to define some of their cases in the following functions. Unfortunately, I have
-- no idea what is wrong about them.

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep (vpair a b) t step = ?


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
  lemma (vnat x) (fst p) ()
  lemma (vnat x) (snd p) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ steps1)
deterministic (E-IsZero steps1) (E-IsZero steps2) = cong iszero (deterministic steps1 steps2)
deterministic E-Fst E-Fst = {! refl !}
deterministic E-Snd E-Snd = {! refl  !}
deterministic (E-Pair-Fst p) step = cong {! !} {!   !}
deterministic (E-Pair-Snd p) step = ?

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
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t) t2 t3 with iszero-reduces t
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (fst t) t2 t3 with fst-reduces t
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (snd t) t2 t3 with snd-reduces t
  ... | Reduces x = Reduces (E-If-If x)


  fst-reduces : {ty ty' : Type} -> (t : Term (PAIR ty ty')) -> Red (fst t)
  fst-reduces t = Reduces E-Fst

  snd-reduces : {ty ty' : Type} -> (t : Term (PAIR ty ty')) -> Red (snd t)
  snd-reduces t = Reduces E-Snd

  iszero-reduces : (t : Term NAT) -> Red (iszero t)
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst p) = Reduces (E-IsZero E-Fst)
  iszero-reduces (snd p) = Reduces (E-IsZero E-Snd)

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (fst p) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (snd p) nf (Reduces x) = nf (Reduces (E-Succ x))

  fst-nf : {ty ty' : Type} -> {a : Term ty} -> (p : Term (PAIR ty ty')) -> NF p -> NF a
  fst-nf (if p then p2 else p3) nf x with if-reduces p p2 p3
  ... | Reduces step = nf (Reduces step)
  fst-nf (pair p p2) nf x = nf (Reduces {!   !})
  fst-nf (fst p) nf (Reduces x) = nf (Reduces E-Fst)
  fst-nf (snd p) nf x = nf (Reduces E-Snd)

  snd-nf : {ty ty' : Type} -> {b : Term ty'} -> (p : Term (PAIR ty ty')) -> NF p -> NF b
  snd-nf (if t then t2 else t3) nf x with if-reduces t t2 t3
  ... | Reduces step = nf (Reduces step)
  snd-nf (pair t t2) nf (Reduces x) = nf (Reduces {!   !})
  snd-nf (fst t) nf x = nf (Reduces E-Fst)
  snd-nf (snd t) nf x = nf (Reduces E-Snd)

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (pair a b) nf with normal-forms-are-values a (fst-nf (pair a b) nf) | normal-forms-are-values b (snd-nf (pair a b) nf)
  normal-forms-are-values (pair .(⌜ v ⌝) .(⌜ v2 ⌝)) nf | is-value v | is-value v2 = is-value (vpair v v2)
  normal-forms-are-values (fst p) nf = contradiction (nf (fst-reduces p))
  normal-forms-are-values (snd p) nf = contradiction (nf (snd-reduces p))

  values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
  values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

  lemma : (t : Term NAT) -> (Red t -> Empty) -> Red (succ t) -> Empty
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  lemma2 : {ty ty' : Type} -> {a : Term ty} {b : Term ty'} -> (p : Term (PAIR ty ty')) -> NF a -> NF b -> NF p
  lemma2 p nf nf2 (Reduces x) = nf (Reduces {!   !})

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
  progress (pair a b) with progress a | progress b
  progress (pair a b) | Left x | Left y = Left (values-are-normal-forms (pair a b) (normal-forms-are-values (pair a b) (lemma2 (pair a b) x y)))
  progress (pair a b) | Left x | Right y = Right (Reduces {!   !})
  progress (pair a b) | Right x | y = {!   !}
  progress (fst p) = ?
  progress (snd p) = ?


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

E-Fst-Steps : {ty ty' : Type} {a a' : Term ty} {b : Term ty'} -> Steps a a' -> Steps (pair a b) (pair a' b)
E-Fst-Steps Nil = Nil
E-Fst-Steps (Cons x steps) = Cons (E-Pair-Fst x) (E-Fst-Steps steps)

E-Snd-Steps : {ty ty' : Type} {a : Term ty} {b b' : Term ty'} -> Steps b b' -> Steps (pair a b) (pair a b')
E-Snd-Steps Nil = Nil
E-Snd-Steps (Cons x steps) = Cons (E-Pair-Snd x) (E-Snd-Steps steps)


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
termination (iszero (fst t)) = ?
termination (iszero (snd t)) = ?
termination (iszero zero) = terminates vtrue (Cons E-IsZeroZero Nil)
termination (iszero (succ t)) with termination t
termination (iszero (succ t)) | terminates v x =
   terminates vfalse (E-IsZero-Steps (E-Succ-Steps x) ++ [ E-IsZeroSucc {v} ])
termination (pair a b) = ?
termination (fst p) = ?
termination (snd p) = ?

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalZero : zero ⇓ vnat Zero
  EvalSucc : forall {s r} -> s ⇓ vnat r -> succ s ⇓ vsucc (vnat r)
  EvalIsZeroTrue : forall {t} -> t ⇓ vnat Zero -> iszero t ⇓ vtrue
  EvalIsZeroFalse : forall {t k} -> t ⇓ vnat (Succ k) -> iszero t ⇓ vfalse
  EvalIfTrue : forall {ty} {c} {t e : Term ty} {v : Value ty} -> c ⇓ vtrue -> t ⇓ v -> (if c then t else e) ⇓ v
  EvalIfFalse : forall {ty} {c} {t e : Term ty} {v : Value ty} -> c ⇓ vfalse -> e ⇓ v -> (if c then t else e) ⇓ v
  EvalFst : forall {ty ty'} {a : Term ty} {b : Term ty'} {v : Value ty} -> a ⇓ v -> (fst (pair a b)) ⇓ v
  EvalSnd : forall {ty ty'} {a : Term ty} {b : Term ty'} {v : Value ty'} -> b ⇓ v -> (snd (pair a b)) ⇓ v

-- And also for these big step semantics, I'm quite confident that the tuple related constructors
-- are incorrect.

-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small EvalZero = Nil
big-to-small (EvalIsZeroTrue p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroFalse p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroSucc ]
big-to-small (EvalSucc {s} {r} p)  = E-Succ-Steps (big-to-small p)
big-to-small (EvalIfTrue p1 p2) = (E-If-Steps (big-to-small p1) ++ [ E-If-True ]) ++ big-to-small p2
big-to-small (EvalIfFalse p1 p2) = (E-If-Steps (big-to-small p1) ++ [ E-If-False ]) ++ big-to-small p2
big-to-small (EvalFst p) = {!   !}
big-to-small (EvalSnd p) = ?

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} {v : Value ty} -> ⌜ v ⌝ ⇓ v
value-to-value {v = vtrue} = EvalTrue
value-to-value {v = vfalse} = EvalFalse
value-to-value {v = (vnat Zero)} = EvalZero
value-to-value {v = (vnat (Succ x))} = EvalSucc (value-to-value {v = (vnat x)})
value-to-value {v = (vpair a b)} = ?


prepend-step : {ty : Type} -> {t : Term ty}  {t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True p = EvalIfTrue EvalTrue p
prepend-step E-If-False p = EvalIfFalse EvalFalse p
prepend-step (E-If-If step) (EvalIfTrue p1 p2) = EvalIfTrue (prepend-step step p1) p2
prepend-step (E-If-If step) (EvalIfFalse p1 p2) = EvalIfFalse (prepend-step step p1) p2
prepend-step (E-Succ step) (EvalSucc p) = EvalSucc (prepend-step step p)
prepend-step E-IsZeroZero EvalTrue = EvalIsZeroTrue EvalZero
prepend-step E-IsZeroSucc EvalFalse = EvalIsZeroFalse (EvalSucc (value-to-value))
prepend-step (E-IsZero step) (EvalIsZeroTrue p) = EvalIsZeroTrue (prepend-step step p)
prepend-step (E-IsZero step) (EvalIsZeroFalse p) = EvalIsZeroFalse (prepend-step step p)
prepend-step (E-Fst) p = ?
prepend-step (E-Snd) p = ?
prepend-step (E-Pair-Fst p) p2 = {!   !}
prepend-step (E-Pair-Snd p) p2 = ?


small-to-big : {ty : Type} -> {t : Term ty} -> (v : Value ty) → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big v Nil = value-to-value
small-to-big {t} v (Cons x steps) = prepend-step x (small-to-big v steps)


--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t1 else t2) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t1 else t2) | vtrue | y = EvalIfTrue y (⇓-complete t1)
⇓-complete (if t then t1 else t2) | vfalse | y = EvalIfFalse y (⇓-complete t2)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | y = EvalSucc y
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | y = EvalIsZeroTrue y
⇓-complete (iszero t) | vnat (Succ x) | y = EvalIsZeroFalse y
⇓-complete (pair a b) = ?
⇓-complete (fst p) = ?
⇓-complete (snd p) = ?


-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) {v : Value ty} → t ⇓ v → v == ⟦ t ⟧
⇓-sound true EvalTrue = refl
⇓-sound false EvalFalse = refl
⇓-sound (if t then t1 else t2) (EvalIfTrue p1 p2) with ⟦ t ⟧ | ⇓-sound t p1
⇓-sound (if t then t1 else t2) (EvalIfTrue p1 p2) | .vtrue | refl = ⇓-sound t1 p2
⇓-sound (if t then t1 else t2) (EvalIfFalse p1 p2) with ⟦ t ⟧ | ⇓-sound t p1
⇓-sound (if t then t1 else t2) (EvalIfFalse p1 p2) | .vfalse | refl = ⇓-sound t2 p2
⇓-sound zero EvalZero = refl
⇓-sound (succ s) (EvalSucc p) = cong vsucc (⇓-sound s p)
⇓-sound (iszero t) (EvalIsZeroTrue p) with ⟦ t ⟧ | ⇓-sound t p
⇓-sound (iszero t) (EvalIsZeroTrue p) | vnat .Zero | refl = refl
⇓-sound (iszero t) (EvalIsZeroFalse p) with ⟦ t ⟧ | ⇓-sound t p
⇓-sound (iszero t) (EvalIsZeroFalse p) | ._ | refl = refl
⇓-sound (pair a b) p = ?
⇓-sound (fst p) p2 = ?
⇓-sound (snd p) p2 = ?

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
