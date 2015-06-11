
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
  TUPLE : Type → Type → Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL 
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  _,_           : {ty1 ty2 : Type} → Term ty1 → Term ty2 → Term (TUPLE ty1 ty2)
  fst           : {ty1 ty2 : Type} → Term (TUPLE ty1 ty2) → Term ty1
  snd           : {ty1 ty2 : Type} → Term (TUPLE ty1 ty2) → Term ty2


-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT
  vtuple : {ty1 ty2 : Type} → Value ty1 → Value ty2 → Value (TUPLE ty1 ty2)

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
-- And a new
⌜ vnat k ⌝ = natTerm k
⌜ vtuple v1 v2 ⌝ = ⌜ v1 ⌝ , ⌜ v2 ⌝


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
⟦ t1 , t2 ⟧ = vtuple ⟦ t1 ⟧ ⟦ t2 ⟧
⟦ fst t ⟧ with ⟦ t ⟧
⟦ fst t ⟧ | vtuple x x₁ = x
⟦ snd t ⟧ with ⟦ t ⟧
⟦ snd t ⟧ | vtuple x x₁ = x₁


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
  E-Tup1 : forall {ty1 ty2}{t1 t1' : Term ty1}{t2 : Term ty2} → Step t1 t1' → Step (t1 , t2) (t1' , t2)
  E-Tup2 : forall {ty1 ty2}{t1 : Term ty1}{t2 t2' : Term ty2} → Step t2 t2' → Step (t1 , t2) (t1 , t2')
  E-Fst : forall {ty1 ty2} → (t1 : Term ty1)(t2 : Term ty2) → (t : Term (TUPLE ty1 ty2)) → Step (fst t) t1
  E-Snd : forall {ty1 ty2} → (t1 : Term ty1)(t2 : Term ty2) → (t : Term (TUPLE ty1 ty2)) → Step (snd t) t2

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep (vtuple v v₁) t step with valuesDoNotStep v | valuesDoNotStep v₁
valuesDoNotStep (vtuple v v₁) .(t1' , ⌜ v₁ ⌝) (E-Tup1 {_} {_} {.(⌜ v ⌝)} {t1'} step) | p | _ = p t1' step
valuesDoNotStep (vtuple v v₁) .(⌜ v ⌝ , t2') (E-Tup2 {_} {_} {.(⌜ v ⌝)} {.(⌜ v₁ ⌝)} {t2'} step) | _ | p = p t2' step

-- Steps are deterministic: the same term can not be evaluated in more than one manner.
tupleReflL : ‌∀{ty1 ty2} → {t1 t1' : Term ty1}{t2 : Term ty2} → t1 == t1' → (t1 , t2) == (t1' , t2)
tupleReflL refl = refl

tupleReflR : ‌∀{ty1 ty2} → {t1 : Term ty1}{t2 t2' : Term ty2} → t2 == t2' → (t1 , t2) == (t1 , t2')
tupleReflR refl = refl


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
deterministic (E-Tup1 s1) (E-Tup1 s2) = tupleReflL (deterministic s1 s2)
deterministic (E-Tup1 s1) (E-Tup2 s2) = deterministic (E-Tup1 s1) (E-Tup2 s2)
deterministic (E-Tup2 s1) (E-Tup1 s2) = deterministic (E-Tup2 s1) (E-Tup1 s2)
deterministic (E-Tup2 s1) (E-Tup2 s2) = tupleReflR (deterministic s1 s2)
deterministic {ty} {.(fst t)} {t₁} {t₂} (E-Fst .t₁ t2 t) (E-Fst .t₂ t3 .t) = deterministic (E-Fst t₁ t3 t) (E-Fst t₂ t3 t)
deterministic {ty} {.(snd t)} {t₁} {t₂} (E-Snd t1 .t₁ t) (E-Snd t2 .t₂ .t) = deterministic (E-Snd t2 t₁ t) (E-Snd t2 t₂ t)

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
  if-reduces (fst p) t2 t3 = Reduces (E-If-If (E-Fst (fst p) (snd p) p))
  if-reduces (snd p) t2 t3 = Reduces (E-If-If (E-Snd (fst p) (snd p) p))

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst t) = Reduces (E-IsZero (E-Fst zero (snd t) t))
  iszero-reduces (snd t) = Reduces (E-IsZero (E-Snd (fst t) zero t))

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (t , t₁) nf = normal-forms-are-values (t , t₁) nf
  normal-forms-are-values (fst t) nf = contradiction (nf (Reduces (E-Fst (fst t) (snd t) t)))
  normal-forms-are-values (snd t) nf = contradiction (nf (Reduces (E-Snd (fst t) (snd t) t)))

  values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
  values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

  lemma : (t : Term NAT) -> (Red t -> Empty) -> Red (succ t) -> Empty
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  lemma' : ∀{ty1 ty2}{t₁ : Term ty1}{t₂ : Term ty2} → NF t₁ → NF t₂ → NF (t₁ , t₂)
  lemma' n n₁ (Reduces (E-Tup1 x)) = n (Reduces x)
  lemma' n n₁ (Reduces (E-Tup2 x)) = n₁ (Reduces x)

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
  progress (t , t₁) with progress t | progress t₁
  progress (t , t₁) | Left x | Left x₁ = Left (lemma' x x₁)
  progress (t , t₁) | Left x | Right (Reduces x₁) = Right (Reduces (E-Tup2 x₁))
  progress (t , t₁) | Right (Reduces x) | q = Right (Reduces (E-Tup1 x))
  progress (fst t) = Right (Reduces (E-Fst (fst t) (snd t) t))
  progress (snd t) = Right (Reduces (E-Snd (fst t) (snd t) t))

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

E-Tuple-Steps : ∀{ty1 ty2}{t1' t2'}{t1 : Term ty1}{t2 : Term ty2} → Steps t1 t1' → Steps t2 t2' → Steps (t1 , t2) (t1' , t2')
E-Tuple-Steps Nil Nil = Nil
E-Tuple-Steps Nil (Cons x s2) = Cons (E-Tup2 x) (E-Tuple-Steps Nil s2)
E-Tuple-Steps (Cons x s1) s2 = Cons (E-Tup1 x) (E-Tuple-Steps s1 s2)

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
termination (iszero (fst t)) | terminates v x = terminates vtrue ([ E-IsZero (E-Fst zero (snd t) t)] ++ [ E-IsZeroZero ])
termination (iszero (snd t)) with termination t
termination (iszero (snd t)) | terminates v x = terminates vtrue ([ E-IsZero (E-Snd (fst t) zero t)] ++ [ E-IsZeroZero ])
termination (t , t₁) with termination t | termination t₁
termination (t , t₁) | terminates v x | terminates v₁ x₁ = terminates (vtuple v v₁) (E-Tuple-Steps x x₁) 
termination (fst t) with termination t
termination (fst t) | terminates (vtuple v v₁) x = terminates v [ E-Fst ⌜ v ⌝ (snd t) t ]
termination (snd t) with termination t
termination (snd t) | terminates (vtuple v v₁) x = terminates v₁ [ E-Snd (fst t) ⌜ v₁ ⌝ t ]

------------------------------------------------------------------------
-- Big-step semantics.

-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} → Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalIfTrue : ∀{ty : Type}{i}{t e : Term ty}{v : Value ty} → i ⇓ vtrue → t ⇓ v → if i then t else e ⇓ v
  EvalIfFalse : ∀{ty : Type}{i}{t e : Term ty}{v : Value ty} → i ⇓ vfalse → e ⇓ v → if i then t else e ⇓ v
  EvalZero : zero ⇓ vnat Zero
  EvalSucc : {n : Nat}{t : Term NAT} → t ⇓ vnat n → succ t ⇓ vnat (Succ n)
  EvalZeroZero : {t : Term NAT} → t ⇓ vnat Zero → iszero t ⇓ vtrue
  EvalZeroSucc : {t : Term NAT} → {n : Nat} → t ⇓ vnat (Succ n) → iszero t ⇓ vfalse
  EvalTuple : ∀{ty1 ty2}{t1 : Term ty1}{t2 : Term ty2}{v1 : Value ty1}{v2 : Value ty2}
    → t1 ⇓ v1 → t2 ⇓ v2 → (t1 , t2) ⇓ vtuple v1 v2 
  EvalFst : ∀{ty1 ty2 v2}{tup : Term (TUPLE ty1 ty2)}{v1 : Value ty1} → tup ⇓ vtuple v1 v2  → fst tup ⇓ v1
  EvalSnd : ∀{ty1 ty2 v1}{tup : Term (TUPLE ty1 ty2)}{v2 : Value ty2} → tup ⇓ vtuple v1 v2  → snd tup ⇓ v2
  
-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small {.BOOL} {true} {vtrue} EvalTrue = Nil
big-to-small {.BOOL} {false} {vfalse} EvalFalse = Nil
big-to-small {.BOOL} {iszero t} {vtrue} (EvalZeroZero p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small {.BOOL} {iszero t} {vfalse} (EvalZeroSucc {.t}{n} p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroSucc {vnat n} ]
big-to-small {_} {if t then t₁ else t₂} (EvalIfTrue p p₁) = E-If-Steps (big-to-small p) ++ [ E-If-True ] ++ big-to-small p₁
big-to-small {_} {if t then t₁ else t₂} (EvalIfFalse p p₁) = E-If-Steps (big-to-small p) ++ [ E-If-False ] ++ big-to-small p₁
big-to-small {.NAT} {zero} {vnat .Zero} EvalZero = Nil
big-to-small {.NAT} {succ t} {vnat (Succ x)} (EvalSucc p) = E-Succ-Steps (big-to-small p)
big-to-small {.(TUPLE _ _)} {t , t₁} {vtuple v v₁} (EvalTuple p p₁) = E-Tuple-Steps (big-to-small p) (big-to-small p₁)
big-to-small {_} {fst t} {v} p = [ E-Fst ⌜ v ⌝ (snd t) t ]
big-to-small {_} {snd t} {v} p = [ E-Snd (fst t) ⌜ v ⌝ t ]

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = EvalTrue
value-to-value vfalse = EvalFalse
value-to-value (vnat Zero) = EvalZero
value-to-value (vnat (Succ x)) = EvalSucc (value-to-value (vnat x))
value-to-value (vtuple v v₁) = EvalTuple (value-to-value v) (value-to-value v₁)

prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step (if true then ._ else _) _ _ E-If-True p = EvalIfTrue EvalTrue p
prepend-step (if false then _ else ._) _ _ E-If-False p = EvalIfFalse EvalFalse p
prepend-step (if t then ._ else ._) (if t' then _ else _) _ (E-If-If p) (EvalIfTrue p1 p2) = EvalIfTrue (prepend-step t t' vtrue p p1) p2
prepend-step (if t then ._ else ._) (if t' then _ else _) _ (E-If-If p) (EvalIfFalse p1 p2) = EvalIfFalse (prepend-step t t' vfalse p p1) p2
prepend-step .(iszero zero) .true .vtrue E-IsZeroZero EvalTrue = EvalZeroZero EvalZero
prepend-step .(iszero (succ (natTerm x))) .false .vfalse (E-IsZeroSucc {vnat x}) EvalFalse = EvalZeroSucc (EvalSucc (value-to-value (vnat x)))
prepend-step .(succ t₁) .(succ t) .(vnat (Succ n)) (E-Succ {t₁} s) (EvalSucc {n} {t} p) = EvalSucc (prepend-step t₁ t (vnat n) s p)
prepend-step (iszero t) .(iszero t₁) .vtrue (E-IsZero s) (EvalZeroZero {t₁} p) = EvalZeroZero (prepend-step t t₁ (vnat Zero) s p)
prepend-step (iszero t) .(iszero t₁) .vfalse (E-IsZero s) (EvalZeroSucc {t₁} p) = EvalZeroSucc (prepend-step t t₁ (vnat (Succ _)) s p)
prepend-step (t , t₁) (t1' , .t₁) .(vtuple _ _) (E-Tup1 s) (EvalTuple p p₁) = EvalTuple (prepend-step t t1' _ s p) p₁
prepend-step (t , t₁) .(t , _) .(vtuple _ _) (E-Tup2 s) (EvalTuple p p₁) = EvalTuple p (prepend-step t₁ _ _ s p₁)
prepend-step (fst (if t then t₁ else t₂)) t' v (E-Fst .t' t2 .(if t then t₁ else t₂)) p = {!!}
prepend-step (fst (t , t₁)) t' v (E-Fst .t' t2 .(t , t₁)) p = {!!}
prepend-step (fst (fst t)) t' v (E-Fst .t' t2 .(fst t)) p = {!!}
prepend-step (fst (snd t)) t' v (E-Fst .t' t2 .(snd t)) p = {!!}
prepend-step (snd (t , t₁)) t' v (E-Snd t1 .t' .(t , t₁)) p = {!!}
prepend-step (snd t) t' v s p = {!!}

small-to-big : {ty : Type} -> {t : Term ty} -> {v : Value ty} → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big {ty}{t}{v} (Cons x s) = prepend-step t _ v x (small-to-big s)
small-to-big {BOOL} {.true} {vtrue} Nil = EvalTrue
small-to-big {BOOL} {.false} {vfalse} Nil = EvalFalse
small-to-big {NAT} {.zero} {vnat Zero} Nil = EvalZero
small-to-big {NAT} {.(succ (natTerm x))} {vnat (Succ x)} Nil = EvalSucc (small-to-big Nil)
small-to-big {TUPLE ty ty₁} {.(⌜ v ⌝ , ⌜ v₁ ⌝)} {vtuple v v₁} Nil = EvalTuple (small-to-big Nil) (small-to-big Nil)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.

⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t₁ else t₂) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t₁ else t₂) | vtrue | p = EvalIfTrue p (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | vfalse | p = EvalIfFalse p (⇓-complete t₂)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | p = EvalSucc p
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | p = EvalZeroZero p
⇓-complete (iszero t) | vnat (Succ x) | p = EvalZeroSucc p
⇓-complete (t , t₁) = EvalTuple (⇓-complete t) (⇓-complete t₁)
⇓-complete (fst t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (fst t) | vtuple p p₁ | q = EvalFst q
⇓-complete (snd t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (snd t) | vtuple p p₁ | q = EvalSnd q

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound true vtrue EvalTrue = refl
⇓-sound false vfalse EvalFalse = refl
⇓-sound (if t then t₁ else t₂) v (EvalIfTrue p p₁) with ⟦ t ⟧ | ⇓-sound t vtrue p
⇓-sound (if t then t₁ else t₂) v (EvalIfTrue p p₁) | .vtrue | refl = ⇓-sound t₁ v p₁
⇓-sound (if t then t₁ else t₂) v (EvalIfFalse p p₁) with ⟦ t ⟧ | ⇓-sound t vfalse p
⇓-sound (if t then t₁ else t₂) v (EvalIfFalse p p₁) | .vfalse | refl = ⇓-sound t₂ v p₁
⇓-sound zero (vnat .Zero) EvalZero = refl
⇓-sound (succ t) (vnat .(Succ n)) (EvalSucc {n} p) with ⟦ t ⟧ | ⇓-sound t (vnat n) p
⇓-sound (succ t) (vnat .(Succ n)) (EvalSucc {n} p) | vnat ._ | refl = refl
⇓-sound (iszero t) .vtrue (EvalZeroZero p) with ⟦ t ⟧ | ⇓-sound t (vnat Zero) p
⇓-sound (iszero t) .vtrue (EvalZeroZero p) | vnat .Zero | refl = refl
⇓-sound (iszero t) .vfalse (EvalZeroSucc p) with ⟦ t ⟧ | ⇓-sound t (vnat _) p
⇓-sound (iszero t) .vfalse (EvalZeroSucc {.t} {n} p) | vnat .(Succ n) | refl = refl
⇓-sound (t , t₁) .(vtuple v1 v2) (EvalTuple {ty1} {ty2} {.t} {.t₁} {v1} {v2} p p₁) with ⇓-sound t v1 p | ⇓-sound t₁ v2 p₁
⇓-sound (_ , t₁) .(vtuple ⟦ t₁ ⟧ ⟦ t ⟧) (EvalTuple {_} {t} p p₁) | refl | refl = refl
⇓-sound (fst t) v p with ⟦ t ⟧ | ⇓-sound t {!!} {!!}
⇓-sound (fst (if t then t₁ else t₂)) v (EvalFst p) | vtuple q q₁ | r = {!!}
⇓-sound (fst (t , t₁)) v (EvalFst (EvalTuple p p₁)) | vtuple q q₁ | r = {!!}
⇓-sound (fst (fst t)) v (EvalFst p) | vtuple q q₁ | r = {!!}
⇓-sound (fst (snd t)) v (EvalFst p) | vtuple q q₁ | r = {!!}
⇓-sound (snd t) v p = {!!}


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
