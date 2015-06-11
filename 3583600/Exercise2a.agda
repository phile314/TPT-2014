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

data Type  : Set where
  NAT : Type 
  BOOL : Type 
  _,_ : Type -> Type -> Type

-- Our Term language
data Term  : Type  -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : {ty : Type } -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  pair           : { ty ty1 : Type } -> (a : Term ty) -> (b : Term ty1) -> Term (ty , ty1)
  fst             : { ty ty1 : Type } -> (a : Term ( ty , ty1 )) ->  Term ty 
  snd           : { ty ty1 : Type } -> (a : Term ( ty , ty1 )) ->  Term ty1 

-- The set of atomic values within the language.
data Value : Type  -> Set where
  vtrue : Value BOOL 
  vfalse : Value BOOL
  -- And a new value
  vnat : Nat -> Value NAT
  vpair : {ty ty1 : Type } -> (a : Value ty) -> (b : Value ty1) -> Value (ty , ty1)

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- Associate each value with a term.
⌜_⌝ : {ty : Type } -> Value ty → Term ty
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
⟦ pair a b ⟧ = vpair ⟦ a ⟧ ⟦ b ⟧
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ k ⟧ = vsucc ⟦ k ⟧
⟦ iszero t ⟧ = viszero ⟦ t ⟧
⟦ fst x ⟧ with ⟦  x ⟧
⟦ fst x ⟧ | vpair p p₁ = p
⟦ snd x ⟧ with ⟦  x ⟧
⟦ snd x ⟧ | vpair p p₁ = p₁

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
  E-PairLeft : forall {ty ty1 : Type} {t t1 : Term ty} { v : Term ty1} -> Step t t1 -> Step (pair t v) (pair t1 v)
  E-PairRight :  {ty ty1 : Type} {t : Value ty} { v  v1 : Term ty1} -> Step v v1 -> Step (pair ⌜ t ⌝ v) (pair ⌜ t ⌝ v1)
--  E-PairRight :  {ty ty1 : Type} {t : Term ty} { v  v1 : Term ty1} -> Step v v1 -> Step (pair t v) (pair t v1)
  E-Fst : forall {ty ty1} {t v1 : Value ty} {t1 v2 : Value ty1} -> Step (fst (⌜ vpair t t1 ⌝)) ⌜ t ⌝
  E-Snd : forall {ty ty1} {t v1 : Term ty} {t1 v2 : Term ty1} -> Step (snd (pair t t1)) t1
--addsteps

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep (vpair a b) (if t then t₁ else t₂) ()
valuesDoNotStep (vpair a b) (pair c d) x = {!!}
valuesDoNotStep (vpair a b) (fst t) ()
valuesDoNotStep (vpair a b) (snd t) ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
  where
  lemma : (n : Nat) -> (t : Term NAT) -> Step (natTerm n) t -> Empty
  lemma Zero t ()
  lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step


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
  lemma (vnat x) (fst b) ()
  lemma (vnat x) (snd b) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ steps1)
deterministic (E-IsZero steps1) (E-IsZero steps2) = cong iszero (deterministic steps1 steps2)
deterministic (E-PairLeft {c} {d} {e} {f} {g} a) (E-PairLeft b) with deterministic a b
deterministic (E-PairLeft a) (E-PairLeft b) | refl = refl
deterministic (E-PairLeft a) (E-PairRight b) = {!!}
deterministic (E-PairRight a) b = {!b!}
deterministic E-Fst x = {!!} -- lemma zoals bij E-isZeroSucc {v}
deterministic E-Snd E-Snd = refl

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
  if-reduces (fst a) b c = {!!}
  if-reduces (snd a) b c = {!!}


  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst a) = {!!}
  iszero-reduces (snd a) = {!!}

  succ-nf : (k : Term NAT) -> NF (succ k) -> NF k
  succ-nf (if t1 then t2 else t3) nf x with if-reduces t1 t2 t3
  ... | Reduces step = nf (Reduces (E-Succ step))
  succ-nf zero nf (Reduces ())
  succ-nf (succ k) nf (Reduces x) = nf (Reduces (E-Succ x))
  succ-nf (fst a) b x = {!!}
  succ-nf (snd a) b x = {!!}
  
  fst-reduces : forall {ty ty1} ( t : Term ( ty , ty1 ) ) -> Red (fst ( t ) )
  fst-reduces (if a then a₁ else a₂) with if-reduces a a₁ a₂
  fst-reduces (if a then a₁ else a₂) | Reduces x = Reduces {!!}
  fst-reduces (pair a a₁) = {!!}
  fst-reduces (fst a) with fst-reduces a
  fst-reduces (fst ._) | Reduces E-Fst = Reduces {!  !} 
  fst-reduces (snd a) = {!!}

  pair-reduces : forall {ty ty1} (t : Term ty) -> (t1 : Term ty1) -> Red (pair t t1)
  pair-reduces a b = {!!}

  snd-reduces : forall {ty ty1} ( t : Term ( ty , ty1 ) ) -> Red (snd ( t ) )
  snd-reduces a = {!!}
--pair reduces
--fst reduces
--snd reduces

  -- A normal form must be a value.
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true nf = is-value vtrue
  normal-forms-are-values ( pair a b ) nf = contradiction (nf (pair-reduces a b))
  normal-forms-are-values false nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf  = is-value (vnat (Zero))
  normal-forms-are-values (succ k) nf with normal-forms-are-values k (succ-nf k nf)
  normal-forms-are-values (succ ._) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero v) nf = contradiction (nf (iszero-reduces v))
  normal-forms-are-values (fst a) b = contradiction (b (fst-reduces a))
  normal-forms-are-values (snd a) b = contradiction (b ( snd-reduces a))

  values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
  values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

  lemma : (t : Term NAT) -> (Red t -> Empty) -> Red (succ t) -> Empty
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true = Left (values-are-normal-forms true (is-value vtrue))
  progress false = Left (values-are-normal-forms false (is-value vfalse))
  progress (if t then t₁ else t₂) = Right (if-reduces t _ _)
  progress zero = Left (values-are-normal-forms zero (is-value (vnat (Zero))))
  progress (pair a b) with progress a | progress b
  progress (pair a b) | Left x | Left x₁ with normal-forms-are-values a x | normal-forms-are-values b x₁
  progress (pair .(⌜ v ⌝) .(⌜ v₁ ⌝)) | Left x | Left x₁ | is-value v | is-value v₁ = Left (values-are-normal-forms (pair ⌜ v ⌝ ⌜ v₁ ⌝ ) (is-value (vpair v v₁)))
  progress (pair a b) | Left x | Right (Reduces x₁) = Right (Reduces (E-PairLeft {! !}))
  progress (pair a b) | Right x | Left y = Right {!!} 
  progress (pair a b) | Right x | Right y = Right {!!} 
  progress (succ t) with progress t 
  progress (succ t) | Left x = Left (lemma t x)
  progress (succ t) | Right (Reduces step) = Right (Reduces (E-Succ step))
  progress (iszero t) with progress t
  progress (iszero t) | Left x with normal-forms-are-values t x
  progress (iszero .zero) | Left x₁ | is-value (vnat Zero) = Right (Reduces E-IsZeroZero)
  progress (iszero .(succ (natTerm x))) | Left x₁ | is-value (vnat (Succ x)) = 
    Right (Reduces (E-IsZeroSucc {vnat x}))
  progress (iszero t) | Right (Reduces step) = Right (Reduces (E-IsZero step))
  progress (fst x) = Right {!!}
  progress (snd x) = {!!}



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

E-Pair-Steps : ∀ {ty ty1} {t t' : Term ty} {v v1 : Term ty1} -> Steps t t' →  Steps v v1 ->      Steps (pair t v) ( pair t' v1 )
E-Pair-Steps Nil Nil = Nil
E-Pair-Steps Nil (Cons x y) = Cons ( E-PairRight x  ) ( E-Pair-Steps Nil y)
E-Pair-Steps (Cons x x₁) Nil = Cons  (E-PairLeft x) (E-Pair-Steps x₁ Nil)
E-Pair-Steps (Cons x x₁) (Cons x₂ y) = Cons (E-PairLeft x) (Cons (E-PairRight x₂) (E-Pair-Steps x₁ y))

E-Fst-Steps : forall {ty ty1} {t v1 : Value ty} {t1 v2 : Value ty1} -> Step (fst (⌜ vpair t t1 ⌝)) ⌜ t ⌝
E-Fst-Steps = E-Fst

-- All steps terminate.
termination : ∀ {ty} (t : Term ty) → t ⇓
termination true = terminates vtrue Nil
termination false = terminates vfalse Nil
termination (pair a b) with termination a | termination b
termination (pair a b) | terminates v x | terminates v₁ x₁ =  terminates (vpair v v₁) (E-Pair-Steps x x₁)
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
termination (iszero (if t then t₁ else t₂)) | terminates vtrue x₂ | terminates (vnat Zero) x₁ =   terminates vtrue 
    (E-IsZero-Steps (E-If-Steps x₂ ++ [ E-If-True ]) ++ E-IsZero-Steps x₁ ++ [ E-IsZeroZero ])
termination (iszero (if t then t₁ else t₂)) | terminates vtrue x₂ | terminates (vnat (Succ x)) x₁ =   terminates vfalse 
    (E-IsZero-Steps (E-If-Steps x₂ ++ [ E-If-True ]) ++ E-IsZero-Steps x₁ ++ [ E-IsZeroSucc {vnat x} ])
termination (iszero (if t then t₁ else t₂)) | terminates vfalse x with termination t₂
termination (iszero (if t then t₁ else t₂)) | terminates vfalse x₂ | terminates (vnat Zero) x₁ =   terminates vtrue 
    (E-IsZero-Steps (E-If-Steps x₂ ++ [ E-If-False ] ++ x₁) ++ [ E-IsZeroZero ])
termination (iszero (if t then t₁ else t₂)) | terminates vfalse x₂ | terminates (vnat (Succ x)) x₁ =  terminates vfalse 
     (E-IsZero-Steps (E-If-Steps x₂ ++ [ E-If-False ] ++ x₁) ++ [ E-IsZeroSucc {vnat x} ])
termination (iszero zero) = terminates vtrue (Cons E-IsZeroZero Nil)
termination (iszero (succ t)) with termination t
termination (iszero (succ t)) | terminates v x =  terminates vfalse (E-IsZero-Steps (E-Succ-Steps x) ++ [ E-IsZeroSucc {v} ])
termination (iszero (fst x)) = {!!}
termination (iszero (snd x)) = {!!}
termination (fst x) with termination x
termination (fst x) | terminates (vpair v v₁) y =  terminates v {!!} -- terminates v {! x !}  -- ?
termination (snd x) = {!!}

------------------------------------------------------------------------
-- Big-step semantics.


-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  B-True :   true ⇓ vtrue
  B-False :  false ⇓ vfalse
  B-Pair : {a b : Type} {c :  Term a}{d : Term b}  {e : Value a} {f : Value b} -> c ⇓ e -> d ⇓ f -> pair c d ⇓ vpair e f
  B-If-True : forall {c} -> {ty : Type } -> {t : Term ty} -> {e : Term ty} -> {v : Value ty} -> c ⇓ vtrue -> t ⇓ v -> if c then t else e ⇓ v 
  B-If-False  : forall {c} -> {ty : Type } -> {t : Term ty} -> {e : Term ty} -> {v : Value ty} -> c ⇓ vfalse -> e ⇓ v -> if c then t else e ⇓ v
  B-Zero :  zero ⇓ vnat Zero
  B-Succ : {k : Term NAT}  {f : Nat} -> k ⇓ vnat  f ->  succ k  ⇓ vnat (Succ f)
  B-IsZeroT : {t : Term NAT} -> t  ⇓ vnat Zero -> iszero t ⇓ vtrue
  B-IsZeroF :  {t : Term NAT} {x : Nat} -> t  ⇓ vnat (Succ x) -> iszero t ⇓ vfalse 
  B-Fst :  {a b : Type } -> {c : Term ( a , b )} {e : Value a} {f : Value b}  -> c ⇓ vpair e f -> fst c  ⇓ e 
  B-Snd :  {a b : Type } -> {c : Term ( a , b ) } { й : Value a } {f : Value b}  -> c ⇓ vpair й f -> snd c  ⇓ f 

-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small  B-True = Nil
big-to-small  B-False = Nil
big-to-small  (B-Succ k) = E-Succ-Steps (big-to-small k)
big-to-small (B-If-True x x₁) = E-If-Steps (big-to-small x) ++ [ E-If-True ] ++ big-to-small x₁
big-to-small (B-If-False x x₁) = E-If-Steps (big-to-small x) ++ [ E-If-False ] ++ big-to-small x₁
big-to-small B-Zero = Nil
big-to-small (B-Pair {c} {d} {e} {f} a b) =  E-Pair-Steps (big-to-small a) (big-to-small b)
big-to-small  (B-IsZeroT y) = E-IsZero-Steps (big-to-small y) ++ [ E-IsZeroZero ]
big-to-small  (B-IsZeroF {g} {f} y) = E-IsZero-Steps (big-to-small y) ++  [  E-IsZeroSucc {vnat f } ]
big-to-small (B-Fst x) = Cons {!!} {!!}
big-to-small (B-Snd x) = Cons {!!} {!!} --  Cons E-Snd (big-to-small x)

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = B-True
value-to-value vfalse = B-False
value-to-value (vpair a b) = B-Pair (value-to-value a) (value-to-value b) 
value-to-value (vnat Zero) = B-Zero
value-to-value (vnat (Succ x)) = B-Succ (value-to-value (vnat x))

prepend-step : {ty : Type} -> {t t' : Term ty} -> {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True B-True = B-If-True B-True B-True
prepend-step E-If-True B-False = B-If-True B-True B-False
prepend-step E-If-True (B-If-True b b₁) = B-If-True B-True (B-If-True b b₁)
prepend-step E-If-True (B-If-False b b₁) = B-If-True B-True (B-If-False b b₁)
prepend-step E-If-True B-Zero = B-If-True B-True B-Zero
prepend-step E-If-True (B-Succ b) = B-If-True B-True (B-Succ b)
prepend-step E-If-True (B-IsZeroT b) = B-If-True B-True (B-IsZeroT b) 
prepend-step E-If-True (B-IsZeroF b) = B-If-True B-True (B-IsZeroF b)
prepend-step E-If-False b = B-If-False B-False b
prepend-step (E-If-If a) (B-If-True b b₁) = B-If-True (prepend-step a b) b₁
prepend-step (E-If-If a) (B-If-False b b₁) = B-If-False (prepend-step a b) b₁
prepend-step (E-Succ a) (B-Succ b) = B-Succ (prepend-step a b)
prepend-step E-IsZeroZero B-True = B-IsZeroT B-Zero
prepend-step (E-IsZero a) (B-IsZeroT b) = B-IsZeroT (prepend-step a b)
prepend-step (E-IsZero a) (B-IsZeroF b) = B-IsZeroF (prepend-step a b)
prepend-step {t' = false} {vtrue} E-IsZeroSucc ()
prepend-step E-IsZeroSucc B-False = B-IsZeroF  (value-to-value _)    ---???
prepend-step E-If-True (B-Pair y y₁) = B-If-True B-True (B-Pair y y₁)
prepend-step E-If-True (B-Fst y) = B-If-True B-True (B-Fst y)
prepend-step E-If-True (B-Snd y) = B-If-True B-True (B-Snd y)
prepend-step E-Fst y =  B-Fst ( {!!}  ) -- B-Fst (B-Pair y y₁)
prepend-step E-Snd y = {!!}
prepend-step (E-PairLeft x) (B-Pair y y₁) = B-Pair (prepend-step x y) y₁
prepend-step (E-PairRight x) (B-Pair y y₁) = B-Pair y (prepend-step x y₁)  -- B-Pair (prepend-step x y) (prepend-step x₁ y)₁

small-to-big : {ty : Type} -> (t : Term ty) -> (v : Value ty) → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big .(⌜ b ⌝) b Nil = value-to-value b
small-to-big ._ b (Cons E-If-True c) = B-If-True B-True (small-to-big _ _ c)
small-to-big ._ b (Cons E-If-False c) = B-If-False B-False (small-to-big _ _ c)
small-to-big ._ b (Cons (E-If-If x) c) = prepend-step (E-If-If x) (small-to-big _ _ c)
small-to-big ._ b (Cons (E-Succ x₁) c) = prepend-step (E-Succ x₁)  (small-to-big _ _ c)
small-to-big .(iszero zero) b (Cons E-IsZeroZero c) = prepend-step E-IsZeroZero (small-to-big _ _ c) 
small-to-big ._ b (Cons E-IsZeroSucc c) = prepend-step E-IsZeroSucc (small-to-big _ _ c) 
small-to-big ._ b (Cons (E-IsZero x) c) = prepend-step (E-IsZero x) (small-to-big _ _ c) 
small-to-big ._ b (Cons E-Fst c) = prepend-step E-Fst (small-to-big _ _ c) 
small-to-big ._ b (Cons E-Snd c) = prepend-step E-Snd (small-to-big _ _ c) 
small-to-big ._ b (Cons (E-PairLeft x) c) = prepend-step (E-PairLeft x) (small-to-big _ _ c)
small-to-big ._ b (Cons (E-PairRight x) c) = prepend-step (E-PairRight x) (small-to-big _ _ c)  -- prepend-step  (E-Pair x x₁) (small-to-big _ _ c)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = B-True
⇓-complete false = B-False
⇓-complete (pair a b) = B-Pair (⇓-complete a) (⇓-complete b) --add a pair rule
⇓-complete (if t then t₁ else t₂) with ⇓-complete t
⇓-complete (if true then t₁ else t₂) | B-True = B-If-True B-True (⇓-complete t₁) 
⇓-complete (if false then t₁ else t₂) | B-False =  B-If-False B-False (⇓-complete t₂) 
⇓-complete (if a then t₃ else t₄) | c with ⟦ a  ⟧
⇓-complete (if a then t₃ else t₄) | c | vtrue = B-If-True c ((⇓-complete t₃) )
⇓-complete (if a then t₃ else t₄) | c | vfalse =  B-If-False c ((⇓-complete t₄) )
⇓-complete zero = B-Zero
⇓-complete (succ x)  with ⟦ x  ⟧ |  ⇓-complete x
⇓-complete (succ ._) | vnat x | B-If-True y y₁ = B-Succ (B-If-True y y₁)
⇓-complete (succ ._) | vnat x | B-If-False y y₁ = B-Succ (B-If-False y y₁)
⇓-complete (succ .zero) | vnat .Zero | B-Zero = B-Succ B-Zero
⇓-complete (succ ._) | vnat ._ | B-Succ y = B-Succ (B-Succ y)
⇓-complete (succ ._) | vnat x | B-Fst y = B-Succ (B-Fst y)
⇓-complete (succ ._) | vnat x | B-Snd y = B-Succ (B-Snd y)
⇓-complete (iszero t) with ⟦ t ⟧  |  ⇓-complete t
⇓-complete (iszero ._) | vnat Zero | B-If-True y y₁ = B-IsZeroT (B-If-True y y₁)
⇓-complete (iszero ._) | vnat (Succ x) | B-If-True y y₁ = B-IsZeroF (B-If-True y y₁)
⇓-complete (iszero ._) | vnat Zero | B-If-False y y₁ = B-IsZeroT (B-If-False y y₁)
⇓-complete (iszero ._) | vnat (Succ x) | B-If-False y y₁ = B-IsZeroF (B-If-False y y₁)
⇓-complete (iszero .zero) | vnat .Zero | B-Zero = B-IsZeroT B-Zero
⇓-complete (iszero ._) | vnat ._ | B-Succ y = B-IsZeroF (B-Succ y)
⇓-complete (iszero ._) | vnat Zero | B-Fst y = B-IsZeroT (B-Fst y)
⇓-complete (iszero ._) | vnat (Succ x) | B-Fst y = B-IsZeroF (B-Fst y)
⇓-complete (iszero ._) | vnat Zero | B-Snd y = B-IsZeroT (B-Snd y)
⇓-complete (iszero ._) | vnat (Succ x) | B-Snd y = B-IsZeroF (B-Snd y)
⇓-complete (fst a) with ⟦ a  ⟧ |  ⇓-complete a
⇓-complete (fst a) | vpair p p₁ | f = B-Fst f 
⇓-complete (snd a) with ⟦ a  ⟧ |  ⇓-complete a
⇓-complete (snd a) | vpair a' b | f = B-Snd f

⇓-sound : ∀ {ty} -> {t : Term ty} -> {v : Value ty} → t ⇓ v → v == ⟦ t ⟧
⇓-sound B-True = refl
⇓-sound B-False = refl
⇓-sound B-Zero = refl
⇓-sound (B-Pair a b) with  ⇓-sound a | ⇓-sound b
⇓-sound (B-Pair a₁ b₁) | refl | refl = refl 
⇓-sound (B-Succ x) = cong vsucc (⇓-sound x)
⇓-sound {v = z} (B-If-True {a} {b} {c} {d} x x₁) with ⟦ a ⟧ | ⇓-sound x
⇓-sound (B-If-True {a} {b} {c} {d}  x x₁) | .vtrue | refl = ⇓-sound x₁
⇓-sound (B-If-False {a} {b} {c} {d} x x₁) with ⟦ a ⟧ | ⇓-sound x
⇓-sound (B-If-False x x₁) | .vfalse | refl = ⇓-sound x₁
⇓-sound (B-IsZeroT {a} x) with ⟦ a ⟧ | ⇓-sound x
⇓-sound (B-IsZeroT x) | .(vnat Zero) | refl = refl
⇓-sound (B-IsZeroF {a} {b} x₁) with ⟦ a ⟧ | ⇓-sound x₁
⇓-sound (B-IsZeroF x₁) | ._ | refl = refl
⇓-sound (B-Fst x)  with ⇓-sound x
... | p = {!!}
⇓-sound (B-Snd x) = {!!}

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
-- ⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
-- ⇓-sound true vtrue B-True = refl
-- ⇓-sound true vfalse ()
-- ⇓-sound false vtrue ()
-- ⇓-sound (if a then a₁ else a₂) (vpair b c) d with ⟦ a  ⟧ 
-- ⇓-sound (if a then a₁ else a₂) (vpair b c) d | vtrue with ⟦ a₁  ⟧
-- ⇓-sound (if a then a₁ else a₂) (vpair b c) d | vtrue | vpair p p₁ = pairEq (vpair b c) (vpair p p₁) 
-- ⇓-sound (if a then a₁ else a₂) (vpair b c) d | vfalse with ⟦ a₂  ⟧
-- ⇓-sound (if a then a₁ else a₂) (vpair b c) d | vfalse | vpair p p₁ = pairEq (vpair b c) (vpair p p₁)
-- ⇓-sound (pair a a₁) (vpair b c) d with  ⟦ pair a a₁ ⟧
-- ⇓-sound (pair a a₁) (vpair b c) d | vpair p p₁ = pairEq (vpair b c) (vpair p p₁) 
-- ⇓-sound false vfalse B-False = refl
-- ⇓-sound (if a then a₁ else a₂) va b with  ⟦ a  ⟧ 
-- ⇓-sound (if a then a₁ else a₂) va b | vtrue  with  ⟦ a₁  ⟧
-- ⇓-sound (if a then a₁ else a₂) vtrue b | vtrue | vtrue = refl
-- ⇓-sound (if a then a₁ else a₂) vfalse b | vtrue | vtrue = contradiction {!!} 
-- ⇓-sound (if a then a₁ else a₂) vtrue b | vtrue | vfalse =  contradiction {!!} 
-- ⇓-sound (if a then a₁ else a₂) vfalse b | vtrue | vfalse = refl
-- ⇓-sound (if a then a₁ else a₂) (vnat x₁) b | vtrue | vnat x = cong vnat (natEq x₁ x)
-- ⇓-sound (if a then a₁ else a₂) (vpair va va₁) b | vtrue | vpair p p₁ = {!!} 
-- ⇓-sound (if a then a₁ else a₂) va b | vfalse with  ⟦ a₂  ⟧
-- ⇓-sound (if a then a₁ else a₂) vtrue b | vfalse | vtrue = refl
-- ⇓-sound (if a then a₁ else a₂) vfalse b | vfalse | vtrue = contradiction {!!}
-- ⇓-sound (if a then a₁ else a₂) vtrue b | vfalse | vfalse = contradiction {!!}
-- ⇓-sound (if a then a₁ else a₂) vfalse b | vfalse | vfalse = refl
-- ⇓-sound (if a then a₁ else a₂) (vnat x₁) b | vfalse | vnat x = cong vnat (natEq x₁ x)
-- ⇓-sound (if a then a₁ else a₂) (vpair va va₁) b | vfalse | vpair p p₁ = {!!}
-- ⇓-sound zero (vnat .Zero) B-Zero = refl
-- ⇓-sound (iszero a) vtrue c with viszero ⟦ a ⟧
-- ⇓-sound (iszero a) vtrue c | vtrue = refl
-- ⇓-sound (iszero a) vtrue c | vfalse = contradiction {!!}  
-- ⇓-sound (iszero a) vfalse c  with viszero ⟦ a ⟧
-- ⇓-sound (iszero a) vfalse c | vtrue = contradiction {!!} 
-- ⇓-sound (iszero a) vfalse c | vfalse = refl
-- ⇓-sound (succ x) f (B-Succ c) = cong vsucc (⇓-sound x (vnat {!!} ) c)
-- -- ⇓-sound (succ (if k then k₁ else k₂)) (vnat ._) (B-Succ c) = {!!}
-- -- ⇓-sound (succ zero) (vnat ._) (B-Succ c) = {!!} -- absurd
-- -- ⇓-sound (succ (succ k)) (vnat ._) (B-Succ c) = {!!}



-- -- -- Retrospective
-- -- -- * Three styles of semantics: denotational, small step and big step
-- -- -- * All three can be shown to be equivalent
-- -- -- * To avoid handling 'stuck' terms, we introduced a typing discipline
-- -- -- * And proved type soundness -- 'well-typed terms can't go wrong'
-- -- --
-- -- --   (the proof was easy using Agda - because we only considered well-typed 
-- -- --   terms to begin with; usually we would need to do induction over the typing
-- -- --   derivation)
-- -- -- 
-- -- -- * All proofs are by easy induction -- finding the right definitions is hard!
