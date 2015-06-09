
module Exercise2a where

{-

F142001

Hey there, person who has been assigned to check my work!

I have (mistakenly) interpreted the word "tuples" in the assignment
to mean tuples. It should have been obvious that the word "tuples" does not
denote tuples but pairs :D

So, my implementation implements the functionality of arbitrary n-tuples,
but combined with fst/snd (not an arbitrary projection function that allows
access to the ith element in a tuple). Since I only discovered this on the
day the assignment was due, and since the tuple functionality is more general
than pairs, Wouter told me it was ok to leave it like this.

So, it's not your standard implementation and maybe not as easily checkable
with the answer model, and I feel bad for putting you through this. Sorry!

Hopefully it will strucurally resemble the pairs extension enough for you
to be able to easily verify my solutions.

PS. the "mutual" makes it take veeeeerry long to load/compile. If you're
checking a different part of the exercise, you might want to temporarily
comment that section out. 

-}


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

symm : {a : Set} {x y : a} → x == y → y == x
symm refl = refl
  
cong : {a b : Set} {x y : a} (f : a -> b) -> x == y -> f x == f y
cong f refl = refl

-- Contradiction type.
data Empty : Set where

-- Reducto ad absurdum.
contradiction : {A : Set} → Empty → A
contradiction ()

-- Negation
Not : Set → Set
Not A = A → Empty

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

_+_ : Nat → Nat → Nat
Zero + b = b
Succ a + b = Succ (a + b)

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b


-- I have added some standard functionality here. It will be needed for the tuples.

data Vec (a : Set) : Nat → Set where
  Nil : Vec a Zero
  Cons : {n : Nat} → (x : a) → (xs : Vec a n) → Vec a (Succ n)

data Fin : Nat → Set where
  Zero : ∀ {n} → Fin (Succ n)
  Succ : ∀ {n} → Fin n → Fin (Succ n)

head : {a : Set} {n : Nat} → Vec a (Succ n) → a
head (Cons x xs) = x

tail : {a : Set} {n : Nat} → Vec a (Succ n) → Vec a n
tail (Cons x xs) = xs


-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

data Type : Set where
  NAT : Type
  BOOL : Type
  TUPLE : {n : Nat} → Vec Type n → Type
  PAIR : Type → Type → Type

-- Our Term language
data Term : Type -> Set where
  -- Booleans
  true          : Term BOOL 
  false         : Term BOOL
  if_then_else_ : {ty : Type} -> (c : Term BOOL) -> (t e : Term ty) → Term ty
  -- Natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- Tuples:
  -- They are basically a list of terms that implicitly carry length information
  tuplenil      : Term (TUPLE {Zero} Nil)
  tuplecons     : {n : Nat} {ty : Type} {tys : Vec Type n} → (t : Term ty) → (ts : Term (TUPLE {n} tys)) → Term (TUPLE {Succ n} (Cons ty tys))
  fst           : {n : Nat} {ty : Type} {tys : Vec Type n} → (ts : Term (TUPLE {Succ n} (Cons ty tys))) → Term ty
  snd           : {n : Nat} {ty1 ty2 : Type} {tys : Vec Type n} → (ts : Term (TUPLE {Succ (Succ n)} (Cons ty1 (Cons ty2 tys)))) → Term ty2



-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue      : Value BOOL 
  vfalse     : Value BOOL
  vnat       : Nat -> Value NAT
  vtuplenil  : Value (TUPLE Nil)
  vtuplecons : {ty : Type} → {n : Nat} → {tys : Vec Type n} → Value ty → Value (TUPLE tys) → Value (TUPLE (Cons ty tys))

natTerm : Nat -> Term NAT
natTerm Zero = zero
natTerm (Succ k) = succ (natTerm k)

-- TODO needed?
data MultiTypeTermVec : (n : Nat) → Vec Type n → Set where
  Nil  : MultiTypeTermVec Zero Nil
  Cons : {n : Nat} → {ty : Type} {tys : Vec Type n} → (t : Term ty) → (ts : MultiTypeTermVec n tys) → MultiTypeTermVec (Succ n) (Cons ty tys)

data MultiTypeValueVec : (n : Nat) → Vec Type n → Set where
  Nil  : MultiTypeValueVec Zero Nil
  Cons : {n : Nat} → {ty : Type} {tys : Vec Type n} → (v : Value ty) → (ts : MultiTypeValueVec n tys) → MultiTypeValueVec (Succ n) (Cons ty tys)

--turn a list of terms into a term of type tuple
vecToTuple : {n : Nat} → {tys : Vec Type n} → MultiTypeTermVec n tys → Term (TUPLE tys)
vecToTuple Nil = tuplenil
vecToTuple (Cons t mttv) = tuplecons t (vecToTuple mttv)


singletonMTTV : ∀ {ty} → Term ty → MultiTypeTermVec (Succ Zero) (Cons ty Nil)
singletonMTTV t = Cons t Nil

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝           = true
⌜ vfalse ⌝          = false
⌜ vnat k ⌝          = natTerm k
⌜ vtuplenil ⌝       = tuplenil
⌜ vtuplecons v vs ⌝ = tuplecons ⌜ v ⌝ ⌜ vs ⌝


valuesToTerms : ∀ {n tys} → MultiTypeValueVec n tys → MultiTypeTermVec n tys
valuesToTerms Nil = Nil
valuesToTerms (Cons v vs) = Cons ⌜ v ⌝ (valuesToTerms vs)


valueVecToTermTuple : {n : Nat} → {tys : Vec Type n} → MultiTypeValueVec n tys → Term (TUPLE tys)
valueVecToTermTuple Nil = tuplenil
valueVecToTermTuple (Cons v mttv) = tuplecons ⌜ v ⌝ (valueVecToTermTuple mttv)



-- Example term.
ex : Term NAT -> Term BOOL 
ex t = if iszero t then false else true

------------------------------------------------------------------------
-- Denotational semantics.
--------------------------------------------------------------------------------

-- Evaluation of if-then-else expressions applied to values.
cond : forall {ty} -> Value BOOL → Value ty → Value ty → Value ty
cond vtrue  v2 v3 = v2
cond vfalse v2 v3 = v3

vsucc : Value NAT -> Value NAT
vsucc (vnat x) = vnat (Succ x)

viszero : Value NAT -> Value BOOL
viszero (vnat Zero)     = vtrue
viszero (vnat (Succ x)) = vfalse

-- Get first element of a tuple; this only works for tuples of length at least one
vfirst : ∀ {n : Nat} {ty : Type} {tys : Vec Type n} → Value (TUPLE (Cons ty tys)) → Value ty
vfirst (vtuplecons v vs) = v

-- Similar for snd; the tuple should have length >= 2
vsecond : ∀ {n : Nat} {ty1 ty2 : Type} {tys : Vec Type n} → Value (TUPLE (Cons ty1 (Cons ty2 tys))) → Value ty2
vsecond (vtuplecons v₁ (vtuplecons v₂ vs)) = v₂

-- Evaluation function.
⟦_⟧ : forall {ty} -> Term ty  → Value ty
⟦ true ⟧                 = vtrue
⟦ false ⟧                = vfalse
⟦ if t then t₁ else t₂ ⟧ = cond ⟦ t ⟧ ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ zero ⟧                 = vnat Zero
⟦ succ k ⟧               = vsucc ⟦ k ⟧
⟦ iszero t ⟧             = viszero ⟦ t ⟧
⟦ tuplenil ⟧             = vtuplenil
⟦ tuplecons t ts ⟧       = vtuplecons ⟦ t ⟧ ⟦ ts ⟧
⟦ fst t ⟧                = vfirst ⟦ t ⟧
⟦ snd t ⟧                = vsecond ⟦ t ⟧

-- What can we do to define a denotational semantics?
--   Add types!

-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True    : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False   : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If      : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
                   Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ       : forall {t t' : Term NAT} -> Step {NAT} t t' -> Step {NAT} (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) (true)
  E-IsZeroSucc : {v : Value NAT} -> Step (iszero (succ ⌜ v ⌝)) false
  E-IsZero     : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  -- Two possible steps for tuples: either the step occurs because the first element can be stepped (TupleHead),
  -- or because the tail can be stepped.
  -- Note that if t2 -> t2' and t3 -> t3', we can only derive
  -- [t1, t2, t3, t4, t5]   -> [t1, t2', t3, t4, t5]
  -- and not
  -- [t1, t2, t3, t4, t5]   -> [t1, t2, t3', t4, t5]
  -- because E-TupleTail ensures that we can only add normal forms to the front of the list (and t2 is not a normal form).
  -- This is ensured by the requirement of the proof p : t == ⌜ v ⌝
  E-TupleTail  : forall {n ty tys} {v : Value ty} {t : Term ty} {p : t == ⌜ v ⌝ } {ts1 ts2 : Term (TUPLE {n} tys)} →
                   Step ts1 ts2 → Step (tuplecons t ts1) (tuplecons t ts2)
  E-TupleHead  : forall {n ty tys} {t1 t2 : Term ty} {ts : Term (TUPLE {n} tys)} →
                   Step t1 t2 → Step (tuplecons t1 ts) (tuplecons t2 ts)
  -- Two possible steps for fst: we can only evaluate (t1, t2, t3) to t1 if all terms in the list are normal forms
  -- (as ensured by the proofs p, q)
  E-FstTuple   : forall {n ty tys}  {t : Term ty} {v : Value ty} {ts : Term (TUPLE {n} tys)} {vs : Value (TUPLE tys)}
                   {p : t == ⌜ v ⌝} {q : ts == ⌜ vs ⌝} →
                   Step (fst (tuplecons t ts)) t
  E-Fst        : forall {n ty tys} {ts1 ts2 : Term (TUPLE {Succ n} (Cons ty tys))} →
                   Step ts1 ts2 → Step (fst ts1) (fst ts2)
  -- Snd is similar to fst, but just a little bit longer.
  E-SndTuple   : forall {n ty1 ty2 tys}  {t1 : Term ty1} {v1 : Value ty1} {t2 : Term ty2} {v2 : Value ty2}
                   {ts : Term (TUPLE {n} tys)} {vs : Value (TUPLE tys)}
                   {p : t1 == ⌜ v1 ⌝} {q : t2 == ⌜ v2 ⌝} {r : ts == ⌜ vs ⌝} →
                   Step (snd (tuplecons t1 (tuplecons t2 ts))) t2
  E-Snd        : forall {n ty1 ty2 tys} {ts1 ts2 : Term (TUPLE {Succ (Succ n)} (Cons ty1 (Cons ty2 tys)))} →
                   Step ts1 ts2 → Step (snd ts1) (snd ts2)

valuesDoNotStep : forall {ty} -> (v : Value ty) (t : Term ty) -> Step (⌜ v ⌝) t -> Empty
valuesDoNotStep vtrue t ()
valuesDoNotStep vfalse t ()
valuesDoNotStep (vnat x) t step = lemma x t step
   where
   lemma : (n : Nat) → (t : Term NAT) → Step (natTerm n) t → Empty
   lemma Zero t ()
   lemma (Succ n) ._ (E-Succ {._} {t} step) = lemma n (t) step
valuesDoNotStep vtuplenil t ()
valuesDoNotStep (vtuplecons v vs) ._ (E-TupleTail step) = valuesDoNotStep vs _ step
valuesDoNotStep (vtuplecons v vs) ._ (E-TupleHead step) = valuesDoNotStep v  _ step


-- This has become a monster...!
deterministic : ∀ {ty} {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic E-If-True           E-If-True        = refl
deterministic E-If-True           (E-If-If ())
deterministic E-If-False          E-If-False       = refl
deterministic E-If-False          (E-If-If ())
deterministic (E-If-If ())        E-If-True
deterministic (E-If-If ())        E-If-False
deterministic (E-If-If step1)     (E-If-If step2)  = cong (\x → if x then _ else _) (deterministic step1 step2)
deterministic (E-Succ step1)      (E-Succ step2)   = cong succ (deterministic step1 step2)
deterministic E-IsZeroZero        E-IsZeroZero     = refl
deterministic E-IsZeroZero        (E-IsZero ())
deterministic (E-IsZeroSucc {v})  step2            = lemma v _ step2
  where
  lemma : (v : Value NAT) → (t : Term BOOL) → Step (iszero (succ ⌜ v ⌝)) t → false == t
  lemma (vnat x) true                   ()
  lemma (vnat x) false                  step                     = refl
  lemma (vnat x) (if t then t₁ else t₂) ()
  lemma (vnat x) (iszero ._)            (E-IsZero (E-Succ step)) = contradiction (valuesDoNotStep (vnat x) _ step)
  lemma (vnat x) (fst t)                ()
  lemma (vnat x) (snd t)                ()
deterministic (E-IsZero ())       E-IsZeroZero
deterministic (E-IsZero (E-Succ step1)) (E-IsZeroSucc {v}) = contradiction (valuesDoNotStep v _ step1)
deterministic (E-IsZero step1)    (E-IsZero step2)         = cong iszero (deterministic step1 step2)
-- There are a lot of cases to check, but most of them are contradictions (i.e. there is no possible step),
-- because a lot of the tuple/fst/snd steps are evaluated ONLY if a lot of their contents are already in normal form.
deterministic (E-TupleTail step1) (E-TupleTail step2)      = cong (\xs → tuplecons _ xs) (deterministic step1 step2)
-- e.g. E-TupleTail ensures that the first element of the tuple is in normal form, so it is impossible that
-- that same tuple is derived from E-TupleHead.
deterministic (E-TupleTail {_} {_} {_} {v} {.(⌜ v ⌝)} {p = refl} {_} {_} step1) (E-TupleHead step2)
                                                   = contradiction (valuesDoNotStep v _ step2)
deterministic (E-TupleHead step1)     (E-TupleTail {_} {_} {_} {v} {.(⌜ v ⌝)} {p = refl} {_} {_} step2)
                                                   = contradiction (valuesDoNotStep v _ step1)
deterministic (E-TupleHead step1)     (E-TupleHead step2)  = cong (\x → tuplecons x _) (deterministic step1 step2)
deterministic E-FstTuple          E-FstTuple       = refl
deterministic (E-FstTuple {_} {_} {_} {.(⌜ v ⌝)} {v} {.(⌜ vs ⌝)} {vs} {p = refl} {q = refl}) (E-Fst step2)
                                                   = contradiction (valuesDoNotStep (vtuplecons v vs) _ step2)
deterministic (E-Fst step1)       (E-FstTuple {_} {_} {_} {.(⌜ v ⌝)} {v} {.(⌜ vs ⌝)} {vs} {p = refl} {q = refl})
                                                   = contradiction (valuesDoNotStep (vtuplecons v vs) _ step1)
deterministic (E-Fst step1)       (E-Fst step2)    = cong fst (deterministic step1 step2)
deterministic E-SndTuple          E-SndTuple       = refl
deterministic (E-SndTuple {_} {_} {_} {_} {.(⌜ v1 ⌝)} {v1} {.(⌜ v2 ⌝)} {v2} {.(⌜ vs ⌝)} {vs} {p = refl} {q = refl} {r = refl}) (E-Snd step2)
                                                   = contradiction (valuesDoNotStep (vtuplecons v1 (vtuplecons v2 vs)) _ step2)
deterministic (E-Snd step1)       (E-SndTuple {_} {_} {_} {_} {.(⌜ v1 ⌝)} {v1} {.(⌜ v2 ⌝)} {v2} {.(⌜ vs ⌝)} {vs} {p = refl} {q = refl} {r = refl})
                                                   = contradiction (valuesDoNotStep (vtuplecons v1 (vtuplecons v2 vs)) _ step1)
deterministic (E-Snd step1)       (E-Snd step2)    = cong snd (deterministic step1 step2)

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
  -- If-then-else terms are reducible
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t₂ t₃  = Reduces E-If-True
  if-reduces false t₂ t₃ = Reduces E-If-False
  if-reduces (if t₁ then t₂ else t₃) t₄ t₅ with if-reduces t₁ t₂ t₃
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t₁) t₂ t₃ with iszero-reduces t₁
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (fst t₁) t₂ t₃ with fst-reduces t₁
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (snd t₁) t₂ t₃ with snd-reduces t₁
  ... | Reduces x = Reduces (E-If-If x)

  -- iszero terms are reducible
  iszero-reduces : (t : Term NAT) → Red (iszero t)
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  ... | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x with normal-forms-are-values t x
  iszero-reduces (succ .(⌜ v ⌝)) | Left x | is-value v = Reduces (E-IsZeroSucc {v})
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst t) with fst-reduces t
  ... | Reduces x = Reduces (E-IsZero x)
  iszero-reduces (snd t) with snd-reduces t
  ... | Reduces x = Reduces (E-IsZero x)

  -- fst terms are reducible
  fst-reduces : ∀ {n ty} {tys : Vec Type n} (tuple : Term (TUPLE (Cons ty tys))) → Red (fst tuple)
  fst-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  ... | Reduces x = Reduces (E-Fst x)
  fst-reduces (tuplecons t ts) with progress t
  ... | Left x with normal-forms-are-values t x
  fst-reduces (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v with progress ts
  fst-reduces (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v | Left y with normal-forms-are-values ts y
  fst-reduces (tuplecons .(⌜ v ⌝) .(⌜ vs ⌝)) | Left x | is-value v | Left y | is-value vs = Reduces (E-FstTuple {_} {_} {_} {_} {v} {_} {vs} {refl} {refl}) --tuplecons t ts is NF
  fst-reduces (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v | Right (Reduces y) = Reduces (E-Fst (E-TupleTail {_} {_} {_} {v} {_} {refl} y))   -- ts reduces, t is NF
  fst-reduces (tuplecons t ts) | Right (Reduces x) = Reduces (E-Fst (E-TupleHead x))    -- t reduces
  fst-reduces (fst t) with fst-reduces t
  ... | Reduces x = Reduces (E-Fst x)
  fst-reduces (snd t) with snd-reduces t
  ... | Reduces x = Reduces (E-Fst x) 

  -- snd terms are reducible: the proof is similar in structure to that of fst
  snd-reduces : ∀ {n ty1 ty2} {tys : Vec Type n} (tuple : Term (TUPLE (Cons ty1 (Cons ty2 tys)))) → Red (snd tuple)
  snd-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  ... | Reduces x = Reduces (E-Snd x)
  snd-reduces (tuplecons t ts) with progress t
  ... | Left x with normal-forms-are-values t x
  snd-reduces (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v with progress ts
  snd-reduces (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v | Left y with normal-forms-are-values ts y
  snd-reduces (tuplecons .(⌜ v ⌝) .(tuplecons ⌜ v₂ ⌝ ⌜ vs ⌝)) | Left x | is-value v | Left y | is-value (vtuplecons v₂ vs) = Reduces (E-SndTuple {_} {_} {_} {_} {_} {v} {_} {v₂} {_} {vs} {refl} {refl} {refl}) -- tuplecons t ts is a NF
  snd-reduces (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v | Right (Reduces y) = Reduces (E-Snd (E-TupleTail {_} {_} {_} {v} {_} {refl} y)) -- ts reduces (t is NF)
  snd-reduces (tuplecons t ts) | Right (Reduces x) = Reduces (E-Snd (E-TupleHead x)) -- t reduces
  snd-reduces (fst t) with fst-reduces t
  ... | Reduces x = Reduces (E-Snd x)
  snd-reduces (snd t) with snd-reduces t
  ... | Reduces x = Reduces (E-Snd x)

  -- If a succ term is a normal form, then so is its argument term
  succ-nf : (k : Term NAT) → NF (succ k) → NF k
  succ-nf t nf (Reduces x) = nf (Reduces (E-Succ x))

  -- If a tuple term is a normal form, then so is the term at the head position
  head-nf : ∀ {ty n tys} → (t : Term ty) → {ts : Term (TUPLE {n} tys)} → NF (tuplecons t ts) → NF t
  head-nf t nf (Reduces x) = nf (Reduces (E-TupleHead x))

  -- If a tuple term is a normal form, then so is the tuple consituting its tail
  tail-nf : ∀ {ty n tys} → {t : Term ty} → (ts : Term (TUPLE {n} tys)) → NF (tuplecons t ts) → NF ts
  tail-nf {_} {_} {_} {t} ts nf (Reduces x) with normal-forms-are-values t (head-nf t nf)
  tail-nf ts nf (Reduces x) | is-value v = nf (Reduces (E-TupleTail {_} {_} {_} {v} {_} {refl} x))
  
  -- A normal form must be a value
  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → Is-value t
  normal-forms-are-values true       nf = is-value vtrue
  normal-forms-are-values false      nf = is-value vfalse
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero       nf = is-value (vnat Zero)
  normal-forms-are-values (succ t)   nf with normal-forms-are-values t (succ-nf t nf)
  normal-forms-are-values (succ .(natTerm x)) nf | is-value (vnat x) = is-value (vnat (Succ x))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))
  normal-forms-are-values tuplenil   nf = is-value vtuplenil
  normal-forms-are-values (tuplecons t ts) nf with normal-forms-are-values t (head-nf t nf)
  normal-forms-are-values (tuplecons .(⌜ v ⌝) ts) nf | is-value v with normal-forms-are-values ts (tail-nf ts nf)
  normal-forms-are-values (tuplecons .(⌜ v ⌝) .(⌜ vs ⌝)) nf | is-value v | is-value vs = is-value (vtuplecons v vs)
  normal-forms-are-values (fst t)    nf = contradiction (nf (fst-reduces t))
  normal-forms-are-values (snd t)    nf = contradiction (nf (snd-reduces t))

  -- All values are themselves normal forms
  values-are-normal-forms : forall {ty} (t : Term ty) -> Is-value t -> NF t
  values-are-normal-forms .(⌜ v ⌝) (is-value v) (Reduces {t} x) = valuesDoNotStep v t x

  
  

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true       = Left (values-are-normal-forms true (is-value vtrue))
  progress false      = Left (values-are-normal-forms false (is-value vfalse))
  progress (if t then t₁ else t₂) = Right (if-reduces t t₁ t₂)
  progress zero       = Left (values-are-normal-forms zero (is-value (vnat Zero)))
  progress (succ t)   with progress t
  progress (succ t) | Left x = Left (sublemma t x)    
    where
    sublemma : (t : Term NAT) -> (Red t -> Empty) -> Red (succ t) -> Empty
    sublemma t nf (Reduces (E-Succ x)) = nf (Reduces x)
  progress (succ t) | Right (Reduces x) = Right (Reduces (E-Succ x))
  progress (iszero t) = Right (iszero-reduces t)
  progress tuplenil   = Left (values-are-normal-forms tuplenil (is-value vtuplenil))
  progress (tuplecons t ts) with progress t
  progress (tuplecons t ts) | Left x with normal-forms-are-values t x
  progress (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v with progress ts
  progress (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v | Left y with normal-forms-are-values ts y
  progress (tuplecons .(⌜ v ⌝) .(⌜ vs ⌝)) | Left x | is-value v | Left y | is-value vs
                      = Left (values-are-normal-forms (tuplecons ⌜ v ⌝ ⌜ vs ⌝) (is-value (vtuplecons v vs)))
  progress (tuplecons .(⌜ v ⌝) ts) | Left x | is-value v | Right (Reduces y) = Right (Reduces (E-TupleTail {_} {_} {_} {v} {_} {refl} y))
  progress (tuplecons t ts) | Right (Reduces x) = Right (Reduces (E-TupleHead x))
  progress (fst t)    = Right (fst-reduces t)
  progress (snd t)    = Right (snd-reduces t)


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

--Include proofs for tuples, fst, snd. They are quite straightforward variations on the previous code.
E-TupleHead-Steps : ∀ {ty n tys} {t t' : Term ty} {ts : Term (TUPLE {n} tys)} →
        Steps t t' →
        Steps (tuplecons t ts) (tuplecons t' ts)
E-TupleHead-Steps Nil = Nil
E-TupleHead-Steps (Cons x steps) = Cons (E-TupleHead x) (E-TupleHead-Steps steps)

E-TupleTail-Steps : ∀ {ty n tys} {ts ts' : Term (TUPLE {n} tys)} (v : Value ty) →
        Steps ts ts' →
        Steps (tuplecons ⌜ v ⌝ ts) (tuplecons ⌜ v ⌝ ts')
E-TupleTail-Steps v Nil = Nil
E-TupleTail-Steps v (Cons x steps) = Cons (E-TupleTail {_} {_} {_} {v} {⌜ v ⌝} {refl} {_} {_} x) (E-TupleTail-Steps v steps)

E-Fst-Steps : ∀ {ty n tys} {ts ts' : Term (TUPLE {Succ n} (Cons ty tys))} →
        Steps ts ts' →
        Steps (fst ts) (fst ts')
E-Fst-Steps Nil = Nil
E-Fst-Steps (Cons x steps) = Cons (E-Fst x) (E-Fst-Steps steps)

-- Sorry for all the implicit arguments...
E-FstTuple-Steps : ∀ {ty n tys} {tts : Term (TUPLE {Succ n} (Cons ty tys))} {v : Value ty} {vs : Value (TUPLE tys)} →
        Steps tts ⌜ vtuplecons v vs ⌝ →
        Steps (fst tts) ⌜ v ⌝
E-FstTuple-Steps {_} {_} {_} {.(tuplecons ⌜ v ⌝ ⌜ vs ⌝)} {v} {vs} Nil = [ E-FstTuple {_} {_} {_} {⌜ v ⌝} {v} {⌜ vs ⌝} {vs} {refl} {refl} ]
E-FstTuple-Steps {_} {_} {_} {_} {v} {vs} (Cons x steps) = Cons (E-Fst x) (E-FstTuple-Steps {_} {_} {_} {_} {v} {vs} steps)

E-Snd-Steps : ∀ {ty1 ty2 n tys} {ts ts' : Term (TUPLE {Succ (Succ n)} (Cons ty1 (Cons ty2 tys)))} →
        Steps ts ts' →
        Steps (snd ts) (snd ts')
E-Snd-Steps Nil = Nil
E-Snd-Steps (Cons x steps) = Cons (E-Snd x) (E-Snd-Steps steps)

E-SndTuple-Steps : ∀ {ty1 ty2 n tys} {t1t2ts : Term (TUPLE {Succ (Succ n)} (Cons ty1 (Cons ty2 tys)))} {v1 : Value ty1} {v2 : Value ty2} {vs : Value (TUPLE tys)} →
        Steps t1t2ts ⌜ vtuplecons v1 (vtuplecons v2 vs) ⌝ →
        Steps (snd t1t2ts) ⌜ v2 ⌝
E-SndTuple-Steps {_} {_} {_} {_} {.(tuplecons ⌜ v1 ⌝ (tuplecons ⌜ v2 ⌝ ⌜ vs ⌝))} {v1} {v2} {vs} Nil = [ E-SndTuple {_} {_} {_} {_} {⌜ v1 ⌝} {v1} {⌜ v2 ⌝} {v2} {⌜ vs ⌝} {vs} {refl} {refl} {refl} ]
E-SndTuple-Steps {_} {_} {_} {_} {_} {v1} {v2} {vs} (Cons x steps) = Cons (E-Snd x) (E-SndTuple-Steps {_} {_} {_} {_} {_} {v1} {v2} {vs} steps)


-- All steps terminate.
termination : ∀ {ty} (t : Term ty) → t ⇓
termination true      = terminates vtrue Nil
termination false     = terminates vfalse Nil
termination (if t then t₁ else t₂) with termination t
termination (if t then t₁ else t₂) | terminates vtrue x with termination t₁
termination (if t then t₁ else t₂) | terminates vtrue x | terminates v x₁
                      = terminates v (E-If-Steps x ++ [ E-If-True ] ++ x₁)
termination (if t then t₁ else t₂) | terminates vfalse x with termination t₂
termination (if t then t₁ else t₂) | terminates vfalse x | terminates v x₂
                      = terminates v (E-If-Steps x ++ [ E-If-False ] ++ x₂)
termination zero = terminates (vnat Zero) Nil
termination (succ t) with termination t
termination (succ t) | terminates (vnat n) x = terminates (vnat (Succ n)) (E-Succ-Steps x)
termination (iszero t) with termination t
termination (iszero t) | terminates (vnat Zero) x     = terminates vtrue ( E-IsZero-Steps x ++ [ E-IsZeroZero ] )
termination (iszero t) | terminates (vnat (Succ n)) x = terminates vfalse (E-IsZero-Steps x ++ [ E-IsZeroSucc {vnat n} ] )
--Tuples: termination exists because all elements in the tuple terminate
termination tuplenil = terminates vtuplenil Nil
termination (tuplecons t ts) with termination t
termination (tuplecons t ts) | terminates v x with termination ts
termination (tuplecons t ts) | terminates v x | terminates vs y = terminates (vtuplecons v vs) (E-TupleHead-Steps x ++ E-TupleTail-Steps v y)
-- again, this is just intimidating because of all of the implicit arguments. If you ignore those, then it should be fine.
-- e.g. fst: given that we know that t terminates (and those steps are called x), then we know that fst t also terminates,
-- simply by first applying all those steps, but wrapped inside a fst constructor by E-Fst-Steps, and finally getting the value out of the
-- fst-constructor again using an E-FstTuple step.
termination (fst t) with termination t
termination (fst t) | terminates (vtuplecons v vs) x = terminates v (E-Fst-Steps x ++ [ E-FstTuple {_} {_} {_} {_} {v} {_} {vs} {refl} {refl} ] )
termination (snd t) with termination t
termination (snd t) | terminates (vtuplecons v₁ (vtuplecons v₂ vs)) x = terminates v₂ (E-Snd-Steps x ++ [ E-SndTuple {_} {_} {_} {_} {_} {v₁} {_} {v₂} {_} {vs} {refl} {refl} {refl} ])



------------------------------------------------------------------------
-- Big-step semantics.
-- A different kind of representation for evaluation rules. 'a ⇓ b'
-- denotes that a will evaluate to value b after a complete execution
-- of the term.
-- I had to change the definition from data _⇓_ {ty : Type} : ...
--                                to   data _⇓_ : {ty : Type} → ...
-- because otherwise terms like EvalTrue would have to have definitions for both BOOL and NAT.
data _⇓_ : {ty : Type} → Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalIfTrue : forall {ty : Type} {c : Term BOOL} {t e : Term ty} {v : Value ty} →
               c ⇓ vtrue → t ⇓ v → if c then t else e ⇓ v
  EvalIfFalse : forall {ty : Type} {c : Term BOOL} {t e : Term ty} {v : Value ty} →
                c ⇓ vfalse → e ⇓ v → if c then t else e ⇓ v
  -- Natural numbers:
  EvalZero : zero ⇓ (vnat Zero)
  EvalSucc : forall {t : Term NAT} {n : Nat} → t ⇓ vnat n → (succ t) ⇓ vsucc (vnat n)
  EvalIsZeroZero : forall {t : Term NAT} → t ⇓ (vnat Zero) → (iszero t) ⇓ vtrue
  EvalIsZeroSucc : forall {t : Term NAT} {n : Nat} → t ⇓ (vsucc (vnat n)) → (iszero t) ⇓ vfalse
  -- Tuples:
  EvalTupleNil : tuplenil ⇓ vtuplenil
  EvalTupleCons : forall {ty n tys} {t : Term ty} {v : Value ty} {ts : Term (TUPLE {n} tys)} {vs : Value (TUPLE tys)} →
                    t ⇓ v → ts ⇓ vs → tuplecons t ts ⇓ vtuplecons v vs
  EvalFst      : forall {ty n tys} {tts : Term (TUPLE {Succ n} (Cons ty tys))} {v : Value ty} {vs : Value (TUPLE tys)} →
                    tts ⇓ vtuplecons v vs → fst tts ⇓ v
  EvalSnd      : forall {ty1 ty2 n tys} {t1t2ts : Term (TUPLE {Succ (Succ n)} (Cons ty1 (Cons ty2 tys)))} {v1 : Value ty1} {v2 : Value ty2} {vs : Value (TUPLE tys)} →
                    t1t2ts ⇓ vtuplecons v1 (vtuplecons v2 vs) → snd t1t2ts ⇓ v2


-- Converstion from big- to small-step representations.
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue           = Nil
big-to-small EvalFalse          = Nil
big-to-small (EvalIfTrue p q)   = E-If-Steps (big-to-small p) ++ [ E-If-True ] ++ big-to-small q
big-to-small (EvalIfFalse p q)  = E-If-Steps (big-to-small p) ++ [ E-If-False ] ++ big-to-small q
big-to-small EvalZero           = Nil
big-to-small (EvalSucc p)       = E-Succ-Steps (big-to-small p)
big-to-small (EvalIsZeroZero p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroSucc {_} {n} p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroSucc {vnat n} ]
big-to-small EvalTupleNil       = Nil
-- Note how we FIRST evaluate the head, and THEN the tail
big-to-small (EvalTupleCons {_} {_} {_} {_} {v} {_} {vs} p ps) = E-TupleHead-Steps (big-to-small p) ++ E-TupleTail-Steps v (big-to-small ps)
-- Here too: first evaluate the term inside the fst/snd, and as a last step evaluate the fst/snd
big-to-small (EvalFst {ty} {n} {tys} {tts} {v} {vs} p) = E-FstTuple-Steps {_} {_} {_} {tts} {v} {vs} (big-to-small p)
big-to-small (EvalSnd {_} {_} {_} {_} {tts} {v1} {v2} {vs} p) = E-SndTuple-Steps {_} {_} {_} {_} {tts} {v1} {v2} {vs} (big-to-small p)


-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (v : Value ty) -> ⌜ v ⌝ ⇓ v
value-to-value vtrue = EvalTrue
value-to-value vfalse = EvalFalse
value-to-value (vnat Zero) = EvalZero
value-to-value (vnat (Succ n)) = EvalSucc (value-to-value (vnat n))
value-to-value vtuplenil = EvalTupleNil
value-to-value (vtuplecons v vs) = EvalTupleCons (value-to-value v) (value-to-value vs)

--Auxiliary lemma
lemma : forall {ty n tys} {t : Term ty} {v : Value ty} {vs : Value (TUPLE {n} tys)} → t ⇓ v → tuplecons t ⌜ vs ⌝ ⇓ vtuplecons v vs
lemma p = EvalTupleCons p (value-to-value _)

prepend-step : {ty : Type} → {t t' : Term ty} → {v : Value ty} → Step t t' → t' ⇓ v → t ⇓ v
prepend-step E-If-True          p                    = EvalIfTrue EvalTrue p
prepend-step E-If-False         p                    = EvalIfFalse EvalFalse p
prepend-step (E-If-If step)     (EvalIfTrue p q)     = EvalIfTrue (prepend-step step p) q
prepend-step (E-If-If step)     (EvalIfFalse p q)    = EvalIfFalse (prepend-step step p) q
prepend-step (E-Succ step)      (EvalSucc p)         = EvalSucc (prepend-step step p)
prepend-step E-IsZeroZero       EvalTrue             = EvalIsZeroZero EvalZero
prepend-step (E-IsZeroSucc {vnat n}) EvalFalse       = EvalIsZeroSucc (value-to-value (vnat (Succ n)))
prepend-step (E-IsZero step)    (EvalIsZeroZero p)   = EvalIsZeroZero (prepend-step step p)
prepend-step (E-IsZero step)    (EvalIsZeroSucc p)   = EvalIsZeroSucc (prepend-step step p)
prepend-step (E-TupleTail step) (EvalTupleCons p ps) = EvalTupleCons p (prepend-step step ps)
prepend-step (E-TupleHead step) (EvalTupleCons p ps) = EvalTupleCons (prepend-step step p) ps
prepend-step (E-FstTuple {_} {_} {_} {_} {_} {.(⌜ vs ⌝)} {vs} {_} {refl})  p = EvalFst (EvalTupleCons p (value-to-value vs))
prepend-step (E-Fst step)       (EvalFst p)          = EvalFst (prepend-step step p)
prepend-step (E-SndTuple {_} {_} {_} {_} {.(⌜ v1 ⌝)} {v1} {_} {_} {.(⌜ vs ⌝)} {vs} {refl} {_} {refl}) p = EvalSnd (EvalTupleCons (value-to-value v1) (EvalTupleCons p (value-to-value vs)))
prepend-step (E-Snd step)       (EvalSnd p)         = EvalSnd (prepend-step step p)



small-to-big : {ty : Type} {t : Term ty} {v : Value ty} → Steps t ⌜ v ⌝ → t ⇓ v
small-to-big Nil = value-to-value _
small-to-big (Cons step steps) = prepend-step step (small-to-big steps)


--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if c then t else e) with ⇓-complete c
... | p with ⟦ c ⟧
⇓-complete (if c then t else e) | p | vtrue = EvalIfTrue p (⇓-complete t)
⇓-complete (if c then t else e) | p | vfalse = EvalIfFalse p (⇓-complete e)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⇓-complete t
... | p with ⟦ t ⟧
⇓-complete (succ t) | p | vnat n = EvalSucc p
⇓-complete (iszero t) with ⇓-complete t
... | p with ⟦ t ⟧
⇓-complete (iszero t) | p | vnat Zero = EvalIsZeroZero p
⇓-complete (iszero t) | p | vnat (Succ n) = EvalIsZeroSucc p
⇓-complete tuplenil = EvalTupleNil
⇓-complete (tuplecons t ts) = EvalTupleCons (⇓-complete t) (⇓-complete ts)
⇓-complete (fst t) with ⇓-complete t
... | p with ⟦ t ⟧
⇓-complete (fst t) | p | vtuplecons v vs = EvalFst p
⇓-complete (snd t) with ⇓-complete t
... | p with ⟦ t ⟧
⇓-complete (snd t) | p | vtuplecons v₁ (vtuplecons v₂ vs) = EvalSnd p



-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → v == ⟦ t ⟧
⇓-sound EvalTrue = refl
⇓-sound EvalFalse = refl
⇓-sound (EvalIfTrue p q) = sublemma (⇓-sound p) (⇓-sound q)
   where
   sublemma : ∀ {ty} {c : Value BOOL} {v t e : Value ty} → vtrue == c → v == t → v == cond c t e
   sublemma refl refl = refl
⇓-sound (EvalIfFalse p q) = sublemma (⇓-sound p) (⇓-sound q)
   where
   sublemma : ∀ {ty} {c : Value BOOL} {v t e : Value ty} → vfalse == c → v == e → v == cond c t e
   sublemma refl refl = refl
-- Natural numbers:
⇓-sound EvalZero = refl
⇓-sound (EvalSucc p) = cong vsucc (⇓-sound p)
⇓-sound (EvalIsZeroZero p) = sublemma (⇓-sound p)
   where
   sublemma : ∀ {v : Value NAT} → vnat Zero == v → vtrue == viszero v
   sublemma refl = refl
⇓-sound (EvalIsZeroSucc p) = sublemma (⇓-sound p)
   where
   sublemma : ∀ {v : Value NAT} {n : Nat} → vnat (Succ n) == v → vfalse == viszero v
   sublemma refl = refl
-- Tuples:
⇓-sound EvalTupleNil = refl
⇓-sound (EvalTupleCons p ps) = sublemma (⇓-sound p) (⇓-sound ps)
   where
   sublemma : ∀ {ty n tys} {v v' : Value ty} {vs vs' : Value (TUPLE {n} tys)} → v == v' → vs == vs' → vtuplecons v vs == vtuplecons v' vs'
   sublemma refl refl = refl
⇓-sound (EvalFst p) = sublemma (⇓-sound p)
   where
   sublemma : ∀ {ty n tys} {v : Value ty} {vs : Value (TUPLE {n} tys)} {vvs : Value (TUPLE (Cons ty tys))} → vtuplecons v vs == vvs → v == vfirst vvs
   sublemma refl = refl
⇓-sound (EvalSnd p) = sublemma (⇓-sound p)
   where
   sublemma : ∀ {ty1 ty2 n tys} {v1 : Value ty1} {v2 : Value ty2} {vs : Value (TUPLE {n} tys)} {vvvs : Value (TUPLE (Cons ty1 (Cons ty2 tys)))} →
              vtuplecons v1 (vtuplecons v2 vs) == vvvs → v2 == vsecond vvvs
   sublemma refl = refl


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
