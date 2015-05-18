module Ex1 where

---------------------
------ Prelude ------
---------------------

data Bool : Set where
  True : Bool
  False : Bool

data Nat : Set where
  Zero : Nat 
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ k + m = Succ (k + m)

_*_ : Nat -> Nat -> Nat
Zero * n = Zero
(Succ k) * n = n + (k * n)

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a 0
  Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

head : {a : Set} {n : Nat}-> Vec a (Succ n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {α}{a : Set α} (x : a) : a -> Set α where
  Refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL Refl #-}

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

subst : ∀ {α} {A : Set α} (P : A → Set α) {x y : A} → x == y → P x → P y
subst _ Refl p = p

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} -> Empty -> a
magic ()

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

fst : {A B : Set} → Pair A B → A
fst (a , b) = a

snd : {A B : Set} → Pair A B → B
snd (a , b) = b

data Fin : Nat -> Set where
  Fz : forall {n} -> Fin (Succ n)
  Fs : forall {n} -> Fin n -> Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero} _   = Nil
pure {Succ n} a = Cons a (pure a)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil         <*> Nil         = Nil
(Cons f fs) <*> (Cons a as) = Cons (f a) (fs <*> as)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f v = pure f <*> v

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m

mpure : {m n : Nat}{a : Set} → a → Matrix a m n
mpure a = pure (pure a)

mmap : {m n : Nat}{a b : Set} → (a → b) → Matrix a m n → Matrix b m n
mmap f m = vmap (vmap f) m

_<**>_ : {m n : Nat}{a b : Set} 
       → Matrix (a → b) m n → Matrix a m n → Matrix b m n
Nil         <**> Nil = Nil
Cons fs fss <**> Cons as ass = Cons (fs <*> as) (fss <**> ass)

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd xss yss = mmap _+_ xss <**> yss

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero}   
  = Nil
idMatrix {Succ k} 
  = Cons (Cons 1 (pure 0)) (vmap (Cons 0) idMatrix)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil           = pure Nil
transpose (Cons as ass) = vmap Cons as <*> (transpose ass)
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs j) = Succ (forget j)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs i) = Fs (embed i)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs fi) = cong Succ (correct fi)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

abs : {n m : Nat} → Compare n m → Nat
abs (GreaterThan k) = Succ k
abs (LessThan k)    = Succ k
abs Equal           = Zero

-- Show that there is a 'covering function'
cmp : (n m : Nat) -> Compare n m 
cmp Zero Zero     = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) with cmp n m 
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k = LessThan k
cmp (Succ n) (Succ .n)            | Equal = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m = abs (cmp m n)

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

nat-cata : {C : Nat → Set} → (n : Nat) → ({m : Nat} → C m → C (Succ m)) → C Zero → C n
nat-cata Zero f b = b
nat-cata {C} (Succ n) f b = f {n} (nat-cata {C} n f b)

_∘_ : ∀ {α β γ}
    → {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ}
    → (f : {x : A} → (y : B x) → C y)
    → (g : (x : A) → B x)
    → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero n = nat-cata {C = λ n → (n + 0) == n } n (cong Succ) Refl

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero m = sym (plusZero m)
plusCommutes (Succ n) m = trans (cong Succ (plusCommutes n m)) (plusSucc m n)

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k 
  = trans (cong (λ x → (m + k) + x) (distributivity n m k)) (my-assoc {m})
  where
    exchange : (k i j : Nat) → (k + (i + j)) == (i + (k + j))
    exchange Zero i j     = Refl
    exchange (Succ k) i j = trans (cong Succ (exchange k i j)) (plusSucc i (k + j))

    my-assoc : {m k i j : Nat} → ((m + k) + (i + j)) == ((m + i) + (k + j))
    my-assoc {Zero} {k} {i} {j} = exchange k i j
    my-assoc {Succ m}           = cong Succ (my-assoc {m})

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {xs = Nil}       = Base
SubListRefl {xs = Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans xy Base             = xy
SubListTrans (Keep xy) (Keep yz) = Keep (SubListTrans xy yz)
SubListTrans (Drop xy) (Keep yz) = Drop (SubListTrans xy yz)
SubListTrans xy (Drop yz)        = Drop (SubListTrans xy yz)

SubListHead : {a : Set}{x : a}{xs ys : List a} → SubList (Cons x xs) ys → SubList xs ys
SubListHead (Keep xy) = Drop xy
SubListHead (Drop xy) = Drop (SubListHead xy)

SubListTail : {a : Set}{x : a}{xs ys : List a} → SubList (Cons x xs) (Cons x ys) → SubList xs ys
SubListTail (Keep xy) = xy
SubListTail (Drop xy) = SubListHead xy

SubListDoubleInd : {a : Set}{x : a}{xs ys : List a} → SubList (Cons x xs) ys → SubList ys xs → Empty
SubListDoubleInd (Keep p) q = SubListDoubleInd q p
SubListDoubleInd (Drop p) q = SubListDoubleInd p (SubListHead q)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base yx          = Refl
SubListAntiSym (Keep {x} xy) yx = cong (Cons x) (SubListAntiSym xy (SubListTail yx))
SubListAntiSym (Drop xy) yx     = magic (SubListDoubleInd yx xy)


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Leq0 : ∀{n}   → LEQ n n
  LeqS : ∀{n m} → LEQ n m → LEQ n (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqZero : {n : Nat} → LEQ Zero n
leqZero {Zero} = Leq0
leqZero {Succ n} = LeqS leqZero

leqRefl : (n : Nat) -> LEQ n n
leqRefl = λ _ → Leq0

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Leq0 mk             = mk
leqTrans (LeqS nm) Leq0      = LeqS nm
leqTrans (LeqS nm) (LeqS mk) = LeqS (leqTrans (LeqS nm) mk)

leqDown : {n m : Nat} → LEQ (Succ n) m → LEQ n m
leqDown Leq0 = LeqS Leq0
leqDown (LeqS mn) = LeqS (leqDown mn)

leqDec : {n m : Nat} → LEQ (Succ n) (Succ m) → LEQ n m
leqDec Leq0 = Leq0
leqDec (LeqS mn) = leqDown mn

leqSucc : {n m : Nat} → LEQ n m → LEQ (Succ n) (Succ m)
leqSucc Leq0 = Leq0
leqSucc (LeqS leq) = LeqS (leqSucc leq)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym {Zero} Leq0 nm = Refl
leqAntiSym {Zero} (LeqS mn) ()
leqAntiSym {Succ n} {Zero} () nm
leqAntiSym {Succ n} {Succ m} mn nm = cong Succ (leqAntiSym (leqDec mn) (leqDec nm))

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= {Zero} mn = Refl
leq<= {Succ n} {Zero} ()
leq<= {Succ n} {Succ m} mn = leq<= (leqDec mn)

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m prf = leqZero
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) prf = leqSucc (<=leq n m prf) 

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP x y = y x

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

orAbsorb : {P : Set} → Or P Empty → P
orAbsorb (Inr ())
orAbsorb (Inl p) = p

{- Here's a few logical equivalences we are going to need -}
private
  DeMorgan : {P Q : Set} → Not (Or P Q) → Pair (Not P) (Not Q)
  DeMorgan n = (n ∘ Inl) , (n ∘ Inr)

  DeMorgan2 : {P Q : Set} → Or (Not P) Q → Not (Pair P (Not Q))
  DeMorgan2 (Inl x) x₁ = x (fst x₁)
  DeMorgan2 (Inr x) x₁ = snd x₁ x

  absurd : {P : Set} → Pair (Not P) P → Empty
  absurd (f , p) = f p

  -- And a few point-free operators to make our life easier.
  id : ∀{a}{A : Set a} → A → A
  id x = x

  _><_ : {A B C D : Set}(f : A → B)(g : C → D) → Pair A C → Pair B D
  (f >< g) (a , c) = (f a , g c)

notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle hip = hip (Inr (λ x → hip (Inl x)))

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.


doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...

-- The proof starts by proving (Not (Not (Or (Not P) P))).
-- with a few tricks and a DeMorgan we can derive Empty.
step1 : doubleNegation → excludedMiddle
step1 dn {P} = dn ((absurd ∘ (id >< dn)) ∘ DeMorgan)

step2 : excludedMiddle → impliesToOr
step2 lem f = orCase (Inr ∘ f) Inl lem

step3 : impliesToOr → doubleNegation
step3 ito {P} hip = orCase (λ x → magic (hip x)) id (ito (id {A = P}))

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

{-
  If we have implications as disjunctions, it's easy to see how
  this implication goes!

    ((P → Q) → P) → P
  ≡ (¬ (P → Q) ∨ P) → P
  ≡ (¬ (¬ P ∨ Q) ∨ P) → P
  ≡ ((P ∧ ¬ Q) ∨ P) → P

  Well, to prove Pierce's law, we need to provide a way to construct a P
  given ((P ∧ ¬ Q) ∨ P). We have a positive P in both disjuncts, therefore
  this is trivial.
-}
step4 : impliesToOr → piercesLaw
step4 ito {P} {Q} f = orCase (step3 ito ∘ (fst ∘ DeMorgan)) id (ito (f ∘ aux))
  where
    aux : Or (Not P) Q → (P → Q)
    aux = orCase (λ x p → magic (x p)) (λ x _ → x)

{-
  The other way around is just a clever application of Pierce's Law.
  Given that we can, from a (Z → Y) → Z, construct a Z, (that's pierce's law!)

  we want to prove that, given a (f : P → Q), we can construct a (Or (Not P) Q).
  We proceed by constructing a (Or (Not P) Q → Y) → Or (Not P) Q object, and
  apply our hypothesis. 

  Constructing such function, in Agda, is very simple.
  We have something of type ∀ Y . (Or (Not P) Q → Y) as a variable (z). We are going to construct
  a (Not P), which is the same as given a P, constructing empty.

  Note how our z has a type variable universsaly quantified. Let us choose Y = Empty.

  Given a (p : P), Inr (f p) has type Or (Not P) Q, which is then fed to z and concludes the proof.
-}
step5 : piercesLaw → impliesToOr
step5 law {P} {Q} f = law (λ z → Inl (λ p → z (Inr (f p))))

----------------------
----- Exercise 9 -----
----------------------

-- Here is a data type for 'Raw' lambda terms that have not yet
--   been type checked.

data Raw : Set where
  Lam : Raw -> Raw
  App : Raw -> Raw -> Raw
  Var : Nat -> Raw

-- The Agda tutorial shows how to define a type for the well-typed
--   lambda terms, and a type checker mapping Raw terms to well-typed
--   terms (or an error)
--
-- Adapt their development to instead restrict yourself to
-- 'scope checking' -- i.e. give a data type for the well-scoped
-- lambda terms and a function that maps a raw term to a well-scoped
-- lambda term.
--
-- This makes it possible to represent ill-typed terms such as (\x . x
-- x).

-- Note:
--     Since we are not using the agda-stdlib, 
--     some functions defined here are pure boilerplate.
--     mainly to handle and match fin's.

-- Default definition,
data WS : Nat → Set where
  WSVar : ∀{n} → Fin n → WS n
  WSApp : ∀{n} → WS n → WS n → WS n
  WSLam : ∀{n} → WS (Succ n) → WS n

-- Embeding of terms.
embedWS : {n : Nat} → WS n → WS (Succ n)
embedWS (WSVar x) = WSVar (embed x)
embedWS (WSLam t) = WSLam (embedWS t)
embedWS (WSApp t u) = WSApp (embedWS t) (embedWS u)

-- We need some sort of existential to prove the existence of
-- a scope bound.
record Σ (A : Set)(B : A → Set) : Set
  where 
    constructor _,_
    field 
      p1 : A
      p2 : B p1

-- Housekeeping
toFin : (n : Nat) → Fin (Succ n)
toFin Zero = Fz
toFin (Succ n) = Fs (toFin n)

-- Wrapping a term into a lambda.
wrapLam : Σ Nat WS → Σ Nat WS
wrapLam (n , t) = n , WSLam (embedWS t)

-- Wrapping two terms into an application.
wrapApp : Σ Nat WS → Σ Nat WS → Σ Nat WS
wrapApp (n₁ , t) (n₂ , u) = (n₁ ⊔ n₂) , WSApp (match n₁ n₂ t) (subst WS (⊔-comm {n₂} {n₁}) (match n₂ n₁ u))
  where
    -- We are going to need some lattices here.
    -- In the end, it's obvious you can always inject a (Fin n) into
    -- a (Fin (max n x)), for all x.
    _⊔_ : Nat → Nat → Nat
    Zero   ⊔ y = y
    Succ x ⊔ Zero = Succ x
    Succ x ⊔ Succ y = Succ (x ⊔ y)

    ⊔-zero : {x : Nat} → (x ⊔ Zero) == x
    ⊔-zero {Zero} = Refl
    ⊔-zero {Succ x} = Refl

    ⊔-comm : {x y : Nat} → (x ⊔ y) == (y ⊔ x)
    ⊔-comm {Zero} = sym ⊔-zero
    ⊔-comm {Succ x} {Zero} = Refl
    ⊔-comm {Succ x} {Succ y} = cong Succ (⊔-comm {x} {y})

    ⊔-leq : {x y : Nat} → LEQ x (x ⊔ y)
    ⊔-leq {Zero} = leqZero
    ⊔-leq {Succ x} {Zero} = Leq0
    ⊔-leq {Succ x} {Succ y} = leqSucc ⊔-leq

    inject-leq : {n m : Nat} → LEQ n m → Fin n → Fin m
    inject-leq Leq0 x = x
    inject-leq (LeqS leq) x = embed (inject-leq leq x)

    inject : {n m : Nat} → Fin n → Fin (n ⊔ m)
    inject = inject-leq ⊔-leq

    match : (n m : Nat) → WS n → WS (n ⊔ m)
    match n m (WSVar x) = WSVar (inject x)
    match n m (WSApp t₁ t₂) = WSApp (match n m t₁) (match n m t₂)
    match n m (WSLam t₁) = WSLam (match (Succ n) (Succ m) t₁)

infixl 90 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
Nothing  >>= _ = Nothing
(Just a) >>= f = f a

-- (fix-scope s n) will return a just x, as long
-- as we can represent index n within scope s.
fix-scope : (s : Nat) → Nat → Maybe (Fin s)
fix-scope s n with cmp n s
fix-scope .(n + Succ k) n | LessThan k = Just (gen-fin {n} {k})
  where
    gen-fin : {n m : Nat} → Fin (n + Succ m)
    gen-fin {Zero} = Fz
    gen-fin {Succ n} = Fs (gen-fin {n})
fix-scope s n | _ = Nothing

check-aux : Nat → Raw → Maybe (Σ Nat WS)
check-aux s (Var x) with fix-scope s x
...| Just x' = Just (s , WSVar x')
...| Nothing = Nothing
check-aux s (Lam t) = check-aux (Succ s) t >>= (Just ∘ wrapLam)
check-aux s (App t u) = check-aux s t 
                    >>= λ t' → check-aux s u
                    >>= λ u' → Just (wrapApp t' u')

check : Raw → Maybe (Σ Nat WS)
check = check-aux 0

t1 : Raw
t1 = App (Lam (Var 0)) (Lam (Var Zero))
