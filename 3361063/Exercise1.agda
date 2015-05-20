module Exercise1 where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits. 

If you have any questions, don't hesitate to email me or ask in class.
-}

{-
       Robert Hensing

       3361063


       I have left some unused lemmas lying around. Sorry about that :)
-}


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
{-# BUILTIN ZERO Zero #-}
{-# BUILTIN SUC Succ #-}

infixr 4 _+_
_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ k + m = Succ (k + m)

infixr 5 _*_
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

infixr 3 _==_
data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} -> Empty -> a
magic ()

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

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
pure {Zero} x = Nil
pure {Succ n} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons x p <*> Cons x₁ q = Cons (x x₁) (p <*> q)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f q = pure f <*> q

_<$>_ : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
_<$>_ = vmap

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m 

plus : Nat -> Nat -> Nat
plus = (_+_)

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd xss yss = ((\xs ys -> (plus <$> xs) <*> ys) <$> xss) <*> yss

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = pure (pure 1)
idMatrix {Succ n} = append (Cons (Cons 1 (pure 0)) Nil) (vmap (Cons 0) idMatrix)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = pure Nil
transpose (Cons p ps) = (Cons <$> p) <*> transpose ps
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ x} = Cons Fz (vmap Fs plan)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs f) = Succ (forget f)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs f) = Fs (embed f)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs i₁) = cong Succ (correct i₁)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

-- Show that there is a 'covering function'
cmp : (n m : Nat) -> Compare n m 
cmp Zero Zero = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k = LessThan k
cmp (Succ .m) (Succ m) | Equal = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

cmp→nat : {n m : Nat} -> Compare n m -> Nat
cmp→nat (LessThan k) = Succ k
cmp→nat Equal = Zero
cmp→nat (GreaterThan k) = Succ k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m = cmp→nat (cmp n m)

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

transr : {a : Set} {x y z : a} -> y == x -> z == y -> z == x
-- transr Refl Refl = Refl  -- boring, DRY ;)
transr p q = sym (trans (sym p) (sym q))

infixr 2 _⟨_⟩_
_⟨_⟩_ : forall {a : Set} -> (x : a) -> {y z : a} -> x == y -> y == z -> x == z
x ⟨ p ⟩ q = trans p q

infixr 3 _∎
_∎ : {a : Set} -> (x : a) -> x == x
x ∎ = Refl

-- Visible reduction steps make the proof more explicit
definition : {a : Set} -> {x : a} -> x == x
definition = Refl

infixr 2 _`trans`_
_`trans`_ : forall {a : Set} -> {x y z : a} -> x == y -> y == z -> x == z
p `trans` q = trans p q

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero _ = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero = Refl
plusCommutes Zero (Succ m) = cong Succ (plusCommutes Zero m)
plusCommutes (Succ n) Zero = cong Succ (plusCommutes n Zero)
plusCommutes (Succ n) (Succ m) =
   Succ n + Succ m
     ⟨ definition ⟩
   Succ (n + Succ m)
     ⟨ cong Succ (
             n + Succ m    ⟨ sym (plusSucc n m) ⟩
             Succ (n + m)  ⟨ plusCommutes (Succ n) m ⟩
             m + Succ n    ∎ )
     ⟩
   Succ (m + Succ n)
     ⟨ definition ⟩
   Succ m + Succ n
   ∎

plusAssoc : (k m n : Nat) -> (k + m) + n == k + m + n
plusAssoc Zero m n = Refl
plusAssoc (Succ k) m n = cong Succ (plusAssoc k m n)

succTimes : (k n : Nat) -> ((Succ k) * n) == (n + k * n)
succTimes k n = Refl

timesZero : (k : Nat) -> (k * Zero) == Zero
timesZero Zero = Refl
timesZero (Succ k) = timesZero k

plusFlip : (k m n : Nat) -> k + n + m == n + k + m
plusFlip k m n = k + n + m     ⟨ sym (plusAssoc k n m) ⟩
                 (k + n) + m   ⟨ cong (\x -> x + m) (plusCommutes k n) ⟩
                 (n + k) + m   ⟨ plusAssoc n k m ⟩
                 n + k + m     ∎

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k =
   (m + k) + n * (m + k)     ⟨ cong (\x -> (m + k) + x) (distributivity n m k) ⟩
   (m + k) + n * m + n * k   ⟨ plusAssoc m k (n * m + n * k) ⟩
   m + k + n * m + n * k     ⟨ cong (\x -> m + x) (plusFlip k (n * k) (n * m)) ⟩
   m + n * m + k + n * k     ⟨ sym (plusAssoc m (n * m) (k + n * k)) ⟩
   (m + n * m) + k + n * k   ∎

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {_} {Nil} = Base
SubListRefl {_} {Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base ys = ys
SubListTrans (Keep xs₁) (Keep ys₂) = Keep (SubListTrans xs₁ ys₂)
SubListTrans (Drop xs₁) (Keep ys₂) = Drop (SubListTrans xs₁ ys₂)
SubListTrans xs₁        (Drop ys₂) = Drop (SubListTrans xs₁ ys₂)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base q = Refl
SubListAntiSym (Keep {x} p) (Keep q) = cong (Cons x) (SubListAntiSym p q)
SubListAntiSym (Keep {x} p) (Drop q) = cong (Cons x) (SubListAntiSym p (SubListTrans (Drop SubListRefl) q))
SubListAntiSym (Drop q) (Keep {x} p) = cong (Cons x) (SubListAntiSym (SubListTrans (Drop SubListRefl) q) p)
SubListAntiSym (Drop p) (Drop q) = SubListAntiSym (Drop p) (Drop q)


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Eq : (n : Nat) -> LEQ n n
  Lt : (n m : Nat) -> LEQ n m -> LEQ n (Succ m)

leqRefl : (n : Nat) -> LEQ n n
leqRefl = Eq

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k

leqTrans (Eq _) mk = mk
leqTrans nm (Eq _) = nm
leqTrans (Lt n m nm) (Lt .(Succ m) m₁ mk) = Lt n m₁ (leqTrans (Lt n m nm) mk)

leqWeaken : {n m : Nat} -> LEQ (Succ n) m -> LEQ n m
leqWeaken {n} (Eq .(Succ n)) = Lt n n (Eq n)
leqWeaken {n} (Lt .(Succ n) m leq) = Lt n m (leqWeaken leq)

leqDecr : {n m : Nat} -> LEQ (Succ n) (Succ m) -> LEQ n m
leqDecr {m} (Eq .(Succ m)) = Eq m
leqDecr {n} {m} (Lt .(Succ n) .m leq) = leqWeaken leq

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym (Eq _) _ = Refl
leqAntiSym _ (Eq _) = Refl
leqAntiSym (Lt .(Succ m₁) m nm) (Lt .(Succ m) m₁ mn) = cong Succ (leqAntiSym (leqWeaken nm) (leqWeaken mn))

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= (Eq Zero) = Refl
leq<= (Eq (Succ m)) = leq<= (Eq m)
leq<= (Lt Zero _ _) = Refl
leq<= (Lt (Succ n) m leq) = leq<= (leqWeaken leq)

leqIncr : {n m : Nat} -> LEQ n m -> LEQ (Succ n) (Succ m)
leqIncr (Eq m) = Eq (Succ m)
leqIncr (Lt n m l) = Lt (Succ n) (Succ m) (leqIncr l)

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero Zero _ = Eq Zero
<=leq Zero (Succ m) _ = Lt Zero m (<=leq Zero m Refl)
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) p = leqIncr (<=leq n m p)

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP p f = f p

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle p = p (Inr (\ x → p (Inl x))) 

orSym : {a b : Set} -> Or a b -> Or b a
orSym (Inl x) = Inr x
orSym (Inr x) = Inl x

mpRight : {a b c : Set} -> (b -> c) -> Or a b -> Or a c
mpRight impl (Inl x) = Inl x
mpRight impl (Inr x) = Inr (impl x)

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.

doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...


step1 : doubleNegation -> excludedMiddle
step1 dn = dn (\f → f (Inr (\x → f (Inl x)))) 

step2 : excludedMiddle -> impliesToOr
step2 em {P} {Q} impl = mpRight impl (orSym (em {P}))

step3 : impliesToOr -> doubleNegation
step3 ito {P} h with ito (\(x : P) -> x)
step3 ito h | Inl x with h x
... | ()
step3 ito h | Inr x = x

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P
stepA : doubleNegation -> piercesLaw
stepA dn {P} {Q} plLhs = dn (λ z₂ → z₂ (plLhs (λ z₃ → dn (λ _ → z₂ z₃))))

stepB : piercesLaw -> excludedMiddle
stepB pl = pl (λ plLhs → Inr (λ x → plLhs (Inl x)))

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

data WellScoped (scopeSize : Nat) : Set where
  Var : (d : Nat) -> {leq : (Succ d) <= scopeSize == True} -> WellScoped scopeSize
  App : WellScoped scopeSize -> WellScoped scopeSize -> WellScoped scopeSize
  Lam : WellScoped (Succ scopeSize) -> WellScoped scopeSize

erase : forall {scopeSize} -> WellScoped scopeSize -> Raw
erase (Var d) = Var d
erase (App scoped scoped₁) = App (erase scoped) (erase scoped₁)
erase (Lam scoped) = Lam (erase scoped)

data CheckScope (scopeSize : Nat) : Raw -> Set where
  ok  : (ws : WellScoped scopeSize) -> CheckScope scopeSize (erase ws)
  bad : {e : Raw} -> CheckScope scopeSize e

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x == y -> Inspect x
inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x Refl

checkScope : (scopeSize : Nat) (e : Raw) -> CheckScope scopeSize e
checkScope scopeSize (Lam e) with checkScope (Succ scopeSize) e
checkScope scopeSize (Lam .(erase ws)) | ok ws = ok (Lam ws)
checkScope scopeSize (Lam e) | bad = bad
checkScope scopeSize (App e e₁) with checkScope scopeSize e
checkScope scopeSize (App .(erase ws) e₁) | ok ws with checkScope scopeSize e₁
checkScope scopeSize (App .(erase ws₁) .(erase ws)) | ok ws₁ | ok ws = ok (App ws₁ ws)
checkScope scopeSize (App .(erase ws) e₁) | ok ws | bad = bad
checkScope scopeSize (App e e₁) | _ = bad
checkScope scopeSize (Var x) with inspect (Succ x <= scopeSize)
checkScope scopeSize (Var x) | it True proof = ok (Var x {proof})
checkScope scopeSize (Var x) | it False proof = bad

example₁ : WellScoped 0
example₁ = Lam (Var 0 {Refl})

-- One unbound variable
example₂ : WellScoped 1
example₂ = Var 0 {Refl}

ex0 : WellScoped Zero
ex0 = Lam (Lam (Var 1 {Refl}))

is-ok : {scopeSize : Nat}{e : Raw} -> CheckScope scopeSize e -> Bool
is-ok (ok _) = True
is-ok (_) = False

test₁ : is-ok (checkScope 0 (Lam (App (Var 0) (Var 0)))) == True
test₁ = Refl

test₂ : is-ok (checkScope 0 (Lam (App (Var 0) (Var 1)))) == False
test₂ = Refl

-- Probably too ambitious for now
-- checkScope-is-complete : (scopeSize : Nat)(ws : WellScoped scopeSize) -> checkScope scopeSize (erase ws) == ok ws
-- checkScope-is-complete Zero (Var d {()})
-- checkScope-is-complete (Succ scopeSize) (Var Zero {Refl}) = Refl
-- checkScope-is-complete (Succ Zero) (Var (Succ n) {()})
-- checkScope-is-complete (Succ (Succ scopeSize)) (Var (Succ s)) = {!!}
-- checkScope-is-complete scopeSize (App ws ws₁) = {!!}
-- checkScope-is-complete scopeSize (Lam ws) = {!!}

