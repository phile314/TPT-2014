module Exercise1 where

{-

Using Agda version 2.4.2.2

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

-- Apply every ith function in the first vector to every ith element in the second vector
_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons f fs <*> Cons x xs = Cons (f x) (fs <*> xs)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m 

-- Define matrix addition
-- TEST CASE: madd (Cons (Cons 1 (Cons 2 Nil)) (Cons (Cons 3 (Cons 4 Nil)) Nil)) (Cons (Cons 5 (Cons 6 Nil)) (Cons (Cons 7 (Cons 8 Nil)) Nil))
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons xs xss) (Cons ys yss) = Cons ((vmap _+_ xs) <*> ys) (madd xss yss)

-- Define the identity matrix
-- Induction step: add a line of 0's above the nxn identity matrix, and add a (1, 0, 0, ..., 0) column in front
-- TEST CASE: idMatrix {3}
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ n} = Cons (Cons 1 (pure 0)) (vmap (Cons 0) (idMatrix {n}))

-- Define matrix transposition
-- Induction step: add all elements of the new column at the top of all other (transposed) columns
-- TEST CASE: transpose (Cons (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons (Cons 4 (Cons 5 (Cons 6 Nil))) (Cons (Cons 7 (Cons 8 (Cons 9 Nil))) Nil)))
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = pure Nil
transpose (Cons xs xss) = vmap Cons xs <*> (transpose xss)
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
-- TEST CASE: plan {5}
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs (plan {n}))

-- Define a forgetful map, mapping Fin to Nat
-- TODO check with forget defined in the lecture
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs i) = Succ (forget i)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
-- TEST CASE: embed (Fs (Fs (Fs Fz)))
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs x) = Fs (embed x)

-- TEST CASE: correct (Fs (Fs (Fs Fz)))   gives Refl
correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs i) = cong Succ (correct i)

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
cmp Zero Zero = Equal                -- could have written Equal {Zero}
cmp Zero (Succ m) = LessThan m       -- there are m numbers in between Zero and (Succ m)
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k    = LessThan k
cmp (Succ n) (Succ .n)            | Equal         = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k      -- the result doesn't change, only the type changes

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
-- TEST CASES: difference 3 7
--             difference 7 3
--             difference 5 5
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k    = Succ k
difference n .n            | Equal         = Zero
difference .(m + Succ k) m | GreaterThan k = Succ k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation introduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

infixr 2 _⟨_⟩_
_⟨_⟩_ : (x : Nat) -> {y z : Nat} -> (x == y) -> (y == z) -> x == z
x ⟨ p ⟩ q = trans p q

_▪ : {A : Set} (x : A) -> x == x
_▪ x = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero m = sym (plusZero m)
plusCommutes (Succ n) m =
  Succ (n + m)                         -- this expression can be  automatically unified with (Succ n) + m, by defintion of _+_
  ⟨ cong Succ (plusCommutes n m) ⟩
  Succ (m + n)
  ⟨ plusSucc m n ⟩
  (m + (Succ n))
  ▪
-- alternatively -- less readable, but easier to understand what's going on for a beginner ;) :
--plusCommutes (Succ n) m = trans (cong Succ (plusCommutes n m)) (plusSucc m n)

-- Before we show distributivity of * over +, we need to show associativity of +:
plusAssociativity : (n m k : Nat) -> (n + (m + k)) == ((n + m) + k)
plusAssociativity Zero m k = Refl
plusAssociativity (Succ n) m k = cong Succ (plusAssociativity n m k) 

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl           -- Zero * ... immediately evaluates to Zero
distributivity (Succ n) m k =
  ((m + k) + (n * (m + k)))
   ⟨ cong (_+_ (m + k)) (distributivity n m k) ⟩                -- instead of _+_ (m + k), we could write \x -> (m + k) + x                 
  ((m + k) + ((n * m) + (n * k)))
   ⟨ cong (_+_ (m + k)) (plusCommutes (n * m) (n * k)) ⟩
  ((m + k) + ((n * k) + (n * m)))
   ⟨ sym (plusAssociativity m k ((n * k) + (n * m))) ⟩          -- sym because we need (_ + _) + _ = _ + (_ + _)
  (m + (k + ((n * k) + (n * m))))
   ⟨ cong (_+_ m) (plusAssociativity k (n * k) (n * m)) ⟩
  (m + ((k + (n * k)) + (n * m)))
   ⟨ cong (_+_ m) (plusCommutes (k + (n * k)) (n * m)) ⟩
  (m + ((n * m) + (k + (n * k))))
   ⟨ plusAssociativity m (n * m) (k + (n * k)) ⟩
  ((m + (n * m)) + (k + (n * k)))
   ▪

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {xs = Nil} = Base
SubListRefl {xs = Cons y ys} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base     Base     = Base
SubListTrans (Keep p) (Keep q) = Keep (SubListTrans p q)
SubListTrans (Drop p) (Keep q) = Drop (SubListTrans p q)
SubListTrans p        (Drop q) = Drop (SubListTrans p q)

-- for the antisymmetry, I define two extra functions.

-- Firstly, if x:xs is a sublist of ys, then so is xs
SubListSmaller : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList xs ys
SubListSmaller p = SubListTrans (Drop SubListRefl) p

-- Secondly, x:xs can never be a sublist of xs
SubListError : {a : Set} {x : a} {xs : List a} -> SubList (Cons x xs) xs -> Empty
SubListError (Keep p) = SubListError p
SubListError (Drop p) = SubListError (SubListSmaller p)

SubListAntiSym : {a : Set} {xs ys : List a} -> SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base Base = Refl
SubListAntiSym (Keep p) (Keep q) = cong (Cons _) (SubListAntiSym p q)
SubListAntiSym (Keep p) (Drop q) = cong (Cons _) (SubListAntiSym p (SubListSmaller q))
SubListAntiSym (Drop p) (Keep q) = cong (Cons _) (SubListAntiSym (SubListSmaller p) q)
-- The final case is the interesting one: if we obtained a superlist of xs by dropping the first element of ys,
-- and obtain a superlist of ys by dropping the first element of xs, we end up with a situation where
-- x:xs sub ys    and     y:ys sub xs
-- and hence y:x:xs sub y:ys sub xs, which is an error!
SubListAntiSym (Drop p) (Drop q) with SubListError (SubListTrans p (SubListSmaller q))
SubListAntiSym (Drop p) (Drop q) | ()


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Base : forall {n} -> LEQ Zero n
  Step : forall {n m} -> LEQ n m -> LEQ (Succ n) (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base     q        = Base
leqTrans (Step p) (Step q) = Step (leqTrans p q)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base     Base     = Refl
leqAntiSym (Step p) (Step q) = cong Succ (leqAntiSym p q)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= Base = Refl          -- Then necessarily n = 0, so n <= m == True by definition
leq<= (Step p) = leq<= p   -- p is a proof that n-1 <= m-1 is true. By the third line of <=-definition, n <= m follows immediately

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero      m       p = Base
<=leq (Succ n)  Zero    ()
<=leq (Succ n) (Succ m) p = Step (<=leq n m p)       -- automatic unification in p: (Succ n <= Succ m == True) with (n <= m == True) 

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP x = \y -> (y x)
{- Explanation:
   When given x of type P, and y of type P -> Empty (=Not P), apply y to x to get something of type Empty
   Constructive syntactic proof:
   [Not P]2   [P]1
   --------------- FALSUM-intro
        FALSUM
   --------------- Not-intro, 2
      Not Not P
   --------------- -> -intro, 1
    P -> Not Not P
-}

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
notNotExcludedMiddle = \x -> (x (Inr (\y -> x (Inl y))))

{-
  The λx in the above case corresponds to the introduction of [Not(P v Not P)]1 as an assumption,
  the λy corresponds to the introduction of [P]2 as an assumption.
  Constructive syntactic proof:

                    [P]2
                  --------- v-intro
                  P v Not P          [Not(P v Not P)]1
                  ------------------------------------ FALSUM-intro
                              FALSUM
                              ------ Not-intro, 2
                               Not P
                           ----------- v-intro
 [Not(P v Not P)]1          P v Not P
 ------------------------------------ Not-intro, 1
     Not Not (P v Not P) 

-}

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
step1 dn = dn notNotExcludedMiddle
-- it allows us to derive (P v Not P) from (Not Not (P v Not P)), which was already proven above


--auxiliary for step 2: commutativity of or:
commutativeOr : {P Q : Set} -> (Or P Q) -> (Or Q P)
commutativeOr x = orCase (\p -> Inr p) (\q -> Inl q) x
{-

The v-elim step corresponds to the orCase function that was provided.

            [Q]1             [P]1
           ------ v-intro   ------- v-intro
  Q v P     P v Q            P v Q
 ---------------------------------- v-elim, 1
         P v Q

-}

step2 : excludedMiddle -> impliesToOr
step2 em = \x -> orCase (\left -> Inl left) (\right -> Inr (x right)) (commutativeOr em)
{-
                        [P]2    [P->Q]1
                        ---------------- -> elim
Not P v P    [Not P]2       Q
---------------------------------------- v elim, 2
             Not P v Q
---------------------------------------- -> I, 1
          (P -> Q) -> (Not P) v Q

-}

identity : {A : Set} -> A -> A
identity x = x

exFalso : {P : Set} -> Empty -> P
exFalso ()

step3 : impliesToOr -> doubleNegation
step3  ito {P} h = orCase (\np -> exFalso (h np))
                          identity         -- p case
                          (ito identity)   --np v p
{-
  
  identity                  [Not P]2   [Not Not P]1
  --------                  ----------------------- -> elim
   P -> P     ito                FALSUM
  ---------------- -> elim      -------- exfalso
   (Not P) v P                     P                            [P]2
  ------------------------------------------------------------------- v-elim
                                   P
                           -----------------
                           (Not Not P) -> P

-}

-- HARDER: show that these are equivalent to Peirces law:
peircesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

step4 : excludedMiddle -> peircesLaw
step4 em = orCase (\p  -> \pqp -> p)
                  (\np -> \pqp -> pqp (\p -> exFalso (np p)))
                  em -- p v np
{- 
                                                                     [P]4     [Not P]1
                                                                     ------------------ -> elim
                                                                          FALSUM
                                                                        --------- FALSUM-elim
                                                                            Q
                                                                          ------ -> intro, 4
                          (here's the               [(P -> Q) -> P]3      P -> Q      
                          unused \pqp)              ----------------------------- -> elim
                              [P]1                                 P
                    -------------------- -> intro, 2   ---------------------- -> intro, 3
    P v Not P       ((P -> Q) -> P) -> P                ((P -> Q) -> P) -> P
   -------------------------------------------------------------------------- v-elim, 1
                            ((P -> Q) -> P) -> P

-}

step5 : peircesLaw -> excludedMiddle
step5 pl = pl (\x -> exFalso (notNotExcludedMiddle x))
{-
    notNotExcludedMiddle
    --------------------
    Not Not (P v Not P)    [Not (P v Not P)]1
    ----------------------------------------- -> elim
                     FALSUM
                   ----------- FALSUM-elim
                    P v Not P
    ------------------------------------------ -> intro, 1
     ((P v Not P) -> FALSUM) -> (P v Not P)                 Peirce (P := P v Not P, Q := FALSUM)
    --------------------------------------------------------------------------------------------- -> Elim
                                                   P v Not P  
-}


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

-- from the lecture:
data Type : Set where
  I : Type
  _=>_ : Type -> Type -> Type


-- The list of indices of the variables in the context (not necessarily de bruijn indices)
Context = List Nat

-- Helper type for the Term data type (see p.25 of the Agda tutorial)
data _∈_ {A : Set}(x : A) : List A -> Set where
  Head : ∀ {xs} -> x ∈ (Cons x xs)
  Tail : ∀ {xs y} -> x ∈ xs -> x ∈ (Cons y xs)

-- Helper function for the Term data type
index : {A : Set}{x : A}{xs : List A} -> (x ∈ xs) -> Nat
index Head = Zero
index (Tail p) = Succ (index p)

-- Well-scoped lambda terms:
data Term (Γ : Context) : Set where
  SLam : ∀ {n} -> Term (Cons n Γ) -> Term Γ   -- If the nth variable is in scope, abstracting over it will make it out of scope
                                              -- for use outside of the λ (unless, of course, it occurs multiple times in Γ)
  SApp : Term Γ -> Term Γ -> Term Γ           -- Function application does not change anything about the scope of the variables
  SVar : ∀ {n} -> n ∈ Γ -> Term Γ             -- If the nth variable is in scope (i.e. in context), we can use it as a valid term!

-- A function to transform a well-scoped lambda term into a raw term
-- TEST CASES: erase {Cons 5 Nil} (SVar Head)         => Var 0
--             erase {Nil} (SLam (SVar Head))         => Lam (Var 0)
--             erase {Cons 3 (Cons 5 Nil)} (SApp (SLam (SVar (Tail (Tail Head)))) (SVar Head))    => App (Lam (Var 2)) (Var 0)
--                              (in the last case, 5∈Γ is proven by "Tail (Tail Head)" because inside the lambda, the context (Γ) is [_,3,5])
erase : {Γ : Context} -> Term Γ -> Raw
erase (SLam t) = Lam (erase t)
erase (SApp t u) = App (erase t) (erase u)
erase (SVar p) = Var (index p) -- Just erase the proof that the variable is in scope, and rename to de Bruijn index
--erase (SVar {n} p) = Var n


-- Helper view lookup (see tutorial p 25)
length : {A : Set} -> List A -> Nat
length Nil = Zero
length (Cons x xs) = Succ (length xs)

data Lookup {A : Set}(xs : List A) : Nat -> Set where
  Inside : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
  Outside : (m : Nat) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : Nat) -> Lookup xs n
Nil ! n            = Outside n
Cons x xs ! Zero   = Inside x Head
Cons x xs ! Succ n with xs ! n
Cons x xs ! Succ .(index p)       | Inside y p = Inside y (Tail p)
Cons x xs ! Succ .(length xs + n) | Outside n  = Outside n

max : Nat -> Nat -> Nat
max Zero m = m
max (Succ n) Zero = Succ n
max (Succ n) (Succ m) = Succ (max n m)

data Infer (Γ : Context) : Raw -> Set where
  Ok  : (t : Term Γ) -> Infer Γ (erase t)
  Bad : {e : Raw} -> Infer Γ e


{-
Idea of infer function:
A raw term has de Bruijn indices (implicitly). We now use Γ to keep track of a list of λ-abstractions
(each with a fresh variable to avoid confusion), and use the lookup function to make sure we refer
to the correct abstraction: in a raw λ-term (with de Bruijn indices), the index of the variable refers
to the number of λ's enclosing the variable before the binding λ is encountered. This is reflected by the
length of the list Γ.

OK EXAMPLE: the term λ V0 λ (V1 V0). Here, the first V0 and V1 refer to the outer λ. The second V0
refers to the inner λ.

             [y,x] ⊢ V1 (**)     [y,x] ⊢ V0 (***)
              -----------------------------------
                     [y,x] ⊢ V1 V0
                     ---------------
[x] ⊢ V0 (*)         [x] ⊢ λ (V1 V0)
----------------------------------------
          [x] ⊢ V0 λ (V1 V0)
        ----------------------
          ∅ ⊢ λ V0 λ (V1 V0) 

(*)   OK because the 0th index in Γ (= [x]) is inhabited by a variable (i.e. there is a corresponding λ-abstraction).
      In the well-scoped term rewrite, this variable will be replaced by "x".
(**)  OK because the 1th index in Γ (= [y,x]) is inhabited. This variable will be replaced by "x".
(***) OK because the 0th index in Γ (= [y,x]) is inhabited. This variable will be replaced by "y".
The well-scoped term will be λx. x λy.(x y). Because we don't use x / y / etc as variable names, we find a "fresh variable"
by using a previously unused number. The term will then become λ0. 0 λ1.(0 1). (Note that these numbers do NOT correspond
one-to-one to the de Bruijn indices!!!)

BAD EXAMPLE: (λ V0) (λ (V0 V1))

                                                   
                               [y] ⊢ V0 (OK)         [y] ⊢ V1  (BAD *)
                               --------------------------------
  [x] ⊢ V0 (OK)                         [y] ⊢ V0 V1
  --------------                     -----------------
    ∅ ⊢ λ V0                           ∅ ⊢ λ (V0 V1)
   ---------------------------------------------------
                    ∅ ⊢ (λ V0) (λ (V0 V1))

(*) BAD because the 1th index (start counting from 0) in [y] is not inhabited, so there is
    no corresponding λ-abstraction. Hence, this term is not well-scoped.
Note, by the way, that even though in this proof we have given diffent fresh variable names (x / y)
in the different branches of the proof, our algorithm will not be able to do this: it will assign the
same "fresh" variable 0 to both branches. This is not a problem, however, because
       (λ x. x) (λ x. (x y)) is a perfectly valid (although not closed/well-scoped) λ-term.


-}

--Find a variable (= an index) that is not already in the list Γ.
freshVariable : Context -> Nat
freshVariable Nil = Zero
freshVariable (Cons x Γ) = max (Succ x) (freshVariable Γ)

--The infer function that checks whether or not a raw term is well-scoped
--and if so, it will return the well-scoped version of the term.
infer : (Γ : Context)(e : Raw) -> Infer Γ e

-- λ case: add a fresh variable to the start of the list.
-- 
--
--            [8,3,5,7] ⊢ RAW    <- if this one checks out ("OK t" for some well-scoped term t that uses only the free
--          -------------------     variables in [8,3,5,7]), we can infer the bottom line: λ will abstract over 8, the
--             [3,5,7] ⊢ λ RAW      resulting term λ t will be well-scoped and use only the free variables in [3,5,7].
--
--
infer Γ (Lam e) with infer (Cons (freshVariable Γ) Γ) e
infer Γ (Lam .(erase t)) | Ok t = Ok (SLam t)
infer Γ (Lam e)          | Bad  = Bad

-- Application case: both terms need to be OK for the entire term to be OK.
--
--    Γ ⊢ RAW1         Γ ⊢ RAW2    <- if both RAW1 and RAW2 are well-scoped, they can be turned into two Terms (t1 and t2),
--   ---------------------------      and the bottom term can be turned into the Term (t1 t2). If, however, at least one of
--       Γ ⊢ (RAW1 RAW2)              RAW1 and RAW2 is Bad, then the entire term is Bad.
--
infer Γ (App f a) with infer Γ f
infer Γ (App f a)           | Bad         = Bad                           -- if the functor is bad, the entire term is bad
infer Γ (App .(erase t₁) a) | Ok t₁ with infer Γ a                        -- if functor is Ok (rewrites to t₁), we need to check the argument
infer Γ (App .(erase t₁) a)           | Ok t₁  | Bad = Bad                -- if the argument is bad, the entire term is bad
infer Γ (App .(erase t₁) .(erase t₂)) | Ok t₁ | Ok t₂ = Ok (SApp t₁ t₂)   -- if both scope-check, then the entire term is ok!


-- Variable case: if we encounter the deBruijn index 2, that means that that variable
-- refers to a λ-abstraction that is (Succ 2) steps outside of the current term.
-- This λ-abstraction exists if and only if there are at least (Succ 2) elements in Γ,
-- that is, the index 2 in Γ is a valid lookup. In that case, we have immediately
-- found the name for the variable (it is stored in Γ at index 2), and the corresponding
-- proof that it is stored there. Otherwise, the term is not well-scoped.
infer Γ (Var n) with Γ ! n
infer Γ (Var .(index p))      | Inside n p = Ok (SVar p)
infer Γ (Var .(length Γ + n)) | Outside n  = Bad -- the variable is not in scope!

-- TEST CASES for infer: infer Nil           (Lam (App   (Var 0)   (Lam (App (Var 1) (Var 0)) )  ))
--                       --> OK λ0. (0 λ1.(1 0)) -- this was example 1
--
--                       infer Nil           (App (Lam   (Var 0))  (Lam (App (Var 1) (Var 0)) )   )
--                       --> BAD                 -- this was example 2
--
--                       infer (Cons 5 Nil) (App (Lam   (Var 0))  (Lam (App (Var 1) (Var 0)) )   )
--                       --> OK (λ6. 6) (λ6.(5 6))     -- in this case, the term is not closed,
--                                                     -- but it is well-scoped since the variable 5 is in the context.

