Theory of Programming and Types
Exercise Set 3
June 2015
3701441

---------------------------------------
Exercise 1
---------------------------------------
\begin{code}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

import qualified Generics.Regular as R

data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)
data GList f a = GNil | GConst a (GList f (f a))
data Bush a = Bush a (GList Bush (Bush a))
data HFix f a = HIn {hout :: f (HFix f) a}
data Exists b where
    Exists :: a -> ((a -> b) -> Exists b)
data Exp where
    Bool    :: Bool -> Exp
    Int     :: Int -> Exp
    GT      :: Exp -> Exp -> Exp
    IsZero  :: Exp -> Exp
    Succ    :: Exp -> Exp
    If      :: Exp -> Exp -> Exp -> Exp
\end{code}

Loading the above code into GHCi and consequently 
querying it for kind-information resulted in the following:

Tree :: * -> * -> *
GList :: (* -> *) -> * -> *
Bush :: * -> *
HFix :: ((* -> *) -> * -> *) -> * -> *
Exists :: * -> *
Exp :: *

---------------------------------------
Exercise 2
---------------------------------------

---
a
---

\begin{code}
eval :: Exp -> Maybe (Either Int Bool)
eval (Bool a) = Just (Right a)
eval (Int i) = Just (Left i)
eval (Main.GT i1 i2) = f e1 e2 where
                    e1 = eval i1
                    e2 = eval i2
                    f (Just (Left a)) (Just (Left b)) = Just (Right (a > b))
                    f _ _ = Nothing
eval (IsZero i) = f e where 
                    e = eval i
                    f (Just (Left a)) = Just (Right (a == 0))
                    f _ = Nothing
eval (Succ i) = f e where
                    e = eval i
                    f (Just (Left a)) = Just (Left (a +1))
                    f _ = Nothing
eval (If c b1 b2) = f ec eb1 eb2 where
                    ec = eval c
                    eb1 = eval b1
                    eb2= eval b2
                    f (Just (Right True)) (Just _) _ = eb1
                    f (Just (Right False)) _ (Just _) = eb2
                    f _ _ _ = Nothing
\end{code}

The above function pattern matches on the type of constructor.
Each function follows the same pattern: if applicable, it is 
checked whether the recursive arguments result in actual values. 
If this is the case, they will bill evaluated according to the 
expression's semantics.

A test case:

\begin{code}
test :: Exp
test = If (Main.GT (Int 3) (Int 4)) (Int 2) (Succ (Int 3))
\end{code}

*Main> eval test
Just (Left 4)

Yay!

---
b
---

\begin{code}
newtype Fix f = In {out :: f (Fix f)}
type Exp' = Fix ExpF

data ExpF r where
    BoolF   :: Bool -> ExpF r
    IntF    :: Int -> ExpF r
    GTF     :: r -> r -> ExpF r
    IsZeroF :: r -> ExpF r
    SuccF   :: r -> ExpF r
    IfF     :: r -> r -> r -> ExpF r



\end{code}
TODO:  Show that there is an isomorphism betwee these two types.
Write from/to functions. (Necessary?)

---
c
---

\begin{code}

instance Functor ExpF where
    fmap f (BoolF b)    = BoolF b
    fmap f (IntF i)     = IntF i
    fmap f (GTF e1 e2)  = GTF (f e1) (f e2)
    fmap f (IsZeroF e)  = IsZeroF (f e)
    fmap f (SuccF e)    = SuccF (f e)
    fmap g (IfF c t f)  = IfF (g c) (g t) (g f)

evalAlg :: (ExpF (Maybe (Either Int Bool))) -> (Maybe (Either Int Bool))
evalAlg (BoolF b)   = Just (Right b)
evalAlg (IntF i)    = Just (Left i)
evalAlg (GTF e1 e2) = f e1 e2 where
                        f (Just (Left a)) (Just (Left b)) = Just (Right (a > b))
                        f _ _ = Nothing
evalAlg (IsZeroF e) = f e where
                        f (Just (Left i)) = Just (Right (i == 0))   
                        f _ = Nothing
evalAlg (SuccF e)   = f e where
                        f (Just (Left i)) = Just (Left (i + 1))     
                        f _ = Nothing
evalAlg (IfF c t f) = g c t f where
                        g (Just (Right True)) (Just _) _ =  t
                        g (Just (Right False))  _ (Just _)  = f
                        g _ _ _ = Nothing                                       

fold :: Functor f => (f a -> a) -> Fix f -> a
fold f =  f . fmap (fold f) . out

eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg

\end{code}

I wrote the following test case, which is isomorphic to test (defined above):

\begin{code}
test' :: Exp'
test' = In (IfF (In (GTF (In (IntF 3)) (In (IntF 4)))) (In (IntF 2)) (In (SuccF (In (IntF 3)))))

\end{code}

The result:

*Main> eval test
Just (Left 4)
*Main> eval' test'
Just (Left 4)

---
d
---

\begin{code}
type ExpT' = HFix ExpTF

data ExpTF r a where
    BoolTF      :: Bool -> ExpTF r Bool
    IntTF       :: Int -> ExpTF r Int
    GTTF        :: r Int -> r Int -> ExpTF r Bool
    IsZeroTF    :: r Int-> ExpTF r Bool
    SuccTF      :: r Int -> ExpTF r Int
    IfTF        :: r Bool -> r b -> r b -> ExpTF r b
\end{code}

Consider the follwing expression e:

\begin{code}
e :: Exp
e = If (IsZero (Int 3)) (Succ (Int 3)) (Bool True)
\end{code}

 This evaluates just fine:

 *Main> eval e
Just (Right True)

However, ExpT' demands that the true and false branch of your 
IfTF-expression are of the same type.

---
e
---

\begin{code}

class HFunctor f where
    hfmap :: (forall b. g b -> h b) -> f g a -> f h a
    hfold :: HFunctor f => (forall b. f r b -> r b) -> HFix f a -> r a
    hfold f = f . hfmap (hfold f) . hout

newtype Id a = Id {unId :: a}   

evalT' :: ExpT' a -> a
evalT' = unId .  hfold evalAlgT

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (BoolTF b) = Id b
evalAlgT (IntTF i) = Id i
evalAlgT (GTTF (Id i1) (Id i2)) = Id (i1 > i2)
evalAlgT (IsZeroTF (Id i)) = Id (i == 0)
evalAlgT (SuccTF (Id i)) = Id (i + 1)
evalAlgT (IfTF (Id c) (Id t) (Id f)) = Id (if c then t else f)

instance HFunctor ExpTF where
    hfmap f (BoolTF b) = BoolTF b
    hfmap f (IntTF i) = IntTF i
    hfmap f (GTTF i1 i2) = GTTF (f i1) (f i2)
    hfmap f (IsZeroTF i) = IsZeroTF (f i)
    hfmap f (SuccTF i) = SuccTF (f i)
    hfmap g (IfTF c t f) = IfTF (g c) (g t) (g f)

\end{code}


---------------------------------------
Exercise 3
---------------------------------------
---
a
---

\begin{code}
children :: (R.Regular r, Children (R.PF r)) => r -> [r]
children = children' . R.from

class Children f where
    children' :: f r -> [r]

\end{code}

---
b
---

\begin{code}
instance Children R.U where
    children' u = []

instance Children (R.K a) where
    children' k =  []

instance Children f => Children (R.C c f) where
    children' (R.C x) = children' x

instance Children R.I where       
    children' (R.I r) = [r]

instance (Children f, Children g) => Children (f R.:+: g) where
    children' (R.L l) = children' l
    children' (R.R r) = children' r

instance (Children f, Children g) => Children (f R.:*: g) where
    children' (l R.:*: r) = children' l ++ children' r
\end{code}

\begin{code}

type instance (R.PF [a])  = R.U R.:+: (R.K a R.:*: R.I)

instance R.Regular [a] where
    from [] = R.L R.U
    from (x:xs) = R.R (R.K x R.:*: R.I xs)
    to (R.L R.U) = []
    to (R.R (R.K x R.:*: R.I xs)) = x:xs
\end{code}

---------------------------------------
Exercise 4
---------------------------------------

\begin{code}
parents :: (R.Regular r, Children (R.PF r), Subs (R.PF r)) => r -> [r]
parents r = filter (not . null . children) $ r : (subs $ R.from r)



class Subs f where
    subs :: (R.Regular r, Subs (R.PF r)) => f r -> [r]

instance Subs R.U where
    subs u =  []

instance Subs (R.K a) where
    subs k = []
instance Subs f => Subs (R.C c f) where
    subs (R.C x) = subs x
instance Subs R.I where
    subs (R.I r) = r : subs (R.from r)
    
instance (Subs f, Subs g) => Subs (f R.:+: g) where
    subs (R.L l) = subs l
    subs (R.R r) = subs r
            
instance (Subs f, Subs g) => Subs (f R.:*: g) where
    subs (l R.:*: r) = subs l ++ subs r                                
\end{code}