\begin{code}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

import Prelude hiding (GT)
import Data.Maybe
import qualified Generics.Regular as R

data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)

data GList f a = GNil | GCons a (GList f (f a))

data Bush a = Bush a (GList Bush (Bush a))

data HFix f a = HIn {hout :: f (HFix f) a}

data Exists b where
    Exists :: a -> (a -> b) -> Exists b

data Exp where
    Bool :: Bool -> Exp
    Int :: Int -> Exp
    GT :: Exp -> Exp -> Exp
    IsZero :: Exp -> Exp
    Succ :: Exp -> Exp
    If :: Exp -> Exp -> Exp -> Exp
\end{code}

Exercise 1
Tree   :: * -> * -> *
GList  :: (* -> *) -> * -> *
Bush   :: * -> *
HFix   :: ((* -> *) -> * -> *) -> * -> *
Exists :: * -> *
Exp    :: *


Exercise 2a
\begin{code}
-- raises and error, when no correct expression has been found
tryint :: Exp -> Int
tryint e = case eval e of
    Just e -> case e of
        Left i -> i
        otherwise -> error "Not an integer expression"
    Nothing -> error "Empty expression"

eval :: Exp -> Maybe (Either Int Bool)
eval (Bool b)   = Just $ Right b
eval (Int i)    = Just $ Left i
eval (GT e1 e2) = Just $ Right $ (tryint e1) > (tryint e2)
eval (IsZero e) = Just $ Right $ (tryint e == 0)
eval (Succ e)   = Just $ Left (tryint e + 1)
eval (If c t e) = case eval c of
    Just (Right True) -> eval t
    otherwise -> eval e
\end{code}

Exercise 2b
\begin{code}
data ExpF :: * -> * where
    BoolF   :: Bool -> ExpF r
    IntF    :: Int -> ExpF r
    GTF     :: r -> r -> ExpF r
    IsZeroF :: r -> ExpF r
    SuccF   :: r -> ExpF r
    IfF     :: r -> r -> r -> ExpF r

newtype Fix f = In {out :: f (Fix f)}
type Exp' = Fix ExpF
\end{code}

Exercise 2c
\begin{code}
instance Functor ExpF where
    --fmap :: (a -> b) -> f a -> f b
    fmap f (BoolF b) = BoolF b
    fmap f (IntF i) = IntF i
    fmap f (GTF r1 r2) = GTF (f r1) (f r2)
    fmap f (IsZeroF r) = IsZeroF (f r)
    fmap f (SuccF r) = SuccF (f r)
    fmap f (IfF c t e) = IfF (f c) (f t) (f e)

tryint' :: Maybe (Either Int Bool) -> Int
tryint' e = case e of
    Just a -> case a of
        Left i -> i
        otherwise -> error "Not an integer expression"
    Nothing -> error "Empty Expression"

evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg (BoolF b) = Just $ Right b
evalAlg (IntF i) = Just $ Left i
evalAlg (GTF e1 e2) = Just $ Right (tryint' e1 > tryint' e2)
evalAlg (IsZeroF e) = Just $ Right (tryint' e == 0)
evalAlg (SuccF e) = Just $ Left (tryint' e + 1)
evalAlg (IfF c t e) = case c of
    Just (Right True) -> t
    otherwise -> e

fold :: Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out
eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg
\end{code}

Exercise 2d
\begin{code}
data ExpTF :: (* -> *) -> * -> * where
    BoolTF      :: Bool -> ExpTF r Bool
    IntTF       :: Int  -> ExpTF r Int
    GTTF        :: r Int -> r Int -> ExpTF r Bool
    IsZeroTF    :: r Int -> ExpTF r Bool
    SuccTF      :: r Int -> ExpTF r Int
    IfTF        :: r Bool -> r a -> r a -> ExpTF r a

type ExpT' = HFix ExpTF
\end{code}
If an expression e :: Exp evaluates succesfull, but cannot be defined in ExpT',
it means is is not well typed. As the definition of Exp is not strict on the
types of expressions that can be given as an argument (every type of expression
is allowed).  ExpTF is stricter, for example it only allows succesors of Ints,
not Bools.


Exercise 2e
\begin{code}
class HFunctor f where
    hfmap :: (forall b. g b -> h b) -> f g a -> f h a

instance HFunctor ExpTF where
    hfmap f (BoolTF b) = BoolTF b
    hfmap f (IntTF i)  = IntTF i
    hfmap f (GTTF r1 r2) = GTTF (f r1) (f r2)
    hfmap f (IsZeroTF i) = IsZeroTF (f i)
    hfmap f (SuccTF i) = SuccTF (f i)
    hfmap f (IfTF c t e) = IfTF (f c) (f t) (f e)

hfold :: HFunctor f => (forall b. f r b -> r b) -> HFix f a -> r a
hfold f = f . hfmap (hfold f) . hout

newtype Id a = Id {unId :: a}
evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (BoolTF b) = Id b
evalAlgT (IntTF i) = Id i
evalAlgT (GTTF (Id e1) (Id e2)) = Id (e1 > e2)
evalAlgT (IsZeroTF (Id e)) = Id (e == 0)
evalAlgT (SuccTF (Id e)) = Id (e + 1)
evalAlgT (IfTF (Id c) (Id t) (Id e)) = Id (if c then t else e)
\end{code}

Exercise 3
\begin{code}
-- This is needed, so we can transform a list to a Regular
instance R.Regular [a] where
    from [] = R.L R.U
    from (a:as) = R.R (R.K a R.:*: R.I as)
    to = undefined -- we don't need it for now

type instance R.PF [a] = R.U R.:+: R.K a R.:*: R.I


class Children f where
    children' :: f a -> [a]

instance Children R.U where
    children' a = []

instance Children (R.K a) where
    children' x = []

instance Children b => Children (R.C a b) where
    children' (R.C x) = children' x

instance Children R.I where
    children' i = [R.unI i]

instance (Children f, Children g) => Children (f R.:+: g) where
    children' (R.L x) = children' x
    children' (R.R x) = children' x

instance (Children a, Children b) => Children (a R.:*: b) where
    children' (a R.:*: b) = children' a ++ children' b

children :: (R.Regular r, Children (R.PF r)) => r -> [r]
children = children' . R.from

example3 = children [1,2] == [[2]]
\end{code}


Exercise 4
\begin{code}
parents :: (R.Regular r, Children (R.PF r)) => r -> [r]
parents x | null $ children x   = []
          | otherwise           = x : parents (head $ children x)

example4 = parents [1,2,3] == [[1,2,3], [2,3], [3]]
\end{code}
