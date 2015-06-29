\begin{code}
{-#LANGUAGE GADTs, RankNTypes, FlexibleContexts, TypeOperators, TemplateHaskell, TypeFamilies #-}
module Exercises where

import Prelude hiding (GT)
import qualified Generics.Regular as R
import Generics.Regular.TH

-- Exercise 1

-- Tree     :: * -> * -> *
-- GList    :: (* -> *) -> * -> *
-- Bush     :: * -> *
-- HFix     :: ((* -> *) -> * -> *) -> * -> *
-- Exists   :: * -> *
-- Exp      :: *


-- Exercise 2

data Exp where
    Bool    :: Bool -> Exp
    Int     :: Int -> Exp
    GT      :: Exp -> Exp -> Exp
    IsZero  :: Exp -> Exp
    Succ    :: Exp -> Exp
    If      :: Exp -> Exp -> Exp -> Exp

-- a

eval :: Exp -> Maybe (Either Int Bool)
eval (Bool b) = Just $ Right b
eval (Int n) = Just $ Left n
eval (GT e1 e2) = case eval e1 of
                       Just (Left n) -> case eval e2 of
                                            Just (Left m) -> Just . Right $ if n > m then True else False
                                            _             -> Nothing
                       _             -> Nothing
eval (IsZero e) = case eval e of
                       Just (Left n) -> Just . Right $ if n == 0 then True else False
                       _             -> Nothing
eval (Succ e) = case eval e of
                     Just (Left n) -> Just . Left $ n + 1
                     _             -> Nothing
eval (If e1 e2 e3) = case eval e1 of
                          Just (Right True)  -> eval e2
                          Just (Right False) -> eval e3
                          _                  -> Nothing
                          
-- b
data ExpF a =
    BoolF   Bool a              |
    IntF    Int a               |
    GTF     (ExpF a) (ExpF a) a |
    IsZeroF (ExpF a) a          |
    SuccF   (ExpF a) a          |
    IfF     (ExpF a) (ExpF a) (ExpF a) a

newtype Fix f = In {out::f (Fix f)}

type Exp' = Fix ExpF

-- c

instance Functor ExpF where
    fmap f (BoolF b x)      = BoolF b (f x)
    fmap f (IntF n x)       = IntF n (f x)
    fmap f (GTF e1 e2 x)    = GTF (fmap f e1) (fmap f e2) (f x)
    fmap f (IsZeroF e x)    = IsZeroF (fmap f e) (f x)
    fmap f (SuccF e x)      = SuccF (fmap f e) (f x)
    fmap f (IfF e1 e2 e3 x) = IfF (fmap f e1) (fmap f e2) (fmap f e3) (f x)

evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg (BoolF b _)         = Just $ Right b
evalAlg (IntF n _)          = Just $ Left n
evalAlg (GTF e1 e2 _)       = case evalAlg e1 of
                                   Just (Left n) -> case evalAlg e2 of
                                                         Just (Left m) -> Just . Right $ if n > m then True else False
                                                         _             -> Nothing
                                   _             -> Nothing
evalAlg (IsZeroF e _)       = case evalAlg e of
                                   Just (Left n) -> Just . Right $ if n == 0 then True else False
                                   _             -> Nothing
evalAlg (SuccF e _)         = case evalAlg e of
                                   Just (Left n) -> Just . Left $ n + 1
                                   _             -> Nothing
evalAlg (IfF e1 e2 e3 _)    = case evalAlg e1 of
                                   Just (Right True)  -> evalAlg e2
                                   Just (Right False) -> evalAlg e3
                                   _                  -> Nothing

fold ::Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg


-- Some examples
fix :: (a -> a) -> a
fix f = f (fix f)

ex1' :: Exp'
ex1' = fix (In . BoolF True)

ex1 :: Exp
ex1 = Bool True

test1 :: Bool
test1 = eval ex1 == eval' ex1'

ex2' :: Exp'
ex2' = fix (In . IfF (BoolF True ex2') (SuccF (IntF 3 ex2') ex2') (BoolF False ex2'))

ex2 :: Exp
ex2 = If (Bool True) (Succ (Int 3)) (Bool False)

test2 :: Bool
test2 = eval ex2 == eval' ex2'


-- d
data HFix f a = HIn {hout::f (HFix f) a}

data ExpTF f t where
    BoolTF   :: (f Bool) -> ExpTF f Bool
    IntTF    :: (f Int) -> ExpTF f Int
    GTTF     :: ExpTF f Int -> ExpTF f Int -> ExpTF f Bool
    IsZeroTF :: ExpTF f Int -> ExpTF f Bool
    SuccTF   :: ExpTF f Int -> ExpTF f Int
    IfTF     :: ExpTF f Bool -> ExpTF f a -> ExpTF f a -> ExpTF f a

type ExpT' = HFix ExpTF

-- Answer to the question:
-- ex2 can't be defined in ExpT', because the branches of the if-then-else return expressions of different types
-- ex2 = If (Bool True) (Succ (Int 3)) (Bool False)


-- e
class HFunctor f where
    hfmap :: (forall b . g b -> h b) -> f g a -> f h a
    hfold ::HFunctor f => (forall b . f r b -> r b) -> HFix f a -> r a
    hfold f = f.hfmap (hfold f) . hout
    
newtype Id a = Id {unId :: a}

instance HFunctor ExpTF where
    hfmap f (BoolTF x) = BoolTF (f x)
    hfmap f (IntTF x) = IntTF (f x)
    hfmap f (GTTF e1 e2) = GTTF (hfmap f e1) (hfmap f e2)
    hfmap f (IsZeroTF e) = IsZeroTF (hfmap f e)
    hfmap f (SuccTF e) = SuccTF (hfmap f e)
    hfmap f (IfTF e1 e2 e3) = IfTF (hfmap f e1) (hfmap f e2) (hfmap f e3)

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (BoolTF b)         = b
evalAlgT (IntTF n)          = n
evalAlgT (GTTF e1 e2)       = Id $ if unId (evalAlgT e1) > unId (evalAlgT e2) then True else False
evalAlgT (IsZeroTF e)       = Id $ if unId (evalAlgT e) == 0 then True else False
evalAlgT (SuccTF e)         = Id $ unId (evalAlgT e) + 1
evalAlgT (IfTF e1 e2 e3)    = if unId (evalAlgT e1) then evalAlgT e2 else evalAlgT e3


-- Exercise 3
children :: (R.Regular r, Children (R.PF r)) => r -> [r]
children = children' . R.from

class Children f where
    children' :: f a -> [a]

instance Children R.U where
    children' x = []

instance Children (R.K a) where
    children' x = []
    
instance Children f => Children (R.C a f) where
    children' (R.C x) = children' x

instance Children R.I where
    children' (R.I x) = [x]
    
instance (Children f, Children g) => Children (f R.:+: g) where
    children' (R.L x) = children' x
    children' (R.R x) = children' x
    
instance (Children f, Children g) => Children (f R.:*: g) where
    children' (x R.:*: y) = children' x ++ children' y
    
-- Regular instance of lists for testing
data List a = Nil | Cons a (List a) deriving Show

$(deriveAll ''List "PFList")
type instance R.PF (List a) = PFList a

-- An example list
exList :: List Int
exList = Cons 4 . Cons 3 . Cons 2 . Cons 1 $ Nil

-- Exercise 4
parents :: (R.Regular r, Children (R.PF r)) => r -> [r]
parents x = case children x of
                 [] -> []
                 xs -> x : concatMap parents xs


\end{code}