\begin{code}
{-# LANGUAGE GADTs, KindSignatures, InstanceSigs, RankNTypes #-}

module Exercise1 where

import Prelude hiding (GT)
import Data.Function (on)

\end{code}

1. What are the kinds of these datatypes?

\begin{code}
data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)

data GList f a = GNil | GCons a (GList f (f a))

data Bush a = Bush a (GList Bush (Bush a))

data HFix f a = HIn { hout :: f (HFix f) a }

data Exists b where
    Exists :: a -> (a -> b) -> Exists b

data Exp :: * where
    Bool   :: Bool -> Exp
    Int    :: Int  -> Exp
    GT     :: Exp  -> Exp -> Exp
    IsZero :: Exp  -> Exp
    Succ   :: Exp  -> Exp
    If     :: Exp  -> Exp -> Exp -> Exp
\end{code}

The kinds of the above datatypes are:
Tree :: * -> * -> *
GList :: (* -> *) -> * -> *
Bush :: * -> *
HFix :: ((* -> *) -> * -> *) -> * -> *
Exists :: * -> *
Exp :: *


2a. Write the eval function.

\begin{code}
eval :: Exp -> Maybe (Either Int Bool)
eval (Bool b)   = return $ Right b
eval (Int i)    = return $ Left i
eval (GT e1 e2) = do
    i1 <- eval e1
    i2 <- eval e2
    return . Right $ i1 > i2
eval (IsZero e) = eval e >>= either (return . Right . (== 0)) (const Nothing)
eval (Succ e)   = eval e >>= either (return . Left . succ) (const Nothing)
eval (If i t e) = eval i >>= \i' -> case i' of
    Right b -> eval (if b then t else e)
    _       -> Nothing
\end{code}

2b. Define ExpF such that Exp' is isomorphic to Exp

\begin{code}
newtype Fix f = In { out :: f (Fix f) }

data ExpF r
    = Bool' Bool
    | Int' Int
    | GT' r r
    | IsZero' r
    | Succ' r
    | If' r r r

type Exp' = Fix ExpF
\end{code}

2c. Give a functor instance and an evaluation algebra for ExpF

\begin{code}
instance Functor ExpF where
    fmap :: (a -> b) -> ExpF a -> ExpF b
    fmap _ (Bool' b) = Bool' b
    fmap _ (Int' i) = Int' i
    fmap f (GT' e1 e2) = (GT' `on` f) e1 e2
    fmap f (IsZero' e) = IsZero' $ f e
    fmap f (Succ' e) = Succ' $ f e
    fmap f (If' i t e) = If' (f i) (f t) (f e)

fold :: Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg exp = case exp of
    Bool' b                  -> return $ Right b
    Int' i                   -> return $ Left i
    GT' e1 e2                -> do i1 <- e1
                                   i2 <- e2
                                   return . Right $ i1 > i2
    IsZero' (Just (Left i))  -> return . Right $ i == 0
    Succ' (Just (Left i))    -> return . Left $ succ i
    If' (Just (Right b)) t e -> if b then t else e
    _                        -> Nothing

eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg
\end{code}


2d. Define ExpTF such that ExpT' is well-typed
\begin{code}
data ExpTF (r :: (* -> *)) a where
    BoolTF :: Bool -> ExpTF r Bool
    IntTF :: Int -> ExpTF r Int
    GTTF :: ExpTF r Int -> ExpTF r Int -> ExpTF r Bool
    IsZeroTF :: ExpTF r Int -> ExpTF r Bool
    SuccTF :: ExpTF r Int -> ExpTF r Int
    IfTF :: ExpTF r Bool -> ExpTF r a -> ExpTF r a -> ExpTF r a

type ExpT' = HFix ExpTF
\end{code}

What expression evaluates, but can't be defined in ExpT'?
?

2e. Give the HFunctor instance and the evaluation algebra
\begin{code}
class HFunctor f where
    hfmap :: (forall b. g b -> h b) -> f g a -> f h a

instance HFunctor ExpTF where
    hfmap :: (forall b. g b -> h b) -> ExpTF g a -> ExpTF h a
    hfmap f e = case e of
        BoolTF b   -> BoolTF b
        IntTF i    -> IntTF i
        GTTF i1 i2 -> GTTF (hfmap f i1) (hfmap f i2)
        IsZeroTF i -> IsZeroTF (hfmap f i)
        SuccTF i   -> SuccTF (hfmap f i)
        IfTF i t e -> IfTF (hfmap f i) (hfmap f t) (hfmap f e)

hfold :: HFunctor f => (forall b. f r b -> r b) -> HFix f a -> r a
hfold f = f . hfmap (hfold f) . hout

newtype Id a = Id {unId :: a}

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

evalAlgT :: ExpTF Id a -> Id a
evalAlgT e = case e of
    BoolTF b   -> Id b
    IntTF i    -> Id i
    GTTF i1 i2 -> Id $ ((>) `on` unId . evalAlgT) i1 i2
    IsZeroTF i -> Id . (== 0) . unId $ evalAlgT i
    SuccTF i   -> Id . succ . unId $ evalAlgT i
    IfTF i t e | unId (evalAlgT i) -> evalAlgT t
               | otherwise         -> evalAlgT e


\end{code}
