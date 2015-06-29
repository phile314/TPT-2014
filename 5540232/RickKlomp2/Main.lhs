\begin{code}
{-# LANGUAGE GADTs, KindSignatures, RankNTypes, FlexibleContexts, TypeOperators, NoMonomorphismRestriction, TypeFamilies #-}
module Main where

import qualified Generics.Regular as R
\end{code}

Exercise 1:

Tree kind: * -> * -> *
GList kind: (* -> *) -> * -> *
Bush kind: * -> *
HFix kind: ((* -> *) -> * -> *) -> * -> *
Exists kind: * -> *
Exp kind: *



Exercise 2:

a.

\begin{code}
data Exp where
  Bool   :: Bool              -> Exp
  Int    :: Int               -> Exp
  GT     :: Exp -> Exp        -> Exp
  IsZero :: Exp               -> Exp
  Succ   :: Exp               -> Exp
  Add    :: Exp -> Exp        -> Exp
  If     :: Exp -> Exp -> Exp -> Exp

eval :: Exp -> Maybe (Either Int Bool)
eval (Bool b) = Just (Right b)
eval (Int i)  = Just (Left i)
eval (Main.GT e1 e2)
  = do
  e1' <- eval e1
  e2' <- eval e2
  case e1' of
    (Left i) -> case e2' of
                  (Left j) -> Just (Right (i > j))
                  _        -> Nothing
    _        -> Nothing
eval (IsZero e)
  = do
  e' <- eval e
  case e' of
    (Left i) -> Just (Right (i == 0))
    _        -> Nothing
eval (Succ e)
  = do
  e' <- eval e
  case e' of
    (Left i) -> Just (Left (i + 1))
    _        -> Nothing
eval (Add e0 e1)
  = do
  e0' <- eval e0
  e1' <- eval e1
  case e0' of
    (Left i) -> case e1' of
                  (Left j) -> Just (Left (i + j))
                  _        -> Nothing
    _        -> Nothing
eval (If e0 e1 e2)
  = do
  e0' <- eval e0
  case e0' of
    (Right True)  -> eval e1
    (Right False) -> eval e2
    _             -> Nothing
\end{code}

b.

\begin{code}
newtype Fix f = In {out :: f (Fix f)}
type Exp' = Fix ExpF

data (ExpF a) where
  FI      :: Int  -> ExpF a
  FB      :: Bool -> ExpF a
  FGT     :: a -> a -> ExpF a
  FIsZero :: a -> ExpF a
  FSucc   :: a -> ExpF a
  FAdd    :: a -> a -> ExpF a
  FIf     :: a -> a -> a -> ExpF a
\end{code}

c.

\begin{code}
instance Functor ExpF where
  fmap eval (FI i) = FI i
  fmap eval (FB b) = FB b
  fmap eval (FGT e1 e2) = FGT (eval e1) (eval e2)
  fmap eval (FIsZero e) = FIsZero (eval e)
  fmap eval (FSucc e) = FSucc (eval e)
  fmap eval (FAdd e1 e2) = FAdd (eval e1) (eval e2)
  fmap eval (FIf e1 e2 e3) = FIf (eval e1) (eval e2) (eval e3)

fold :: Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg

evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg (FI i) = Just (Left i)
evalAlg (FB b) = Just (Right b)
evalAlg (FGT (Just (Left i)) (Just (Left j))) | i > j     = Just (Right True)
                                              | otherwise = Just (Right False)
evalAlg (FIsZero (Just (Left i))) | i == 0    = Just (Right True)
                                  | otherwise = Just (Right False)
evalAlg (FSucc (Just (Left i))) = Just (Left (i + 1))
evalAlg (FAdd (Just (Left i)) (Just (Left j))) = Just (Left (i + j))
evalAlg (FIf (Just (Right b)) e1 e2) | b         = e1
                                     | otherwise = e2
\end{code}

d.

\begin{code}
data HFix f a = HIn { hout :: f (HFix f) a }
type ExpT' = HFix ExpTF

data ExpTF :: (* -> *) -> * -> * where
  TI      :: Int    -> ExpTF a Int
  TB      :: Bool   -> ExpTF a Bool
  TGT     :: a Int  -> a Int        -> ExpTF a Bool
  TIsZero :: a Int  -> ExpTF a Bool
  TSucc   :: a Int  -> ExpTF a Int
  TAdd    :: a Int  -> a Int        -> ExpTF a Int
  TIf     :: a Bool -> a b          -> a b          -> ExpTF a b
\end{code}
Answer to 2d: <if True then 4 else False> can be evaluated by eval, but cannot be defined using ExpT'

e.

\begin{code}
class HFunctor f where
  hfmap :: (forall b. g b -> h b) -> f g a -> f h a

hfold :: HFunctor f => (forall b. f r b -> r b) -> HFix f a -> r a
hfold f = f.hfmap (hfold f) . hout

newtype Id a = Id { unId :: a }

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (TI i) = Id $ i
evalAlgT (TB b) = Id $ b
evalAlgT (TGT e1 e2) | unId e1 > unId e2 = Id $ True
                     | otherwise         = Id $ False
evalAlgT (TIsZero e) | unId e == 0 = Id $ True
                     | otherwise   = Id $ False
evalAlgT (TSucc e) = Id $ unId e + 1
evalAlgT (TAdd e1 e2) = Id $ unId e1 + unId e2
evalAlgT (TIf e1 e2 e3) | unId e1   = e2
                        | otherwise = e3

instance HFunctor ExpTF where
  hfmap eval (TI i) = TI i
  hfmap eval (TB b) = TB b
  hfmap eval (TGT e1 e2) = TGT (eval e1) (eval e2)
  hfmap eval (TIsZero e) = TIsZero (eval e)
  hfmap eval (TSucc e) = TSucc (eval e)
  hfmap eval (TAdd e1 e2) = TAdd (eval e1) (eval e2)
  hfmap eval (TIf e1 e2 e3) = TIf (eval e1) (eval e2) (eval e3)
\end{code}

Exercise 3

a.

\begin{code}
class Children f where
  children' :: f a -> [a]
\end{code}

b.

\begin{code}
instance R.Regular [a] where
  from [] = R.L R.U
  from (a:as) = R.R (R.K a R.:*: R.I as)
  to = undefined -- Not used

type instance R.PF [a] = R.U R.:+: R.K a R.:*: R.I

instance Children R.U where
  children' _ = []

instance Children (R.K a) where
  children' _ = []

instance Children (R.I) where
  children' i = [R.unI i]

instance Children (R.C a b) where
  children' (R.C v) = []

instance (Children f, Children g) => Children (f R.:+: g) where
  children' (R.L a) = children' a
  children' (R.R a) = children' a

instance (Children f, Children g) => Children (f R.:*: g) where
  children' (a R.:*: b) = children' a ++ children' b


children :: (R.Regular r, Children (R.PF r)) => r -> [r]
children = children' . R.from

example3 = children [1,2,3]
\end{code}

Exercise 4

\begin{code}
parents :: (R.Regular r, Children (R.PF r)) => r -> [r]
parents x | null $ children x = []
          | otherwise         = x : parents (head $ children x)


example4 = parents [1,2,3]
\end{code}
