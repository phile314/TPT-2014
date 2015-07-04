\documentclass{article}
%include lhs2TeX.fmt
%include lhs2TeX.sty

\begin{document}

\begin{code}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
import qualified Generics.Regular as R
import Generics.Regular ((:+:), (:*:))
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Kinds}

\begin{code}
data Tree a b  = Tip a | Branch (Tree a b) b (Tree a b)
data GList f a = GNil | GCons a (GList f (f a))
data Bush a    = Bush a (GList Bush (Bush a))
data HFix f a = HIn { hout :: f (HFix f) a }
data Exists b where
  Exists :: a -> (a -> b) -> Exists b
data Exp where
  Bool   :: Bool              -> Exp
  Int    :: Int               -> Exp
  GT     :: Exp -> Exp        -> Exp
  IsZero :: Exp               -> Exp
  Succ   :: Exp               -> Exp
  If     :: Exp -> Exp -> Exp -> Exp
\end{code}
\\
The kind of \textbf{Tree} is   \texttt{* -> * -> *} \\
The kind of \textbf{GList} is  \texttt{(* -> *) -> * -> *} \\
The kind of \textbf{Bush} is   \texttt{* -> *} \\
The kind of \textbf{HFix} is   \texttt{((* -> *) -> * -> *) -> * -> *} \\
The kind of \textbf{Exists} is \texttt{* -> *} \\
The kind of \textbf{Exp} is    \texttt{*}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Exp}

\subsection{Evaluation (a)}

\begin{code}
eval :: Exp -> Maybe (Either Int Bool)
eval (Bool b) = Just $ Right b
eval (Int i)  = Just $ Left i
eval (Main.GT e1 e2) = evalGT (eval e1) (eval e2)
  where evalGT (Just (Left i1)) (Just (Left i2)) = Just $ Right (i1 > i2)
        evalGT _ _ = Nothing
eval (IsZero e) = evalIsZero (eval e)
  where evalIsZero (Just (Left i)) = Just $ Right (i == 0)
        evalIsZero _ = Nothing
eval (Succ e) = evalSucc (eval e)
  where evalSucc (Just (Left i)) = Just $ Left (i + 1)
        evalSucc _ = Nothing
eval (If c t e) = pickBranch (eval c)
  where pickBranch (Just (Right True)) = eval t
        pickBranch (Just (Right False)) = eval e
        pickBranch _ = Nothing
\end{code}


\subsection{Isomorphic fixpoint version (b)}

\begin{code}
newtype Fix f = In { out :: f (Fix f) }
type Exp' = Fix ExpF

data ExpF r where
  BoolF   :: Bool ->        ExpF r
  IntF    :: Int ->         ExpF r
  GTF     :: r -> r ->      ExpF r
  IsZeroF :: r ->           ExpF r
  SuccF   :: r ->           ExpF r
  IfF     :: r -> r -> r -> ExpF r
\end{code}
\\
\texttt{Exp'} is isomorphic to \texttt{Exp}.


\subsection{Evaluation algebra (c)}

\begin{code}
fold :: Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg

instance Functor ExpF where
  fmap _ (BoolF b)   = BoolF b
  fmap _ (IntF i)    = IntF i
  fmap f (GTF e1 e2) = GTF (f e1) (f e2)
  fmap f (IsZeroF e) = IsZeroF (f e)
  fmap f (SuccF e)   = SuccF (f e)
  fmap f (IfF c t e) = IfF (f c) (f t) (f e)

evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg (BoolF b)                               = Just $ Right b
evalAlg (IntF i)                                = Just $ Left i
evalAlg (GTF (Just (Left i1)) (Just (Left i2))) = Just $ Right (i1 > i2)
evalAlg (IsZeroF (Just (Left i)))               = Just $ Right (i == 0)
evalAlg (SuccF (Just (Left i)))                 = Just $ Left (i + 1)
evalAlg (IfF (Just (Right True)) t _)           = t
evalAlg (IfF (Just (Right False)) _ e)          = e
evalAlg _ = Nothing
\end{code}


\subsection{Well-typedness (d)}

\begin{code}
data ExpTF r t where
  BoolTF   :: Bool -> ExpTF r Bool
  IntTF    :: Int  -> ExpTF r Int
  GTTF     :: r Int -> r Int -> ExpTF r Bool
  IsZeroTF :: r Int -> ExpTF r Bool
  SuccTF   :: r Int -> ExpTF r Int
  IfTF     :: r Bool -> r t -> r t -> ExpTF r t

type ExpT' = HFix ExpTF
\end{code}
\\
An example of an expression \texttt {e :: Exp} that evaluates successfully but can not be defined as an \texttt{ExpT'} is \texttt{e = If (Bool True) (Int 1) (Bool False)}.


\subsection{Evaluation algebra (again) (e)}

\begin{code}
class HFunctor f where
  hfmap :: (forall b . g b -> h b) -> f g a -> f h a

hfold :: HFunctor f => (forall b . f r b -> r b) -> HFix f a -> r a
hfold f = f . hfmap (hfold f) . hout

newtype Id a = ID { unId :: a }

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

instance HFunctor ExpTF where
  hfmap _ (BoolTF b)   = BoolTF b
  hfmap _ (IntTF i)    = IntTF i
  hfmap f (GTTF e1 e2) = GTTF (f e1) (f e2)
  hfmap f (IsZeroTF e) = IsZeroTF (f e)
  hfmap f (SuccTF e)   = SuccTF (f e)
  hfmap f (IfTF c t e) = IfTF (f c) (f t) (f e)

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (BoolTF b)   = ID b
evalAlgT (IntTF i)    = ID i
evalAlgT (GTTF i1 i2) = ID (unId i1 > unId i2)
evalAlgT (IsZeroTF i) = ID (unId i == 0)
evalAlgT (SuccTF i)   = ID (unId i + 1)
evalAlgT (IfTF c t e) = if (unId c == True) then t else e
\end{code}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Child collection}

\begin{code}
type instance R.PF [a] = R.U :+: R.K a :*: R.I

instance R.Regular [a] where
  from []      = R.L R.U
  from (x:xs)  = R.R ((R.:*:) (R.K x) (R.I xs))
  to (R.L R.U) = []
  to (R.R ((R.:*:) (R.K x) (R.I xs))) = x:xs

children :: (R.Regular r, Children (R.PF r)) => r -> [r]
children = children' . R.from

class Children c where
  children' :: c r -> [r]

instance Children R.U where
  children' R.U = []

instance Children (R.K a) where
  children' (R.K a) = []

instance Children f => Children (R.C c f) where
  children' (R.C f) = children' f

instance Children R.I where
  children' (R.I r) = [r]

instance (Children f, Children g) => Children (f :+: g) where
  children' (R.L f) = children' f
  children' (R.R g) = children' g

instance (Children f, Children g) => Children (f :*: g) where
  children' ((R.:*:) f g) = children' f ++ children' g

example3 = children [1, 2] == [[2]]

\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Parent collection}

\begin{code}
parents :: (R.Regular r, AllChildren (R.PF r)) => r -> [r]
parents x = (filter $ not . null . children) (x : (allChildren' $ R.from x))

class Children c => AllChildren c where
  allChildren' :: (R.Regular r, AllChildren (R.PF r)) => c r -> [r]

instance AllChildren R.U where
  allChildren' R.U = []

instance AllChildren (R.K a) where
  allChildren' (R.K a) = []

instance AllChildren f => AllChildren (R.C c f) where
  allChildren' (R.C f) = allChildren' f

instance AllChildren R.I where
  allChildren' (R.I r) = r :  allChildren' (R.from r)

instance (AllChildren f, AllChildren g) => AllChildren (f :+: g) where
  allChildren' (R.L f) = allChildren' f
  allChildren' (R.R g) = allChildren' g

instance (AllChildren f, AllChildren g) => AllChildren (f :*: g) where
  allChildren' ((R.:*:) f g) = allChildren' f ++ allChildren' g

example4 = parents [1, 2, 3] == [[1, 2, 3], [2, 3], [3]]
\end{code}

\end{document}
