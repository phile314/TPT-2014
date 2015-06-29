\documentclass{article}

\usepackage{listings}
\lstnewenvironment{code}{\lstset{language=Haskell,basicstyle=\small}}{}

\title{Exercises 3.1 and 3.2}
\author{F142001}
\date{June 19, 2015}

\begin{document}
\maketitle

Some preliminaries:
\begin{code}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

import Generics.LIGD
\end{code}


\section*{Exercise 1}
\begin{code}
data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)
\end{code}
Kind:        $* \rightarrow * \rightarrow *$\\
Explanation: one type for the inner nodes, and one type for the leafs. These types
             can be anything.

\begin{code}
data GList f a = GNil | GCons a (GList f (f a))
\end{code}
Kind:        $(* \rightarrow *) \rightarrow * \rightarrow *$\\
Explanation: The first argument must be a function that can take at least one argument
             (so it is of type $* \rightarrow *$). \texttt{Glist} then requires another argument.

\begin{code}
data Bush a = Bush a (GList Bush (Bush a))
\end{code}
Kind:        $* \rightarrow *$\\
Explanation: We only need to provide a single type (\texttt{a}), the rest is taken care of
             (i.e. the arguments of \texttt{GList} etc)

\begin{code}
data HFix f a = HIn {hout::f (HFix f) a}
\end{code}
Kind:        $((* \rightarrow *) \rightarrow * \rightarrow *) \rightarrow * \rightarrow *$\\
Explanation: This data type has two parameters. The second one, \texttt{a}, can be anything.
             The first one, \texttt{f}, has to be a function that can take at least to arguments:
             something of type \texttt{HFix f} (i.e. $* \rightarrow *$), and something of type \texttt{a} (i.e. $*$).

\begin{code}
data Exists b where
   Exists :: a -> (a -> b) -> Exists b
\end{code}
Kind:        $* \rightarrow *$\\
Explanation: Only the single type \texttt{b} is needed as a parameter. The type  \texttt{a} is also in there
             but it is not fixed as a parameter when we talk about the type \texttt{Exists b};
             this type still allows for any \texttt{x :: A} and \texttt{f :: A -> b} in order to provide the
             proof for the existence of something of type \texttt{b} (i.e. \texttt{f(x)}).

\begin{code}
data Exp where
   Bool   :: Bool -> Exp
   Int    :: Int -> Exp
   GrT    :: Exp -> Exp -> Exp
   IsZero :: Exp -> Exp
   Succ   :: Exp -> Exp
   If     :: Exp -> Exp -> Exp -> Exp
\end{code}
Kind:        $*$\\
Explanation: There are no parameters to fill in.






\section*{Exercise 2}
\subsection*{Exercise 2a}
I had to change the definition from \texttt{GT} to \texttt{GrT} in order to avoid
a conflict with \texttt{Prelude.GT}. Other than that, the code is pretty straightforward.

\begin{code}
eval :: Exp -> Maybe (Either Int Bool)
eval (Bool b)     = Just (Right b)
eval (Int  i)     = Just (Left i)
eval (GrT e1 e2)  = case eval e1 of
   Just (Left i1) -> case eval e2 of
      Just (Left i2)  -> Just (Right (i1 > i2))
      _ -> Nothing
   _ -> Nothing
eval (IsZero e)   = case eval e of
   Just (Left  i) -> Just (Right (i == 0))
   _              -> Nothing
eval (Succ e)     = case eval e of
   Just (Left  i) -> Just (Left (i+1))
   _              -> Nothing
eval (If c e1 e2) = case eval c of
   Just (Right True ) -> eval e1
   Just (Right False) -> eval e2
   _                  -> Nothing
\end{code}



\subsection*{Exercise 2b}
\texttt{ExpF} should be of kind $* \rightarrow *$ (in order to become an argument to \texttt{Fix}). \texttt{r} is the recursion parameter.

\begin{code}
newtype Fix f = In {out :: f (Fix f)}

data ExpF r where
  BoolF   :: Bool        -> ExpF r
  IntF    :: Int         -> ExpF r
  GTF     :: r -> r      -> ExpF r
  IsZeroF :: r           -> ExpF r
  SuccF   :: r           -> ExpF r
  IfF     :: r -> r -> r -> ExpF r
  
type Exp' = Fix ExpF
\end{code}
(Note that we could have written \texttt{data ExpF r = BoolF Bool | IntF Int | GTF r r | IsZeroF r | SuccF r | IfF r r r} if we wanted to
avoid the GADT-notation. But I think this is more readable, especially in relation to the definitions in the other exercises.

Below, I give the isomorphism between \texttt{Exp'} and \texttt{Exp}. I omit the proof that this is actually an isomorphism.
\begin{code}
iso_to :: Exp' -> Exp
iso_to (In (BoolF b))   = Bool   b
iso_to (In (IntF  i))   = Int    i
iso_to (In (GTF x y))   = GrT    (iso_to x) (iso_to y)
iso_to (In (IsZeroF x)) = IsZero (iso_to x)
iso_to (In (SuccF x))   = Succ   (iso_to x)
iso_to (In (IfF c t e)) = If     (iso_to c) (iso_to t) (iso_to e)

iso_from :: Exp -> Exp'
iso_from (Bool b)   = In (BoolF b)
iso_from (Int  i)   = In (IntF  i)
iso_from (GrT x y)  = In (GTF (iso_from x) (iso_from y))
iso_from (IsZero x) = In (IsZeroF (iso_from x))
iso_from (Succ x)   = In (SuccF (iso_from x))
iso_from (If c t e) = In (IfF (iso_from c) (iso_from t) (iso_from e))
\end{code}




\subsection*{Exercise 2c}
\begin{code}
instance Functor ExpF where
  fmap f (BoolF b)   = BoolF   b
  fmap f (IntF  i)   = IntF    i
  fmap f (GTF x y)   = GTF     (f x) (f y)
  fmap f (IsZeroF x) = IsZeroF (f x)
  fmap f (SuccF x)   = SuccF   (f x)
  fmap f (IfF c t e) = IfF     (f c) (f t) (f e)
\end{code}

The following definition is given in the pdf file of the exercise:
\begin{code}
fold :: Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out
\end{code}

From type signatures of \texttt{ExpF} and \texttt{fold}, we deduce the type signature of \texttt{evalAlg}
\begin{code}
evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg (BoolF  b) = Just (Right b)
evalAlg (IntF   i) = Just (Left  i)
evalAlg (GTF     (Just (Left i)) (Just (Left j))) = Just (Right (i > j))
evalAlg (GTF     _               _              ) = Nothing
evalAlg (IsZeroF (Just (Left i))) = Just (Right (i == 0))
evalAlg (IsZeroF _              ) = Nothing
evalAlg (SuccF   (Just (Left i))) = Just (Left (i + 1))
evalAlg (SuccF   _              ) = Nothing
evalAlg (IfF     (Just (Right True )) (Just t) _) = Just t
evalAlg (IfF     (Just (Right False)) _ (Just e)) = Just e
evalAlg (IfF     _                    _        _) = Nothing

eval' ::Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg
\end{code}



Here are some testing examples for \texttt{eval'}:
\begin{code}
example :: Exp'
example = In (IfF (In (BoolF False)) (In (IntF 5)) (In (IntF 6)))

example2 :: Exp'
example2 = In (SuccF (In (IntF 5)))

example3 :: Exp'
example3 = In (IfF (In (GTF (In (IntF 7)) (In (IntF 8)))) (In (SuccF (In (IntF 5)))) (In (BoolF True)))
\end{code}



\subsection*{Exercise 2d}
To become an argument to \texttt{HFix}, \texttt{ExpTF} should have kind $(* \rightarrow *) \rightarrow * \rightarrow *$

\begin{code}
data ExpTF r a where
  BoolTF   :: Bool                 -> ExpTF r Bool
  IntTF    :: Int                  -> ExpTF r Int
  GTTF     :: r Int  -> r Int      -> ExpTF r Bool
  IsZeroTF :: r Int                -> ExpTF r Bool
  SuccTF   :: r Int                -> ExpTF r Int
  IfTF     :: r Bool -> r a -> r a -> ExpTF r a
  
type ExpT' = HFix ExpTF
\end{code}

Example of an expression \texttt{e::Exp} that cannot be defined as an \texttt{ExpT'}:
\begin{code}
ex2d::Exp
ex2d = If (Bool True) (Bool True) (Int 1)
\end{code}
For the untyped version, we can simply evaluate this (the condition evaluates to true, so we pick the boolean value).
For \texttt{ExpT'}, in order to define an \texttt{If}-expression, we need both arguments to be of the same type (not bool/int like in the example above).

\subsection*{Exercise 2e}
The code below is similar to the previous cases, only with some extra (typing) parameters.
\begin{code}
class HFunctor f where
  hfmap :: (forall b . g b -> h b) -> f g a -> f h a
  
instance HFunctor ExpTF where
  hfmap p (BoolTF b)   = BoolTF   b
  hfmap p (IntTF  i)   = IntTF    i
  hfmap p (GTTF x y)   = GTTF     (p x) (p y)
  hfmap p (IsZeroTF x) = IsZeroTF (p x)
  hfmap p (SuccTF   x) = SuccTF   (p x)
  hfmap p (IfTF c t e) = IfTF     (p c) (p t) (p e)

hfold :: HFunctor f => (forall b . f r b -> r b) -> HFix f a -> r a
hfold f = f.hfmap (hfold f) . hout

newtype Id a = Id {unId :: a}

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (BoolTF b)            = Id b
evalAlgT (IntTF  i)            = Id i
evalAlgT (GTTF (Id i) (Id j))  = Id (i > j)
evalAlgT (IsZeroTF (Id i))     = Id (i == 0)
evalAlgT (SuccTF (Id i))       = Id (i+1)
evalAlgT (IfTF (Id True)  t e) = t
evalAlgT (IfTF (Id False) t e) = e

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT
\end{code}

Test with: ("If 5 > 38 then 10 else succ-10")
\begin{code}
exampleH = HIn (IfTF (HIn (GTTF (HIn (IntTF 5)) (HIn (IntTF 38)))) (HIn (IntTF 10)) (HIn (SuccTF (HIn (IntTF 10)))))
\end{code}

Exercises 3, 4 and 5 are to be found in the next document!

\end{document}


