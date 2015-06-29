\documentclass{llncs}
\usepackage[english]{babel}
\usepackage{amsmath}
%\usepackage{amsthm}
\usepackage{amsfonts}
%\usepackage{proof}
\usepackage[usenames,dvipsnames]{color}
\usepackage[all]{xy}
\usepackage{wrapfig}
\usepackage{bussproofs}
\usepackage{bbold}

\newenvironment{TODO}{%
  \color{blue} \itshape \begin{itemize}
}{%
  \end{itemize}
}

\newcommand{\warnme}[1]{{\color{red} \textbf{$[$} #1 \textbf{$]$}}}


\title{Theory of Programming and Types, Exercise 3}

\author{Victor Cacciari Miraldo}

%include lhs2TeX.fmt

\begin{document}
\maketitle

\section*{Prelude}

\begin{code}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Exercise where

import qualified Generics.Regular.Base as R
\end{code}

\section{Exercise 1}

\begin{itemize}
 \item Kind Tree   $ = * \rightarrow * \rightarrow * $
 \item Kind GList  $ = (* \rightarrow *) \rightarrow * \rightarrow * $
 \item Kind Bush   $ = * \rightarrow * $
 \item Kind HFix   $ = ((* \rightarrow *) \rightarrow * \rightarrow *) \rightarrow * \rightarrow *$
 \item Kind Exists $ = * \rightarrow * $
 \item Kind Exp    $ = * $
\end{itemize}

\section{Exercise 2}
\subsection{A}
\begin{code}
data Exp where
  EBool  :: Bool -> Exp
  EInt   :: Int  -> Exp
  Gt     :: Exp  -> Exp -> Exp
  Add    :: Exp  -> Exp -> Exp
  IsZero :: Exp  -> Exp
  Succ   :: Exp  -> Exp
  If     :: Exp  -> Exp -> Exp -> Exp
  
pair :: a -> b -> (a , b)
pair a b = (a , b)
  
evalInt :: Exp -> Maybe Int
evalInt e = eval e >>= either return (const Nothing)

evalBool :: Exp -> Maybe Bool
evalBool e = eval e >>= either (const Nothing) return
  
eval :: Exp -> Maybe (Either Int Bool)
eval (EBool b) = return (Right b)
eval (EInt  n) = return (Left n)
eval (Add a b) = evalInt a >>= \av -> evalInt b
                           >>= return . Left . (av +)
eval (Gt a b)  = evalInt a >>= \av -> evalInt b 
                           >>= return . Right . (av >=)
eval (IsZero a)= evalInt a >>= return . Right . (== 0)
eval (Succ a)  = evalInt a >>= return . Left  . (+1)
eval (If c t e)
  = do
    b <- evalBool c
    if b then eval t else eval e
    
testExp :: Exp
testExp = If (IsZero (Succ (EInt 3))) (EInt 10) (EInt 15)
\end{code}

\subsection{B}
\begin{code}
data ExpF a
  = EFInt Int
  | EFBool Bool
  | EGt a a
  | EAdd a a
  | EIsZero a
  | ESucc a
  | EIf a a a
  
evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg (EFInt n)  = Just (Left n)
evalAlg (EFBool b) = Just (Right b)
evalAlg (EGt (Just (Left n)) (Just (Left m))) = Just (Right (n >= m))
evalAlg (EAdd (Just (Left n)) (Just (Left m))) = Just (Left (m + n))
evalAlg (EIsZero (Just (Left n))) = Just (Right (n == 0))
evalAlg (ESucc (Just (Left n))) = Just (Left (n+1))
evalAlg (EIf (Just (Right b)) t e) = if b then t else e
evalAlg _ = Nothing
\end{code}

\subsection{C}
\begin{code}  
instance Functor ExpF where
  fmap f (EGt a b)   = EGt (f a) (f b)
  fmap f (EAdd a b)  = EAdd (f a) (f b)
  fmap f (EIsZero x) = EIsZero (f x)
  fmap f (ESucc x)   = ESucc (f x)
  fmap f (EIf c t e) = EIf (f c) (f t) (f e)
  fmap f (EFInt n)   = EFInt n
  fmap f (EFBool b)  = EFBool b

newtype Fix f = In { out :: f (Fix f) }
type Exp' = Fix ExpF

toExp :: Exp' -> Exp
toExp (In (EFInt n)) =  EInt n
toExp (In (EFBool b)) = EBool b
toExp (In (EGt a b))  = Gt (toExp a) (toExp b)
toExp (In (EAdd a b)) = Add (toExp a) (toExp b)
toExp (In (EIsZero a)) = IsZero (toExp a)
toExp (In (ESucc a)) = Succ (toExp a)
toExp (In (EIf c t e)) = If (toExp c) (toExp t) (toExp e)

fromExp :: Exp -> Exp'
fromExp (EInt n) = In (EFInt n)
fromExp (EBool b) = In (EFBool b)
fromExp (Gt a b)  = In (EGt (fromExp a) (fromExp b))
fromExp (Add a b) = In (EAdd (fromExp a) (fromExp b))
fromExp (IsZero a) = In (EIsZero (fromExp a))
fromExp (Succ a)   = In (ESucc (fromExp a))
fromExp (If c t e) = In (EIf (fromExp c) (fromExp t) (fromExp e))

fold :: (Functor f) => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg
\end{code}

\subsection{D}
\begin{code}
data HFix f a = HIn { hout :: f (HFix f) a }

type ExpT' = HFix ExpTF

data ExpTF :: (* -> *) -> * -> * where
  ETInt    :: Int                  -> ExpTF a Int
  ETBool   :: Bool                 -> ExpTF a Bool
  ETAdd    :: a Int -> a Int       -> ExpTF a Int
  ETIsZero :: a Int                -> ExpTF a Bool
  ETGt     :: a Int -> a Int       -> ExpTF a Bool
  ETSucc   :: a Int                -> ExpTF a Int
  ETIf     :: a Bool -> a t -> a t -> ExpTF a t
  
impossible :: Exp
impossible = If (EBool True) (EInt 10) (EBool False)
\end{code}

\subsection{E}
\begin{code}  
newtype Id a = Id { unId :: a }
  
evalAlgT :: ExpTF Id t -> Id t
evalAlgT (ETInt n)             = Id n
evalAlgT (ETBool b)            = Id b
evalAlgT (ETAdd (Id a) (Id b)) = Id (a + b)
evalAlgT (ETIsZero (Id n))     = Id (n == 0)
evalAlgT (ETGt (Id a) (Id b))  = Id (a >= b)
evalAlgT (ETSucc (Id n))       = Id (n + 1)
evalAlgT (ETIf (Id b) t e)     = if b then t else e
  
class HFunctor f where
  hfmap :: (forall b . g b -> h b) -> f g a -> f h a
  
instance HFunctor ExpTF where
  hfmap f (ETInt i)    = ETInt i
  hfmap f (ETBool b)   = ETBool b
  hfmap f (ETAdd a b)  = ETAdd (f a) (f b)
  hfmap f (ETIsZero a) = ETIsZero (f a)
  hfmap f (ETGt a b)   = ETGt (f a) (f b)
  hfmap f (ETSucc a)   = ETSucc (f a)
  hfmap f (ETIf c t e) = ETIf (f c) (f t) (f e)
  
hfold :: HFunctor f => (forall b . f r b -> r b) -> HFix f a -> r a
hfold f = f . hfmap (hfold f) . hout

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT
\end{code}

\section{Exercise 3}
\begin{code}
class Children f where
  getChildren :: f a -> [ a ]
  
instance Children (R.K v) where
  getChildren (R.K a) = []
  
instance Children R.I where
  getChildren (R.I r) = [ r ] 
  
instance Children R.U where
  getChildren R.U = []
  
instance (Children f , Children g) => Children (f R.:+: g) where
  getChildren (R.L fr) = getChildren fr
  getChildren (R.R gr) = getChildren gr
  
instance (Children f , Children g) => Children (f R.:*: g) where
  getChildren (fr R.:*: gr) = getChildren fr ++ getChildren gr
  
instance (Children f) => Children (R.C c f) where
  getChildren (R.C fr) = getChildren fr

-- List instance of PF
type instance R.PF [a] = R.U R.:+: ((R.K a) R.:*: R.I)
instance R.Regular [a] where
  from []       = R.L R.U
  from (a : as) = R.R ((R.K a) R.:*: (R.I as))
  
  to (R.L R.U) = []
  to (R.R ((R.K a) R.:*: (R.I as))) = a : as

children :: (R.Regular r , Children (R.PF r)) => r -> [r]
children = getChildren . R.from

example3 :: Bool
example3 = (children [1,2] == [[2]])
\end{code}

\section{Exercise 4}
\begin{code}
parents :: (R.Regular r , Children (R.PF r)) => r -> [r]
parents r = case children r of
              [] -> []
              cs -> r : (concatMap parents cs)
              
example4 :: Bool
example4 = (parents [1,2,3] == [[1,2,3] , [2,3] , [3]])
\end{code}

\end{document}
