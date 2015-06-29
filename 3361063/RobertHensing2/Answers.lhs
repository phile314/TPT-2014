\documentclass[a4paper]{article}

% This file is both the module to load into ghci and the root file of the lhs2tex document

\usepackage{amsmath}
\usepackage{hyperref}
\hypersetup{colorlinks=true,allcolors=blue}
\usepackage{hypcap}

\usepackage[titletoc]{appendix}

%include lhs2TeX.fmt
%include lhs2TeX.sty

\usepackage{parskip}

\setlength{\parindent}{0pt}

%format -> = "\rightarrow"
%format => = "\Rightarrow"
%format <$> = "~\langle\$\rangle~"
%format <*> = "~\langle*\rangle~"

\author{Robert Hensing \\ 3361063}
\title{Theory of Programming and Types \\ Exercise 3}

\begin{document}
\maketitle
\tableofcontents

\newcommand{\noprint}[1]{}
\noprint{

> {-# LANGUAGE GADTs, KindSignatures, Rank2Types, FlexibleContexts, TypeOperators, TemplateHaskell, TypeFamilies	 #-}
> import Prelude hiding(GT)
> import Control.Applicative
> import Data.Bool
> import Data.Function
> import Control.Monad
> import Control.Monad.Identity
> import qualified Generics.Regular as R
> import Generics.Regular ((:*:)(..),(:+:)(..),C(..),S(..),K(..),I(..),U(..),PF)

}

\section {Exercise 1, datatype kinds}

> data Tree a b   = Tip a | Branch (Tree a b) b (Tree a b)
> data GList f a  = GNil | GCons a (GList f (f a))
> data Bush a     = Bush a (GList Bush (Bush a))
> data HFix f a   = HIn {hout::f (HFix f) a}
> data Exists b where
>   Exists  :: a -> (a -> b) -> Exists b
> data Exp where
>   Bool    :: Bool -> Exp
>   Int     :: Int -> Exp
>   GT      :: Exp -> Exp -> Exp
>   Add     :: Exp -> Exp -> Exp -- I have added this
>   IsZero  :: Exp -> Exp
>   Succ    :: Exp -> Exp
>   If      :: Exp -> Exp -> Exp -> Exp

These are the kinds of the types. The type aliases only provide a
place to put the kind signatures.

> type TreeK    = (Tree    :: * -> * -> *)
> type GListK   = (GList   :: (* -> *) -> * -> *)
> type BushK    = (Bush    :: * -> *)
> type HFixK    = (HFix    :: ((* -> *) -> * -> *) -> * -> *)
> type ExistsK  = (Exists  :: * -> *)
> type ExpK     = (Exp     :: *)

\section{Exercise 2}
\subsection{Exercise 2a, eval Exp}

The eval function evaluates Exps:

> eval :: Exp -> Maybe (Either Int Bool)
> eval (GT a b)    = asBool  <$>  ((>)    <$> evalInt a  <*> evalInt b)
> eval (Add a b)   = asInt   <$>  ((+)    <$> evalInt a  <*> evalInt b)
> eval (If c t e)  =              bool    <$> eval e   <*> eval t     <*> evalBool c
> eval (Bool b)    = return (asBool  b)
> eval (Int i)     = return (asInt   i)
> eval (IsZero n)  = asBool  <$> ((== 0)  <$> evalInt n)
> eval (Succ n)    = asInt   <$> ((+ 1)   <$> evalInt n)

> evalInt :: Exp -> Maybe Int
> evalInt e = eval e >>= safeLeft

> evalBool :: Exp -> Maybe Bool
> evalBool e = eval e >>= safeRight

> asInt = Left
> asBool = Right

> safeLeft :: Either a b -> Maybe a
> safeLeft (Left a)  = Just a
> safeLeft _         = Nothing

> safeRight :: Either a b -> Maybe b
> safeRight (Right b)  = Just b
> safeRight _          = Nothing

\subsection{Exercise 2b, Fix and Exp'}

We define Exp' isomorphically to Exp using Fix by defining ExpF

> newtype Fix f  = In { out :: f (Fix f) }
> type Exp'      = Fix ExpF

> data ExpF e where
>   Bool'    :: Bool ->         ExpF e
>   Int'     :: Int ->          ExpF e
>   GT'      :: e -> e ->       ExpF e
>   Add'     :: e -> e ->       ExpF e
>   IsZero'  :: e ->            ExpF e
>   Succ'    :: e ->            ExpF e
>   If'      :: e -> e -> e ->  ExpF e

\subsection{Exercise 2c, functor and algebra}

> instance Functor ExpF where
>   fmap f (Bool' b)    = Bool'    b
>   fmap f (Int' i)     = Int'     i
>   fmap f (GT' a b)    = GT'      (f a) (f b)
>   fmap f (Add' a b)   = Add'     (f a) (f b)
>   fmap f (IsZero' n)  = IsZero'  (f n)
>   fmap f (Succ' n)    = Succ'    (f n)
>   fmap f (If' c t e)  = If'      (f c) (f t) (f e)

> fold :: Functor f => (f a -> a) -> Fix f -> a
> fold f = f . fmap (fold f) . out
>   where out = undefined

> eval' :: Exp' -> Maybe (Either Int Bool)
> eval' = fold evalAlg
>   where
>     evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
>     evalAlg (Bool' b)    = Just (Right b)
>     evalAlg (Int' i)     = Just (Left i)
>     evalAlg (GT' a b)    = asBool <$> (  (>)  <$> getInt a <*> getInt b)
>     evalAlg (Add' a b)   = asInt  <$> (  (+)  <$> getInt a <*> getInt b)
>     evalAlg (IsZero' n)  = asBool <$> ((0 ==) <$> getInt n)
>     evalAlg (Succ' n)    = asInt  <$> ((1 +)  <$> getInt n)
>     evalAlg (If' c t e)  =               bool <$> e        <*> t        <*> getBool c
>
>     getBool   = (>>= safeRight)
>     getInt    = (>>= safeLeft)

\subsection{Exercise 2d, well-typed language}

> type ExpT' = HFix ExpTF
> data ExpTF e t where
>   PureTF    :: a ->                      ExpTF e a
>   GTTF      :: e Int -> e Int ->         ExpTF e Bool
>   AddTF     :: e Int -> e Int ->         ExpTF e Int
>   IsZeroTF  :: e Int ->                  ExpTF e Bool
>   SuccTF    :: e Int ->                  ExpTF e Int
>   IfTF      :: e Bool -> e a -> e a ->   ExpTF e a

This expression can be evaluated but would be ill-typed

> example = If (Bool True) (Succ (Int 12)  ) (Bool False)

An attempt to define the ill-typed expression in the well-typed representation:

< IfTF (PureTF True) (PureTF (12 :: Int)) (PureTF False) 

The Haskell type checker will complain that it can not match Int with Bool, as expected.

\subsection{Exercise 2e, HFunctor}

The assignment defines the following:

> class HFunctor f where
>   hfmap :: (forall b. g b -> h b) -> f g a -> f h a

> hfold :: HFunctor f => (forall b. f r b -> r b) -> HFix f a -> r a
> hfold f = f . hfmap (hfold f) . hout

> -- newtype Id a = Id { unId :: a }
> type Id = Identity -- I would rather re-use Identity
> unId = runIdentity

> evalT' :: ExpT' a -> a
> evalT' = unId . hfold evalAlgT

> evalAlgT :: ExpTF Id a -> Id a

These definitions can be used to implement the evaluation function:

> instance HFunctor ExpTF where
>   hfmap f (PureTF v)    = PureTF v
>   hfmap f (GTTF a b)    = GTTF (f a) (f b)
>   hfmap f (AddTF a b)   = AddTF (f a) (f b)
>   hfmap f (IsZeroTF a)  = IsZeroTF (f a)
>   hfmap f (SuccTF a)    = SuccTF (f a)
>   hfmap f (IfTF c t e)  = IfTF (f c) (f t) (f e)

The identity data type is an applicative functor, which is useful.

> evalAlgT (PureTF v)    = pure v
> evalAlgT (GTTF a b)    =   (>)   <$> a <*> b
> evalAlgT (AddTF a b)   =   (+)   <$> a <*> b
> evalAlgT (IsZeroTF a)  = (0 ==)  <$> a
> evalAlgT (SuccTF a)    = (1 +)   <$> a
> evalAlgT (IfTF c t e)  =  bool   <$> e <*> t <*> c

\section{Exercise 3, children}

This is the user-visible function:

> children :: (R.Regular r, Children (PF r)) => r -> [r]
> children = children' . R.from

> class Children f where
>   children' :: f a -> [a]

A recursive position has a single child

> instance Children I where
>   children' (I x) = [x]

The unit and constants have no children

> instance Children U where
>   children' _ = []

> instance Children (K f) where
>   children' _ = []

In case of a sum, use whichever we get

> instance (Children l, Children r) => Children (l :+: r) where
>   children' (L l) = children' l
>   children' (R r) = children' r

In case of a product, give both

> instance (Children l, Children r) => Children (l :*: r) where
>   children' (l :*: r) = children' l ++ children' r

Ignore any constructor or selector names

> instance (Children f) => Children (C c f) where
>   children' (C a) = children' a

> instance (Children f) => Children (S c f) where
>   children' (S a) = children' a

> $(R.deriveAll ''Exp "PFExp")
> type instance PF Exp = PFExp

@If@ in @Exp@ has three children

< length (children example ) == 3

\section{Exercise 4, parents}

The user-visible function:

> parents :: (R.Regular r, Parents (PF r), Children (PF r)) => r -> [r]
> parents x = includeself . parents' parents . R.from $ x
>   where includeself = if null (children x)
>                       then id
>	  	        else (x :)

Because @parents'@ needs access to the @parents@ function and the
proper @Parents@ context is lost, we need to pass it explicitly.

> class Parents f where
>   parents' :: (a -> [a]) -> f a -> [a]

Constant and unit have no children, so we don't need to look for
parents (children with children) in them.

> instance Parents I where
>   parents' p (I x) = p x

> instance Parents U where
>   parents' p _ = []

> instance Parents (K f) where
>   parents' p _ = []

In case of a sum, use whichever we get

> instance (Parents l, Parents r) => Parents (l :+: r) where
>   parents' p (L l) = parents' p l
>   parents' p (R r) = parents' p r

In case of a product, give both

> instance (Parents l, Parents r) => Parents (l :*: r) where
>   parents' p (l :*: r) = parents' p l ++ parents' p r

Ignore any constructor or selector names

> instance (Parents f) => Parents (C c f) where
>   parents' p (C a) = parents' p a

> instance (Parents f) => Parents (S c f) where
>   parents' p (S a) = parents' p a



\end{document}