I wrote and tested this (Exercise3.lhs) using GHC 7.8.3
and regular-0.3.4.4.

We'll need some language extensions...

> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE TypeOperators #-}

> module Exercise3 where
> import Prelude hiding (GT)
> import qualified Generics.Regular as R

I included the following dummy main to satisfy some tools
that want to see it. It obviously does nothing.

> main :: IO ()
> main = return ()

Exercise 1

The kinds are as follows:

Tree : * -> * -> *
GList : (* -> *) -> * -> *
Bush : * -> *
HFix : ((* -> *) -> * -> *) -> * -> *
Exists : * -> *
Exp : *

Exercise 2

Definitions:

> data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)
> data GList f a = GNil | GCons a (GList f (f a))
> data Bush a = Bush a (GList Bush (Bush a))
> data HFix f a = HIn { hout :: f (HFix f) a }
> data Exists b where
>     Exists :: a -> (a -> b) -> Exists b
> data Exp where
>     Bool :: Bool -> Exp
>     Int :: Int -> Exp
>     GT :: Exp -> Exp -> Exp
>     IsZero:: Exp -> Exp
>     Succ :: Exp -> Exp
>     If :: Exp -> Exp -> Exp -> Exp

Part a)

Fortunately, Haskell has the handy feature of handling failing pattern matches
in a do-block using the Monad's fail method. For Maybe, fail is defined as
Nothing. The following implementation of eval makes use of this, forcing a
return value of Nothing whenever the type is incorrect. 

> eval :: Exp -> Maybe (Either Int Bool)
> eval (Bool b) = Just (Right b)
> eval (Int i) = Just (Left i)
> eval (GT a b) = do
>     Left ea <- eval a
>     Left eb <- eval b
>     return (Right (ea > eb))
> eval (IsZero i) = do
>     Left ei <- eval i
>     return (Right (ei == 0))
> eval (Succ i) = do
>     Left ei <- eval i
>     return (Left (1 + ei))
> eval (If c t e) = do
>     Right ec <- eval c
>     if ec then eval t else eval e

Part b)

This is simply done by replacing recursive occurrences with the parameter.

> data ExpF f where
>     BoolF :: Bool -> ExpF f
>     IntF :: Int -> ExpF f
>     GTF :: f -> f -> ExpF f
>     IsZeroF :: f -> ExpF f
>     SuccF :: f -> ExpF f
>     IfF :: f -> f -> f -> ExpF f

As given:

> newtype Fix f = In {out ::f (Fix f)}
> type Exp' = Fix ExpF

Part c)

This instance distributes the mapping action over the recursive occurrences.

> instance Functor ExpF where
>     fmap _ (BoolF b) = BoolF b
>     fmap _ (IntF i) = IntF i
>     fmap f (GTF a b) = GTF (f a) (f b)
>     fmap f (IsZeroF i) = IsZeroF (f i)
>     fmap f (SuccF i) = SuccF (f i)
>     fmap f (IfF c t e) = IfF (f c) (f t) (f e)

The same evaluation, but now the recursion is handled for us.

> evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
> evalAlg (BoolF b) = Just (Right b)
> evalAlg (IntF i) = Just (Left i)
> evalAlg (GTF a b) = do
>     Left ea <- a
>     Left eb <- b
>     return (Right (ea > eb))
> evalAlg (IsZeroF i) = do
>     Left ei <- i
>     return (Right (ei == 0))
> evalAlg (SuccF i) = do
>     Left ei <- i
>     return (Left (1 + ei))
> evalAlg (IfF c t e) = do
>     Right ec <- c
>     if ec then t else e

As given:

> fold :: Functor f => (f a -> a) -> Fix f -> a
> fold f = f . fmap (fold f) . out
> eval' :: Exp' -> Maybe (Either Int Bool)
> eval' = fold evalAlg

Part d)

> data ExpTF f a where
>     BoolTF :: Bool -> ExpTF f Bool
>     IntTF :: Int -> ExpTF f Int
>     GTTF :: f Int -> f Int -> ExpTF f Bool
>     IsZeroTF :: f Int -> ExpTF f Bool
>     SuccTF :: f Int -> ExpTF f Int
>     IfTF :: f Bool -> f a -> f a -> ExpTF f a
> type ExpT' = HFix ExpTF

ExpTF enforces that the branches of Ifs have the same type.
The following expression has no ExpTF equivalent, because the
then and else branches of the If have different types. 
(I named it ue instead of e to avoid name shadowing.)

> ue :: Exp
> ue = IsZero (If (Bool True) (Int 0) (Bool False))

It evaluates to a Just because the branch taken happens to have the
type required by IsZero (Int).

> evalue :: Maybe (Either Int Bool)
> evalue = eval ue -- yields Just (Right True)

Part e)

This is very similar to the ExpF Functor.

> instance HFunctor ExpTF where
>     hfmap _ (BoolTF b) = BoolTF b
>     hfmap _ (IntTF i) = IntTF i
>     hfmap f (GTTF a b) = GTTF (f a) (f b)
>     hfmap f (IsZeroTF i) = IsZeroTF (f i)
>     hfmap f (SuccTF i) = SuccTF (f i)
>     hfmap f (IfTF c t e) = IfTF (f c) (f t) (f e)

Because we have types now, we know that we get sensible values, so
the evaluation is very simple.

> evalAlgT :: ExpTF Id a -> Id a
> evalAlgT (BoolTF b) = Id b
> evalAlgT (IntTF i) = Id i
> evalAlgT (GTTF a b) = Id (unId a > unId b)
> evalAlgT (IsZeroTF i) = Id (unId i == 0)
> evalAlgT (SuccTF i) = Id (1 + unId i)
> evalAlgT (IfTF c t e) = if unId c then t else e

As given:

> class HFunctor f where
>     hfmap :: (forall b . g b -> h b) -> f g a -> f h a
> hfold :: HFunctor f => (forall b . f r b -> r b) -> HFix f a -> r a
> hfold f = f . hfmap (hfold f) . hout
> newtype Id a = Id {unId ::a}
> evalT' :: ExpT' a -> a
> evalT' = unId . hfold evalAlgT

Exercise 3 and Exercise 4

To run the examples for Exercises 3 and 4, we must unfortunately
manually define the Regular instance for lists.
(Or use Template Haskell to do it for us... well...)

> type instance R.PF [a] = R.U R.:+: (R.K a R.:*: R.I)

> instance R.Regular [a] where
>     from [] = R.L R.U
>     from (x : xs) = R.R (R.K x R.:*: R.I xs)
>     to (R.L R.U) = []
>     to (R.R (R.K x R.:*: R.I xs)) = x : xs

Exercise 3

Part a)

> class Children p where
>     children' :: p a -> [a]

Part b)

> instance Children R.U where
>     children' R.U = []
> instance Children (R.K a) where
>     children' (R.K v) = []
> instance Children f => Children (R.C c f) where
>     children' (R.C c) = children' c
> instance Children R.I where
>     children' (R.I r) = [r]
> instance (Children f, Children g) => Children (f R.:+: g) where
>     children' (R.L v) = children' v
>     children' (R.R v) = children' v
> instance (Children f, Children g) => Children (f R.:*: g) where
>     children' (l R.:*: r) = children' l ++ children' r

The completed product:

> children :: (R.Regular r, Children (R.PF r)) => r -> [r]
> children = children' . R.from

> example3 = children [1,2] == [[2]]

Exercise 4

There's no need to build a new class - Children is completely suitable
for calculating the parents. The strategy is to calculate v's children.
If it doesn't have any, v is not a parent, and if it does, v is a parent -
return it - and recurse on all the children found.

> parents :: (R.Regular r, Children (R.PF r)) => r -> [r]
> parents v = let vChildren = children v in
>     if null vChildren then [] else v : concatMap parents vChildren 

> example4 = parents [1,2,3] == [[1,2,3], [2,3], [3]]
