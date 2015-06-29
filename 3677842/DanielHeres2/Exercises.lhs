\begin{code}
{-# LANGUAGE GADTs, ExistentialQuantification, RankNTypes, TypeOperators, FlexibleContexts, TypeFamilies #-}

import qualified Generics.Regular as G

data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)

data GList f a = GNil | GCons a (GList f (f a))

data Bush a = Bish a (GList Bush (Bush a))

data HFix f a = HIn {hout :: f (HFix f) a}

data Exists b where
    Exists :: a -> (a -> b) -> Exists b

data Exp where
    Bool :: Bool -> Exp
    Int :: Int -> Exp
    GT :: Exp -> Exp -> Exp
    IsZero :: Exp -> Exp
    Succ :: Exp -> Exp
    Add :: Exp -> Exp -> Exp
    If :: Exp -> Exp -> Exp -> Exp

\end{code}

Exercise 1 (Kinds)

Tree :: * -> * -> *

GList :: (* -> *) -> * -> *

Bush :: * -> *

HFix :: ((* -> *) -> * -> *) -> * -> *)

Exists :: * -> *

Exp : *

\begin{code}

-- Exercise 2a
eval :: Exp -> Maybe (Either Int Bool)
eval e =
    case e of
        Bool b ->
            Just (Right b)
        Int i ->
            Just (Left i)
        Main.GT l r ->
            do
                Left i <- eval l
                Left j <- eval r
                return . Right $ i > j
        IsZero n ->
            do
                Left m <- eval n
                return . Right $ m == 0
        Succ n ->
            do
                Left m <- eval n
                return . Left $ m + 1
        Add l r ->
            do
                Left i <- eval l
                Left j <- eval r
                return . Left $ i + j
        If b e f ->
            do
                Right c <- eval b
                if c then eval e else eval f


-- Exercise 2b
data ExpF a where
    BoolF :: Bool -> ExpF a
    IntF :: Int -> ExpF a
    GTF :: a -> a -> ExpF a
    IsZeroF :: a -> ExpF a
    SuccF :: a -> ExpF a
    AddF :: a -> a -> ExpF a
    IfF :: a -> a -> a -> ExpF a

data Fix f = In {out :: f (Fix f)}
type Exp' = Fix ExpF

-- Exercise 2c
instance Functor ExpF where
    fmap f e = case e of
        BoolF b ->
            BoolF b
        IntF i  ->
            IntF i
        GTF l r ->
            GTF (f l) (f r)
        IsZeroF n ->
            IsZeroF (f n)
        SuccF n ->
            SuccF (f n)
        AddF l r ->
            AddF (f l) (f r)
        IfF c e1 e2 ->
            IfF (f c) (f e1) (f e2)

evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg e = case e of
    BoolF b ->
        Just (Right b)
    IntF i ->
        Just (Left i)
    GTF l r ->
        do
            Left i <- l
            Left j <- r
            return . Right $ i > j
    IsZeroF n ->
        do
            Left m <-  n
            return . Right $ m == 0
    SuccF n ->
        do
            Left m <- n
            return . Left $ m + 1
    AddF l r ->
        do
            Left i <- l
            Left j <- r
            return . Left $ i + j
    IfF b e f ->
        do
            Right c <- b
            if c then e else f

fold :: Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalAlg

--Exercise 2d
data ExpTF f a where
    BoolTF :: Bool -> ExpTF f Bool
    IntTF :: Int -> ExpTF f Int
    GTTF :: f Int -> f Int -> ExpTF f Bool
    IsZeroTF :: f Int -> ExpTF f Bool
    SuccTF :: f Int -> ExpTF f Int
    AddTF :: f Int -> f Int -> ExpTF f Int
    IfTF :: f Bool -> f a -> f a -> ExpTF f a

type ExpT' = HFix ExpTF

\end{code}

An example would be an if expression with different types in the
two branches:

> If (Bool True) (Int 1) (Bool False)

\begin{code}
class HFunctor f where
    hfmap :: (forall b. g b -> h b) -> f g a -> f h a

--Exercise 2e
hfold :: HFunctor f => (forall b. f r b -> r b) -> HFix f a -> r a
hfold f = f . hfmap (hfold f) .  hout

newtype Id a = Id {unId :: a}

evalT'  :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

instance HFunctor ExpTF where
    hfmap f x =
        case x of
            BoolTF b ->
                BoolTF b
            IntTF i ->
                IntTF i
            GTTF l r ->
                GTTF (f l) (f r)
            IsZeroTF n ->
                IsZeroTF (f n)
            SuccTF i ->
                SuccTF (f i)
            AddTF i j ->
                AddTF (f i) (f j)
            IfTF b e e2 ->
                IfTF (f b) (f e) (f e2)


evalAlgT :: ExpTF Id a -> Id a
evalAlgT x =
    case x of
        BoolTF b ->
            Id b
        IntTF i ->
            Id i
        GTTF (Id l) (Id r) ->
            Id (l > r)
        IsZeroTF (Id n) ->
            Id (n == 0)
        SuccTF (Id i) ->
            Id (i + 1)
        AddTF (Id i) (Id j) ->
            Id (i + j)
        IfTF (Id b) (Id e) (Id e2) ->
            Id (if b then e else e2)

class Children c where
    children' :: c r -> [r]

instance Children G.U where
    children' _ = []

instance Children (G.K a) where
    children' (G.K _) = []

instance Children c => Children (G.C a c) where
    children' (G.C a) = children' a

instance Children G.I where
    children' (G.I a) = [a]

instance (Children c1, Children c2) => Children (c1 G.:+: c2) where
    children' (G.L a) = children' a
    children' (G.R b) = children' b

instance (Children c1, Children c2) => Children (c1 G.:*: c2) where
    children' (a G.:*: b) = children' a ++ children' b

example3 = children [1,2] == [[2]]

children :: (G.Regular a, Children (G.PF a)) => a -> [a]
children = children' . G.from

class Subs f where
    subs' :: (G.Regular a, Subs (G.PF a)) => f a -> [a]

instance Subs G.U where
    subs' _ = []

instance Subs (G.K a) where
    subs' (G.K _) = []

instance Subs f => Subs (G.C c f) where
    subs' (G.C a) = subs' a

instance Subs G.I where
    subs' (G.I a) = a : subs' (G.from a)

instance (Subs f, Subs g) => Subs (f G.:+: g) where
    subs' (G.L a) = subs' a
    subs' (G.R b) = subs' b

instance (Subs f, Subs g) => Subs (f G.:*: g) where
    subs' (a G.:*: b) = subs' a ++ subs' b

subs :: (G.Regular a, Subs (G.PF a)) => a -> [a]
subs = subs' . G.from

parents :: (G.Regular a, Children (G.PF a), Subs (G.PF a)) => a -> [a]
parents a = filter (not . null . children) (a : subs a)

instance G.Regular [a] where
    from [] = G.L G.U
    from (x:xs) = G.R (G.K x G.:*: G.I xs)
    to (G.L G.U) = [ ]
    to (G.R (G.K x G.:*: G.I xs)) = x : xs

type instance (G.PF) [a] = G.U G.:+: (G.K a G.:*: G.I)

example4 = parents ([1,2,3] :: [Int] )== [[1,2,3],[2,3],[3]]



\end{code}
