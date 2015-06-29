-- Morten Asscheman (3821382)

{-# LANGUAGE GADTs, KindSignatures, RankNTypes, ImpredicativeTypes, FlexibleContexts, TypeOperators, TypeFamilies #-}


import Data.Maybe (fromJust)
import Data.Functor
import Generics.Regular as R hiding (In, Fix, fold, out)

data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)
data GList f a = GNil | GCons a (GList f (f a))
data Bush a = Bush a (GList Bush (Bush a))
data HFix f a = HIn {hout::f (HFix f) a}

data Exists b where
    Exists :: a -> (a -> b) -> Exists b

data Exp where
    Bool    :: Bool -> Exp
    Int     :: Int  -> Exp
    Gt      :: Exp  -> Exp -> Exp
    IsZero  :: Exp  -> Exp
    Succ    :: Exp  -> Exp
    If      :: Exp  -> Exp -> Exp -> Exp
    deriving (Show)

--Exercise 1

--The kind of each datatype:
--Tree    :: * -> * -> *
--GList   :: (* -> *) -> * -> *
--Bush    :: * -> *
--HFix    :: ((* -> *) -> * -> *) -> * -> *
--Exists  :: * -> *
--Exp     :: * 


--Exercise 2 a


--A function that runs some test cases/sanity checks
executeExpTests = mapM_ (executeTest eval) expTests

executeTest f (label, expr) = print $ label ++ ": " ++ (show $ f expr)

--Some test cases i've defined
expTests = [
    ("True",                    Bool True),
    ("False",                   Bool False),
    ("5",                       Int 5),
    ("5 > 4",                   Gt (Int 5) (Int 4)),
    ("4 > 4",                   Gt (Int 4) (Int 4)),
    ("4 > True",                Gt (Int 4) (Bool True)),
    ("isZero 5",                IsZero (Int 5)),
    ("isZero 0",                IsZero (Int 0)),
    ("isZero True",             IsZero (Bool True)),
    ("Succ 0",                  Succ (Int 0)),
    ("Succ True",               Succ (Bool True)),
    ("If True then 5 else 4",   If (Bool True) (Int 5) (Int 4)),
    ("If False then 5 else 4",  If (Bool False) (Int 5) (Int 4)),
    ("If IsZero 0 then False else 4", 
        If (IsZero (Int 0)) (Bool False) (Int 4)),
    ("If 5 then False else 4", 
        If (Int 5) (Bool False) (Int 4)),
    ("If (If False then False else True) then False else 4", 
        If (If (Bool False) (Bool False) (Bool True)) (Bool False) (Int 4))
    ]

--Shortcut for the result of an evaluation
type Code = Maybe (Either Int Bool)

toBool :: Bool -> Code
toBool = Just . Right

toInt :: Int -> Code
toInt = Just . Left


-------
--Evaluating Exp
-------

eval :: Exp -> Code
eval (Bool a) = toBool a
eval (Int a)  = toInt a
eval (Gt e1 e2) = do
    e1' <- eval e1
    e2' <- eval e2
    evalGt e1' e2'
eval (IsZero e) = eval e >>= evalIsZero
eval (Succ n) = eval n >>= evalSucc
eval (If c t f) = do
    c' <- eval c
    e  <- evalIf c' t f
    eval e



evalGt :: (Either Int Bool) -> (Either Int Bool) -> Code
evalGt (Left a) (Left b) = toBool $ a > b
evalGt _ _ = Nothing

evalIsZero :: (Either Int Bool) -> Code
evalIsZero (Left 0) = toBool True
evalIsZero (Left _) = toBool False
evalIsZero _ = Nothing

evalSucc :: (Either Int Bool) -> Code
evalSucc (Left n) = toInt (n + 1)
evalSucc _ = Nothing

evalIf :: (Either Int Bool) -> Exp -> Exp -> Maybe Exp
evalIf (Right True) t _  = Just t 
evalIf (Right False) _ f = Just f 
evalIf _ _ _ = Nothing



--Exercise 2 b

newtype Fix f = In { out::f (Fix f) }
type Exp' = Fix ExpF

data ExpF r where
    BoolF   :: Bool ->              ExpF r
    IntF    :: Int  ->              ExpF r
    GtF     :: r    -> r ->         ExpF r
    IsZeroF :: r    ->              ExpF r
    SuccF   :: r    ->              ExpF r
    IfF     :: r    -> r -> r ->    ExpF r

--Exercise 2 c

instance Functor ExpF where
    fmap _ (BoolF a)    = BoolF a
    fmap _ (IntF a)     = IntF a
    fmap f (GtF a b)    = GtF (f a) (f b)
    fmap f (IsZeroF a)  = IsZeroF (f a)
    fmap f (SuccF a)    = SuccF (f a)
    fmap f (IfF a b c)  = IfF (f a) (f b) (f c)

fold :: Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

-------
--Evaluating Exp'
-------

eval' :: Exp' -> Code
eval' = fold evalAlg

executeExpTests' = mapM_ (executeTest eval') expTests'
expTests' = [
    ("True",                    In $ BoolF True),
    ("False",                   In $ BoolF False),
    ("5",                       In $ IntF 5),
    ("5 > 4",                   In $ GtF (In $ IntF 5) (In $ IntF 4)),
    ("4 > 4",                   In $ GtF (In $ IntF 4) (In $ IntF 4)),
    ("4 > True",                In $ GtF (In $ IntF 4) (In $ BoolF True)),
    ("isZero 5",                In $ IsZeroF (In $ IntF 5)),
    ("isZero 0",                In $ IsZeroF (In $ IntF 0)),
    ("isZero True",             In $ IsZeroF (In $ BoolF True)),
    ("Succ 0",                  In $ SuccF (In $ IntF 0)),
    ("Succ True",               In $ SuccF (In $ BoolF True)),
    ("If True then 5 else 4",   
        In $ IfF (In $ BoolF True) (In $ IntF 5) (In $ IntF 4)),
    ("If False then 5 else 4",  
        In $ IfF (In $ BoolF False) (In $ IntF 5) (In $ IntF 4)),
    ("If IsZero 0 then False else 4", 
        In $ IfF (In $ IsZeroF (In $ IntF 0)) (In $ BoolF False) (In $ IntF 4)),
    ("If 5 then False else 4", 
        In $ IfF (In $ IntF 5) (In $ BoolF False) (In $ IntF 4)),
    ("If (If False then False else True) then False else 4", 
        In $ IfF (In $ 
            IfF (In $ BoolF False) (In $ BoolF False) (In $ BoolF True)) 
                (In $ BoolF False) 
                (In $ IntF 4))
    ]


evalAlg :: ExpF Code -> Code
evalAlg (BoolF a) = toBool a
evalAlg (IntF a) = toInt a 
evalAlg (GtF (Just a) (Just b)) = case (a, b) of
    (Left a, Left b)    -> toBool $ if a > b then True else False
    otherwise           -> Nothing
evalAlg (IsZeroF (Just (Left a))) = toBool $ if a == 0 then True else False
evalAlg (SuccF (Just (Left a))) = toInt (a + 1)
evalAlg (IfF (Just (Right a)) b c) = if a then b else c
evalAlg _ = Nothing


--Test wether Exp and Exp' evalutate to the same
compareEvaluations = and $ zipWith compareEval expTests expTests'

compareEval (label, a) (_, b) = if (eval a == eval' b) then True else error $ "Evaluation not the same at: " ++ label

--main = print $ compareEvaluations


--Exercise 2 d

type ExpT' = HFix ExpTF

data ExpTF r a where
    BoolTF      :: (r Bool) -> ExpTF r Bool
    IntTF       :: (r Int)  -> ExpTF r Int
    GtTF        :: (r Int)  -> (r Int) -> ExpTF r Bool
    IsZeroTF    :: (r Int)  -> ExpTF r Bool
    SuccTF      :: (r Int)  -> ExpTF r Int
    IfTF        :: (r Bool) -> (r a) -> (r a) -> ExpTF r a

{-
An expression like: If (Bool True) (Int 5) (IsZero (Bool True)) would be valid
in the Exp case, but not in the ExpTF case. This is because in the Exp case
the else branch will not be evaluated unless the condition of the if is false.
With the ExpTF case the compiler would already throw an error because giving
a Bool to IsZeroTF will not typecheck.
-}


--Exercise 2 e

class HFunctor f where
    hfmap :: (forall b. g b -> h b) -> f g a -> f h a

hfold :: HFunctor f => (forall b. f r b -> r b) -> HFix f a -> r a
hfold f = f . hfmap (hfold f) . hout

newtype Id a = Id { unId :: a}

-------
--Evaluating ExpTF
-------

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (BoolTF a)     = a
evalAlgT (IntTF a)      = a
evalAlgT (GtTF (Id a) (Id b)) = Id $ a > b
evalAlgT (IsZeroTF (Id a))   = Id $ a == 0
evalAlgT (SuccTF (Id a))     = Id $ a + 1
evalAlgT (IfTF (Id a) b c)   = if a then b else c

instance HFunctor ExpTF where
    hfmap f (BoolTF a) = BoolTF (f a)
    hfmap f (IntTF a) = IntTF (f a)
    hfmap f (GtTF a b) = GtTF (f a) (f b)
    hfmap f (IsZeroTF a) = IsZeroTF (f a)
    hfmap f (SuccTF a) = SuccTF (f a)
    hfmap f (IfTF a b c) = IfTF (f a) (f b) (f c)


--Exercise 3

class Children f where
    children' :: f a -> [a]

type instance PF [a] = U :+: ((K a) :*: I)

instance Children U where
    children' U = []

instance Children (K a) where
    children' (K _) = []

instance Children I where
    children' (I a) = [a]

instance (Children a, Children b) => Children (a :+: b) where
    children' (L a) = children' a
    children' (R a) = children' a

instance (Children a, Children b) => Children (a :*: b) where
    children' (a :*: b) = children' a ++ children' b

instance Regular [a] where
    from [] = L U
    from (x:xs) = R $ (K x) :*: (I xs)
    to (L U) = []
    to (R ((K x) :*: (I xs))) = x : xs


children :: (R.Regular r, Children (R.PF r)) => r -> [r]
children = children' . from

example3 = children [1,2] == [[2]]


--Exercise 4


class Parents f where
    parents' :: (Regular a, Parents (PF a)) => f a -> [a]

instance Parents U where
    parents' U = []

instance Parents (K a) where
    parents' (K a) = []

instance Parents I where
    parents' (I a) = a : parents' (from a)

instance (Parents a, Parents b) => Parents (a :+: b) where
    parents' (L a) = parents' a
    parents' (R a) = parents' a

instance (Parents a, Parents b) => Parents (a :*: b) where
    parents' (a :*: b) = parents' a ++ parents' b

parents :: (R.Regular r, Parents (R.PF r), Children (R.PF r)) => r -> [r]
parents a = init $ a : (parents' $ from a)

example4 = parents [1,2,3]-- == [[1,2,3],[2,3],[3]]

main = print "Hello, world!"

--Didn't include the last exercise