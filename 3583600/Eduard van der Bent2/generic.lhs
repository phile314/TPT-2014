\begin{code}
{-#LANGUAGE GADTs, RankNTypes, TypeOperators, FlexibleContexts, TypeFamilies #-}

module TPTGeneric where

import Prelude hiding (GT)
import Generics.Regular hiding (fold,Fix,out)
import qualified Generics.Regular as R


data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)
data GList f a = GNil | GCons a (GList f (f a))
data Bush a = Bush a (GList Bush (Bush a))
data HFix f a = HIn {hout :: f (HFix f) a}
data Exists b where
        Exists :: a-> (a-> b)-> Exists b
data Exp where
        Bool ::Bool -> Exp
        Int :: Int -> Exp
        GT :: Exp-> Exp -> Exp
        IsZero :: Exp -> Exp
        Succ :: Exp -> Exp
        If :: Exp-> Exp-> Exp-> Exp
        
{-

Question 1

*TPTGeneric> :k Tree
Tree :: * -> * -> *
*TPTGeneric> :k GList
GList :: (* -> *) -> * -> *
*TPTGeneric> :k Bush
Bush :: * -> *
*TPTGeneric> :k HFix
HFix :: ((* -> *) -> * -> *) -> * -> *
*TPTGeneric> :k Exists
Exists :: * -> *
*TPTGeneric> :k Exp
Exp :: *
-}



-- Question 2a

eval :: Exp -> Maybe (Either Int Bool)
eval (Bool b) = Just (Right b)
eval (Int i) = Just (Left i)
eval (GT a b) = case eval a of 
                Just (Left s1) -> case eval b of 
                          Just (Left s2) -> if s1 > s2 then Just (Right True) else Just (Right False)
                          _ -> Nothing
                _ -> Nothing
eval (IsZero a) = case eval a of 
                  Just (Left s) -> if s == 0 then Just (Right True) else Just (Right False)
                  _ -> Nothing
eval (Succ a) = case eval a of
                Just (Left x) -> Just (Left (succ x)) 
                _ -> Nothing
eval (If a b c) = case eval a of
                  Just (Right x) -> if x then eval b else eval c
                  _ -> Nothing
                  
-- Question 2b
                  
newtype Fix f = In {out :: f (Fix f)}
data ExpF a where
     BoolF :: Bool -> ExpF a
     IntF :: Int -> ExpF a
     GTF :: a -> a -> ExpF a
     IsZeroF ::  a -> ExpF a
     SuccF :: a -> ExpF a
     IfF :: a -> a -> a -> ExpF a
     
type Exp' = Fix ExpF

-- Question 2c

instance Functor ExpF where
        fmap   f (GTF a b) = GTF (f a) ( f b)
        fmap   f (IsZeroF x) = IsZeroF (  f x)
        fmap   f (SuccF x) = SuccF (  f x)
        fmap   f (IfF a b c) = IfF (  f a) (  f b) (  f c)
        fmap   f (BoolF x) = BoolF x
        fmap   f (IntF x) = IntF x
      
evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalAlg (BoolF x) = Just (Right x)
evalAlg (IntF x) = Just (Left x)
evalAlg (GTF (Just (Left a)) (Just (Left b) )) = Just (Right (a > b))
evalAlg (SuccF (Just (Left x))) = Just (Left $ succ x)
evalAlg (IfF (Just (Right a)) b c) = if a then b else c
evalAlg (IsZeroF (Just (Left a))) = Just (Right (a == 0))

fold :: (Functor f ) => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

eval' :: Exp' -> Maybe (Either Int Bool)
eval' e = fold evalAlg e

-- Question 2d

data ExpTF a b where
        BoolFT :: Bool -> ExpTF a Bool
        IntFT :: Int -> ExpTF a Int
        GTFT :: a Int -> a Int -> ExpTF a Bool
        IsZeroFT :: a Int -> ExpTF a Bool
        SuccFT :: a Int -> ExpTF a Int
        IfFT :: a Bool -> a b -> a b -> ExpTF a b
   
type ExpT' = HFix ExpTF

{-
Something that cannot be typed is an expression where the if-branches have different types:

If (Bool True) then (Int 1) else (Bool False)

-}

-- Question 2e

class HFunctor f where
        hfmap :: ( forall b . g b -> h b) -> f g a -> f h a

instance HFunctor ExpTF where
        hfmap f (BoolFT b) = BoolFT b
        hfmap f (IntFT b) = IntFT b
        hfmap f (GTFT a b) = GTFT (f a) (f b)
        hfmap f (IsZeroFT b) = IsZeroFT (f b)
        hfmap f (SuccFT b) = SuccFT (f b)
        hfmap f (IfFT a b c) = IfFT (f a) (f b) (f c)
        
hfold ::  HFunctor f  => ( forall b . f r b -> r b)-> HFix f a -> r a
hfold f = f.hfmap (hfold f) . hout
newtype Id a = Id { unId :: a }

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (BoolFT b ) = Id b
evalAlgT (IntFT b ) = Id b
evalAlgT (GTFT (Id a) (Id b) ) = Id (a > b)
evalAlgT (IsZeroFT (Id a)) = Id (a == 0)
evalAlgT (SuccFT (Id a) ) = Id ( succ a )
evalAlgT (IfFT (Id a) (Id b) (Id c)) = if a then Id b else Id c

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

-- Question 3

-- children x = [tail x]

type instance PF [a] = U :+: K a :*: I
-- Instance declaration so that the example given actually works
instance Regular [a] where
        from [] = L U
        from (x : xs) = R (K x :*: I xs)
        to (L U) = [ ]
        to (R (K x :*: I xs)) = x : xs        

children :: (Regular r, Children (PF r)) => r -> [r]
children = children' . from

class Children f where
        children' :: f r -> [r]
        
instance Children U where 
        children' _ = []

instance Children (K a) where
        children' _ = []
        
instance Children f => Children (C c f) where
        children' (C c) = children' c
        
instance Children I where -- This is the list minus the first item, and thus the droids we are looking for
        children' (I r) = [r]
        
instance (Children f, Children g) => Children ( f :+: g) where
        children' (L x ) = children' x
        children' (R x ) = children' x
        
instance (Children f, Children g) => Children (f :*: g) where 
        children' (x :*: y) = children' x ++ children' y
        
example3 = children [1,2] == [[2]]      

-- *TPTGeneric> example3
-- True

-- Question 4

uncomplicated [] = []
uncomplicated x@(_:xs) = x : uncomplicated xs

-- The below is the regular version of the above function

parents :: (Regular r, Children (PF r), AllChildren (PF r) ) => r -> [r]
parents r = init $ r : allChilds ( from r ) -- We add the given list to all possible childs, and remove the empty (last) result

class AllChildren f where
        allChilds :: (Regular r, AllChildren (PF r)) => f r -> [r]
        
instance AllChildren U where
        allChilds _ = []
instance AllChildren (K a) where
        allChilds _ = []
instance AllChildren f => AllChildren (C c f) where
        allChilds (C c) = allChilds c
instance AllChildren I where -- Instead of just taking one child, we take all the possible children
        allChilds (I r) = r : allChilds (from r)
instance (AllChildren f, AllChildren g) => AllChildren (f :+: g) where
        allChilds (L x) = allChilds x
        allChilds (R x) = allChilds x
instance (AllChildren f, AllChildren g) => AllChildren (f :*: g) where
        allChilds (x :*: y) = allChilds x ++ allChilds y

example4 = parents [1,2,3] == [[1,2,3], [2,3], [3]]
        
\end{code}

