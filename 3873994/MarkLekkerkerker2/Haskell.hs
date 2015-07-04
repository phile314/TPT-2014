{-# LANGUAGE GADTs, RankNTypes, FlexibleContexts, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies #-}
module Haskell where
import Prelude hiding (GT)
import Data.Either
import qualified Generics.Regular as R

-- ___________                           .__                 ____ 
-- \_   _____/__  ___ ___________   ____ |__| ______ ____   /_   |
--  |    __)_\  \/  // __ \_  __ \_/ ___\|  |/  ___// __ \   |   |
--  |        \>    <\  ___/|  | \/\  \___|  |\___ \\  ___/   |   |
-- /_______  /__/\_ \\___  >__|    \___  >__/____  >\___  >  |___|
--         \/      \/    \/            \/        \/     \/        

data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)
-- * -> * -> *

data GList f a = GNil | GCons a (GList f (f a))
-- (* -> *) -> * -> *

data Bush a = Bush a (GList Bush (Bush a))
-- * -> *

data HFix f a = HIn { hout :: f (HFix f) a }
-- ((* -> *) -> * -> *) -> * -> *

data Exists b where
    Exists :: a -> (a -> b) -> Exists b
-- * -> *

data Exp where
    Bool   :: Bool              -> Exp
    Int    :: Int               -> Exp
    GT     :: Exp -> Exp        -> Exp
    IsZero :: Exp               -> Exp
    Succ   :: Exp               -> Exp
    If     :: Exp -> Exp -> Exp -> Exp
-- *



-- ___________                           .__                ________         
-- \_   _____/__  ___ ___________   ____ |__| ______ ____   \_____  \_____   
--  |    __)_\  \/  // __ \_  __ \_/ ___\|  |/  ___// __ \   /  ____/\__  \  
--  |        \>    <\  ___/|  | \/\  \___|  |\___ \\  ___/  /       \ / __ \_
-- /_______  /__/\_ \\___  >__|    \___  >__/____  >\___  > \_______ (____  /
--         \/      \/    \/            \/        \/     \/          \/    \/ 

eval :: Exp -> Maybe (Either Int Bool)
eval (Bool   b) = Just $ Right b
eval (Int    i) = Just $ Left i
eval (GT     e1 e2) = 
    case eval e1 of
        Just (Left x) -> case eval e2 of
            Just (Left y) -> Just $ Right $ x > y
            _             -> Nothing
        _             -> Nothing
eval (IsZero e) =
    do  x <- eval e
        either (Just . Right . ((==) 0)) (const Nothing) x
eval (Succ   e) =
    do  x <- eval e
        either (Just . Left . (+1)) (const Nothing) x
eval (If     c t f) = 
    do  x <- eval c
        either (const Nothing) (\y -> eval (if y then t else f)) x



-- ___________                           .__                ___________.    
-- \_   _____/__  ___ ___________   ____ |__| ______ ____   \_____  \_ |__  
--  |    __)_\  \/  // __ \_  __ \_/ ___\|  |/  ___// __ \   /  ____/| __ \ 
--  |        \>    <\  ___/|  | \/\  \___|  |\___ \\  ___/  /       \| \_\ \
-- /_______  /__/\_ \\___  >__|    \___  >__/____  >\___  > \_______ \___  /
--         \/      \/    \/            \/        \/     \/          \/   \/ 

newtype Fix f = In { out :: f (Fix f) }
type Exp' = Fix ExpF
data ExpF r where
    BoolF   :: Bool        -> ExpF r
    IntF    :: Int         -> ExpF r
    GTF     :: r -> r      -> ExpF r
    IsZeroF :: r           -> ExpF r
    SuccF   :: r           -> ExpF r
    IfF     :: r -> r -> r -> ExpF r


-- ___________                           .__                ________        
-- \_   _____/__  ___ ___________   ____ |__| ______ ____   \_____  \ ____  
--  |    __)_\  \/  // __ \_  __ \_/ ___\|  |/  ___// __ \   /  ____// ___\ 
--  |        \>    <\  ___/|  | \/\  \___|  |\___ \\  ___/  /       \  \___ 
-- /_______  /__/\_ \\___  >__|    \___  >__/____  >\___  > \_______ \___  >
--         \/      \/    \/            \/        \/     \/          \/   \/ 

instance Functor ExpF where
    fmap _ (BoolF   b    ) = BoolF b
    fmap _ (IntF    i    ) = IntF i
    fmap f (GTF     e1 e2) = GTF (f e1) (f e2)
    fmap f (IsZeroF e    ) = IsZeroF (f e)
    fmap f (SuccF   e    ) = SuccF (f e)
    fmap g (IfF     c t f) = IfF (g c) (g t) (g f)

fold :: Functor f => (f a -> a) -> Fix f -> a
fold f = f . fmap (fold f) . out

eval' :: Exp' -> Maybe (Either Int Bool)
eval' = fold evalArg

evalArg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
evalArg (BoolF   b    ) = Just $ Right b
evalArg (IntF    i    ) = Just $ Left i
evalArg (GTF     e1 e2) = 
    case e1 of
        Just (Left x) -> case e2 of
            Just (Left y) -> Just $ Right $ x > y
            _             -> Nothing
        _             -> Nothing
evalArg (IsZeroF e    ) = e >>= either (Just . Right . ((==) 0)) (const Nothing)
evalArg (SuccF   e    ) = e >>= either (Just . Left . (+1)) (const Nothing)
evalArg (IfF     c t f) = c >>= either (const Nothing) (\y -> if y then t else f)

-- ___________                           .__                ________     .___
-- \_   _____/__  ___ ___________   ____ |__| ______ ____   \_____  \  __| _/
--  |    __)_\  \/  // __ \_  __ \_/ ___\|  |/  ___// __ \   /  ____/ / __ | 
--  |        \>    <\  ___/|  | \/\  \___|  |\___ \\  ___/  /       \/ /_/ | 
-- /_______  /__/\_ \\___  >__|    \___  >__/____  >\___  > \_______ \____ | 
--         \/      \/    \/            \/        \/     \/          \/    \/ 

data ExpTF r a where
    BoolTF   :: Bool                 -> ExpTF r Bool
    IntTF    :: Int                  -> ExpTF r Int
    GTTF     :: r Int -> r Int       -> ExpTF r Bool
    IsZeroTF :: r Int                -> ExpTF r Bool
    SuccTF   :: r Int                -> ExpTF r Int
    IfTF     :: r Bool -> r a -> r a -> ExpTF r a

type ExpT' = HFix ExpTF

-- If (Bool True) (Int 1) cannot be defined in ExpT'


-- ___________                           .__                ________        
-- \_   _____/__  ___ ___________   ____ |__| ______ ____   \_____  \ ____  
--  |    __)_\  \/  // __ \_  __ \_/ ___\|  |/  ___// __ \   /  ____// __ \ 
--  |        \>    <\  ___/|  | \/\  \___|  |\___ \\  ___/  /       \  ___/ 
-- /_______  /__/\_ \\___  >__|    \___  >__/____  >\___  > \_______ \___  >
--         \/      \/    \/            \/        \/     \/          \/   \/ 


class HFunctor f where
    hfmap :: (forall b. g b -> h b) -> f g a -> f h a

instance HFunctor ExpTF where
    hfmap _ (BoolTF b) = BoolTF b
    hfmap _ (IntTF i) = IntTF i
    hfmap f (GTTF e1 e2) = GTTF (f e1) (f e2)
    hfmap f (IsZeroTF e) = IsZeroTF (f e)
    hfmap f (SuccTF e) = SuccTF (f e)
    hfmap g (IfTF c t f) = IfTF (g c) (g t) (g f)

hfold :: HFunctor f => (forall b. f r b -> r b) -> HFix f a -> r a
hfold f = f . hfmap (hfold f) . hout

newtype Id a = Id {unId :: a}

evalT' :: ExpT' a -> a
evalT' = unId . hfold evalAlgT

evalAlgT :: ExpTF Id a -> Id a
evalAlgT (BoolTF   b    ) = Id b
evalAlgT (IntTF    i    ) = Id i
evalAlgT (GTTF     e1 e2) = Id (unId e1 > unId e2)
evalAlgT (IsZeroTF e    ) = Id (unId e == 0)
evalAlgT (SuccTF   e    ) = Id (unId e + 1)
evalAlgT (IfTF     c t f) = if unId c then t else f



-- ___________                           .__                ________  
-- \_   _____/__  ___ ___________   ____ |__| ______ ____   \_____  \ 
--  |    __)_\  \/  // __ \_  __ \_/ ___\|  |/  ___// __ \    _(__  < 
--  |        \>    <\  ___/|  | \/\  \___|  |\___ \\  ___/   /       \
-- /_______  /__/\_ \\___  >__|    \___  >__/____  >\___  > /______  /
--         \/      \/    \/            \/        \/     \/         \/ 


children :: (R.Regular r, Children (R.PF r)) => r -> [r]
children = children' . R.from

class Children f where
    children' :: f r -> [r]

instance Children R.U where
    children' R.U = []

instance Children (R.K a) where
    children' (R.K _) = []

instance Children f => Children (R.C c f) where
    children' (R.C x) = children' x

instance Children R.I where
    children' (R.I x) = [x]

instance (Children f, Children g) => Children (f R.:+: g) where
    children' (R.L x) = children' x
    children' (R.R x) = children' x

instance (Children f, Children g) => Children (f R.:*: g) where
    children' (x R.:*: y) = children' x ++ children' y


type instance R.PF [a] = R.U R.:+: (R.K a R.:*: R.I)

instance R.Regular [a] where
    to (R.L _) = []
    to (R.R (R.K x R.:*: R.I xs)) = x : xs
    from (x:xs) = R.R $ R.K x R.:*: R.I xs
    from [] = R.L R.U


example3 = children [1, 2] == [[2]]



-- ___________                           .__                   _____  
-- \_   _____/__  ___ ___________   ____ |__| ______ ____     /  |  | 
--  |    __)_\  \/  // __ \_  __ \_/ ___\|  |/  ___// __ \   /   |  |_
--  |        \>    <\  ___/|  | \/\  \___|  |\___ \\  ___/  /    ^   /
-- /_______  /__/\_ \\___  >__|    \___  >__/____  >\___  > \____   | 
--         \/      \/    \/            \/        \/     \/       |__| 

parents :: (R.Regular r, Children (R.PF r)) => r -> [r]
parents x | null c    = []
          | otherwise = x : concatMap parents c
    where c = children x

example4 = parents [1,2,3] == [[1,2,3], [2,3], [3]]