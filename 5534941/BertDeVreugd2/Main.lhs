> {-#LANGUAGE GADTs, KindSignatures, RankNTypes, FlexibleContexts, TypeOperators #-}
> module Main where
> import Prelude hiding (GT)
> import qualified Generics.Regular as R

$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
Exercise 2.1 -> Kinds
 - Tree  : * -> * -> *
 - GList : (* -> *) -> * -> *
 - Bush  : * -> *
 - HFix  : ((* -> *) -> * -> *) -> * -> *
 - Exists: * -> *
 - Exp   : *
$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$

\begin{code}
  data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)
  data GList f a = GNil | GCons a (GList f (f a))
  data Bush a = Bush a (GList Bush (Bush a))
  data HFix f a = HIn { hout :: f (HFix f) a}
  
  data Exists b where
    Exists :: a -> (a -> b) -> Exists b
    
  data Exp where
    Bool   :: Bool               -> Exp
    Int    :: Int                -> Exp
    GT     :: Exp  -> Exp        -> Exp
    IsZero :: Exp                -> Exp
    Succ   :: Exp                -> Exp
    If     :: Exp  -> Exp -> Exp -> Exp
\end{code}
 
$$$$$$$$$$$$$$$$$$$$$ 
Exercise 2.2a -> eval
$$$$$$$$$$$$$$$$$$$$$

\begin{code}
  eval :: Exp -> Maybe (Either Int Bool)
  eval (Bool b) = Just (Right b)
  eval (Int i) = Just (Left i)
  eval (GT l r) = do { l' <- eval l; r' <- eval r; doGT l' r'}
   where doGT (Left x) (Left y) = Just $ Right (x > y)
         doGT _        _        = Nothing
  eval (IsZero i) = eval i >>= doIsZero
   where doIsZero (Left x) = Just $ Right (x == 0)
         doIsZero _        = Nothing
  eval (Succ i) = eval i >>= doSucc
   where doSucc (Left x) = Just $ Left (x + 1)
         doSucc _        = Nothing
  eval (If c t e) = eval c >>= doIf
   where doIf (Right True)  = eval t
         doIf (Right False) = eval e
         doIf _             = Nothing
\end{code}

$$$$$$$$$$$$$$$$$$$$$
Exercise 2.2b -> ExpF
$$$$$$$$$$$$$$$$$$$$$

\begin{code}
  data ExpF t where
    BoolF   :: Bool                       -> ExpF t
    IntF    :: Int                        -> ExpF t
    GTF     :: ExpF t -> ExpF t           -> ExpF t
    IsZeroF :: ExpF t                     -> ExpF t
    SuccF   :: ExpF t                     -> ExpF t
    IfF     :: ExpF t -> ExpF t -> ExpF t -> ExpF t 

  newtype Fix f = In { out :: f (Fix f) }
  type Exp' = Fix ExpF
\end{code}

$$$$$$$$$$$$$$$$$$$$$$$$
Exercise 2.2c -> Functor
$$$$$$$$$$$$$$$$$$$$$$$$

\begin{code}
  instance Functor ExpF where
    fmap _ (BoolF b)   = BoolF   b
    fmap _ (IntF i)    = IntF    i
    fmap f (GTF l r)   = GTF     (fmap f l) (fmap f r)
    fmap f (IsZeroF i) = IsZeroF (fmap f i)
    fmap f (SuccF i)   = SuccF   (fmap f i)
    fmap f (IfF c t e) = IfF     (fmap f c) (fmap f t) (fmap f e)

  evalAlg :: ExpF (Maybe (Either Int Bool)) -> Maybe (Either Int Bool)
  evalAlg (BoolF b) = Just $ Right b
  evalAlg (IntF i) = Just $ Left i
  evalAlg (GTF l r) = do { l' <- evalAlg l; r' <- evalAlg r; doGT l' r'}
   where doGT (Left x) (Left y) = Just $ Right (x > y)
         doGT _        _        = Nothing
  evalAlg (IsZeroF i) = evalAlg i >>= doIsZero
   where doIsZero (Left x) = Just $ Right (x == 0)
         doIsZero _        = Nothing
  evalAlg (SuccF i) = evalAlg i >>= doSucc
   where doSucc (Left x) = Just $ Left (x + 1)
         doSucc _        = Nothing
  evalAlg (IfF c t e) = evalAlg c >>= doIf
   where doIf (Right True)  = evalAlg t
         doIf (Right False) = evalAlg e
         doIf _             = Nothing

  fold :: Functor f => (f a -> a) -> Fix f -> a
  fold f = f . fmap (fold f) . out
  
  eval' :: Exp' -> Maybe (Either Int Bool)
  eval' = fold evalAlg
\end{code}

$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$
Exercise 2.2d -> GADT
 - Expression that cannot be defined are if-expressions where the branches
   are of different type. This, because, the definition used here requires
   the two branches to be of the same type.
$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$

\begin{code}
  data ExpTF (f :: * -> *) t where
    BoolTF   :: Bool                       -> ExpTF f Bool
    IntTF    :: Int                        -> ExpTF f Int
    GTTF     :: f Int  -> f Int            -> ExpTF f Bool
    IsZeroTF :: f Int                      -> ExpTF f Bool
    SuccTF   :: f Int                      -> ExpTF f Int
    IfTF     :: f Bool -> f t -> f t       -> ExpTF f t
  
  type ExpT' = HFix ExpTF
\end{code}

$$$$$$$$$$$$$$$$$$$$$$$$$
Exercise 2.2e -> HFunctor
$$$$$$$$$$$$$$$$$$$$$$$$$

\begin{code}
  class HFunctor f where
    hfmap :: (forall b . g b -> h b) -> f g a -> f h a
    
  instance HFunctor ExpTF where
    hfmap _ (BoolTF b)   = BoolTF   b
    hfmap _ (IntTF i)    = IntTF    i
    hfmap f (GTTF l r)   = GTTF     (f l) (f r)
    hfmap f (IsZeroTF i) = IsZeroTF (f i)
    hfmap f (SuccTF i)   = SuccTF   (f i)
    hfmap f (IfTF c t e) = IfTF     (f c) (f t) (f e)
    
  hfold :: HFunctor f => (forall b . f r b -> r b) -> HFix f a -> r a
  hfold f = f . hfmap (hfold f) . hout
  
  newtype Id a = Id { unId :: a }
  
  evalT' :: ExpT' a -> a
  evalT' = unId . hfold evalAlgT
  
  evalAlgT :: ExpTF Id a -> Id a
  evalAlgT (BoolTF   b)                    = Id b
  evalAlgT (IntTF    i)                    = Id i
  evalAlgT (GTTF     (Id l) (Id r))        = Id (l > r)
  evalAlgT (IsZeroTF (Id i))               = Id (i == 0)
  evalAlgT (SuccTF   (Id i))               = Id (i + 1)
  evalAlgT (IfTF     (Id c) (Id t) (Id e)) = Id (if c then t else e)
\end{code}

$$$$$$$$$$$$$$$$$$$$$$$$
Exercise 2.3 -> Children
$$$$$$$$$$$$$$$$$$$$$$$$

\begin{code}
  -- Children type class
  class Children f where
    children' :: f r -> [r]
    
  -- instance for Unit
  instance Children (R.U) where
    children' _ = []
  
  -- instance for Constant
  instance Children (R.K a) where
    children' _  = []
  
  -- instance for Constructor
  instance Children f => Children (R.C c f) where
    children' (R.C c) = children' c
  
  -- instance for Recursive Position
  instance Children (R.I) where
    children' (R.I r) = [r]
  
  -- instance for Sum
  instance (Children f, Children g) => Children (f R.:+: g) where
    children' (R.L f) = children' f
    children' (R.R g) = children' g
  
  -- instance for Product
  instance (Children f, Children g) => Children (f R.:*: g) where
    children' (f R.:*: g) = children' f ++ children' g
 
  children :: (R.Regular r, Children (R.PF r)) => r -> [r]
  children = children' . R.from
\end{code}

$$$$$$$$$$$$$$$$$$$$$$$
Exercise 2.4 -> parents
$$$$$$$$$$$$$$$$$$$$$$$

\begin{code}
  -- Parents are all elements except children
  parents :: (R.Regular r, Children (R.PF r), Elems (R.PF r)) => r -> [r]
  parents r = filter (not . null . children) (r : elems r)
  
  -- Elems type class
  class Elems f where
    elems' :: (R.Regular r, Elems (R.PF r)) => f r -> [r]
    
  -- instance for Unit
  instance Elems (R.U) where
    elems' _ = []
  
  -- instance for Constant
  instance Elems (R.K a) where
    elems' _  = []
  
  -- instance for Constructor
  instance Elems f => Elems (R.C c f) where
    elems' (R.C c) = elems' c
  
  -- instance for Recursive Position
  instance Elems (R.I) where
    elems' (R.I r) = r : elems r -- This is where the type classes on elems' comes from
  
  -- instance for Sum
  instance (Elems f, Elems g) => Elems (f R.:+: g) where
    elems' (R.L f) = elems' f
    elems' (R.R g) = elems' g
  
  -- instance for Product
  instance (Elems f, Elems g) => Elems (f R.:*: g) where
    elems' (f R.:*: g) = elems' f ++ elems' g
    
  elems :: (R.Regular r, Elems (R.PF r)) => r -> [r]
  elems = elems' . R.from
\end{code}