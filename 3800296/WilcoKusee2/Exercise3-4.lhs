\begin{code}
{-# LANGUAGE FlexibleContexts, TypeOperators, TypeFamilies, TemplateHaskell #-}

module Exercise3 where

import Generics.Regular

-- List data type and instances
data List a = Nil | Cons a (List a)
	deriving (Eq, Show)

fromList :: [a] -> List a
fromList [] = Nil
fromList (x:xs) = Cons x (fromList xs)

$(deriveAll ''List "PFList")
type instance PF (List a) = PFList a

\end{code}

3. Define a generic function that collects the recursive children

\begin{code}
class Children a where
	children' :: a r -> [r]

instance Children U where
	children' _ = []

instance Children (K a) where
	children' _ = []

instance Children f => Children (C c f) where
	children' (C f) = children' f

instance Children I where
	children' (I r) = [r]

instance (Children f, Children g) => Children (f :+: g) where
	children' (L x) = children' x
	children' (R y) = children' y

instance (Children f, Children g) => Children (f :*: g) where
	children' (x :*: y) = children' x ++ children' y

children :: (Regular r, Children (PF r)) => r -> [r]
children = children' . from


example3 = children (fromList [1,2]) == [fromList [2]]
\end{code}

4. Define parents

\begin{code}
class Parents a where
	parents' :: a r -> [r]

instance Parents U where
	parents' _ = []

instance Parents (K a) where
	parents' _ = []

instance Parents f => Parents (C c f) where
	parents' (C f) = parents' f

instance Parents I where
	parents' (I r) = [r]

instance (Parents f, Parents g) => Parents (f :+: g) where
	parents' (L x) = parents' x
	parents' (R y) = parents' y

instance (Parents f, Parents g) => Parents (f :*: g) where
	parents' (x :*: y) = parents' x ++ parents' y

parents :: (Regular r, Parents (PF r)) => r -> [r]
parents = parents' . from


example4 = parents (fromList [1,2,3]) == [fromList [1,2,3], fromList [2,3], fromList [3]]
\end{code}

5. Implement the embedding
(I didn't do this part)
