>{-# LANGUAGE TypeOperators, GADTs, UnicodeSyntax, KindSignatures, RankNTypes, MultiParamTypeClasses, FlexibleContexts, FlexibleContexts, TypeFamilies, UndecidableInstances #-}
>
>module Exercise3 where
>
>import qualified Generics.Regular as R
>
>{---------------------------------------------------------------
> ▄▄▄▄▄▄▄▄▄▄▄  ▄       ▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄          ▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌       ▄█░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀  ▐░▌   ▐░▌ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀  ▀▀▀▀█░█▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀       ▐░░▌▐░░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌       ▐░▌▐░▌               ▐░▌     ▐░▌          ▐░▌                 ▀▀ ▐░░▌
>▐░█▄▄▄▄▄▄▄▄▄    ▐░▐░▌   ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌▐░▌               ▐░▌     ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄           ▐░░▌
>▐░░░░░░░░░░░▌    ▐░▌    ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░▌               ▐░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌          ▐░░▌
>▐░█▀▀▀▀▀▀▀▀▀    ▐░▌░▌   ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀█░█▀▀ ▐░▌               ▐░▌      ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀           ▐░░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌     ▐░▌  ▐░▌               ▐░▌               ▐░▌▐░▌                    ▐░░▌
>▐░█▄▄▄▄▄▄▄▄▄  ▐░▌   ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌      ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄  ▄▄▄▄█░█▄▄▄▄  ▄▄▄▄▄▄▄▄▄█░▌▐░█▄▄▄▄▄▄▄▄▄       ▄▄▄▄█░░█▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░▌       ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌
> ▀▀▀▀▀▀▀▀▀▀▀  ▀       ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀▀▀
>
>The kinds are in the comments.
>----------------------------------------------------------------}
>
>-- Tree :: * → * → *
>data Tree a b = Tip a | Branch (Tree a b) b (Tree a b)
>-- GList :: (* → *) → * → *
>data GList f a = GNil | GCons a (GList f (f a))
>-- Bush :: * → *
>data Bush a = Bush a (GList Bush (Bush a))
>-- HFix :: ((* → *) → * → *) → * → *
>data HFix f a = HIn { hout :: f (HFix f) a }
>-- Exists :: * → *
>data Exists b where
>    Exists :: a → (a → b) → Exists b
>
>-- Exp :: *
>data Exp where
>    Bool :: Bool → Exp
>    Int :: Int → Exp
>    Gt :: Exp → Exp → Exp
>    Add :: Exp → Exp → Exp
>    IsZero :: Exp → Exp
>    Succ :: Exp → Exp
>    If :: Exp → Exp → Exp → Exp
>
>{---------------------------------------------------------------
>▄▄▄▄▄▄▄▄▄▄▄  ▄       ▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄       ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀  ▐░▌   ▐░▌ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀  ▀▀▀▀█░█▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀█░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌       ▐░▌▐░▌               ▐░▌     ▐░▌          ▐░▌                         ▐░▌▐░▌       ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄    ▐░▐░▌   ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌▐░▌               ▐░▌     ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄                ▐░▌▐░█▄▄▄▄▄▄▄█░▌
>▐░░░░░░░░░░░▌    ▐░▌    ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░▌               ▐░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌      ▄▄▄▄▄▄▄▄▄█░▌▐░░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀    ▐░▌░▌   ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀█░█▀▀ ▐░▌               ▐░▌      ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀      ▐░░░░░░░░░░░▌▐░█▀▀▀▀▀▀▀█░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌     ▐░▌  ▐░▌               ▐░▌               ▐░▌▐░▌               ▐░█▀▀▀▀▀▀▀▀▀ ▐░▌       ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄  ▐░▌   ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌      ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄  ▄▄▄▄█░█▄▄▄▄  ▄▄▄▄▄▄▄▄▄█░▌▐░█▄▄▄▄▄▄▄▄▄      ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌       ▐░▌
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░▌       ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░▌       ▐░▌
> ▀▀▀▀▀▀▀▀▀▀▀  ▀       ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀
>----------------------------------------------------------------}
>eval :: Exp → Maybe (Either Int Bool)
>eval (Bool b) = Just (Right b)
>eval (Int i) = Just (Left i)
>eval (Gt l r) = case (eval l, eval r) of
>                    (Just (Left l'), Just (Left r')) → Just (Right (l' > r'))
>                    _ → Nothing
>eval (Add l r) = case (eval l, eval r) of
>                    (Just (Left l'), Just (Left r')) → Just (Left (l' + r'))
>                    _ → Nothing
>eval (IsZero e) = case eval e of
>                    Just (Left e') → Just . Right $ e' == 0
>                    _ → Nothing
>eval (Succ e) = case eval e of
>                    Just (Left e') → Just . Left . succ $ e'
>                    _ → Nothing
>eval (If c t e) = case (eval c, eval t, eval e) of
>                    (Just (Right b), t', e') → if b then t' else e'
>                    _ → Nothing
>
>
>
>{---------------------------------------------------------------
> ▄▄▄▄▄▄▄▄▄▄▄  ▄       ▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄       ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀  ▐░▌   ▐░▌ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀  ▀▀▀▀█░█▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀█░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌       ▐░▌▐░▌               ▐░▌     ▐░▌          ▐░▌                         ▐░▌▐░▌       ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄    ▐░▐░▌   ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌▐░▌               ▐░▌     ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄                ▐░▌▐░█▄▄▄▄▄▄▄█░▌
>▐░░░░░░░░░░░▌    ▐░▌    ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░▌               ▐░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌      ▄▄▄▄▄▄▄▄▄█░▌▐░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀    ▐░▌░▌   ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀█░█▀▀ ▐░▌               ▐░▌      ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀      ▐░░░░░░░░░░░▌▐░█▀▀▀▀▀▀▀█░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌     ▐░▌  ▐░▌               ▐░▌               ▐░▌▐░▌               ▐░█▀▀▀▀▀▀▀▀▀ ▐░▌       ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄  ▐░▌   ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌      ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄  ▄▄▄▄█░█▄▄▄▄  ▄▄▄▄▄▄▄▄▄█░▌▐░█▄▄▄▄▄▄▄▄▄      ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░▌       ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░▌
> ▀▀▀▀▀▀▀▀▀▀▀  ▀       ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀
>----------------------------------------------------------------}
>newtype Fix f = In { out :: f (Fix f) }
>
>data ExpF rec where
>    FBool   :: Bool → ExpF rec
>    FInt    :: Int  → ExpF rec
>    FGt     :: rec  → rec      → ExpF rec
>    FAdd    :: rec  → rec      → ExpF rec
>    FIsZero :: rec  → ExpF rec
>    FSucc   :: rec  → ExpF rec
>    FIf     :: rec  → rec      → rec       → ExpF rec
>
>
>type Exp' = Fix ExpF
>
>-- Proof of isomorphism:
>fixToNormal :: Exp' → Exp
>fixToNormal fix = convert (out fix)
>    where
>        convert :: ExpF (Fix ExpF) → Exp
>        convert (FBool b)    = Bool   b
>        convert (FInt i)     = Int    i
>        convert (FGt l r)    = Gt     (fixToNormal l) (fixToNormal r)
>        convert (FAdd l r)   = Add    (fixToNormal l) (fixToNormal r)
>        convert (FIsZero e)  = IsZero (fixToNormal e)
>        convert (FSucc e)    = Succ   (fixToNormal e)
>        convert (FIf c t e)  = If     (fixToNormal c) (fixToNormal t) (fixToNormal e)
>
>normalToFix :: Exp → Exp'
>normalToFix (Bool b)    = In $ FBool b
>normalToFix (Int i)     = In $ FInt i
>normalToFix (Gt l r)    = In $ FGt (normalToFix l) (normalToFix r)
>normalToFix (Add l r)   = In $ FAdd (normalToFix l) (normalToFix r)
>normalToFix (IsZero e)  = In $ FIsZero (normalToFix e)
>normalToFix (Succ e)    = In $ FSucc (normalToFix e)
>normalToFix (If c t e)  = In $ FIf (normalToFix c) (normalToFix t) (normalToFix e)
>
>{---------------------------------------------------------------
> ▄▄▄▄▄▄▄▄▄▄▄  ▄       ▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄       ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀  ▐░▌   ▐░▌ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀  ▀▀▀▀█░█▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌       ▐░▌▐░▌               ▐░▌     ▐░▌          ▐░▌                         ▐░▌▐░▌
>▐░█▄▄▄▄▄▄▄▄▄    ▐░▐░▌   ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌▐░▌               ▐░▌     ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄                ▐░▌▐░▌
>▐░░░░░░░░░░░▌    ▐░▌    ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░▌               ▐░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌      ▄▄▄▄▄▄▄▄▄█░▌▐░▌
>▐░█▀▀▀▀▀▀▀▀▀    ▐░▌░▌   ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀█░█▀▀ ▐░▌               ▐░▌      ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀      ▐░░░░░░░░░░░▌▐░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌     ▐░▌  ▐░▌               ▐░▌               ▐░▌▐░▌               ▐░█▀▀▀▀▀▀▀▀▀ ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄  ▐░▌   ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌      ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄  ▄▄▄▄█░█▄▄▄▄  ▄▄▄▄▄▄▄▄▄█░▌▐░█▄▄▄▄▄▄▄▄▄      ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░▌       ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌
> ▀▀▀▀▀▀▀▀▀▀▀  ▀       ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀
>----------------------------------------------------------------}
>
>instance Functor ExpF where
>    fmap f x = case x of
>        FBool   b      → FBool b
>        FInt    i      → FInt i
>        FGt     l r    → FGt (f l) (f r)
>        FAdd    l r    → FAdd (f l) (f r)
>        FIsZero e      → FIsZero (f e)
>        FSucc   e      → FSucc (f e)
>        FIf     c t e  → FIf (f c) (f t) (f e)
>
>
>fold :: Functor f ⇒ (f a → a) → Fix f → a
>fold f = f . fmap (fold f) . out
>
>evalAlg :: ExpF (Maybe (Either Int Bool)) → Maybe (Either Int Bool)
>evalAlg (FBool   b      ) = Just $ Right b
>evalAlg (FInt    i      ) = Just $ Left i
>evalAlg (FGt     l r    ) = case (l, r) of
>                                (Just (Left l'), Just (Left r')) → Just $ Right (l' > r')
>                                _ → Nothing
>
>evalAlg (FAdd    l r    ) = case (l, r) of
>                                (Just (Left l'), Just (Left r')) → Just $ Left (l' + r')
>                                _ → Nothing
>evalAlg (FIsZero e      ) = case e of
>                                Just (Left e') → Just $ Right (e' >= 0)
>                                _ → Nothing
>evalAlg (FSucc   e      ) = case e of
>                                Just (Left e') → Just $ Left (succ e')
>                                _ → Nothing
>evalAlg (FIf     c t e  ) = case (c, t, e) of
>                                (Just (Right c'), t', e') → if c' then t' else e'
>                                _ → Nothing
>
>eval' :: Exp' → Maybe (Either Int Bool)
>eval' = fold evalAlg
>
>{---------------------------------------------------------------
> ▄▄▄▄▄▄▄▄▄▄▄  ▄       ▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄       ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀  ▐░▌   ▐░▌ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀  ▀▀▀▀█░█▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀█░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌       ▐░▌▐░▌               ▐░▌     ▐░▌          ▐░▌                         ▐░▌▐░▌       ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄    ▐░▐░▌   ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌▐░▌               ▐░▌     ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄                ▐░▌▐░▌       ▐░▌
>▐░░░░░░░░░░░▌    ▐░▌    ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░▌               ▐░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌      ▄▄▄▄▄▄▄▄▄█░▌▐░▌       ▐░▌
>▐░█▀▀▀▀▀▀▀▀▀    ▐░▌░▌   ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀█░█▀▀ ▐░▌               ▐░▌      ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀      ▐░░░░░░░░░░░▌▐░▌       ▐░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌     ▐░▌  ▐░▌               ▐░▌               ▐░▌▐░▌               ▐░█▀▀▀▀▀▀▀▀▀ ▐░▌       ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄  ▐░▌   ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌      ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄  ▄▄▄▄█░█▄▄▄▄  ▄▄▄▄▄▄▄▄▄█░▌▐░█▄▄▄▄▄▄▄▄▄      ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░▌       ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░▌
> ▀▀▀▀▀▀▀▀▀▀▀  ▀       ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀
>----------------------------------------------------------------}
>
>data ExpTF :: (* -> *) -> * -> * where
>    TFBool   :: Bool           -> ExpTF rec Bool
>    TFInt    :: Int            -> ExpTF rec Int
>    TFGt     :: rec Int        -> rec Int        -> ExpTF rec Bool
>    TFAdd    :: rec Int        -> rec Int        -> ExpTF rec Int
>    TFIsZero :: rec Int        -> ExpTF rec Bool
>    TFSucc   :: rec Int        -> ExpTF rec Int
>    TFIf     :: rec Bool       -> rec ty         -> rec ty     -> ExpTF rec ty
>
>type ExpT' = HFix ExpTF
>
>-- Example ExpT'
>exampleT' :: ExpT' Int
>exampleT' = HIn (TFIf (HIn (TFBool True)) (HIn (TFInt 3)) (HIn (TFInt 4)))
>
>tfIsoProof :: (ExpT' a -> Exp', Exp' -> ExpT' Bool, Exp' -> ExpT' Int)
>tfIsoProof = (from, toBool, toInt)
>    where
>        from :: ExpT' a -> Exp'
>        from (HIn (TFBool b    )) = In (FBool b)
>        from (HIn (TFInt  i    )) = In (FInt  i)
>        from (HIn (TFGt   l r  )) = In (FGt (from  l) (from r))
>        from (HIn (TFAdd  l r  )) = In (FAdd (from  l) (from  r))
>        from (HIn (TFIsZero e  )) = In (FIsZero (from  e))
>        from (HIn (TFSucc   e  )) = In (FSucc (from  e))
>        from (HIn (TFIf   c t e)) = In (FIf (from  c) (from  t) (from  e))
>
>        toBool :: Exp' -> ExpT' Bool
>        toBool (In (FBool   b    )) = HIn $ TFBool b
>        toBool (In (FGt     l r  )) = HIn $ TFGt (toInt l) (toInt r)
>        toBool (In (FIsZero e    )) = HIn $ TFIsZero (toInt e)
>        toBool (In (FIf     c t e)) = HIn $ TFIf (toBool c) (toBool t) (toBool e)
>        toBool _                    = error "Type error"
>
>        toInt :: Exp' -> ExpT' Int
>        toInt (In (FInt    i    )) = HIn $ TFInt  i
>        toInt (In (FAdd    l r  )) = HIn $ TFAdd (toInt l) (toInt r)
>        toInt (In (FSucc   e    )) = HIn $ TFSucc (toInt e)
>        toInt (In (FIf     c t e)) = HIn $ TFIf (toBool c) (toInt t) (toInt e)
>        toInt _                    = error "Type error"
>
>-- An example of an expression that cannot be expressed in ExpTF:
>-- It cannot be expressed in ExpTF because the types of the 'then' and 'else' branches are different.
>exampleCannotType :: Exp
>exampleCannotType = If (Bool True) (Bool False) (Int 3)
>
>{---------------------------------------------------------------
> ▄▄▄▄▄▄▄▄▄▄▄  ▄       ▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄       ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀  ▐░▌   ▐░▌ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀  ▀▀▀▀█░█▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌       ▐░▌▐░▌               ▐░▌     ▐░▌          ▐░▌                         ▐░▌▐░▌
>▐░█▄▄▄▄▄▄▄▄▄    ▐░▐░▌   ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌▐░▌               ▐░▌     ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄                ▐░▌▐░█▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌    ▐░▌    ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░▌               ▐░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌      ▄▄▄▄▄▄▄▄▄█░▌▐░░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀    ▐░▌░▌   ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀█░█▀▀ ▐░▌               ▐░▌      ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀      ▐░░░░░░░░░░░▌▐░█▀▀▀▀▀▀▀▀▀
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌     ▐░▌  ▐░▌               ▐░▌               ▐░▌▐░▌               ▐░█▀▀▀▀▀▀▀▀▀ ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄  ▐░▌   ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌      ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄  ▄▄▄▄█░█▄▄▄▄  ▄▄▄▄▄▄▄▄▄█░▌▐░█▄▄▄▄▄▄▄▄▄      ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░▌       ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌
> ▀▀▀▀▀▀▀▀▀▀▀  ▀       ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀
>----------------------------------------------------------------}
>
>class HFunctor f where
>    hfmap :: (forall b . g b → h b) → f g a → f h a
>
>hfold :: HFunctor f ⇒ (forall b . f r b → r b) → HFix f a → r a
>hfold f = f . hfmap (hfold f) . hout
>
>newtype Id a = Id {unId :: a}
>
>evalT0 :: ExpT' a → a
>evalT0 = unId . hfold evalAlgT
>
>evalAlgT :: ExpTF Id a → Id a
>evalAlgT (TFBool b      ) = Id b
>evalAlgT (TFInt i       ) = Id i
>evalAlgT (TFGt     l r  ) = Id $ unId l > unId r
>evalAlgT (TFAdd    l r  ) = Id $ unId l + unId r
>evalAlgT (TFIsZero e    ) = Id $ unId e == 0
>evalAlgT (TFSucc   e    ) = Id $ succ $ unId e
>evalAlgT (TFIf     c t e) = if unId c then t else e
>
>instance HFunctor ExpTF where
>    hfmap _ (TFBool b      )      = TFBool b
>    hfmap _ (TFInt i       )      = TFInt i
>    hfmap f (TFGt     l r  )      = TFGt (f l) (f r)
>    hfmap f (TFAdd    l r  )      = TFAdd (f l) (f r)
>    hfmap f (TFIsZero e    )      = TFIsZero (f e)
>    hfmap f (TFSucc   e    )      = TFSucc (f e)
>    hfmap f (TFIf     c t e)      = TFIf (f c) (f t) (f e)
>
>{---------------------------------------------------------------
> ▄▄▄▄▄▄▄▄▄▄▄  ▄       ▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄       ▄▄▄▄▄▄▄▄▄▄▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀  ▐░▌   ▐░▌ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀  ▀▀▀▀█░█▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀█░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌       ▐░▌▐░▌               ▐░▌     ▐░▌          ▐░▌                         ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄    ▐░▐░▌   ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌▐░▌               ▐░▌     ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄       ▄▄▄▄▄▄▄▄▄█░▌
>▐░░░░░░░░░░░▌    ▐░▌    ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░▌               ▐░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀    ▐░▌░▌   ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀█░█▀▀ ▐░▌               ▐░▌      ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀█░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌     ▐░▌  ▐░▌               ▐░▌               ▐░▌▐░▌                         ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄  ▐░▌   ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌      ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄  ▄▄▄▄█░█▄▄▄▄  ▄▄▄▄▄▄▄▄▄█░▌▐░█▄▄▄▄▄▄▄▄▄       ▄▄▄▄▄▄▄▄▄█░▌
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░▌       ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌
> ▀▀▀▀▀▀▀▀▀▀▀  ▀       ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀▀▀
>----------------------------------------------------------------}
>
>-- Useful show instances for regular stuff
>instance Show (f (R.Fix f)) => Show (R.Fix f) where
>    show x = "(" ++ show (R.out x) ++ ")"
>
>instance Show a => Show (R.K a r) where
>    show (R.K x) = "K " ++ show x
>
>instance Show r => Show (R.I r) where
>    show (R.I r) = "I " ++ show r
>
>instance Show (R.U r) where
>    show R.U = "U"
>
>instance (Show (f r), Show (g r)) => Show ((f R.:+: g) r) where
>    show (R.L f) = "L (" ++ show f ++ ")"
>    show (R.R g) = "R (" ++ show g ++ ")"
>
>instance (Show (f r), Show (g r)) => Show ((f R.:*: g) r) where
>    show (f R.:*: g) = "(" ++ show f ++ " :*: " ++ show g ++ ")"
>
>instance Show (f r) => Show (R.C c f r) where
>    show (R.C f) = "C (" ++ show f ++ ")"
>
>-- Type instance PF for lists, used in the example
>type instance R.PF [a] = R.U R.:+: ((R.K a) R.:*: R.I)
>
>-- Regular instance of a list
>-- Used to check the examples
>instance R.Regular [a] where
>    from [] = R.L R.U
>    from (x : xs) = R.R (R.K x R.:*: R.I xs)
>
>    to (R.L R.U) = []
>    to (R.R (R.K x R.:*: R.I xs)) = x : xs
>
>-- The children class
>class Children a where
>    children' :: a r -> [r]
>
>instance Children R.I where
>    children' (R.I x) = [x]
>
>instance Children (R.K a) where
>    children' (R.K _) = []
>
>instance Children R.U where
>    children' _ = []
>
>instance (Children f, Children g) => Children (f R.:+: g) where
>    children' (R.L f) = children' f
>    children' (R.R g) = children' g
>
>instance (Children f, Children g) => Children (f R.:*: g) where
>    children' (f R.:*: g) = children' f ++ children' g
>
>instance (Children f) => Children (R.C c f) where
>    children' (R.C x) = children' x
>
>instance (Children f) => Children (R.S s f) where
>    children' (R.S x) = children' x
>
>
>children :: (R.Regular r, Children (R.PF r)) ⇒ r → [r]
>children = children' . R.from
>
>ex3Example :: [[Integer]]
>ex3Example = children [1,2]
>
>{---------------------------------------------------------------
> ▄▄▄▄▄▄▄▄▄▄▄  ▄       ▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄  ▄▄▄▄▄▄▄▄▄▄▄       ▄         ▄
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░▌       ▐░▌
>▐░█▀▀▀▀▀▀▀▀▀  ▐░▌   ▐░▌ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀  ▀▀▀▀█░█▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀▀▀▀▀▀      ▐░▌       ▐░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌       ▐░▌▐░▌               ▐░▌     ▐░▌          ▐░▌               ▐░▌       ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄    ▐░▐░▌   ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄█░▌▐░▌               ▐░▌     ▐░█▄▄▄▄▄▄▄▄▄ ▐░█▄▄▄▄▄▄▄▄▄      ▐░█▄▄▄▄▄▄▄█░▌
>▐░░░░░░░░░░░▌    ▐░▌    ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░▌               ▐░▌     ▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌     ▐░░░░░░░░░░░▌
>▐░█▀▀▀▀▀▀▀▀▀    ▐░▌░▌   ▐░█▀▀▀▀▀▀▀▀▀ ▐░█▀▀▀▀█░█▀▀ ▐░▌               ▐░▌      ▀▀▀▀▀▀▀▀▀█░▌▐░█▀▀▀▀▀▀▀▀▀       ▀▀▀▀▀▀▀▀▀█░▌
>▐░▌            ▐░▌ ▐░▌  ▐░▌          ▐░▌     ▐░▌  ▐░▌               ▐░▌               ▐░▌▐░▌                         ▐░▌
>▐░█▄▄▄▄▄▄▄▄▄  ▐░▌   ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄ ▐░▌      ▐░▌ ▐░█▄▄▄▄▄▄▄▄▄  ▄▄▄▄█░█▄▄▄▄  ▄▄▄▄▄▄▄▄▄█░▌▐░█▄▄▄▄▄▄▄▄▄                ▐░▌
>▐░░░░░░░░░░░▌▐░▌     ▐░▌▐░░░░░░░░░░░▌▐░▌       ▐░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌▐░░░░░░░░░░░▌               ▐░▌
> ▀▀▀▀▀▀▀▀▀▀▀  ▀       ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀         ▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀  ▀▀▀▀▀▀▀▀▀▀▀                 ▀
>----------------------------------------------------------------}
>parents :: (R.Regular r, Children (R.PF r)) ⇒ r → [r]
>parents x = let cs = children x in
>                if not . null $ cs then x : concatMap parents cs else []
>
>ex4Example :: Bool -- Type of [Integer] is annotated for disambiguation of ==
>ex4Example = parents ([1, 2, 3] :: [Integer]) == [[1, 2, 3], [2, 3], [3]]
