{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections #-}

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer hiding (Sum)
import           Data.Default
import           Data.List
import           Data.List.Utils
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S

listenSandboxed :: (MonadWriter w m) => m a -> m (a, w)
listenSandboxed = pass . fmap (, const mempty) . listen

data Typ = UnitT
         | Prod Typ Typ
         | Sum  Typ Typ
         | Fn   Typ Typ
         | TV   Int
         deriving (Show, Eq)
data Expr = Lam String Expr
          | App Expr Expr
          | Var String
          | Unit
          | Tup Expr Expr
          | Lft Expr
          | Rght Expr
          | DestructTup Expr String String Expr
          | Case Expr String String Expr Expr
          deriving (Show, Eq)

data GatherWrite
   = GatherWrite
   { typesEq :: [(Typ, Typ)]
   , varsUsed :: [String]
   }

instance Semigroup GatherWrite where
  a <> b = GatherWrite { typesEq = typesEq a <> typesEq b, varsUsed = varsUsed a <> varsUsed b }

instance Monoid GatherWrite where
  mempty = GatherWrite { typesEq = mempty, varsUsed = mempty }

instance Default GatherWrite where
  def = mempty

data Env
   = Env
   { vars :: M.Map String Typ
   }

instance Default Env where
  def = Env { vars = M.empty }

data Unification
  = Unification
  { tvsEq :: [(Int, Typ)]
  }

instance Semigroup Unification where
  a <> b = Unification { tvsEq = tvsEq a <> tvsEq b }

instance Monoid Unification where
  mempty = Unification { tvsEq = mempty }

instance Default Unification where
  def = mempty

addTypesEq :: (MonadWriter GatherWrite m) => Typ -> Typ -> m ()
addTypesEq a b = tell $ def { typesEq = [(a, b)] }

useVar :: (MonadWriter GatherWrite m) => String -> m ()
useVar v = tell $ def { varsUsed = [v] }

addVar :: (MonadWriter GatherWrite m, MonadReader Env m, MonadError String m) => String -> Typ -> m a -> m a
addVar v t m = do
  (retval, gw) <- listenSandboxed . local (\e -> e { vars = M.insert v t (vars e) }) $ m
  when (countElem v (varsUsed gw) /= 1) $ throwError ("misused variable " <> v)
  tell $ gw { varsUsed = delete v (varsUsed gw) }
  pure retval

equalUsages :: (MonadWriter GatherWrite m, MonadError String m) => m a -> m b -> m (a, b)
equalUsages ma mb = do
  (va, gwa) <- listenSandboxed ma
  (vb, gwb) <- listenSandboxed mb
  when (not $ S.fromList (varsUsed gwa) == S.fromList (varsUsed gwb)) $ throwError ("unequal usages " <> show (varsUsed gwa) <> " and " <> show (varsUsed gwb))
  tell gwa
  tell $ gwb { varsUsed = mempty } -- TODO what if a var occurs twice in gwb but once in gwa? then we wouldn't catch the problem
  pure (va, vb)

newTV :: (MonadState Int m) => m Typ
newTV = modify (+1) >> gets TV

lookupTVEq :: (MonadState Unification m) => Int -> m (Maybe Typ)
lookupTVEq v = gets (lookup v . tvsEq)

addTVEq :: (MonadState Unification m) => Int -> Typ -> m ()
addTVEq v t = modify (<> def { tvsEq = [(v,t)] })

gather' :: Expr -> WriterT GatherWrite (ReaderT Env (StateT Int (Either String))) Typ
gather' (Lam v e) = do
  t <- newTV
  Fn t <$> addVar v t (gather' e)
gather' (App f x) = do
  tf <- gather' f
  tx <- gather' x
  ty <- newTV
  addTypesEq tf (Fn tx ty)
  pure ty
gather' (Var s) = useVar s >> M.lookup s . vars <$> ask >>= maybe (throwError $ "Undefined variable " <> s) pure
gather' Unit = pure UnitT
gather' (Tup a b) = Prod <$> gather' a <*> gather' b
gather' (Lft e) = Sum <$> gather' e <*> newTV
gather' (Rght e) = Sum <$> newTV <*> gather' e
gather' (DestructTup t va vb e) = do
  ta <- newTV
  tb <- newTV
  addTypesEq (Prod ta tb) =<< gather' t
  addVar va ta $ addVar vb tb $ gather' e
gather' (Case s vl vr el er) = do
  tl <- newTV
  tr <- newTV
  addTypesEq (Sum tl tr) =<< gather' s
  (tel, ter) <- equalUsages (addVar vl tl $ gather' el) (addVar vr tr $ gather' er)
  addTypesEq tel ter
  pure tel

gather :: Expr -> Either String (Typ, GatherWrite)
gather = flip evalStateT def . flip runReaderT def . runWriterT . gather'

replaceUnifyTVs :: (MonadState Unification m) => Typ -> m Typ
replaceUnifyTVs UnitT = pure UnitT
replaceUnifyTVs (Prod a b) = Prod <$> replaceUnifyTVs a <*> replaceUnifyTVs b
replaceUnifyTVs (Sum  a b) = Sum  <$> replaceUnifyTVs a <*> replaceUnifyTVs b
replaceUnifyTVs (Fn   a b) = Fn   <$> replaceUnifyTVs a <*> replaceUnifyTVs b
replaceUnifyTVs (TV v) = fromMaybe (TV v) <$> lookupTVEq v

unifyEq :: Typ -> Typ -> StateT Unification (Either String) ()
unifyEq UnitT UnitT = pure ()
unifyEq (Prod a b) (Prod c d) = unifyEq a c >> unifyEq b d
unifyEq (Sum a b) (Sum c d) = unifyEq a c >> unifyEq b d
unifyEq (Fn a b) (Fn c d) = unifyEq a c >> unifyEq b d
unifyEq (TV v) t = lookupTVEq v >>= maybe (addTVEq v =<< replaceUnifyTVs t) (unifyEq t)
unifyEq t (TV v) = unifyEq (TV v) t
unifyEq ta tb = throwError $ "Failed to unify " <> show ta <> " and " <> show tb

unify :: GatherWrite -> Either String Unification
unify = flip execStateT def . sequence . fmap (uncurry unifyEq) . typesEq

typecheck :: Expr -> Either String Typ
typecheck e = do
  (t, cs) <- gather e
  u <- unify cs
  pure $ evalState (replaceUnifyTVs t) u

example :: Expr
example = Lam "a" $ Lam "b" $ Case (Lft (Var "a")) "x" "y" (Lft (Tup (Var "x") (Var "b"))) (Rght Unit)

main = print $ typecheck example
