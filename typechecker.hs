{-# LANGUAGE FlexibleContexts, LambdaCase #-}

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer hiding (Sum)
import           Data.Default
import qualified Data.Map as M
import           Data.Maybe

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

data Env
   = Env
   { vars :: M.Map String Typ
   }

instance Default Env where
  def = Env { vars = M.empty }

data Constraints
   = Constraints
   { typesEq :: [(Typ, Typ)]
   }

instance Semigroup Constraints where
  a <> b = Constraints { typesEq = typesEq a <> typesEq b }

instance Monoid Constraints where
  mempty = Constraints { typesEq = mempty }

instance Default Constraints where
  def = mempty

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

addVar :: (MonadReader Env m) => String -> Typ -> m a -> m a
addVar v t = local (\e -> e { vars = M.insert v t (vars e) })

newTV :: (MonadState Int m) => m Typ
newTV = modify (+1) >> gets TV

addTypesEq :: (MonadWriter Constraints m) => Typ -> Typ -> m ()
addTypesEq a b = tell $ def { typesEq = [(a, b)] }

lookupTVEq :: (MonadState Unification m) => Int -> m (Maybe Typ)
lookupTVEq v = gets (lookup v . tvsEq)

addTVEq :: (MonadState Unification m) => Int -> Typ -> m ()
addTVEq v t = modify (<> def { tvsEq = [(v,t)] })

gather' :: Expr -> WriterT Constraints (ReaderT Env (StateT Int (Either String))) Typ
gather' (Lam v e) = do
  t <- newTV
  Fn t <$> addVar v t (gather' e)
gather' (App f x) = do
  tf <- gather' f
  tx <- gather' x
  ty <- newTV
  addTypesEq tf (Fn tx ty)
  pure ty
gather' (Var s) = M.lookup s . vars <$> ask >>= maybe (throwError $ "Undefined variable " <> s) pure
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
  tel <- addVar vl tl $ gather' el
  ter <- addVar vr tr $ gather' er
  addTypesEq tel ter
  pure tel

gather :: Expr -> Either String (Typ, Constraints)
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

unify :: Constraints -> Either String Unification
unify = flip execStateT def . sequence . fmap (uncurry unifyEq) . typesEq

typecheck :: Expr -> Either String Typ
typecheck e = do
  (t, cs) <- gather e
  u <- unify cs
  pure $ evalState (replaceUnifyTVs t) u

example :: Expr
example = Lam "a" $ Lam "b" $ Case (Lft (Var "a")) "x" "y" (Lft (Tup (Var "x") (Var "b"))) (Rght Unit)

main = print $ typecheck example
