{-# LANGUAGE BlockArguments, LambdaCase, OverloadedRecordDot #-}

module Language.BlockTypes.Unification where

import Language.BlockTypes.Syntax as Syntax
import Language.BlockTypes.Context as Context
import qualified Language.BlockTypes.Context as Context
import Language.BlockTypes.Normalization as Normalization
import qualified Language.BlockTypes.Inference as Inference 
import qualified Language.BlockTypes.Substitution as Substitution
import Control.Monad.Trans as Trans 
import Control.Monad.Except as Except
import Control.Monad.State as State
import qualified Data.Map as Map
import Prelude hiding (lookup)

-- |
-- == Types

data UnifyState = UnifyState
  { holeCtx :: HoleCtx
  , varCtx :: VarCtx
  , holeSub :: HoleSub }
  deriving (Show)

data UnifyException
  = Incompatible Syn Syn
  | LookupFailure Hole
  deriving (Show)

type Unify a = StateT UnifyState (Except UnifyException) a

runUnify :: Unify a -> Either UnifyException (a, UnifyState)
runUnify m = runExcept $ runStateT m st where
  st = UnifyState
    { holeCtx = mempty
    , varCtx = mempty
    , holeSub = mempty }

-- |
-- == Unify

unify :: Syn -> Syn -> Unify Syn
-- Pi
unify (Pi x1 alpha1 beta1) (Pi x2 alpha2 beta2) = do
  alpha <- unify (normalize_ Uni alpha1) (normalize_ Uni alpha2)
  beta <- locally do
    intro x1 alpha
    intro x2 alpha
    unify (normalize_ Uni beta1) (normalize_ Uni beta2)
  return $ Pi x1 alpha beta
-- Lam
unify (Lam x1 alpha1 b1) (Lam x2 alpha2 b2) = do
  alpha <- unify (normalize_ Uni alpha1) (normalize_ Uni alpha2)
  b <- locally do
    intro x1 alpha
    intro x2 alpha
    unify b1 b1
  return $ Lam x1 alpha b
-- Let
unify (Let x1 alpha1 a1 b1) (Let x2 alpha2 a2 b2) = do
  alpha <- unify (normalize_ Uni alpha1) (normalize_ Uni alpha2)
  a <- unify a1 a2
  b <- locally do
    bind x1 alpha a
    bind x2 alpha a
    unify b1 b2
  return $ Let x1 alpha a b
-- Var
unify (Var x1) (Var x2) = 
  if x1 == x2
    then return $ Var x1
    else throwError $ Incompatible (Var x1) (Var x2)
-- App
unify (App f1 a1) (App f2 a2) = do
  f <- unify f1 f2
  a <- unify a1 a2
  return $ App f a
-- Hole (without variable substitutions)
unify (Hole h1 Nothing) a2 = do
  alpha1 <- lookup h1
  alpha2 <- infer a2
  addHoleSub h1 a2
  return a2
-- Hole (with variable substitutions)
unify (Hole h1 (Just sigma1)) (Hole h2 (Just sigma2)) = do
  if sigma1 == sigma2
    then return $ Hole h1 (Just sigma1)
    else throwError $ Incompatible (Hole h1 (Just sigma1)) (Hole h2 (Just sigma2))
-- Incompatible
unify a a' = throwError $ Incompatible a a'

-- |
-- == Utility functions

-- | Adds a variable, with its type, to the variable context.
intro :: Var -> Syn -> Unify ()
intro x alpha = do
  st <- get
  put $ st { varCtx = Map.insert x VarCtxItem {varTyp = alpha, varVal = Nothing} (varCtx st) }

-- | Adds a variable, with its type and value, to the variable context.
bind :: Var -> Syn -> Syn -> Unify ()
bind x alpha a = do
  st <- get 
  put $ st { varCtx = Map.insert x VarCtxItem { varTyp = alpha, varVal = Just a } (varCtx st) }

-- | Runs a unification locally, with respect to the variable context.
locally :: Unify a -> Unify a
locally m = do
  st <- get
  a <- m
  st' <- get
  put $ st { varCtx = varCtx st }
  return a

-- | Infers the type of a term.
infer :: Syn -> Unify Syn
infer a = Inference.infer <$> (holeCtx <$> get) <*> (varCtx <$> get) <*> (return a)

-- | Looks up the type of a hole.
lookup :: Hole -> Unify Syn
lookup h = Map.lookup h <$> (holeCtx <$> get) >>= \case
  Just item -> return item.holeTyp
  Nothing -> throwError $ LookupFailure h

-- | Substitutes a hole for a term. Applies the substitution to the variable context and the hole context.
addHoleSub :: Hole -> Syn -> Unify ()
addHoleSub h a = do
  st <- get
  put $ st { holeSub = Map.insert h a (holeSub st) }
  applyHoleSub

applyHoleSub :: Unify ()
applyHoleSub = 
  let applyHoleSubInVarCtx :: HoleSub -> VarCtx -> VarCtx
      applyHoleSubInVarCtx sigma = Map.map \item ->
        VarCtxItem
          { varTyp = Substitution.applyHoleSub sigma item.varTyp
          , varVal = Substitution.applyHoleSub sigma <$> item.varVal }
      applyHoleSubInHoleCtx :: HoleSub -> HoleCtx -> HoleCtx
      applyHoleSubInHoleCtx sigma = Map.map \item ->
        HoleCtxItem
          { holeTyp = Substitution.applyHoleSub sigma item.holeTyp
          , holeVarCtx = applyHoleSubInVarCtx sigma item.holeVarCtx }
  in do
    st <- get
    put $ st 
      { varCtx = applyHoleSubInVarCtx st.holeSub st.varCtx
      , holeCtx = applyHoleSubInHoleCtx st.holeSub st.holeCtx }
