{-# LANGUAGE LambdaCase #-}
module Language.BlockTypes.Substitution where

import Language.BlockTypes.Syntax
import qualified Data.Map as Map

joinVarSub :: VarSub -> VarSub -> VarSub
joinVarSub sigma1 sigma2 = sigma1 <> Map.map (applyVarSub sigma1) sigma2

applyVarSub :: VarSub -> Syn -> Syn
applyVarSub sigma = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (applyVarSub sigma alpha) (applyVarSub sigma beta)
  Lam x alpha b -> Lam x (applyVarSub sigma alpha) (applyVarSub sigma b)
  Var x -> maybe (Var x) id (Map.lookup x sigma)
  App f a -> App (applyVarSub sigma f) (applyVarSub sigma a)
  Let x alpha a b -> Let x (applyVarSub sigma alpha) (applyVarSub sigma a) (applyVarSub sigma b)
  Hole h Nothing -> Hole h (Just sigma)
  Hole h (Just sigma') -> Hole h (Just $ joinVarSub sigma sigma')

applyHoleSub :: HoleSub -> Syn -> Syn
applyHoleSub sigma = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (applyHoleSub sigma alpha) (applyHoleSub sigma beta)
  Lam x alpha b -> Lam x (applyHoleSub sigma alpha) (applyHoleSub sigma b)
  Var x -> Var x
  App f a -> App (applyHoleSub sigma f) (applyHoleSub sigma a)
  Let x alpha a b -> Let x (applyHoleSub sigma alpha) (applyHoleSub sigma a) (applyHoleSub sigma b)
  Hole h mb_sigma' -> maybe (Hole h mb_sigma') (maybe id applyVarSub mb_sigma') (Map.lookup h sigma)