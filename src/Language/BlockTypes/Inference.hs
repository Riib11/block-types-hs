{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Language.BlockTypes.Inference where

import Language.BlockTypes.Syntax as Syntax
import Language.BlockTypes.Context as Context
import Language.BlockTypes.Normalization as Normalization
import qualified Data.Map as Map 

-- | Infers the type of a well-typed term.
infer :: HoleCtx -> VarCtx -> Syn -> Syn
infer holeCtx varCtx = \case
  Uni -> Uni
  Pi x alpha beta -> Uni 
  Lam x alpha b -> Pi x alpha beta where
    beta = infer holeCtx (Map.insert x VarCtxItem {varTyp = alpha, varVal = Nothing} varCtx) b
  Var x -> (varCtx Map.! x).varTyp
  App f a -> case infer holeCtx varCtx f of
    Pi x alpha beta -> applyVarSub (Map.insert x a $ toVarSub varCtx)
    _ -> error "Tried to infer the type of a badly-typed term."
  Let x alpha a b -> infer holeCtx (Map.insert VarCtxItem { varTyp = alpha, varVal = Just a })
  