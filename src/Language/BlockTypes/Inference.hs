{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Language.BlockTypes.Inference where

import Language.BlockTypes.Syntax as Syntax
import Language.BlockTypes.Normalization as Normalization
import Language.BlockTypes.Substitution as Substitution
import qualified Data.Map as Map 

-- | Infers the type of a well-typed term.
infer :: Ctx -> Syn -> Syn
infer gamma = \case
  Uni -> Uni
  Pi x alpha beta -> Uni
  Lam x alpha b -> Pi x alpha (infer (Map.insert x alpha gamma) b)
  Var x -> gamma Map.! x
  App f a -> case infer gamma f of
    Pi x alpha beta -> applySub (Map.fromList [(x, a)]) beta
  Let x alpha a b -> 
    applySub (Map.fromList [(x, a)]) (infer (Map.insert x alpha gamma) b)
  Hole h alpha sigma -> alpha
