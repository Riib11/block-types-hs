{-# LANGUAGE LambdaCase #-}
module Language.BlockTypes.Substitution where

import Language.BlockTypes.Syntax as Syntax
import Language.BlockTypes.Normalization as Normalization
import qualified Data.Map as Map

joinSub :: Sub -> Sub -> Sub
joinSub = undefined
-- joinSub sigma1 sigma2 = sigma1 <> Map.map (applySub sigma1) sigma2

applySub :: Sub -> Syn -> Syn
applySub = undefined
-- applySub sigma gamma = \case
--   Uni -> Uni
--   Pi x alpha beta -> Pi x (applySub sigma gamma alpha) (applySub sigma gamma beta)
--   Lam x alpha b -> Lam x (applySub sigma gamma alpha) (applySub sigma gamma b)
--   Var x -> maybe (Var x) id (Map.lookup x sigma)
--   App f a -> App (applySub sigma gamma f) (applySub sigma gamma a)
--   Let x alpha a b -> Let x (applySub sigma gamma alpha) (applySub sigma gamma a) (applySub sigma gamma b)
--   Hole h alpha sigma' -> 
--     if Map.null sigma'
--       then Hole h alpha sigma'
--       else Hole h (normalize  UniNrm (applySub (sigma `joinSub` sigma')  gamma (toSyn alpha))) (sigma `joinSub` sigma')
