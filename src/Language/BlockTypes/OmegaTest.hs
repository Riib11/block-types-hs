module Language.BlockTypes.OmegaTest where

import qualified System.IO.Unsafe as Unsafe
import Control.Monad as Monad
import Data.Maybe as Maybe 
import qualified Data.Map as Map
import qualified Data.List as List
import Prelude hiding (lookup)

import Language.BlockTypes.Omega


test =
  tryRewrite
    (rewrites!!0)
    -- gamma
    mempty 
    -- g
    (Ctx $ Map.fromList
      [ (VarId "alpha", VarCtxItem (readSyn "U") Nothing)
      , (VarId "beta" , VarCtxItem (readSyn "U") Nothing)
      , (VarId "f"    , VarCtxItem (readSyn "(Π x : alpha . beta)") Nothing)
      ])
    -- a
    (readSyn "(λ x : alpha . (f x))")

-- test =
--   fmap showHoleSub $
--   unify
--     (Map.singleton (HoleId 0) (readSyn "U"))
--     mempty
--     (readSyn "()")
--     (readSyn "(Π x : alpha . ?0)")
