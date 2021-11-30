{-# LANGUAGE DuplicateRecordFields #-}

module Language.BlockTypes.Context where

import Language.BlockTypes.Syntax as Syn
import Data.Maybe as Maybe
import Data.Map as Map

type VarCtx = Map Var VarCtxItem
data VarCtxItem = VarCtxItem { varTyp :: Syn, varVal :: Maybe Syn }
  deriving (Show)

toVarSub :: VarCtx -> VarSub
toVarSub = Map.filter isJust . Map.map varVal

type HoleCtx = Map Hole HoleCtxItem
data HoleCtxItem = HoleCtxItem { holeTyp :: Syn, holeVarCtx :: VarCtx }
  deriving (Show)
