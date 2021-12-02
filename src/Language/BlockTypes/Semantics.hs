module Language.BlockTypes.Semantics where

import Language.BlockTypes.Syntax as Syn
import Data.Map as Map

data Sem
  = Syn Syn
  | PiSem Var Sem (Sem -> Sem)
  | LamSem Var Sem (Sem -> Sem)

type SubSem = Map Var Sem