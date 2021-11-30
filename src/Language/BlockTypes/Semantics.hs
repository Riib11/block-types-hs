module Language.BlockTypes.Semantics where

import Language.BlockTypes.Syntax as Syn

data Sem
  = Syn Syn.Syn
  | Arr (Sem -> Sem)
  | Pi Var Sem (Sem -> Sem)