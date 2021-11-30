module Language.BlockTypes.Normalization where

import Language.BlockTypes.Semantics as Sem
import Language.BlockTypes.Syntax as Syn

type Sub = [Sem]

normalize_ :: Syn -> Syn -> Syn
normalize_ alpha a = toSyn $ normalize alpha a

normalize :: Syn -> Syn -> SynNrm
normalize alpha a = reify (evaluate alpha []) (evaluate a []) 0

evaluate :: Syn -> Sub -> Sem
evaluate = undefined

reflect :: Sem -> Syn -> Int -> Sem
reflect = undefined

reify :: Sem -> Sem -> Int -> SynNrm
reify = undefined