{-# LANGUAGE LambdaCase, OverloadedRecordDot #-}

module Language.BlockTypes.Shallow where

import Language.BlockTypes.Syntax
import Data.Map as Map

-- |
-- == Hole Fill

-- | A Fill maps a hole to its type and value.
type Fill = Map Hole FillItem
data FillItem = FillItem
  { fillType :: Sha
  , fillVal :: Sha }

fromFill :: Fill -> Map Hole Syn
fromFill fill = Map.map (\item -> fromSha fill item.fillVal) fill

-- |
-- == Shallow form

type Sha = Fill -> ShaAux
data ShaAux 
  = UniSha
  | PiSha Var Sha Sha
  | LamSha Var Sha Sha
  | VarSha Var
  | AppSha Sha Sha
  | LetSha Var Sha Sha Sha
  | HoleSha Hole Sha ShaSub

-- |
-- == Shallow normal form

type ShaNrm = Fill -> ShaNrmAux
data ShaNrmAux
    = UniShaNrm
    | PiShaNrm Var ShaNrm ShaNrm
    | LamShaNrm Var ShaNrm ShaNrm
    | NeuShaNrm ShaNeu
    | HoleShaNrm Hole Sha ShaSub

type ShaNeu = Fill -> ShaNeuAux 
data ShaNeuAux
    = AppShaNeu ShaNeu ShaNrm
    | VarShaNeu Var

-- |
-- == Variable Context and Substitution

type ShaCtx = Map Var Sha

type ShaSub = Map Var Sha

-- |
-- == Conversions

-- | Abstract all syntactic `Hole`s into a parameter `Fill`.
toSha :: Syn -> Sha
toSha = \case
  Uni -> const UniSha
  Pi x alpha beta -> const $ PiSha x (toSha alpha) (toSha beta)
  Lam x alpha b -> const $ LamSha x (toSha alpha) (toSha b)
  App f a -> const $ AppSha (toSha f) (toSha a)
  Var x -> const $ VarSha x
  Hole h alpha sigma -> \fill ->
    case fill !? h of
      Just item -> item.fillVal fill
      Nothing -> HoleSha h (toSha alpha) (toShaSub sigma)

-- | Concretizes parameter holes in `Fill` into syntactic syntactic holes.
fromSha :: Fill -> Sha -> Syn
fromSha fill sha = case sha fill of
  UniSha -> Uni
  PiSha x alpha beta -> Pi x (fromSha fill alpha) (fromSha fill beta)
  LamSha x alpha b -> Lam x (fromSha fill alpha) (fromSha fill b)
  AppSha f a -> App (fromSha fill f) (fromSha fill a)
  VarSha x -> Var x
  HoleSha h alpha sigma ->
    case fill !? h of
      Just item -> fromSha fill item.fillVal
      Nothing -> Hole h (fromSha fill alpha) (fromShaSub fill sigma)

-- | Same as `toSha` except for `ShaNrm`.
toShaNrm :: SynNrm -> ShaNrm
toShaNrm = undefined

-- | Same as `fromSha` except for `ShaNrm`.
fromShaNrm :: Fill -> ShaNrm -> SynNrm
fromShaNrm = undefined

fromShaNrmToSha :: ShaNrm -> Sha
fromShaNrmToSha = undefined

toShaSub :: Sub -> ShaSub
toShaSub = Map.map toSha
    
fromShaSub :: Fill -> ShaSub -> Sub
fromShaSub fill = Map.map (fromSha fill)

toShaCtx :: Ctx -> ShaCtx
toShaCtx = undefined

fromShaCtx :: Fill -> ShaCtx -> Ctx
fromShaCtx = undefined
