{-# LANGUAGE DuplicateRecordFields #-}
module Language.BlockTypes.Syntax where

import Data.Map as Map

-- |
-- == Types

data Syn
  = Uni
  | Pi Var Syn Syn
  | Lam Var Syn Syn
  | Var Var
  | App Syn Syn
  | Let Var Syn Syn Syn
  | Hole Hole (Maybe VarSub)
  deriving (Eq, Show)

data SynNrm
  = UniNrm
  | PiNrm Var Syn Syn
  | LamNrm Var Syn Syn
  | Neu SynNeu
  deriving (Eq, Show)

data SynNeu
  = VarNrm Var
  | VarApp SynNeu SynNrm
  deriving (Eq, Show)

-- |
-- == Variables and Holes

data Var = MakeVar { name :: String, dbl :: Dbl }
instance Eq Var where x == y = dbl x == dbl y
instance Ord Var where x <= y = dbl x <= dbl y
instance Show Var where show x = name x ++ show (dbl x)

newtype Dbl = Dbl Int deriving (Eq, Ord)
instance Show Dbl where show (Dbl i) = "#" ++ show i

newtype Hole = MakeHole { hid :: HoleId } deriving (Eq, Ord)
instance Show Hole where show h = "?" ++ show (hid h)

newtype HoleId = HoleId Int deriving (Eq, Ord)
instance Show HoleId where show (HoleId i) = show i


-- |
-- == Conversions

-- | Inject a normal form into basic syntax.
toSyn :: SynNrm -> Syn
toSyn = undefined

-- |
-- == Substitutions

type VarSub  = Map Var Syn
type HoleSub = Map Hole Syn

-- |
-- == Utilities

