{-# LANGUAGE DuplicateRecordFields, LambdaCase #-}
module Language.BlockTypes.Syntax where

import Control.Arrow as Arrow
import Data.Maybe as Maybe
import Data.Map as Map
import Data.List as List

-- |
-- == Types

data Syn
  = Uni
  | Pi Var Syn Syn
  | Lam Var Syn Syn
  | App Syn Syn
  | Var Var
  | Hole Hole Sub
  | Let Var Syn Syn Syn
  deriving (Eq)

instance Show Syn where 
  show = \case
    Uni -> "U"
    Pi x alpha beta -> "(Π " <> show x <> " : " <> show alpha <> " . " <> show beta <> ")"
    Lam x alpha b -> "(λ " <> show x <> " : " <> show alpha <> " . " <> show b <> ")"
    App f a -> "(" <> show f <> " " <> show a <> ")"
    Var x -> show x
    Hole h alpha sigma -> 
      "(" <> show h <> " : " <> show alpha <> ")" <>
      if Map.null sigma then "" else showSub sigma

-- |
-- == Normal form

data SynNrm
  = UniNrm
  | PiNrm Var SynNrm SynNrm
  | LamNrm Var SynNrm SynNrm
  | Neu SynNeu
  deriving (Eq, Show)

data SynNeu
  = VarNeu Var
  | HoleNeu Hole Syn Sub
  | AppNeu SynNeu SynNrm
  deriving (Eq, Show)

-- |
-- == Variables and Holes

data Var = MakeVar { name :: String, dbl :: Dbl }
instance Eq Var where x == y = dbl x == dbl y
instance Ord Var where x <= y = dbl x <= dbl y
instance Show Var where show x = name x <> show (dbl x)

newtype Dbl = Dbl Int deriving (Eq, Ord)
instance Show Dbl where show (Dbl i) = "#" <> show i

newtype Hole = MakeHole { hid :: HoleId } deriving (Eq, Ord)
instance Show Hole where show h = "?" <> show (hid h)

newtype HoleId = HoleId Int deriving (Eq, Ord)
instance Show HoleId where show (HoleId i) = show i

-- |
-- == Variable Context and Substitution

type Ctx = Map Var Syn

showCtx :: Ctx -> String
showCtx gamma = 
  if Map.null gamma then
    "{}"
  else
    "{" <>
    ( Map.toList >>>
      List.map (\(x, alpha) -> show x <> " : " <> show alpha) >>>
      List.intercalate ", " )
      gamma <> 
    "}"

type Sub = Map Var Syn

showSub :: Sub -> String
showSub sigma =
  if Map.null sigma then
    "{}"
  else
    "[" <>
    ( Map.toList >>>
      List.map (\(x, a) -> show x <> " = " <> show a) >>>
      List.intercalate ", " )
      sigma <> 
    "]"

-- |
-- == Conversions

-- | Inject a normal form into basic syntax.
toSyn :: SynNrm -> Syn
toSyn = undefined
