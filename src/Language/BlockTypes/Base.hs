-- {-# LANGUAGE LambdaCase, BlockArguments, OverloadedRecordDot, UndecidableInstances, NamedFieldPuns, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveTraversable, GeneralizedNewtypeDeriving, DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.BlockTypes.Base where

-- import qualified System.IO.Unsafe as Unsafe
-- import qualified System.Random as Random
-- import Control.Monad as Monad
-- import Control.Monad.State.Strict as State
-- import Control.Monad.Except as Except
-- import Control.Monad.Trans as Trans
-- import Data.Maybe as Maybe
-- import Data.Either as Either
-- import qualified Data.Map as Map
-- import qualified Data.List as List
import Prelude hiding (lookup)

-- import Data.HList as HList

data TermList = Nil | Cons Term TermList

-- Var

data Var :: Term -> TermList -> * where
  Z :: Var alpha (Cons alpha gamma)
  S :: Var alpha gamma -> Var alpha (Cons beta gamma)

-- Env

data
  Env
    (gamma :: TermList)
    (vars :: Term -> TermList -> *)
    (delta :: TermList) = Env
  {lookup :: forall alpha. Var alpha gamma -> vars alpha delta}

epsilon :: forall vars delta. Env Nil vars delta
epsilon = undefined -- Env {lookup = }

-- Term

data Term

-- Thinning
