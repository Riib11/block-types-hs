{-# LANGUAGE LambdaCase, BlockArguments, OverloadedRecordDot, UndecidableInstances, NamedFieldPuns, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveTraversable, GeneralizedNewtypeDeriving, DuplicateRecordFields #-}

module Language.BlockTypes.Test where

import qualified System.IO.Unsafe as Unsafe
import qualified System.Random as Random
import Control.Monad as Monad
import Control.Monad.State.Strict as State
import Control.Monad.Except as Except
import Control.Monad.Trans as Trans
import Data.Maybe as Maybe
import Data.Either as Either
import qualified Data.Map as Map
import qualified Data.List as List
import Prelude hiding (lookup)

import Language.BlockTypes.Base

-- suite :: 

data Test = Test
  { name :: String
  , prgm :: Prgm
  , cont :: Prgm -> Gen () }

runTest :: Test -> IO ()
runTest test = do
  putStrLn $ "[BEGIN TEST] " ++ test.name
  evalStateT (test.cont test.prgm) (makeGenState test.prgm)
  putStrLn $ "[End TEST] " ++ test.name

suite1 :: IO ()
suite1 = do
  runTest test1

test1 :: Test
test1 = Test
  { name = "test1"
  , prgm = Prgm
      { gammaTop = Ctx
          [ (0, readTrm "U")
          , (1, readTrm "?0") ]
      , aTop = readTrm "?1" }
  , cont = \prgm -> do
      lift $ print prgm
      Just prgm <- tryRewrite (rewrites Map.! "fill Π") Free Here prgm
      lift $ print prgm
      Just prgm <- tryRewrite (rewrites Map.! "fill U") Free (Pi_alpha Here) prgm
      lift $ print prgm
      Just prgm <- tryRewrite (rewrites Map.! "fill U") Free (Pi_beta Here) prgm 
      lift $ print prgm
  }

