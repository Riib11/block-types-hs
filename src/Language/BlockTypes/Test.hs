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
  , cont :: Prgm -> Gen (Maybe Prgm) }

runTest :: Test -> IO ()
runTest test = do
  putStrLn $ "[TEST] " ++ test.name
  putStrLn $ "   input: " ++ show test.prgm
  genSt <- makeGenState test.prgm
  evalStateT (test.cont test.prgm) genSt >>= \case 
    Just prgm -> do
      putStrLn $ "  output: " ++ show prgm
    Nothing ->
      putStrLn "FAILURE"

testVar :: IO ()
testVar = do
  let prgm = Prgm{ aTop = readTerm "(λ #0 : U . ?1)"
                 , gammaTop = Ctx 
                    [ (0, readTerm "U")
                    , (1, readTerm "?0") ] }
  genSt <- makeGenState prgm
  print =<< evalStateT
    (do
      tryVariable 0 (Lam_b Here) prgm
    )
    genSt

suite1 :: IO ()
suite1 = mapM_ runTest
  [
    test1
  , test2
  , test3
  ]

test1 :: Test
test1 = Test
  { name = "construct (Π x : U . U)"
  , prgm = Prgm
      { gammaTop = Ctx
          [ (0, readTerm "U")
          , (1, readTerm "?0") ]
      , aTop = readTerm "?1" }
  , cont = tryRewrites
      [ (rewrite_fill_Pi, Here)
      , (rewrite_fill_U, Pi_alpha Here)
      , (rewrite_fill_U, Pi_beta Here) ]
  }

test2 :: Test
test2 = Test
  { name = "construct (λ x : U . U)"
  , prgm = Prgm
      { gammaTop = Ctx
          [ (0, readTerm "U")
          , (1, readTerm "?0") ]
      , aTop = readTerm "?1" }
  , cont = tryRewrites
      [ (rewrite_fill_lambda, Here)
      , (rewrite_fill_U, Lam_alpha Here)
      , (rewrite_fill_U, Lam_b Here) ]
  }

test3 :: Test
test3 = Test
  { name = "simple β-reduction of ((λ x : U . x) U)" 
  , prgm = Prgm
      { gammaTop = Ctx []
      , aTop = readTerm "((λ #0 : U . #0) U)" }
  , cont = tryRewrites
      [ (rewrite_beta_reduce, Here) ]
  }

test_var :: IO ()
test_var = do
  let prgm = Prgm
        { gammaTop = Ctx
            [ (0, readTerm "U")
            , (1, readTerm "?0") ]
        , aTop = readTerm "?1" }
  genSt <- makeGenState prgm
  let m = do tryRewrites
               [ (rewrite_fill_lambda, Here)
               , (rewrite_fill_U, Lam_alpha Here) ]
               prgm
               >>= \case
                Just prgm -> 
                  tryVariable 2 (Lam_b Here) prgm >>= \case
                    Just prgm -> return $ Just prgm
                    Nothing -> return $ Just prgm
                Nothing -> return $ Just prgm
  prgm <- evalStateT m genSt
  print prgm