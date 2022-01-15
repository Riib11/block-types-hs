{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Pi.Printing where

import Control.Monad.State as State
import Language.Pi.Base
import Prelude hiding (lookup, pi, print)

type Name = String

type Fresh a = State [String] a

type Printer = Fresh String

fresh :: Fresh Name
fresh = do
  names <- get
  put (tail names)
  return $ head names

printing :: Semantics Name Printer
printing =
  Semantics
    { thinnable = \rho w -> w,
      uni = return "U",
      var = return,
      lam = \malpha mb -> do
        x <- fresh
        alpha <- malpha
        b <- mb weaken x
        return $ "(lam " ++ x ++ " : " ++ alpha ++ " . " ++ b ++ ")",
      pi = \malpha mbeta -> do
        x <- fresh
        alpha <- malpha
        beta <- mbeta weaken x
        return $ "(pi " ++ x ++ " : " ++ alpha ++ " . " ++ beta ++ ")",
      app = \mf ma -> do
        f <- mf
        a <- ma
        return $ "(" ++ f ++ " " ++ a ++ ")"
    }

names :: [String]
names = [c : i | i <- "" : map show [1 ..], c <- ['a' .. 'z']]

print :: Trm -> String
print a = fst $ runState (semantics printing epsilon a) $ names
