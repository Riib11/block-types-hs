{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Stlc.Printing where

import Control.Monad.State as State
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as THQuote
import qualified Language.Haskell.TH.Syntax as THSyntax
import Language.Stlc.Base
import Prelude hiding (lookup, print)

type Name = Wrap String

type Fresh a = State [String] a

type Printer = Wrap (Fresh String)

fresh :: forall gamma alpha. Fresh (Name (Cons alpha gamma) alpha)
fresh = do
  names <- get
  put (tail names)
  return (Wrap (head names))

printing :: Semantics Name Printer
printing =
  Semantics
    { thinnableSemanticsDom = \w rho -> Wrap (unWrap w),
      var = mapWrap return,
      app = \mf ma -> Wrap do
        f <- unWrap mf
        a <- unWrap ma
        return $ "(" ++ f ++ " " ++ a ++ ")",
      lam = \mb -> Wrap do
        x <- fresh
        b <- unWrap (mb weaken x)
        return $ "(lam " ++ unWrap x ++ ". " ++ b ++ ")"
    }

names :: [String]
names = [c : i | i <- "" : map show [1 ..], c <- ['a' .. 'z']]

print :: forall alpha. Nil :|- alpha -> String
print a = fst $ runState (unWrap $ semantics printing epsilon a) $ names

-- Test
