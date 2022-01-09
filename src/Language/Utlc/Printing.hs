{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Utlc.Printing where

import Control.Monad.State as State
import Language.Utlc.Base
import Prelude hiding (lookup, print)

type Name = Wrap String

type Fresh a = State [String] a

type Printer = Wrap (Fresh String)

fresh :: Fresh (Name (Suc n))
fresh = do
  names <- get
  put (tail names)
  return (Wrap (head names))

thinnableWrap ::
  Wrap a m ->
  Thinning m n ->
  Wrap a n
thinnableWrap w rho = Wrap (unWrap w)

printing :: Semantics Name Printer
printing =
  Semantics
    { thinnableSemanticsDom = \w rho -> Wrap (unWrap w),
      var = mapWrap return,
      app = \pf pa -> Wrap do
        f <- unWrap pf
        a <- unWrap pa
        return $ "(" ++ f ++ " " ++ a ++ ")",
      lam = \mb -> Wrap do
        x <- fresh
        b <- unWrap (mb weaken x)
        return $ "(" ++ unWrap x ++ " => " ++ b ++ ")"
    }

names :: [String]
names = [c : i | i <- "" : map show [1 ..], c <- ['a' .. 'z']]

print :: Trm Zero -> String
print a = fst $ runState (unWrap printer) $ names
  where
    printer :: Printer Zero
    printer = semantics printing epsilon a
