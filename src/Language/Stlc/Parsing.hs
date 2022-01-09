{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Stlc.Parsing where

import Control.Monad.State as State
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as THQuote
import qualified Language.Haskell.TH.Syntax as THSyntax
import Language.Stlc.Base
import Prelude hiding (lookup, print)

-- stlc :: THQuote.QuasiQuoter
-- stlc = THQuote.QuasiQuoter {THQuote.quoteExp = quoteStlc}

-- quoteStlc :: String -> TH.ExpQ
-- quoteStlc =
