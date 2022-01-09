{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Pi.Normalization where

import Control.Monad.State as State
import Language.Pi.Base
import Prelude hiding (lookup, pi)

normalization :: Semantics Trm Trm
normalization =
  Semantics
    { thinnable = \a rho -> ren rho a,
      uni = Uni,
      var = id,
      lam = \alpha b -> Lam alpha (b weaken (Var Z)),
      pi = \alpha beta -> Pi alpha (beta weaken (Var Z)),
      app = \(Lam alpha b) a -> sub (subEnv a) b
    }

norm :: Env Trm -> Trm -> Trm
norm = semantics normalization
