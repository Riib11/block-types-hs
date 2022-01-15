{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module Language.Pi.Normalization where

import Control.Monad.State as State
import Language.Pi.Base
import Prelude hiding (lookup, pi)

data Nrm
  = NrmUni
  | NrmPi Nrm Nrm
  | NrmLam Nrm Nrm
  | NrmNeu Neu
  deriving (Show)

data Neu
  = NeuVar Var
  | NeuApp Neu Nrm
  deriving (Show)

thinnableNeu :: Thinnable Neu
thinnableNeu rho n = undefined

data Sem
  = SemUni
  | SemPi Sem (Thinning -> Sem -> Sem)
  | SemLam Sem (Thinning -> Sem -> Sem)
  | SemNeu Neu

reify :: Nrm -> Sem -> Nrm
reify NrmUni SemUni = NrmUni
reify NrmUni (SemPi alpha beta) =
  NrmPi
    (reify NrmUni alpha)
    (reify NrmUni (beta weaken (SemNeu (NeuVar Z))))
reify (NrmPi _ beta) (SemLam alpha b) =
  NrmLam
    (reify NrmUni alpha)
    (reify beta (b weaken (SemNeu (NeuVar Z))))

reflect :: Nrm -> Neu -> Sem
reflect NrmUni n = SemNeu n
reflect (NrmPi alpha beta) n =
  SemLam
    undefined
    ( \rho a ->
        let b = thinnableNeu rho n
         in reflect undefined (NeuApp b (reify alpha a))
    )
reflect (NrmNeu _) n = SemNeu n

normalization :: Semantics Sem Sem
normalization =
  Semantics
    { thinnable = \rho a -> a,
      uni = SemUni,
      var = id,
      pi = \alpha beta -> SemPi alpha beta,
      lam = \alpha b -> SemLam alpha b,
      app = \case
        SemLam alpha b -> b weaken
        SemNeu f -> \a -> SemNeu (NeuApp f (reify undefined a))
    }

nbe :: Env Sem -> Trm -> Sem
nbe = semantics normalization

norm :: Nrm -> Trm -> Nrm
norm alpha a =
  reify
    alpha
    (nbe (Env {lookup = \x -> reflect undefined (NeuVar x)}) a)
