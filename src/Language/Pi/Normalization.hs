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
  | SemFun (Thinning -> Sem -> Sem)
  | SemNeu Neu

thinnableSem :: Thinnable Sem
thinnableSem rho a = undefined

reify :: Sem -> Sem -> Nrm
reify SemUni SemUni = NrmUni
reify SemUni (SemPi alpha beta) =
  NrmPi
    (reify SemUni alpha)
    (reify SemUni (beta weaken (SemNeu (NeuVar Z))))
reify (SemPi alpha beta) (SemFun b) =
  NrmLam
    (reify SemUni alpha)
    (reify (beta weaken (SemNeu (NeuVar Z))) (b weaken (SemNeu (NeuVar Z))))

reflect :: Sem -> Neu -> Sem
reflect SemUni n = SemNeu n
reflect (SemPi alpha beta) n =
  SemFun
    ( \rho a ->
        let b = thinnableNeu rho n
         in reflect (beta idThinning a) (NeuApp b (reify alpha a))
    )
reflect (SemNeu _) n = SemNeu n

normalization :: Semantics Sem Sem
normalization =
  Semantics
    { thinnable = thinnableSem,
      uni = SemUni,
      var = id,
      pi = \alpha beta -> SemPi alpha beta,
      lam = \alpha b -> SemFun b,
      app = \(SemFun b) a -> b idThinning a
    }

eval :: Env Sem -> Trm -> Sem
eval = semantics normalization

norm :: Trm -> Trm -> Nrm
norm alpha a =
  reify
    (eval (Env {lookup = SemNeu . NeuVar}) alpha)
    (eval (Env {lookup = SemNeu . NeuVar}) a)
