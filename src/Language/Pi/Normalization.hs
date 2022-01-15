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

reify :: Sem -> Sem -> Nrm
reify SemUni SemUni = NrmUni
reify SemUni (SemPi alpha beta) =
  NrmPi
    (reify SemUni alpha)
    (reify SemUni (beta weaken (SemNeu (NeuVar Z))))
reify (SemPi _ beta) (SemLam alpha b) =
  NrmLam
    (reify SemUni alpha)
    (reify (beta weaken (SemNeu (NeuVar Z))) (b weaken (SemNeu (NeuVar Z))))

reflect :: Sem -> Neu -> Sem
reflect SemUni n = SemNeu n
reflect (SemPi alpha beta) n =
  SemLam
    alpha
    ( \rho a ->
        let b = thinnableNeu rho n
         in reflect undefined (NeuApp b (reify alpha a))
    )
reflect (SemNeu _) n = SemNeu n

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

eval :: Env Sem -> Trm -> Sem
eval = semantics normalization

norm :: Sem -> Trm -> Nrm
norm alpha a =
  reify
    alpha
    (eval (Env {lookup = \x -> reflect undefined (NeuVar x)}) a)
