{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Utlc.Normalization where

import Control.Monad.State as State
import Language.Utlc.Base
import Prelude hiding (lookup, print)

data Nrm :: Nat -> * where
  LamNrm :: forall n. Nrm (Suc n) -> Nrm n
  NeuNrm :: forall n. Neu n -> Nrm n

data Neu :: Nat -> * where
  VarNeu :: forall n. Var n -> Neu n
  AppNeu :: forall n. Neu n -> Nrm n -> Neu n

deriving instance Show (Nrm n)

deriving instance Show (Neu n)

fromNrm :: Nrm n -> Trm n
fromNrm (LamNrm b) = Lam (fromNrm b)
fromNrm (NeuNrm (VarNeu x)) = Var x
fromNrm (NeuNrm (AppNeu f a)) = App (fromNrm (NeuNrm f)) (fromNrm a)

renamingNrm :: Semantics Var Nrm
renamingNrm =
  Semantics
    { thinnableSemanticsDom = \a gamma -> lookup gamma a,
      var = NeuNrm . VarNeu,
      app = \(NeuNrm f) a -> NeuNrm (AppNeu f a),
      lam = \b -> LamNrm (b weaken Z)
    }

renNrm :: Thinning m n -> Trm m -> Nrm n
renNrm = semantics renamingNrm

substitutionNrm :: Semantics Nrm Nrm
substitutionNrm =
  Semantics
    { thinnableSemanticsDom = \a gamma -> renNrm gamma (fromNrm a),
      var = id,
      app = \(NeuNrm f) a -> NeuNrm (AppNeu f a),
      lam = \b -> LamNrm (b weaken (NeuNrm (VarNeu Z)))
    }

subNrm :: Env Nrm m n -> Trm m -> Nrm n
subNrm = semantics substitutionNrm

normalization :: Semantics Var Nrm
normalization =
  Semantics
    { thinnableSemanticsDom = \a gamma -> lookup gamma a,
      var = NeuNrm . VarNeu,
      app = \(LamNrm b) a ->
        subNrm
          (append Env {lookup = NeuNrm . VarNeu} a)
          (fromNrm b),
      lam = \b -> LamNrm (b weaken Z)
    }

norm :: Thinning m n -> Trm m -> Nrm n
norm = semantics normalization
