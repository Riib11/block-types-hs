{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Stlc.Base where

import Prelude hiding (lookup, print)

-- Nat

data Nat = Zero | Suc Nat deriving (Eq, Ord, Show)

-- Typ

data Typ = Typ :-> Typ

deriving instance Show Typ

-- Ctx

data Ctx where
  Nil :: Ctx
  Cons :: Typ -> Ctx -> Ctx

deriving instance Show Ctx

-- Var

data (:|-@) :: Ctx -> Typ -> * where
  Z :: forall gamma alpha. Cons alpha gamma :|-@ alpha
  S :: forall gamma alpha beta. gamma :|-@ alpha -> Cons beta gamma :|-@ alpha

deriving instance Show (gamma :|-@ alpha)

-- Trm

data (:|-) :: Ctx -> Typ -> * where
  Var ::
    forall gamma alpha.
    gamma :|-@ alpha ->
    gamma :|- alpha
  App ::
    forall gamma alpha beta.
    gamma :|- (alpha :-> beta) ->
    gamma :|- alpha ->
    gamma :|- beta
  Lam ::
    forall gamma alpha beta.
    Cons alpha gamma :|- beta ->
    gamma :|- (alpha :-> beta)

deriving instance Show (gamma :|- alpha)

-- Env

data Env (dom :: Ctx -> Typ -> *) (gamma :: Ctx) (delta :: Ctx) = Env
  {lookup :: forall alpha. gamma :|-@ alpha -> delta `dom` alpha}

epsilon ::
  forall dom gamma.
  Env dom Nil gamma
epsilon = Env {lookup = \case }

append ::
  forall dom gamma delta alpha.
  Env dom gamma delta ->
  delta `dom` alpha ->
  Env dom (Cons alpha gamma) delta
append gamma a = Env {lookup = \case Z -> a; (S x) -> lookup gamma x}

mapEnv ::
  forall dom1 dom2 gamma delta theta.
  (forall alpha. delta `dom1` alpha -> theta `dom2` alpha) ->
  Env dom1 gamma delta ->
  Env dom2 gamma theta
mapEnv f gamma = Env {lookup = \x -> f (lookup gamma x)}

-- Thinning

type Thinning (gamma :: Ctx) (delta :: Ctx) = Env (:|-@) gamma delta

idThinning :: forall gamma. Thinning gamma gamma
idThinning = Env {lookup = \x -> x}

weaken :: forall gamma alpha. Thinning gamma (Cons alpha gamma)
weaken = Env {lookup = S}

select ::
  forall dom1 gamma delta theta.
  Thinning gamma delta ->
  Env dom1 delta theta ->
  Env dom1 gamma theta
select rho gamma = Env {lookup = \x -> lookup gamma (lookup rho x)}

-- Semantics

data Semantics (dom1 :: Ctx -> Typ -> *) (dom2 :: Ctx -> Typ -> *) = Semantics
  { thinnableSemanticsDom ::
      forall gamma delta alpha.
      gamma `dom1` alpha ->
      Thinning gamma delta ->
      delta `dom1` alpha,
    var ::
      forall gamma alpha.
      gamma `dom1` alpha ->
      gamma `dom2` alpha,
    app ::
      forall gamma alpha beta.
      gamma `dom2` (alpha :-> beta) ->
      gamma `dom2` alpha ->
      gamma `dom2` beta,
    lam ::
      forall gamma alpha beta.
      ( forall delta.
        Thinning gamma delta ->
        delta `dom1` alpha ->
        delta `dom2` beta
      ) ->
      gamma `dom2` (alpha :-> beta)
  }

semantics ::
  forall dom1 dom2 gamma delta alpha.
  Semantics dom1 dom2 ->
  Env dom1 gamma delta ->
  gamma :|- alpha ->
  delta `dom2` alpha
semantics sem gamma (Var x) = var sem (lookup gamma x)
semantics sem gamma (App f a) =
  app
    sem
    (semantics sem gamma f)
    (semantics sem gamma a)
semantics sem gamma (Lam b) =
  lam
    sem
    ( \rho a ->
        semantics
          sem
          (append (mapEnv (\x -> thinnableSemanticsDom sem x rho) gamma) a)
          b
    )

renaming :: Semantics (:|-@) (:|-)
renaming =
  Semantics
    { thinnableSemanticsDom = \a gamma -> lookup gamma a,
      var = Var,
      app = App,
      lam = \b -> Lam (b Env {lookup = S} Z)
    }

substitution :: Semantics (:|-) (:|-)
substitution =
  Semantics
    { thinnableSemanticsDom = \a gamma -> ren gamma a,
      var = id,
      app = App,
      lam = \b -> Lam (b Env {lookup = S} (Var Z))
    }

ren ::
  forall gamma delta alpha.
  Thinning gamma delta ->
  gamma :|- alpha ->
  delta :|- alpha
ren = semantics renaming

sub ::
  forall gamma delta alpha.
  Env (:|-) gamma delta ->
  gamma :|- alpha ->
  delta :|- alpha
sub = semantics substitution

-- Wrapping

newtype Wrap (a :: *) (gamma :: Ctx) (alpha :: Typ) = Wrap {unWrap :: a}

mapWrap ::
  forall a b gamma alpha.
  (a -> b) ->
  Wrap a gamma alpha ->
  Wrap b gamma alpha
mapWrap f w = Wrap (f (unWrap w))
