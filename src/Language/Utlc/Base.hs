{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Utlc.Base where

import Prelude hiding (lookup, print)

-- Nat

data Nat = Zero | Suc Nat deriving (Eq, Ord, Show)

-- Var

data Var :: Nat -> * where
  Z :: Var (Suc n)
  S :: Var n -> Var (Suc n)

deriving instance Show (Var n)

-- Utlc

data Trm :: Nat -> * where
  Var :: forall n. Var n -> Trm n
  App :: forall n. Trm n -> Trm n -> Trm n
  Lam :: forall n. Trm (Suc n) -> Trm n

deriving instance Show (Trm n)

-- Env

data Env (dom1 :: Nat -> *) (m :: Nat) (n :: Nat) = Env
  {lookup :: Var m -> dom1 n}

epsilon ::
  forall dom1 n.
  Env dom1 Zero n
epsilon = Env {lookup}
  where
    lookup :: Var Zero -> dom1 n
    lookup = \case

append ::
  forall dom1 m n.
  Env dom1 m n ->
  dom1 n ->
  Env dom1 (Suc m) n
append gamma a = Env {lookup = lookup'}
  where
    lookup' :: Var (Suc m) -> dom1 n
    lookup' Z = a
    lookup' (S x) = lookup gamma x

mapEnv ::
  forall dom1 dom2 l m n.
  (dom1 m -> dom2 n) ->
  Env dom1 l m ->
  Env dom2 l n
mapEnv f gamma = Env {lookup = lookup'}
  where
    lookup' :: Var l -> dom2 n
    lookup' x = f (lookup gamma x)

-- Thinning

type Thinning (m :: Nat) (n :: Nat) = Env Var m n

idThinning :: Thinning n n
idThinning = Env {lookup = \x -> x}

weaken :: Thinning n (Suc n)
weaken = Env {lookup = S}

select ::
  forall dom1 l m n.
  Thinning l m ->
  Env dom1 m n ->
  Env dom1 l n
select rho gamma = Env {lookup = lookup'}
  where
    lookup' :: Var l -> dom1 n
    lookup' x = lookup gamma (lookup rho x)

type Box (dom1 :: Nat -> *) (m :: Nat) (n :: Nat) = Thinning m n -> dom1 n

type Thinnable (dom1 :: Nat -> *) (m :: Nat) (n :: Nat) =
  dom1 m -> Box dom1 m n

extract :: Box dom1 n n -> dom1 n
extract a = a idThinning

-- duplicate ::
--   forall dom1 dom2 m n.
--   (Thinning m n -> dom1 n) ->
--   -- Thinning m n ->
--   Thinning m n ->
--   Thinning m n ->
--   dom1 n
-- duplicate a rho gamma = a (select rho gamma)

-- undefined -- a (select rho alpha)

-- thinnableBox ::
--   (Thinning m n -> dom1 n) ->
--   Thinning m n ->
--   Thinning m n ->
--   dom1 n
-- thinnableBox = duplicate

-- Semantics

data Semantics (dom1 :: Nat -> *) (dom2 :: Nat -> *) = Semantics
  { thinnableSemanticsDom :: forall m n. dom1 m -> Thinning m n -> dom1 n,
    var :: forall n. dom1 n -> dom2 n,
    app :: forall n. dom2 n -> dom2 n -> dom2 n,
    lam :: forall n. (forall m. Thinning n m -> dom1 m -> dom2 m) -> dom2 n
  }

semantics ::
  forall dom1 dom2 m n.
  Semantics dom1 dom2 ->
  Env dom1 m n ->
  Trm m ->
  dom2 n
semantics sem gamma (Var x) = var sem (lookup gamma x)
semantics sem gamma (App f a) =
  app
    sem
    (semantics sem gamma f)
    (semantics sem gamma a)
semantics sem gamma (Lam b) =
  lam
    sem
    ( \delta a ->
        semantics
          sem
          (append (mapEnv (\x -> thinnableSemanticsDom sem x delta) gamma) a)
          b
    )

renaming :: Semantics Var Trm
renaming =
  Semantics
    { thinnableSemanticsDom = \a gamma -> lookup gamma a,
      var = Var,
      app = App,
      lam = \b -> Lam (b Env {lookup = S} Z)
    }

substitution :: Semantics Trm Trm
substitution =
  Semantics
    { thinnableSemanticsDom = \a gamma -> ren gamma a,
      var = id,
      app = App,
      lam = \b -> Lam (b Env {lookup = S} (Var Z))
    }

ren :: Thinning m n -> Trm m -> Trm n
ren = semantics renaming

sub :: Env Trm m n -> Trm m -> Trm n
sub = semantics substitution

-- Wrapping

newtype Wrap (a :: *) (n :: Nat) = Wrap {unWrap :: a}

mapWrap :: (a -> b) -> Wrap a n -> Wrap b n
mapWrap f w = Wrap (f (unWrap w))
