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

data Var :: Typ -> Ctx -> * where
  Z :: forall alpha. Var alpha (Cons alpha Nil)
  S :: forall alpha beta gamma. Var alpha gamma -> Var alpha (Cons beta gamma)

deriving instance Show (Var alpha gamma)

-- Utlc

data Trm :: Typ -> Ctx -> * where
  Var :: forall alpha gamma. Var alpha gamma -> Trm alpha gamma
  App :: forall alpha beta gamma. Trm (alpha :-> beta) gamma -> Trm alpha gamma -> Trm beta gamma
  Lam :: forall alpha beta gamma. Trm beta (Cons alpha gamma) -> Trm (alpha :-> beta) gamma

deriving instance Show (Trm alpha gamma)

-- Env

data Env (dom :: Typ -> Ctx -> *) (gamma :: Ctx) (delta :: Ctx) = Env
  {lookup :: forall alpha. Var alpha gamma -> dom alpha delta}

epsilon ::
  forall dom gamma.
  Env dom Nil gamma
epsilon = Env {lookup}
  where
    lookup :: forall (alpha :: Typ). Var alpha Nil -> dom alpha gamma
    lookup = \case

append ::
  forall dom alpha gamma delta.
  Env dom gamma delta ->
  dom alpha delta ->
  Env dom (Cons alpha gamma) delta
append gamma a = Env {lookup = lookup'}
  where
    -- lookup' :: Var beta (Cons mu gamma) -> dom beta delta
    lookup' :: forall beta. Var beta (Cons alpha gamma) -> dom beta delta
    lookup' Z = a
    lookup' (S x) = lookup gamma x

mapEnv ::
  forall dom1 dom2 gamma delta theta.
  (forall alpha. dom1 alpha delta -> dom2 alpha theta) ->
  Env dom1 gamma delta ->
  Env dom2 gamma theta
mapEnv f gamma = Env {lookup = lookup'}
  where
    lookup' :: forall beta. Var beta gamma -> dom2 beta theta
    lookup' x = f (lookup gamma x)

-- Thinning

type Thinning (gamma :: Ctx) (delta :: Ctx) = Env Var gamma delta

idThinning :: forall gamma. Thinning gamma gamma
idThinning = Env {lookup = \x -> x}

weaken :: forall gamma alpha. Thinning gamma (Cons alpha gamma)
weaken = Env {lookup = S}

select ::
  forall dom1 gamma delta theta.
  Thinning gamma delta ->
  Env dom1 delta theta ->
  Env dom1 gamma theta
select rho gamma = Env {lookup = lookup'}
  where
    lookup' :: forall alpha. Var alpha gamma -> dom1 alpha theta
    lookup' x = lookup gamma (lookup rho x)

-- Semantics

-- data Semantics (dom1 :: Var -> Ctx -> *) (dom2 :: Var -> Ctx -> *) = Semantics
--   { thinnableSemanticsDom :: forall gamma delta alpha. dom1 alpha gamma -> Thinning gamma delta -> dom1 delta,
--     var :: forall n. dom1 n -> dom2 n,
--     app :: forall n. dom2 n -> dom2 n -> dom2 n,
--     lam :: forall n. (forall m. Thinning n m -> dom1 m -> dom2 m) -> dom2 n
--   }

-- semantics ::
--   forall dom1 dom2 m n.
--   Semantics dom1 dom2 ->
--   Env dom1 m n ->
--   Trm m ->
--   dom2 n
-- semantics sem gamma (Var x) = var sem (lookup gamma x)
-- semantics sem gamma (App f a) =
--   app
--     sem
--     (semantics sem gamma f)
--     (semantics sem gamma a)
-- semantics sem gamma (Lam b) =
--   lam
--     sem
--     ( \delta a ->
--         semantics
--           sem
--           (append (mapEnv (\x -> thinnableSemanticsDom sem x delta) gamma) a)
--           b
--     )

-- renaming :: Semantics Var Trm
-- renaming =
--   Semantics
--     { thinnableSemanticsDom = \a gamma -> lookup gamma a,
--       var = Var,
--       app = App,
--       lam = \b -> Lam (b Env {lookup = S} Z)
--     }

-- substitution :: Semantics Trm Trm
-- substitution =
--   Semantics
--     { thinnableSemanticsDom = \a gamma -> ren gamma a,
--       var = id,
--       app = App,
--       lam = \b -> Lam (b Env {lookup = S} (Var Z))
--     }

-- ren :: Thinning m n -> Trm m -> Trm n
-- ren = semantics renaming

-- sub :: Env Trm m n -> Trm m -> Trm n
-- sub = semantics substitution

-- -- Wrapping

-- newtype Wrap (a :: *) (n :: Nat) = Wrap {unWrap :: a}

-- mapWrap :: (a -> b) -> Wrap a n -> Wrap b n
-- mapWrap f w = Wrap (f (unWrap w))
