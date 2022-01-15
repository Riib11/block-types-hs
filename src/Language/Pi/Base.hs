{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module Language.Pi.Base where

import Prelude hiding (lookup, pi)

-- Ctx

data Ctx
  = Nil
  | Cons Trm Ctx
  deriving (Show)

pushCtx :: Trm -> Ctx -> Ctx
pushCtx = Cons

popCtx :: Ctx -> Ctx
popCtx (Cons _ gamma) = gamma

-- Var

data Var
  = Z
  | S Var
  deriving (Show)

lookupCtx :: Var -> Ctx -> Trm
lookupCtx Z (Cons a _) = a
lookupCtx (S x) (Cons a gamma) = lookupCtx x gamma

-- Trm

data Trm
  = Uni
  | Var Var
  | Pi Trm Trm
  | Lam Trm Trm
  | App Trm Trm
  deriving (Show)

-- Env

data Env dom = Env {lookup :: Var -> dom}

epsilon :: Env dom
epsilon = Env {lookup = \_ -> error "Attempted to lookup in epsilon."}

append :: dom -> Env dom -> Env dom
append a gamma = Env {lookup = \case Z -> a; (S x) -> lookup gamma x}

mapEnv :: (dom1 -> dom2) -> Env dom1 -> Env dom2
mapEnv f gamma = Env {lookup = \x -> f (lookup gamma x)}

subEnv :: Trm -> Env Trm
subEnv a = Env {lookup = \case Z -> a; (S x) -> Var x}

-- Thinning

type Thinning = Env Var

idThinning :: Thinning
idThinning = Env {lookup = \x -> x}

weaken :: Thinning
weaken = Env {lookup = S}

select :: Thinning -> Env dom -> Env dom
select rho gamma = Env {lookup = \x -> lookup gamma (lookup rho x)}

step :: Thinning -> Thinning
step inc = select inc weaken

-- Thinnable

type Thinnable dom = Thinning -> dom -> dom

thinnableVar :: Thinnable Var
thinnableVar inc x = lookup inc x

-- Semantics

data Semantics dom1 dom2 = Semantics
  { thinnable :: Thinnable dom1,
    uni :: dom2,
    var :: dom1 -> dom2,
    pi :: dom2 -> (Thinning -> dom1 -> dom2) -> dom2,
    lam :: dom2 -> (Thinning -> dom1 -> dom2) -> dom2,
    app :: dom2 -> dom2 -> dom2
  }

semantics :: Semantics dom1 dom2 -> Env dom1 -> Trm -> dom2
semantics sem gamma Uni = uni sem
semantics sem gamma (Var x) = var sem (lookup gamma x)
semantics sem gamma (App f a) = app sem f' a'
  where
    f' = semantics sem gamma f
    a' = semantics sem gamma a
semantics sem gamma (Lam alpha b) = lam sem alpha' b'
  where
    alpha' = semantics sem gamma alpha
    b' rho a = semantics sem gamma' b
      where
        gamma' = append a (mapEnv (\x -> thinnable sem rho x) gamma)
semantics sem gamma (Pi alpha beta) = pi sem alpha' beta'
  where
    alpha' = semantics sem gamma alpha
    beta' rho a = semantics sem gamma' beta
      where
        gamma' = append a (mapEnv (\x -> thinnable sem rho x) gamma)

-- Renaming

renaming :: Semantics Var Trm
renaming =
  Semantics
    { thinnable = \rho a -> lookup rho a,
      uni = Uni,
      var = Var,
      pi = \alpha beta -> Pi alpha (beta weaken Z),
      lam = \alpha b -> Lam alpha (b weaken Z),
      app = App
    }

ren :: Thinning -> Trm -> Trm
ren = semantics renaming

thinnableTrm :: Thinnable Trm
thinnableTrm = ren

-- Substitution

substitution :: Semantics Trm Trm
substitution =
  Semantics
    { thinnable = \rho a -> ren rho a,
      uni = Uni,
      var = id,
      pi = \alpha beta -> Pi alpha (beta weaken (Var Z)),
      lam = \alpha b -> Lam alpha (b weaken (Var Z)),
      app = App
    }

sub :: Env Trm -> Trm -> Trm
sub = semantics substitution
