{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Pi.Inference where

import Control.Monad.State as State
import Language.Pi.Base
import Language.Pi.Printing
import Prelude hiding (lookup, pi, print)

type Inference = State Ctx (Trm, Trm)

inferVar :: Var -> Inference
inferVar x = (Var x,) <$> (lookupCtx x <$> get)

inference :: Semantics Var Inference
inference =
  Semantics
    { thinnable = \x rho -> x,
      uni = return (Uni, Uni),
      var = inferVar,
      pi = \malpha mbeta -> do
        (alpha, alphaT) <- malpha
        modify $ pushCtx alphaT
        (beta, _) <- mbeta weaken Z
        modify $ popCtx
        return (Pi alpha beta, Uni),
      lam = \malpha mb -> do
        (alpha, _) <- malpha
        modify $ pushCtx alpha
        (b, beta) <- mb weaken Z
        modify $ popCtx
        return (Lam alpha b, Pi alpha beta),
      app = \mf ma -> do
        (f, phi) <- mf
        (a, alpha) <- ma
        case phi of
          Pi _ beta -> return (App f a, sub (subEnv a) beta)
          _ -> error $ "Attempted to infer type of badly-type application, with applicant type " ++ show phi ++ "."
    }

{-
infer epsilon $ Lam Uni (Lam Uni (Lam (Pi (Var (S Z)) (Var (S Z))) (Lam (Var (S (S Z))) (App (Var (S Z)) (Var Z)))))
==>
Pi Uni (Pi (Var Z) (Var Z))
-}

infer :: Thinning -> Trm -> Inference
infer = semantics inference

-- flip runState Nil $ infer epsilon $ Lam Uni (Lam (Var Z) (Var (S Z)))
