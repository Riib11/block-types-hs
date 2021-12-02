{-# LANGUAGE LambdaCase, BlockArguments #-}

module Language.BlockTypes.Normalization where

import Language.BlockTypes.Semantics as Sem
import Language.BlockTypes.Syntax as Syn
import Data.Map as Map

normalize :: SubSem -> Syn -> Syn -> Syn
normalize sigma alpha a = reify (evaluate sigma alpha) (evaluate sigma a)

evaluate :: SubSem -> Syn -> Sem
evaluate sigma = \case
  Uni -> Syn Uni
  Pi x alpha beta -> PiSem x (evaluate sigma alpha) \a -> evaluate (Map.insert x a sigma) beta
  Lam x alpha b -> LamSem x (evaluate sigma alpha) \a -> evaluate (Map.insert x a sigma) b
  Var x -> Syn $ Var x
  App f a -> 
    let f' = evaluate sigma f in
    let a' = evaluate sigma a in
    case f' of 
      PiSem x alpha beta -> beta a'
      LamSem x alpha b -> b a'
  Let x alpha a b -> evaluate (Map.insert x (evaluate sigma a) sigma) b
  Hole h alpha sigma -> Syn $ Hole h alpha sigma

reflect :: Sem -> Syn -> Sem
reflect = \case
  Syn Uni -> Syn
  Syn (Var x) -> Syn
  Syn (App f a) -> Syn
  Syn (Hole h alpha sigma) -> Syn
  PiSem x alpha beta -> \case
    b@(App _ _) -> LamSem x alpha \a -> reflect (beta a) (App b . reify alpha $ a)
    b@(Var _) -> LamSem x alpha \a -> reflect (beta a) (App b . reify alpha $ a)

reify :: Sem -> Sem -> Syn
reify = \case
  Syn Uni -> \case
    Syn Uni -> Uni
    Syn (App f a) -> App f a
    Syn (Var x) -> Var x 
    Syn (Hole h alpha sigma) -> Hole h alpha sigma
    PiSem x alpha beta -> Pi x (reify (Syn Uni) alpha) (reify (Syn Uni) (beta (reflect alpha (Var x))))
  Syn (Var x) -> \case Syn a -> a
  Syn (App f a) -> \case Syn a -> a
  Syn (Hole h alpha sigma) -> \case Syn a -> a
  PiSem x alpha beta -> \case
    LamSem _ _ b -> Lam x (reify (Syn Uni) alpha) (reify (beta (reflect alpha (Var x))) (b (reflect alpha (Var x))))
