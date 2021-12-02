{-# LANGUAGE BlockArguments, LambdaCase, OverloadedRecordDot #-}

module Language.BlockTypes.Unification where

import Language.BlockTypes.Syntax as Syntax
import Language.BlockTypes.Shallow as Shallow
import Language.BlockTypes.Normalization as Normalization
import qualified Language.BlockTypes.Inference as Inference 
import qualified Language.BlockTypes.Substitution as Substitution
import Control.Monad as Moand
import Control.Monad.Trans as Trans 
import Control.Monad.Except as Except
import Control.Monad.State as State
import qualified Data.Map as Map
import Prelude hiding (lookup)

-- |
-- == Types

type UnifyException = (ShaNrm, ShaNrm)
type UnifyState = Fill 

type Unify = StateT UnifyState (Except UnifyException)

runUnify :: Unify a -> Either UnifyException (a, UnifyState)
runUnify = runExcept . flip runStateT mempty

-- |
-- == Unify

-- TODO: change to ShaCtx -> Sha -> Sha -> Unify ()
-- TODO: only have to normalize when checking types -- in the Hole case, but not the lambda case
unify :: ShaCtx -> ShaNrm -> ShaNrm -> Unify ()
unify gamma a a' = do
  fill <- get
  case (a fill, a' fill) of
    (UniShaNrm, UniShaNrm) -> do
      return ()
    (PiShaNrm x alpha beta, PiShaNrm x' alpha' beta') -> do
      unify gamma alpha alpha'
      unify (Map.insert x (fromShaNrmToSha alpha) gamma) beta beta'
    (LamShaNrm x alpha b, LamShaNrm x' alpha' b') -> do
      unify gamma alpha alpha'
      unify (Map.insert x (fromShaNrmToSha alpha) gamma) b b'
    (NeuShaNrm n, NeuShaNrm n') -> do
      unifyNeu gamma n n'
    (HoleShaNrm h alpha sigma, HoleShaNrm h' alpha' sigma') ->
      undefined
      -- if fromShaCtx fill sigma == fromShaCtx fill sigma' then
      --   undefined
      -- else
      --   undefined
    (HoleShaNrm h alpha sigma, _) -> do
      let alpha' = Inference.infer (fromShaCtx fill gamma) (toSyn . fromShaNrm fill $ a')
      unify gamma (alpha) alpha'
      modify $ Map.insert h FillItem{fillType = alpha, fillVal = fromShaNrmToSha a'}
    _ -> throwError (a, a')

unifyNeu :: ShaCtx -> ShaNeu -> ShaNeu -> Unify ()
unifyNeu gamma n n' = do
  fill <- get
  case (n fill, n' fill) of
    (VarShaNeu x, VarShaNeu x') -> do
      unless (x == x') $
        throwError (const (NeuShaNrm n), const (NeuShaNrm n'))
    (AppShaNeu n a, AppShaNeu n' a') -> do
      unifyNeu gamma n n'
      unify gamma a a'
