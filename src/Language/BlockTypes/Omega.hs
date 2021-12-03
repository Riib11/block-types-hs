{-# LANGUAGE LambdaCase, BlockArguments #-}
module Language.BlockTypes.Omega where 

{-
ASSUMPTIONS
- unique variable names
-}

import Data.Map as Map

-- |
-- == Syntax

data Syn
  = Uni
  | Pi VarId Syn Syn
  | Lam VarId Syn Syn
  | App Syn Syn
  | Var VarId
  | Hole HoleId Sub
  | Let VarId Syn Syn Syn
  deriving (Eq, Show)

type VarId = String
type HoleId = Int

type Ctx = Map VarId (Syn, Maybe Syn) -- var => type, value?
type HoleCtx = Map HoleId Syn -- hole => type

type Sub = Map VarId Syn -- var => value
type HoleSub = Map HoleId Syn -- hole => value

-- |
-- == Normalization

-- inputs/output in normal form
-- a [x -> b]
sub :: Syn -> VarId -> Syn -> Syn 
sub a x b = case a of 
  Uni -> Uni 
  Pi y alpha beta -> Pi x (sub alpha x b) (sub beta x b)
  Lam y alpha c -> Lam x (sub alpha x b) (sub c x b)
  App f a -> app (sub f x b) (sub a x b)
  Var y -> if x == y then b else Var y
  Hole h sigma -> Hole h (Map.insert x b sigma)

-- inputs/output in normal form
app :: Syn -> Syn -> Syn
app f a = case f of
  Lam x alpha b -> sub b x a
  App f' a' -> App (App f' a') a
  Var x -> App (Var x) a
  Hole h sigma -> App (Hole h sigma) a

norm :: Syn -> Syn
norm = \case
  Uni -> Uni 
  Pi x alpha beta -> Pi x (norm alpha) (norm beta)
  Lam x alpha b -> Lam x (norm alpha) (norm b)
  App f a -> app (norm f) (norm a)
  Var x -> Var x 
  Hole h sigma -> Hole h sigma
  Let x alpha a b -> sub b x (norm a)

norm_test1 :: Syn
norm_test1 = norm (Let "x" Uni Uni (Var "x"))

norm_test2 :: Syn
norm_test2 = norm (App (Lam "x" Uni (Var "x")) (Var "y"))

-- |
-- == Renaming

-- Rename x to y in a
rename :: VarId -> VarId -> Syn -> Syn
rename x y = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (rename x y alpha) (rename x y beta)
  Lam x alpha b -> Lam x (rename x y alpha) (rename x y b)
  App f a -> App (rename x y f) (rename x y a)
  Var x' -> if x == x' then Var y else Var x'
  Hole h sigma' -> Hole h (renameSub x y sigma')
  Let x alpha a b -> Let x (rename x y alpha) (rename x y a) (rename x y b)

renameSub :: VarId -> VarId -> Sub -> Sub
renameSub x y =
  Map.mapKeys (\x' -> if x == x' then y else x') .
  Map.map (rename x y)

-- |
-- == Substitution

-- Doesn't normalize things..
applySub :: Sub -> Syn -> Syn
applySub sigma = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (applySub sigma alpha) (applySub sigma beta)
  Lam x alpha b -> Lam x (applySub sigma alpha) (applySub sigma b)
  App f a -> App (applySub sigma f) (applySub sigma a)
  Var x -> case sigma !? x of
    Just a -> a
    Nothing -> Var x
  Hole h sigma' -> Hole h (sigma' <> sigma)
  Let x alpha a b -> Let x (applySub sigma alpha) (applySub sigma a) (applySub sigma b)

applyHoleSub :: HoleSub -> Syn -> Syn 
applyHoleSub sigma = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (applyHoleSub sigma alpha) (applyHoleSub sigma beta)
  Lam x alpha b -> Lam x (applyHoleSub sigma alpha) (applyHoleSub sigma b)
  App f a -> App (applyHoleSub sigma f) (applyHoleSub sigma a)
  Var x -> Var x
  Hole h sigma' -> case sigma !? h of 
    Just a -> applySub sigma' a
    Nothing -> Hole h sigma'

applyHoleSubToHoleCtx :: HoleSub -> HoleCtx -> HoleCtx
applyHoleSubToHoleCtx sigma gamma = 
  Map.map (applyHoleSub sigma) $
  Prelude.foldl (flip Map.delete) gamma (Map.keys sigma)

applyHoleSubToCtx :: HoleSub -> Ctx -> Ctx
applyHoleSubToCtx sigma g = Map.map (\(alpha, mb_a) -> (applyHoleSub sigma alpha, applyHoleSub sigma <$> mb_a)) g

-- None of the keys in sigma1 appear in the keys or values of sigma2
joinHoleSub :: HoleSub -> HoleSub -> HoleSub
joinHoleSub sigma2 sigma1 = Map.map (applyHoleSub sigma2) sigma1 <> sigma2

-- |
-- == Unification

unify :: HoleCtx -> Ctx -> Syn -> Syn -> Maybe HoleSub
unify gamma g a a' = case (a, a') of 
  (Uni, Uni) -> Just mempty
  (Pi x alpha beta, Pi x' alpha' beta') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify gamma (Map.insert x (applyHoleSub sigma1 alpha, Nothing) g) beta (rename x' x beta')
    return $ sigma1 `joinHoleSub` sigma2
  (Lam x alpha b, Lam x' alpha' b') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify gamma (Map.insert x (applyHoleSub sigma1 alpha, Nothing) g) b (rename x' x b')
    return $ sigma1 `joinHoleSub` sigma2
  (App f a, App f' a') -> do
    sigma1 <- unify gamma g f f'
    sigma2 <- unify gamma g a a'
    return $ sigma1 `joinHoleSub` sigma2
  (Var x, Var x') ->
    if x == x' then Just mempty else Nothing
  (Let x alpha a b, Let x' alpha' a' b') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify (applyHoleSubToHoleCtx sigma1 gamma) (applyHoleSubToCtx sigma1 g) (applyHoleSub sigma1 a) (applyHoleSub sigma1 a')
    sigma3 <- unify (applyHoleSubToHoleCtx (sigma2 `joinHoleSub` sigma1) gamma) (applyHoleSubToCtx (sigma2 `joinHoleSub` sigma1) g)  (applyHoleSub (sigma2 `joinHoleSub` sigma1) b) (applyHoleSub (sigma2 `joinHoleSub` sigma1) (rename x' x b'))
    return $ sigma1 `joinHoleSub` sigma2 `joinHoleSub` sigma3
  (Hole h sigma, a') | Map.null sigma -> Just $ Map.singleton h a'
  (a, Hole h' sigma') | Map.null sigma' -> Just $ Map.singleton h' a
  _ -> Nothing
  
  -- |
  -- == Inference

-- Returns a type in normal form
infer :: HoleCtx -> Ctx -> Syn -> Syn
infer gamma g = \case
  Uni -> Uni
  Pi x alpha beta -> Uni
  Lam x alpha b -> Pi x alpha (infer gamma (Map.insert x (alpha, Nothing) g) b)
  App f a -> case infer gamma g f of Pi x alpha beta -> sub beta x (norm a)
  Var x -> norm (fst (g ! x))
  Hole h sigma -> norm $ gamma ! h
  Let x alpha a b -> infer gamma (Map.insert x (alpha, Just a) g) b

-- |
-- == Fixity

data Fix = FixTerm | FixType | Free deriving (Eq, Show)

inferFix :: HoleCtx -> Syn -> Syn -> Fix
inferFix = undefined -- TODO

-- |
-- == Rewriting

data Rewrite = Rewrite HoleCtx Fix Syn Syn

-- TODO: infer fixity of a subterm
-- TODO: find what rewrite rules can be applied to each subterm
-- TODO: generate by applying random available rewrite rule to random subterm
-- TODO: write some test but actually yes
