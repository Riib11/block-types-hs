{-# LANGUAGE LambdaCase, BlockArguments, OverloadedRecordDot, UndecidableInstances, NamedFieldPuns, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveTraversable, GeneralizedNewtypeDeriving, DuplicateRecordFields #-}
module Language.BlockTypes.Base where 

{-

ASSUMPTIONS
- unique variable names

-}

import qualified System.IO.Unsafe as Unsafe
import qualified System.Random as Random
import Control.Monad as Monad
import Control.Monad.State.Strict as State
import Control.Monad.Except as Except
import Control.Monad.Trans as Trans
import Data.Maybe as Maybe
import Data.Either as Either
import qualified Data.Map as Map
import qualified Data.List as List
import Prelude hiding (lookup)

-- |
-- == Term

data Prgm = Prgm { aTop :: Term, gammaTop :: HoleCtx } deriving (Show)

data Term
  = Uni
  | Pi VarId Term Term
  | Lam VarId Term Term
  | App Term Term
  | Var VarId
  | Hole HoleId VarSub VarWkn
  | Let VarId Term Term Term
  deriving (Eq)

data TermIx
  = Here
  | Pi_alpha TermIx | Pi_beta TermIx
  | Lam_alpha TermIx | Lam_b TermIx
  | App_f TermIx | App_a TermIx
  | Let_alpha TermIx | Let_a TermIx | Let_b TermIx
  deriving (Show)

type VarWkn = [VarId]

newtype VarId = VarId Int deriving (Eq, Ord, Num) -- x
newtype HoleId = HoleId Int deriving (Eq, Ord, Num) -- h

instance Show Term where
  show = \case
    Uni -> "U"
    Pi x alpha beta -> "(Π " ++ show x ++ " : " ++ show alpha ++ " . " ++ show beta ++ ")"
    Lam x alpha b -> "(λ " ++ show x ++ " : " ++ show alpha ++ " . " ++ show b ++ ")"
    App f a -> "(" ++ show f ++ " " ++ show a ++ ")"
    Var x -> show x
    Hole h s w -> show h ++ (if s == mempty then "" else show s) ++ (if w == mempty then "" else show w)
    Let x alpha a b -> "(let " ++ show x ++ " : " ++ show alpha ++ " = " ++ show a ++ " in " ++ show b ++ ")"

alphabet = [[c] | c <- ['a'..'z']]

instance Show VarId where
  show (VarId i) = "#" ++ show i 
  -- show (VarId i)
  --   | i < length alphabet = alphabet!!i
  --   | otherwise = alphabet!!(i `mod` length alphabet) ++ show (i `div` length alphabet)

instance Show HoleId where
  show (HoleId i) = "?" ++ show i

getSubterm :: Term -> TermIx -> Term
getSubterm a ix = case (a, ix) of
  (Pi x alpha beta, Pi_alpha ix) -> getSubterm alpha ix
  (Pi x alpha beta, Pi_beta ix) -> getSubterm beta ix
  (Lam x alpha b, Lam_alpha ix) -> getSubterm alpha ix
  (Lam x alpha b, Lam_b ix) -> getSubterm b ix
  (App f a, App_f ix) -> getSubterm f ix
  (App f a, App_a ix) -> getSubterm a ix
  (Let x alpha a b, Let_alpha ix) -> getSubterm alpha ix
  (Let x alpha a b, Let_a ix) -> getSubterm a ix 
  (Let x alpha a b, Let_b ix) -> getSubterm b ix 
  (a, Here) -> a

replaceSubterm :: Term -> TermIx -> Term -> Term
replaceSubterm a ix a' = case (a, ix) of
  (Pi x alpha beta, Pi_alpha ix) -> Pi x (replaceSubterm alpha ix a') beta
  (Pi x alpha beta, Pi_beta ix) -> Pi x alpha (replaceSubterm beta ix a')
  (Lam x alpha b, Lam_alpha ix) -> Lam x (replaceSubterm alpha ix a') b
  (Lam x alpha b, Lam_b ix) -> Lam x alpha (replaceSubterm b ix a')
  (App f a, App_f ix) -> App (replaceSubterm f ix a') a
  (App f a, App_a ix) -> App f (replaceSubterm a ix a')
  (Let x alpha a b, Let_alpha ix) -> Let x (replaceSubterm alpha ix a') a b
  (Let x alpha a b, Let_a ix) -> Let x alpha (replaceSubterm a ix a') b
  (Let x alpha a b, Let_b ix) -> Let x alpha a (replaceSubterm b ix a')
  (a, Here) -> a'

-- |
-- === Ctx

type VarCtx = Ctx VarId VarCtxItem -- g :: var |-> type, value?
data VarCtxItem = VarCtxItem { typ :: Term, val :: Maybe Term }

type HoleCtx = Ctx HoleId Term -- gamma :: hole => type

newtype Ctx k v = Ctx [(k, v)]
  deriving (Eq, Semigroup, Monoid, Functor, Foldable, Traversable)

instance Show VarCtxItem where
  show item = show item.typ ++ case item.val of Nothing -> ""; Just a -> " = " ++ show a

instance Ord k => Indexable (Ctx k v) k v where
  index k (Ctx ctx) = Maybe.fromJust $ List.lookup k ctx

instance Ord k => Lookupable (Ctx k v) k v where
  lookup k (Ctx ctx) = List.lookup k ctx

instance Ord k => Insertable (Ctx k v) k v where
  insert k v (Ctx ctx) = Ctx $ (k, v) : ctx

instance Ord k => Deletable (Ctx k v) k where
  delete k (Ctx ctx) = Ctx $ deleteAssoc k ctx 

deleteAssoc :: Eq k => k -> [(k, v)] -> [(k, v)]
deleteAssoc k ls = List.deleteBy (\(k1, _) (k2, _) -> k1 == k2) (k, undefined) ls

instance (Show k, Show v) => Show (Ctx k v) where
  show (Ctx ctx) =
    "{" ++
    ( List.intercalate ", " .
      List.map (\(k, v) -> show k ++ " : " ++ show v)
    $ ctx )
    ++ "}"

-- |
-- === Sub

type VarSub = Sub VarId Term
type HoleSub = Sub HoleId Term

newtype Sub k v = Sub (Map.Map k v)
  deriving (Eq, Functor, Foldable, Traversable)

instance (Ord k, Substitutable k v v) => Semigroup (Sub k v) where
  -- sigma2 after sigma1
  Sub sigma2 <> Sub sigma1 =
    case fmap (substitute (Sub sigma2)) (Sub sigma1) of
      Sub sigma1 -> Sub (sigma2 <> sigma1)

instance (Ord k, Substitutable k v v) => Monoid (Sub k v) where
  mempty = Sub mempty

instance Ord k => Lookupable (Sub k v) k v where
  lookup k (Sub sub) = sub Map.!? k

instance Ord k => Insertable (Sub k v) k v where
  insert k v (Sub sub) = Sub $ Map.insert k v sub

instance Ord k => Deletable (Sub k v) k where
  delete k (Sub sub) = Sub $ Map.delete k sub

instance (Show k, Show v) => Show (Sub k v) where
  show (Sub sub) =
    "[" ++
    ( List.intercalate ", " .
      List.map (\(k, v) -> show k ++ " = " ++ show v) .
      Map.toList
    $ sub )
    ++ "]"

-- |
-- === Indexable

class Indexable c k v where
  index :: k -> c -> v

-- |
-- === Lookupable

class Lookupable c k v where
  lookup :: k -> c -> Maybe v

-- |
-- === Insertable

class Insertable c k v where
  insert :: k -> v -> c -> c

-- |
-- === Deletable

class Deletable c k where
  delete :: k -> c -> c

-- |
-- == Normalization

weak :: VarId -> Term -> Term
weak y = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (weak y alpha) (weak y beta)
  Lam x alpha b -> Lam x (weak y alpha) (weak y b)
  App f a -> App (weak y f) (weak y a)
  Var x -> Var x
  Hole h s w -> Hole h (weak y <$> s) (y : w)
  Let x alpha a b -> Let x (weak y alpha) (weak y a) (weak y b)

-- | inputs/output are normal
-- `a [x |-> b]`
sub :: Term -> VarId -> Term -> Term 
sub a x b = case a of 
  Uni -> Uni
  Pi y alpha beta -> Pi y (sub alpha x b) (sub beta x b)
  Lam y alpha c -> Lam y (sub alpha x b) (sub c x (weak y b))
  App f a -> app (sub f x b) (sub a x b)
  Var y -> if x == y then b else Var y
  Hole h s w ->
    if x `elem` w
      then Hole h (insert x b s) (x `List.delete` w)
      else Hole h (insert x b s) w

-- | inputs/output is normal
app :: Term -> Term -> Term
app f a = case f of
  Lam x alpha b -> sub b x a
  App f' a' -> App (App f' a') a
  Var x -> App (Var x) a
  Hole h s w -> App (Hole h s w) a
  _ -> error (show f)

-- | output is normal
norm :: VarCtx -> Term -> Term
norm g = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (norm g alpha) (norm (insert x VarCtxItem{ typ = alpha, val = Nothing } g) beta)
  Lam x alpha b -> Lam x (norm g alpha) (norm (insert x VarCtxItem{ typ = alpha, val = Nothing } g) b)
  App f a -> app (norm g f) (norm g a)
  Var x -> Var x 
    -- -- let (Ctx ctx) = g in
    -- case val (index x g) of
    --   Just a -> Var x -- TODO: need to weaken val by rest of context after x
    --   Nothing -> Var x
  Hole h s w -> Hole h s w
  Let x alpha a b -> sub (norm g' b) x (norm g a)
    where g' = (insert x VarCtxItem{ typ = alpha, val = Just (norm g a) } g)

norm_test1 :: Term
norm_test1 = norm mempty . readTerm $
  "(let #0 : U = U in #0)"

norm_test2 :: Term
norm_test2 = norm
  (Ctx [(1, VarCtxItem{ typ = readTerm "U", val = Nothing })]) . 
  readTerm $
  "((λ #0 : U . #0) #1)"

-- |
-- == Renaming

type RenVar = Ren VarId
type RenHole = Ren HoleId

newtype Ren k = Ren (Map.Map k k)
  deriving (Eq, Semigroup, Monoid)

instance Show k => Show (Ren k) where
  show (Ren ren) = "[" ++ (List.intercalate "," $ (\(x, x') -> show x ++ " -> " ++ show x') <$> Map.toList ren) ++ "]"

instance Ord k => Lookupable (Ren k) k k where
  lookup k (Ren ren) = Map.lookup k ren

class Renamable id a where
  rename :: Ren id -> a -> a

renameSingle :: Renamable id a => id -> id -> a -> a
renameSingle id1 id2 = rename (Ren $ Map.singleton id1 id2)

instance Renamable VarId Term where
  rename ren = \case
    Uni -> Uni
    Pi x alpha beta -> Pi (maybe x id (lookup x ren)) (rename ren alpha) (rename ren beta)
    Lam x alpha b -> Lam (maybe x id (lookup x ren)) (rename ren alpha) (rename ren b)
    App f a -> App (rename ren f) (rename ren a)
    Var x -> Var $ maybe x id (lookup x ren)
    Hole h s w -> Hole h (rename ren s) (rename ren w)
    Let x alpha a b -> Let (maybe x id (lookup x ren)) (rename ren alpha) (rename ren a) (rename ren b)

instance Renamable VarId VarWkn where
  rename (Ren ren) = fmap (\x -> maybe x id (Map.lookup x ren))

instance Renamable VarId VarSub where
  rename ren (Sub sub) =
    Sub .
    Map.mapKeys (\x -> maybe x id (lookup x ren)) .
    Map.map (rename ren)
    $ sub

instance Renamable VarId HoleCtx where
  rename ren gamma = rename ren <$> gamma

instance Renamable VarId VarCtx where
  rename ren (Ctx ctx) = Ctx $ fmap
    (\(x, alpha) -> (maybe x id (lookup x ren), rename ren alpha))
    ctx

instance Renamable VarId VarCtxItem where
  rename ren item = item{ typ = rename ren item.typ
                        , val = rename ren <$> item.val }

instance Renamable HoleId Term where
  rename ren = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (rename ren alpha) (rename ren beta)
    Lam x alpha b -> Lam x (rename ren alpha) (rename ren b)
    App f a -> App (rename ren f) (rename ren a)
    Var x -> Var x
    Hole h s w -> Hole (maybe h id (lookup h ren)) (rename ren s) w
    Let x alpha a b -> Let x (rename ren alpha) (rename ren a) (rename ren b)

instance Renamable HoleId HoleCtx where
  rename ren (Ctx ctx) = Ctx $ fmap
    (\(h, alpha) -> (maybe h id (lookup h ren), rename ren alpha))
    ctx

instance Renamable HoleId VarCtx where
  rename ren g = rename ren <$> g

instance Renamable HoleId VarCtxItem where
  rename ren item = item{ typ = rename ren item.typ 
                        , val = rename ren <$> item.val }

instance Renamable HoleId VarSub where
  rename ren s = rename ren <$> s

-- |
-- == Substitution

class Substitutable k v a where
  substitute :: Sub k v -> a -> a

instance Substitutable VarId Term Term where
  -- | Doesn't normalize things
  substitute s@(Sub sub) = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (substitute s alpha) (substitute s beta)
    Lam x alpha b -> Lam x (substitute s alpha) (substitute s b)
    App f a -> App (substitute s f) (substitute s a)
    Var x -> case lookup x s of
      Just a -> a
      Nothing -> Var x
    Hole h s' w -> Hole h (s' <> s) (foldl (flip List.delete) w (Map.keys sub))
    Let x alpha a b -> Let x (substitute s alpha) (substitute s a) (substitute s b)

instance Substitutable HoleId Term Term where
  substitute sigma = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (substitute sigma alpha) (substitute sigma beta)
    Lam x alpha b -> Lam x (substitute sigma alpha) (substitute sigma b)
    App f a -> App (substitute sigma f) (substitute sigma a)
    Var x -> Var x
    Hole h s w -> case lookup h sigma of 
      Just a -> substitute (substitute sigma s) (substitute sigma a)
      Nothing -> Hole h (substitute sigma s) w
    Let x alpha a b -> Let x (substitute sigma alpha) (substitute sigma a) (substitute sigma b)

instance Substitutable HoleId Term HoleCtx where
  substitute (Sub sub) (Ctx ctx) = Ctx $
    foldl
      (flip deleteAssoc)
      (fmap (fmap (substitute (Sub sub))) ctx)
      (Map.keys sub)

instance Substitutable HoleId Term VarCtx where
  substitute sigma = fmap (\item ->
    VarCtxItem{ typ  = substitute sigma item.typ
              , val = substitute sigma <$> item.val })

instance Substitutable HoleId Term VarSub where
  substitute sigma = fmap (substitute sigma)

-- |
-- == Unification

unify :: HoleCtx -> VarCtx -> Term -> Term -> Maybe HoleSub
-- unify gamma g a a' = (return $! debug $ show a ++ " ~ " ++ show a') >> case (a, a') of 
unify gamma g a a' = case (a, a') of 
  (Uni, Uni) -> return mempty
  (Pi x alpha beta, Pi x' alpha' beta') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify
                (substitute sigma1 gamma)
                (insert x
                  VarCtxItem{typ = substitute sigma1 alpha, val = mzero}
                  (substitute sigma1 g))
                (substitute sigma1 beta)
                (renameSingle x' x (substitute sigma1 beta'))
    return $ sigma2 <> sigma1
  (Lam x alpha b, Lam x' alpha' b') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify
                (substitute sigma1 gamma)
                (insert x
                  VarCtxItem{typ = substitute sigma1 alpha, val = mzero}
                  (substitute sigma1 g))
                (substitute sigma1 b)
                (renameSingle x' x (substitute sigma1 b'))
    return $ sigma2 <> sigma1
  (App f a, App f' a') -> do
    sigma1 <- unify gamma g f f'
    sigma2 <- unify gamma g a a'
    return $ sigma1 <> sigma2
  (Var x, Var x') ->
    if x == x' then return mempty else mzero
  (Let x alpha a b, Let x' alpha' a' b') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify
                (substitute sigma1 gamma)
                (substitute sigma1 g)
                (substitute sigma1 a)
                (substitute sigma1 a')
    sigma3 <- unify
                (substitute (sigma2 <> sigma1) gamma)
                (substitute (sigma2 <> sigma1) g)
                (substitute (sigma2 <> sigma1) b)
                (substitute (sigma2 <> sigma1) (renameSingle x' x b'))
    return $ sigma3 <> sigma2 <> sigma1
  (Hole h s w, a) | not (isHole a) && validHoleFill h s w a -> return $ Sub $ Map.singleton h (substitute s a)
  (a, Hole h s w) | not (isHole a) && validHoleFill h s w a -> return $ Sub $ Map.singleton h (substitute s a)
  (Hole h s w, Hole h' s' w') | h == h' && s == s' -> return mempty
  (Hole h s w, Hole h' s' w') | s == mempty -> return $ Sub $ Map.singleton h (Hole h' s' w)
  (Hole h s w, Hole h' s' w') | s' == mempty -> return $ Sub $ Map.singleton h' (Hole h s w')
  _ -> mzero

validHoleFill :: HoleId -> VarSub -> VarWkn -> Term -> Bool
validHoleFill h s w = \case
  Uni -> True
  Pi x alpha beta -> validHoleFill h s w alpha || validHoleFill h s w beta
  Lam x alpha b -> validHoleFill h s w alpha || validHoleFill h s w b 
  App f a -> validHoleFill h s w f || validHoleFill h s w a
  Var x -> not $ x `elem` w
  Hole h' s' w' -> all (`elem` w) w'
  Let x alpha a b -> validHoleFill h s w alpha || validHoleFill h s w a || validHoleFill h s w b

-- |
-- == Inference

-- | Returns a type in normal form
infer :: HoleCtx -> VarCtx -> Term -> Term
infer gamma g = \case
  Uni -> Uni
  Pi x alpha beta -> Uni
  Lam x alpha b -> Pi x alpha beta where
    beta = infer gamma (insert x VarCtxItem{ typ = alpha , val = mzero} g) b
  App f a -> substitute (Sub $ Map.singleton x beta) (norm g a) where
    Pi x alpha beta = infer gamma g f
  Var x -> 
    norm g (typ $ case (lookup x g) of Just item -> item; Nothing -> error "here!")
    -- norm g (typ (index x g))
  Hole h s w -> norm g (index h gamma)
  Let x alpha a b -> infer gamma beta b where
    beta = insert x VarCtxItem{ typ = alpha, val = Just a } g

-- |
-- == Fixity

-- | free < type < term
-- `fix1 < fix2` implies that `fix1` is "less fixed" than `fix2`.
data Fix = Free | FixType | FixTerm deriving (Eq, Ord, Show)

-- TODO: where do variables get term-fixed?
fixIn :: VarId -> Term -> Fix -> Fix
fixIn x a fix = case a of
  Uni -> Free
  Pi y alpha beta -> maximum [fixIn x alpha fixAlpha, fixIn x beta fixBeta] where
    fixAlpha | fix >= FixTerm = FixTerm
             | fixIn x beta fixBeta >= FixType = FixTerm
             | otherwise = FixType
    fixBeta | fix >= FixTerm = FixTerm
            | otherwise = FixType
  Lam y alpha b -> maximum [fixIn x alpha fixAlpha, fixIn x b fixB] where
    fixAlpha | fix >= FixTerm = FixTerm
             | fixIn x b fixB >= FixType = FixTerm
             | otherwise = FixType
    fixB = fix
  App f a -> maximum [fixIn x f fix, fixIn x a fix]
  Var y -> if x == y then fix else Free
  Hole h s w -> Free
  Let y alpha a b -> maximum [fixIn x alpha fixAlpha, fixIn x a fixA, fixIn x b fixB] where
    fixAlpha | fix >= FixTerm = FixTerm
             | fixIn x b fixB >= FixType = FixTerm
             | otherwise = FixType
    fixA | fixIn x b fixB >= FixTerm = FixTerm
         | fixIn x b fixB >= FixType = FixType
         | fixAlpha >= FixTerm = FixType
         | otherwise = Free
    fixB = fix

isHole :: Term -> Bool
isHole = \case 
  Hole _ _ _ -> True
  _ -> False

-- |
-- == Rewriting

-- | `gamma |- patternIn{maxFix} ~> patternOut{maxFix}`
-- TODO: how to keep track of the local bindings in the contexts of some holes?
data Rewrite = Rewrite
  { gamma :: HoleCtx
  , maxFix :: Fix
  , patternIn :: Term
  , patternOut :: Term }
  deriving (Show)

-- | Makes a rewrite rule in this form:
-- `gamma |- patternIn{fix <= maxFix} ~> patternOut{fix <= maxFix}`
makeRewriteRule :: HoleCtx -> Term -> Term -> Fix -> Rewrite
makeRewriteRule gamma patternIn patternOut maxFix = Rewrite
  { gamma
  , maxFix -- inferMaxFix gamma patternIn patternOut
  , patternIn
  , patternOut }

-- | Infers the maximumity of for the patternIn/patternOut of a rewrite rule.
-- check if patternInType ~ patternOutType unify for type fixedness
-- check if patternIn ~ patternOut unify for term fixedness
inferMaxFix :: HoleCtx -> Term -> Term -> Fix
inferMaxFix gamma patternIn patternOut = FixTerm -- TODO

tryRewriteAt_aux_Here :: Rewrite -> HoleCtx -> VarCtx -> Fix -> Term -> Term -> Gen (Maybe (Term, HoleCtx, RenVar, RenHole, HoleSub))
tryRewriteAt_aux_Here rew gamma g fix aTop a = do
  -- renew holes in rewrite patterns
  rho   <- renewHoles rew.gamma
  gammaRew   <- return $ rename rho rew.gamma
  patternIn  <- return $ rename rho rew.patternIn
  patternOut <- return $ rename rho rew.patternOut
  -- renew variables (in both rewrite patterns and input program)
  r <- renewVars [patternIn, patternOut, aTop]
  gammaRew   <- return $ rename r gammaRew
  patternIn  <- return $ rename r patternIn
  patternOut <- return $ rename r patternOut
  gamma      <- return $ rename r gamma
  g          <- return $ rename r g
  a          <- return $ rename r a
  -- 
  -- lift $ putStrLn $ unlines
  --   [ "rho        = " ++ show rho
  --   , "r          = " ++ show r 
  --   , "gammaRew   = " ++ show gammaRew 
  --   , "patternIn  = " ++ show patternIn
  --   , "patternOut = " ++ show patternOut
  --   , "gamma      = " ++ show gamma
  --   , "g          = " ++ show g
  --   , "a          = " ++ show a ]
  -- 
  return do
    -- check maximum fix
    guard $ fix <= rew.maxFix
    -- unify patternIn's type with target's type
    let patternInType = infer gammaRew mempty patternIn
    let alpha = infer gamma g a
    sigma1 <- unify gammaRew g (norm g patternInType) (norm g alpha)
    -- unify patternIn with target
    sigma2 <- unify (substitute sigma1 (gamma <> gammaRew))
                    (substitute sigma1 g)
                    (substitute sigma1 patternIn)
                    (substitute sigma1 a)
    return (patternOut, gamma <> gammaRew, r, rho, sigma2 <> sigma1)

tryRewriteAt_aux :: Rewrite -> HoleCtx -> VarCtx -> Fix -> Term -> Term -> TermIx -> Gen (Maybe (Term, HoleCtx, RenVar, RenHole, HoleSub))
tryRewriteAt_aux rew gamma g fix aTop a ix = case (a, ix) of
  
  (Pi x alpha beta, Pi_alpha ix) ->
    tryRewriteAt_aux rew gamma g fixAlpha aTop alpha ix where
      fixAlpha | fix >= FixTerm = FixTerm
               | fixIn x beta fixBeta >= FixType = FixTerm
               | otherwise = FixType
      fixBeta | fix >= FixTerm = FixTerm
              | otherwise = FixType
  
  (Pi x alpha beta, Pi_beta ix) ->
    tryRewriteAt_aux rew gamma (insert x VarCtxItem{ typ = alpha, val = Nothing } g) fixBeta aTop beta ix where
      fixAlpha | fix >= FixTerm = FixTerm
               | fixIn x beta fixBeta >= FixType = FixTerm
               | otherwise = FixType
      fixBeta | fix >= FixTerm = FixTerm
              | otherwise = FixType
  
  (Lam x alpha b, Lam_alpha ix) ->
    tryRewriteAt_aux rew gamma g fixAlpha aTop alpha ix where
      fixAlpha | fix >= FixTerm = FixTerm
             | fixIn x b fixB >= FixType = FixTerm
             | otherwise = FixType
      fixB = fix
  
  (Lam x alpha b, Lam_b ix) -> 
    tryRewriteAt_aux rew gamma (insert x VarCtxItem{ typ = alpha, val = Nothing } g) fixB aTop b ix where
      fixAlpha | fix >= FixTerm = FixTerm
             | fixIn x b fixB >= FixType = FixTerm
             | otherwise = FixType
      fixB = fix
  
  (App f a, App_f ix) ->
    tryRewriteAt_aux rew gamma g fix aTop f ix
  
  (App f a, App_a ix) ->
    tryRewriteAt_aux rew gamma g fix aTop a ix
  
  (Let x alpha a b, Let_alpha ix) ->
    tryRewriteAt_aux rew gamma g fixAlpha aTop alpha ix where
      fixAlpha | fix >= FixTerm = FixTerm
               | fixIn x b fixB >= FixType = FixTerm
               | otherwise = FixType
      fixA | fixIn x b fixB >= FixTerm = FixTerm
           | fixIn x b fixB >= FixType = FixType
           | fixAlpha >= FixTerm = FixType
           | otherwise = Free
      fixB = fix
  
  (Let x alpha a b, Let_a ix) -> 
    tryRewriteAt_aux rew gamma g fixA aTop a ix where
      fixAlpha | fix >= FixTerm = FixTerm
               | fixIn x b fixB >= FixType = FixTerm
               | otherwise = FixType
      fixA | fixIn x b fixB >= FixTerm = FixTerm
           | fixIn x b fixB >= FixType = FixType
           | fixAlpha >= FixTerm = FixType
           | otherwise = Free
      fixB = fix
  
  (Let x alpha a b, Let_b ix) ->
    tryRewriteAt_aux rew gamma (insert x VarCtxItem{ typ = alpha, val = Nothing } g) fixB aTop b ix where
      fixAlpha | fix >= FixTerm = FixTerm
               | fixIn x b fixB >= FixType = FixTerm
               | otherwise = FixType
      fixA | fixIn x b fixB >= FixTerm = FixTerm
           | fixIn x b fixB >= FixType = FixType
           | fixAlpha >= FixTerm = FixType
           | otherwise = Free
      fixB = fix
  
  (a, Here) -> tryRewriteAt_aux_Here rew gamma g fix aTop a

tryRewrite :: Rewrite -> TermIx -> Prgm -> Gen (Maybe Prgm)
tryRewrite rew ix prgm =
  tryRewriteAt_aux rew prgm.gammaTop mempty Free prgm.aTop prgm.aTop ix >>= \case
    Just (b, gamma, r, rho, sigma) -> do
      aTop <- return $ rename r prgm.aTop
      aTop <- return $ rename rho aTop
      aTop <- return $ replaceSubterm aTop ix b
      aTop <- return $ substitute sigma aTop
      gammaTop <- return $ substitute sigma gamma
      return $ Just Prgm{ aTop, gammaTop }
    Nothing -> return Nothing

tryRewrites :: [(Rewrite, TermIx)] -> Prgm -> Gen (Maybe Prgm)
tryRewrites rew_ixs prgm = foldM go (Just prgm) rew_ixs where
  go mb_prgm (rew, ix) = case mb_prgm of
    Just prgm -> tryRewrite rew ix prgm
    Nothing -> return Nothing

tryVariable :: VarId -> TermIx -> Prgm -> Gen (Maybe Prgm)
tryVariable x ix prgm = do
  tryVariable_aux x ix prgm.gammaTop mempty prgm.aTop >>= \case
    Just sigma ->
      return $ Just Prgm{ aTop = substitute sigma prgm.aTop
                 , gammaTop = substitute sigma prgm.gammaTop }
    Nothing -> return Nothing

tryVariable_aux :: VarId -> TermIx -> HoleCtx -> VarCtx -> Term -> Gen (Maybe HoleSub)
tryVariable_aux y ix gamma g a = case (a, ix) of
  (Pi x alpha beta, Pi_alpha ix) -> tryVariable_aux y ix gamma g alpha
  (Pi x alpha beta, Pi_beta ix) -> tryVariable_aux y ix gamma (insert x VarCtxItem{ typ = alpha, val = Nothing } g) beta
  (Lam x alpha b, Lam_alpha ix) -> tryVariable_aux y ix gamma g alpha
  (Lam x alpha b, Lam_b ix) -> tryVariable_aux y ix gamma (insert x VarCtxItem{ typ = alpha, val = Nothing } g) b
  (App f a, App_f ix) -> tryVariable_aux y ix gamma g f
  (App f a, App_a ix) -> tryVariable_aux y ix gamma g a
  (Let x alpha a b, Let_alpha ix) -> tryVariable_aux y ix gamma g alpha
  (Let x alpha a b, Let_a ix) -> tryVariable_aux y ix gamma g a
  (Let x alpha a b, Let_b ix) -> tryVariable_aux y ix gamma (insert x VarCtxItem{ typ = alpha, val = Just a } g) b
  (a, Here) ->
    -- if variable is in `g`
    case lookup y g :: Maybe VarCtxItem of
      Just item -> return do
        -- unify `a`'s type with `y`'s type
        return $! debug $ show "hello"
        let aType = infer gamma g a
        let yType = infer gamma g (Var y)
        sigma1 <- unify gamma g (norm g aType) (norm g yType)
        -- unify `a` with `y`
        sigma2 <- unify (substitute sigma1 gamma)
                        (substitute sigma1 g)
                        (substitute sigma1 (Var y))
                        (substitute sigma1 a)
        return (sigma2 <> sigma1)
      Nothing -> return Nothing

rewrite_fill_U, rewrite_fill_Pi, rewrite_fill_lambda, rewrite_eta_reduce, rewrite_beta_reduce, rewrite_swap_parameters, rewrite_dig_parameter, rewrite_wrap_let :: Rewrite

rewrite_fill_U = makeRewriteRule
  (Ctx [ (0, readTerm "U") ])
  (readTerm "?0")
  (readTerm "U")
  FixType

rewrite_fill_Pi = makeRewriteRule
  (Ctx [ (0, readTerm "U")
       , (1, readTerm "U")
       , (2, readTerm "U") ])
  (readTerm "?0")
  (readTerm "(Π #0 : ?1 . ?2)")
  FixType

rewrite_fill_app = makeRewriteRule
  (Ctx [ (0, readTerm "U")
       , (1, readTerm "?0")
       , (2, readTerm "U")
       , (3, readTerm "U")
       , (4, readTerm "U")
       , (5, readTerm "(Π #1 : ?3 . ?4)")
       , (6, readTerm "?3")
       , (7, readTerm "U")
      ,  (8, readTerm "?7") ])
  (readTerm "?1")
  (readTerm "(let #0 : ?2 = (?5 ?6) in ?8)")
  Free

rewrite_fill_lambda = makeRewriteRule
  (Ctx [ (0, readTerm "U")
       , (1, readTerm "?0")
       , (2, readTerm "U")
       , (3, readTerm "U")
       , (4, readTerm "?3") ])
  (readTerm "?1")
  (readTerm "(λ #0 : ?2 . ?4)")
  Free

rewrite_eta_reduce = makeRewriteRule
  (Ctx [ (0, readTerm "U")
        , (1, readTerm "U")
        , (2, readTerm "(Π #0 : ?0 . ?1)")
        , (3, readTerm "?0") ])
  (readTerm "(λ #0 : ?0 . (?2 #0))")
  (readTerm "?2")
  FixTerm

rewrite_beta_reduce = makeRewriteRule
  (Ctx [ (0, readTerm "U")
        , (1, readTerm "U")
        , (2, readTerm "?0")
        , (3, readTerm "?1") ])
  (readTerm "((λ #0 : ?0 . ?2) ?3)")
  (readTerm "?2[#0 = ?3]")
  FixTerm

rewrite_swap_parameters = makeRewriteRule
  (Ctx [ (0, readTerm "U")
       , (1, readTerm "U")
       , (2, readTerm "U")
       , (3, readTerm "?2") ])
  (readTerm "(λ #0 : ?0 . (λ #1 : ?1 . ?3))")
  (readTerm "(λ #2 : ?1 . (λ #3 : ?0 . ?3))")
  Free

rewrite_dig_parameter = makeRewriteRule
  (Ctx [ (0, readTerm "U")
        , (1, readTerm "U")
        , (2, readTerm "?0")
        , (3, readTerm "?1")
        ])
  (readTerm "(λ #0 : ?0 . ?3)")
  (readTerm "?3[?0 = ?2]")
  Free 

rewrite_wrap_let = makeRewriteRule 
  (Ctx [ (0, readTerm "U")
       , (1, readTerm "U")
       , (2, readTerm "?0")
       , (3, readTerm "?1") ])
  (readTerm "?3")
  (readTerm "(let #0 : ?1 = ?2 in ?3)")
  FixTerm

rewrite_unwrap_let = makeRewriteRule
  (Ctx [ (0, readTerm "U")
       , (1, readTerm "U")
       , (2, readTerm "?0")
       , (3, readTerm "?1") ])
  (readTerm "(let #0 : ?1 = ?2 in ?3)")
  (readTerm "?3[#0 = ?2]")
  FixTerm

rewrite_wrap_lambda = makeRewriteRule
  (Ctx [ (0, readTerm "U")
       , (1, readTerm "?0")
       , (2, readTerm "U") ])
  (readTerm "?1")
  (readTerm "(λ #0 : ?2 . ?1[#0])")
  Free

getMaxVarId :: VarId -> Term -> VarId
getMaxVarId varId = \case
  Uni -> varId
  Pi x alpha beta -> maximum [varId, x, getMaxVarId varId alpha, getMaxVarId varId beta]
  Lam x alpha b -> maximum [varId, x, getMaxVarId varId alpha, getMaxVarId varId b]
  App f a -> maximum [varId, getMaxVarId varId f, getMaxVarId varId a]
  Var x -> maximum [varId, x]
  Let x alpha a b -> maximum [varId, x, getMaxVarId varId alpha, getMaxVarId varId a, getMaxVarId varId b]
  Hole _ s w -> maximum (foldl max varId ((getMaxVarId varId <$> s)) : w)

getMaxHoleId :: HoleId -> Term -> HoleId
getMaxHoleId holeId = \case
  Uni -> holeId
  Pi x alpha beta -> maximum [holeId, getMaxHoleId holeId alpha, getMaxHoleId holeId beta]
  Lam x alpha b -> maximum [holeId, getMaxHoleId holeId alpha, getMaxHoleId holeId b]
  App f a -> maximum [holeId, getMaxHoleId holeId f, getMaxHoleId holeId a]
  Var x -> holeId
  Let x alpha a b -> maximum [holeId, getMaxHoleId holeId alpha, getMaxHoleId holeId a, getMaxHoleId holeId b]
  Hole h s w -> foldl max (holeId `max` h) (getMaxHoleId holeId <$> s)

makeGenState :: Prgm -> IO GenState
makeGenState prgm = do
  stdGen <- Random.newStdGen
  return GenState
    { holeId = maximum (0 : fmap fst (case prgm.gammaTop of Ctx ctx -> ctx))
    , varId = getMaxVarId 0 prgm.aTop
    , stdGen }

-- |
-- == Generation

-- |
-- === Gen

type Gen a = StateT GenState IO a

data GenState = GenState
  { holeId :: HoleId
  , varId :: VarId
  , stdGen :: Random.StdGen }
  deriving (Show)

nextHoleId :: Gen HoleId
nextHoleId = do
  h <- gets holeId
  modify $ \st -> st { holeId = h + 1 }
  return (h + 1)

nextVarId :: Gen VarId
nextVarId = do
  x <- gets varId
  modify $ \st -> st { varId = x + 1 }
  return (x + 1)

nextRandR :: Int -> Int -> Gen Int
nextRandR iMin iMax = do
  g <- gets stdGen
  let (i, g') = Random.randomR (iMin, iMax) g
  modify $ \st -> st { stdGen = g' }
  return i

choice :: [a] -> Gen a
choice as = (as !!) <$> nextRandR 0 (length as - 1)

choiceWeighted :: [(Int, a)] -> Gen a
choiceWeighted as = go as 0 <$> nextRandR 0 ((sum . fmap fst $ as) - 1) where
  go :: [(Int, a)] -> Int -> Int -> a
  go ((w, a) : as) acc r = if r < acc + w then a else go as (acc + w) r

-- |
-- === Generating Random Well-Typed Terms

prgmInit :: Prgm
prgmInit = Prgm
  { aTop = readTerm "?1"
  , gammaTop = Ctx [ (0, readTerm "U")
                    , (1, readTerm "?0") ] }

runGenTerm :: IO Term
runGenTerm = do
  genSt <- makeGenState prgmInit
  aTop . fst <$> runStateT (genTerm prgmInit) genSt

genTerm :: Prgm -> Gen Prgm
genTerm prgmInit = fst <$> while c k (prgmInit, 0) where
  c :: (Prgm, Int) -> Gen Bool
  c = return . hasHoles . aTop . fst
  k :: (Prgm, Int) -> Gen (Prgm, Int)
  k (prgm, time) = do
    lift $ print prgm.aTop
    -- choose TermIx `ix`
    ix <- genTermIx prgm.aTop
    -- collect variables `xs` in scope at `ix`
    let g@(Ctx ctx) = getVarCtxAt prgm.aTop ix
    lift $ print g
    -- choose rewrite or variable fill
    let choices =
          [ (time, tryRewrite rewrite_fill_U ix prgm)
          -- , (1, tryRewrite rewrite_fill_Pi ix prgm)
          , (4, tryRewrite rewrite_fill_lambda ix prgm)
          , (8, tryRewrite rewrite_fill_app ix prgm)
          , (4, tryRewrite rewrite_wrap_lambda ix prgm)
          -- , (4, tryRewrite rewrite_unwrap_let ix prgm)
          ] 
          <>
          [ (2 * time, tryVariable x ix prgm) | (x, alpha) <- ctx ]
    update <- choiceWeighted choices
    update >>= \case
      Just prgm -> return (prgm, time + 1)
      Nothing -> k (prgm, time) -- TODO: simple loop?

getVarCtxAt :: Term -> TermIx -> VarCtx
getVarCtxAt a ix = case (a, ix) of
  (Pi x alpha beta, Pi_alpha ix) -> getVarCtxAt alpha ix
  (Pi x alpha beta, Pi_beta ix) -> insert x VarCtxItem{ typ = alpha, val = Nothing } $ getVarCtxAt beta ix
  (Lam x alpha b, Lam_alpha ix) -> getVarCtxAt alpha ix
  (Lam x alpha b, Lam_b ix) -> insert x VarCtxItem{ typ = alpha, val = Nothing } $ getVarCtxAt b ix
  (Let x alpha a b, Let_alpha ix) -> getVarCtxAt alpha ix
  (Let x alpha a b, Let_a ix) -> getVarCtxAt a ix
  (Let x alpha a b, Let_b ix) -> insert x VarCtxItem{ typ = alpha, val = Just a } $ getVarCtxAt b ix
  (App f a, App_f ix) -> getVarCtxAt f ix
  (App f a, App_a ix) -> getVarCtxAt a ix
  (_, Here) -> mempty
  _ -> error $ show (a, ix)

-- weight holes higher
genTermIx :: Term -> Gen TermIx
genTermIx a = choice (getTermIxs a)
    
getTermIxs :: Term -> [TermIx]
getTermIxs = \case
  Uni -> [Here]
  Pi x alpha beta -> [Pi_alpha ix | ix <- getTermIxs alpha] <>
                     [Pi_beta ix | ix <- getTermIxs beta]
  Lam x alpha b -> [Lam_alpha ix | ix <- getTermIxs alpha] <>
                   [Lam_b ix | ix <- getTermIxs b]
  Var x -> [Here]
  App f a -> [App_f ix | ix <- getTermIxs f] <>
             [App_a ix | ix <- getTermIxs a]
  Hole h s w -> replicate 10 Here
  Let x alpha a b -> [Let_alpha ix | ix <- getTermIxs alpha] <>
                     [Let_a ix | ix <- getTermIxs a] <>
                     [Let_b ix | ix <- getTermIxs b]

while :: Monad m => (a -> m Bool) -> (a -> m a) -> a -> m a
while c k a = do
  c a >>= \case 
    True -> while c k =<< k a
    False -> return a

hasHoles :: Term -> Bool
hasHoles = \case
  Uni -> False
  Pi _ alpha beta -> hasHoles alpha || hasHoles beta
  Lam _ alpha b -> hasHoles alpha || hasHoles b
  App f a -> hasHoles f || hasHoles a
  Var _ -> False
  Hole _ _ _ -> True
  Let x alpha a b -> hasHoles alpha || hasHoles a || hasHoles b

-- |
-- === Renewable

renewHoles :: HoleCtx -> Gen RenHole
renewHoles (Ctx ctx) =
  Ren . Map.fromList <$> 
    traverse (\(h, _) -> (h,) <$> nextHoleId) ctx

-- |
-- === RenewableVars

renewVars :: [Term] -> Gen RenVar
renewVars = fmap (Ren . Map.fromList) . foldM (flip go) [] where
  go :: Term -> [(VarId, VarId)] -> Gen [(VarId, VarId)]
  go a ren = case a of
    Uni -> return ren
    Pi x alpha beta -> do x' <- nextVarId
                          go alpha ((x, x') : ren) >>= go beta
    Lam x alpha b -> do x' <- nextVarId
                        go alpha ((x, x') : ren) >>= go b
    App f a -> go f ren >>= go a
    Var x -> return ren
    Hole h s w -> return ren
    Let x alpha a b -> do x' <- nextVarId
                          go alpha ((x, x') : ren) >>= go a >>= go b

-- |
-- == Parsing

readTerm :: String -> Term
readTerm = unsafeEvalParser parseTerm

type Parser a = StateT String (Except String) a

runParser :: Parser a -> String -> Either String (a, String)
runParser p s = runExcept . flip runStateT s $ p

evalParser :: Parser a -> String -> Either String a
evalParser p = fmap fst . runParser p

unsafeEvalParser :: Parser a -> String -> a
unsafeEvalParser p s = case evalParser p s of
  Left msg -> error $ "Parse error when parsing " ++ show s ++ ":\n" ++ msg
  Right a -> a

-- |
-- === Parsing Utilities

parseNextChar :: Parser Char
parseNextChar =
  get >>= \case
    [] -> throwError "Attempted to parseNextChar but found end of input instead."
    (c : cs) -> put cs >> return c

parseChar :: Char -> Parser ()
parseChar c = do
  c' <- parseNextChar
  unless (c == c') $
    throwError $ "Attempted to parseChar " ++ show c ++ " but found the char " ++ show c' ++ " instead."

parsePredicatedChar :: (Char -> Bool) -> Parser Char
parsePredicatedChar p = do
  c <- parseNextChar
  if p c
    then return c
    else throwError $ "Attempted to parsePredicatedChar but found " ++ show c ++ " instead"

parseString :: String -> Parser ()
parseString = mapM_ parseChar

parseWhitespace :: Parser ()
parseWhitespace = do
  -- str0 <- get
  parseTry (parseChar ' ') >>= \case
    Just _ -> parseWhitespace
    Nothing -> return ()

parseNextNonemptyWord :: Parser String
parseNextNonemptyWord = (:) <$> parsePredicatedChar (not . (`elem` separators)) <*> parseNextWord

separators :: [Char]
separators = " (),.:=[]"

parseNextWord :: Parser String
parseNextWord = do
  parseTry (parsePredicatedChar (not . (`elem` separators))) >>= \case
    Just c -> (c :) <$> parseNextWord
    Nothing -> return ""

parseNextInt :: Parser Int
parseNextInt = do
  s <- parseNextWord
  case reads s of
    [(i, "")] -> return i
    _ -> throwError $ "Attempted to parseNextInt but found that word '" ++ s ++ "'"

lexeme :: Parser a -> Parser a
lexeme p = do
  parseWhitespace
  a <- p
  parseWhitespace
  return a

-- | Tries to do a given parser. If the attempts succeeds, then modifies state. Otherwise, resets to the state before attempt.
parseTry :: Parser a -> Parser (Maybe a)
parseTry p = do
  str0 <- get
  case runParser p str0 of
    Left msg -> put str0 >> return Nothing
    Right (a, str1) -> put str1 >> return (Just a)

-- | Tries each parser in list until one succeeds. If none succeed, then returns Nothing.
parseFirstOf :: [Parser a] -> Parser (Maybe a)
parseFirstOf [] = return mzero
parseFirstOf (p : ps) = do
  str0 <- get
  parseTry p >>= \case
    Just a -> return $ Just a
    Nothing -> put str0 >> parseFirstOf ps

-- |
-- === Parsing Term

parseTerm :: Parser Term
parseTerm = do
  mb_a <- parseFirstOf . map lexeme $
    [ parseUni
    , parsePi
    , parseLam
    , parseLet
    , parseApp
    , parseHole
    , parseVar ]
  case mb_a of
    Just a -> return a
    Nothing -> throwError $ "Attempted to parseTerm but failed all cases"

parseUni, parsePi, parseLam, parseApp, parseVar, parseHole, parseLet :: Parser Term

parseUni = do
  lexeme $ parseString "U"
  return $ Uni 

parsePi = do
  lexeme $ parseString "("
  lexeme $ parseString "Π"
  x     <- lexeme $ parseVarId
  lexeme $ parseString ":"
  alpha <- lexeme $ parseTerm
  lexeme $ parseString "."
  beta  <- lexeme $ parseTerm
  lexeme $ parseString ")"
  return $ Pi x alpha beta 

parseLam = do
  lexeme $ parseString "("
  lexeme $ parseString "λ"
  x     <- lexeme $ parseVarId
  lexeme $ parseString ":"
  alpha <- parseTerm
  lexeme $ parseString "."
  b     <- lexeme $ parseTerm
  lexeme $ parseString ")"
  return $ Lam x alpha b 

parseApp = do
  lexeme $ parseString "("
  f     <- lexeme $ parseTerm
  a     <- lexeme $ parseTerm
  lexeme $ parseString ")"
  return $ App f a 

parseVar = do
  x     <- lexeme $ parseVarId
  return $ Var x 

parseLet = do
  lexeme $ parseString "("
  lexeme $ parseString "let"
  x     <- lexeme $ parseVarId
  lexeme $ parseString ":"
  alpha <- parseTerm
  lexeme $ parseString "="
  a     <- lexeme $ parseTerm
  lexeme $ parseString "in"
  b     <- lexeme $ parseTerm
  lexeme $ parseString ")"
  return $ Let x alpha a b 

parseHole = do
  lexeme $ parseString "?"
  h     <- parseHoleId
  parseTry parseVarSub >>= \case
    Just s  -> 
      parseTry parseVarWkn >>= \case
        Just w -> return $ Hole h s w 
        Nothing -> return $ Hole h s mempty
    Nothing ->
      parseTry parseVarWkn >>= \case
        Just w -> return $ Hole h mempty w 
        Nothing -> return $ Hole h mempty mempty

parseVarId :: Parser VarId
parseVarId = do
  lexeme $ parseString "#"
  VarId <$> lexeme parseNextInt

parseHoleId :: Parser HoleId
parseHoleId = HoleId <$> lexeme parseNextInt

parseVarSub :: Parser VarSub
parseVarSub = do
  lexeme $ parseString "["
  subList <- lexeme $ parseManySeparated (lexeme $ parseString ",") parseVarSubItem
  lexeme $ parseString "]"
  return $ Sub $ Map.fromList subList
  
parseVarWkn :: Parser VarWkn
parseVarWkn = do
  lexeme $ parseString "["
  w <- lexeme $ parseManySeparated (lexeme $ parseString ",") parseVarId
  lexeme $ parseString "]"
  return w

parseVarSubItem :: Parser (VarId, Term)
parseVarSubItem = do
  x <- lexeme $ parseVarId
  lexeme $ parseString "="
  a <- lexeme $ parseTerm
  return (x, a)

parseMany :: Parser a -> Parser [a]
parseMany p =
  parseTry p >>= \case
    Just a -> (a :) <$> parseMany p
    Nothing -> return []

parseManySeparated :: Parser () -> Parser a -> Parser [a]
parseManySeparated pSep p =
  parseTry p >>= \case
    Just a -> parseTry pSep >>= \case
      Just _ -> (a :) <$> parseManySeparated pSep p
      Nothing -> return [a]
    Nothing -> return []
    

-- |
-- == Debugging

debug :: String -> ()
debug = Unsafe.unsafePerformIO . putStrLn
