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
-- == Trmtax

data Trm
  = Uni
  | Pi VarId Trm Trm
  | Lam VarId Trm Trm
  | App Trm Trm
  | Var VarId
  | Hole HoleId VarSub VarWkn
  | Let VarId Trm Trm Trm
  deriving (Eq)

data TrmIx
  = Here
  | Pi_alpha TrmIx | Pi_beta TrmIx
  | Lam_alpha TrmIx | Lam_b TrmIx
  | App_f TrmIx | App_a TrmIx
  | Let_alpha TrmIx | Let_a TrmIx | Let_b TrmIx

type VarWkn = [VarId]

newtype VarId = VarId Int deriving (Eq, Ord, Num) -- x
newtype HoleId = HoleId Int deriving (Eq, Ord, Num) -- h

instance Show Trm where
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

getSubterm :: Trm -> TrmIx -> Trm
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

replaceSubterm :: Trm -> TrmIx -> Trm -> Trm
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
data VarCtxItem = VarCtxItem { typ :: Trm, val :: Maybe Trm }

type HoleCtx = Ctx HoleId Trm -- gamma :: hole => type

newtype Ctx k v = Ctx (Map.Map k v)
  deriving (Eq, Semigroup, Monoid, Functor, Foldable, Traversable)

instance Show VarCtxItem where
  show item = show item.typ ++ case item.val of Nothing -> ""; Just a -> " = " ++ show a

instance Ord k => Indexable (Ctx k v) k v where
  index k (Ctx ctx) = ctx Map.! k

instance Ord k => Insertable (Ctx k v) k v where
  insert k v (Ctx ctx) = Ctx $ Map.insert k v ctx

instance Ord k => Deletable (Ctx k v) k where
  delete k (Ctx ctx) = Ctx $ Map.delete k ctx

instance (Show k, Show v) => Show (Ctx k v) where
  show (Ctx ctx) =
    "{" ++
    ( List.intercalate ", " .
      List.map (\(k, v) -> show k ++ " : " ++ show v) .
      Map.toList
    $ ctx )
    ++ "}"

-- |
-- === Sub

type VarSub = Sub VarId Trm
type HoleSub = Sub HoleId Trm

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

weak :: VarId -> Trm -> Trm
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
sub :: Trm -> VarId -> Trm -> Trm 
sub a x b = case a of 
  Uni -> Uni
  Pi y alpha beta -> Pi y (sub alpha x b) (sub beta x b)
  Lam y alpha c -> Lam y (sub alpha x b) (sub c x (weak x b))
  App f a -> app (sub f x b) (sub a x b)
  Var y -> if x == y then b else Var y
  Hole h s w ->
    if x `elem` w
      then Hole h (insert x b s) (x `List.delete` w)
      else Hole h (insert x b s) w

-- | inputs/output is normal
app :: Trm -> Trm -> Trm
app f a = case f of
  Lam x alpha b -> sub b x a
  App f' a' -> App (App f' a') a
  Var x -> App (Var x) a
  Hole h s w -> App (Hole h s w) a

-- | output is normal
norm :: Trm -> Trm
norm = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (norm alpha) (norm beta)
  Lam x alpha b -> Lam x (norm alpha) (norm b)
  App f a -> app (norm f) (norm a)
  Var x -> Var x
  Hole h s w -> Hole h s w
  Let x alpha a b -> sub b x (norm a)

norm_test1 :: Trm
norm_test1 = norm . readTrm $
  "(let #0 : U = U in #0)"

norm_test2 :: Trm
norm_test2 = norm . readTrm $
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

instance Renamable VarId Trm where
  rename ren = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (rename ren alpha) (rename ren beta)
    Lam x alpha b -> Lam (maybe x id (lookup x ren)) (rename ren alpha) (rename ren b)
    App f a -> App (rename ren f) (rename ren a)
    Var x -> Var $ maybe x id (lookup x ren)
    Hole h s' w -> Hole h (rename ren s') (rename ren w)
    Let x alpha a b -> Let x (rename ren alpha) (rename ren a) (rename ren b)

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
  -- rename ren g = rename ren <$> g
  rename ren (Ctx ctx) =
    Ctx .
    Map.mapKeys (\x -> maybe x id (lookup x ren)) .
    Map.map (rename ren)
    $ ctx

instance Renamable VarId VarCtxItem where
  rename ren item = item{ typ = rename ren item.typ
                        , val = rename ren <$> item.val }

instance Renamable HoleId Trm where
  rename ren = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (rename ren alpha) (rename ren beta)
    Lam x alpha b -> Lam x (rename ren alpha) (rename ren b)
    App f a -> App (rename ren f) (rename ren a)
    Var x -> Var x
    Hole h s w -> Hole (maybe h id (lookup h ren)) (rename ren s) w

instance Renamable HoleId HoleCtx where
  rename ren gamma = rename ren <$> gamma 

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

instance Substitutable VarId Trm Trm where
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

instance Substitutable HoleId Trm Trm where
  substitute sigma = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (substitute sigma alpha) (substitute sigma beta)
    Lam x alpha b -> Lam x (substitute sigma alpha) (substitute sigma b)
    App f a -> App (substitute sigma f) (substitute sigma a)
    Var x -> Var x
    Hole h s w -> case lookup h sigma of 
      Just a -> substitute (substitute sigma s) (substitute sigma a)
      Nothing -> Hole h (substitute sigma s) w


instance Substitutable HoleId Trm HoleCtx where
  substitute (Sub sigma) =
    fmap (substitute (Sub sigma)) .
    (flip $ foldl (flip delete)) (Map.keys sigma)

instance Substitutable HoleId Trm VarCtx where
  substitute sigma = fmap (\item ->
    VarCtxItem{ typ  = substitute sigma item.typ
              , val = substitute sigma <$> item.val })

instance Substitutable HoleId Trm VarSub where
  substitute sigma s = fmap (substitute sigma) s

-- |
-- == Unification

unify :: HoleCtx -> VarCtx -> Trm -> Trm -> Maybe HoleSub
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
  (Hole h s w, a') | not (isHole a') ->
    return $ Sub $ Map.singleton h (substitute s a')
  (a, Hole h' sigma' w) | not (isHole a) ->
    return $ Sub $ Map.singleton h' (substitute sigma' a)
  _ -> mzero
  
-- |
-- == Inference

-- | Returns a type in normal form
infer :: HoleCtx -> VarCtx -> Trm -> Trm
infer gamma g = \case
  Uni -> Uni
  Pi x alpha beta -> Uni
  Lam x alpha b -> Pi x alpha beta where
    beta = infer gamma (insert x VarCtxItem{ typ = alpha , val = mzero} g) b
  App f a -> sub beta x (norm a) where
    Pi x alpha beta = infer gamma g f
  Var x -> norm (typ $ index x g)
  Hole h s w -> norm $ index h gamma
  Let x alpha a b -> infer gamma beta b where
    beta = insert x VarCtxItem{ typ = alpha, val = Just a } g

-- |
-- == Fixity

-- | free < type < term
-- `fix1 < fix2` implies that `fix1` is "less fixed" than `fix2`.
data Fix = Free | FixType | FixTerm deriving (Eq, Ord, Show)

-- TODO: where do variables get term-fixed?
fixIn :: VarId -> Trm -> Fix -> Fix
fixIn x a fix = case a of
  Uni -> Free
  Pi y alpha beta -> maximum [fixIn x alpha fixAlpha, fixIn x beta fixBeta] where
    fixAlpha | fix >= FixType = FixTerm
             | fixIn x beta fixBeta >= FixType = FixTerm
             | otherwise = FixType
    fixBeta | fix >= FixTerm = FixTerm
            | otherwise = FixType
  Lam y alpha b -> maximum [fixIn x alpha fixAlpha, fixIn x b fixB] where
    fixAlpha | fix >= FixType = FixTerm
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

isHole :: Trm -> Bool
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
  , patternIn :: Trm
  , patternOut :: Trm }
  deriving (Show)

-- | Makes a rewrite rule in this form:
-- `gamma |- patternIn{fix <= maxFix} ~> patternOut{fix <= maxFix}`
makeRewriteRule :: HoleCtx -> Trm -> Trm -> Rewrite
makeRewriteRule gamma patternIn patternOut = Rewrite
  { gamma
  , maxFix = inferMaxFix gamma patternIn patternOut
  , patternIn
  , patternOut }

-- | Infers the maximumity of for the patternIn/patternOut of a rewrite rule.
-- check if patternInType ~ patternOutType unify for type fixedness
-- check if patternIn ~ patternOut unify for term fixedness
inferMaxFix :: HoleCtx -> Trm -> Trm -> Fix
inferMaxFix gamma patternIn patternOut = FixTerm -- TODO

-- | Tries to rewrite the term `a`, of fixness `fix`, in contexts `gamma` and `g`, with rewrite `rew`, after renewing the holes/variables of the input and output patterns. Returns the resulting unifying hole substitution and the (unsubstituted) output pattern.
-- In the result `Just (a, a', r, rho, sigma)`, `a` and `a'` have had `r` and `rho` applied, but not `sigma`.
tryRewrite :: Rewrite -> HoleCtx -> VarCtx -> Fix -> Trm -> Gen (Maybe (Trm, Trm, RenVar, RenHole, HoleSub))
tryRewrite rew gamma g fix a = do
  -- lift $ putStrLn $ "rewrite:\n  " ++ show rew.patternIn ++ "~~>\n  " ++ show rew.patternOut
  
  -- renew holes in rewrite patterns
  rho   <- renewHoles rew.gamma
  gammaRew   <- return $ rename rho rew.gamma
  patternIn  <- return $ rename rho rew.patternIn
  patternOut <- return $ rename rho rew.patternOut
  -- lift $ putStrLn $ "rho:\n  " ++ show rho
  
  -- renew variables
  r <- renewVars [patternIn, patternOut, a]
  -- rename variables in rewrite pattern
  gammaRew   <- return $ rename r gammaRew
  patternIn  <- return $ rename r patternIn
  patternOut <- return $ rename r patternOut
  -- rename variables in target
  gamma      <- return $ rename r gamma
  g          <- return $ rename r g
  a          <- return $ rename r a
  
  -- lift $ putStrLn $ "r:\n  " ++ show r
  -- lift $ putStrLn $ "gammaRew   = " ++ show gammaRew
  -- lift $ putStrLn $ "patternIn  = " ++ show patternIn
  -- lift $ putStrLn $ "patternOut = " ++ show patternOut
  -- lift $ putStrLn $ "gamma      = " ++ show gamma
  -- lift $ putStrLn $ "g          = " ++ show g
  -- lift $ putStrLn $ "a          = " ++ show a

  --
  return do
    -- check maximum fix
    guard $ fix <= rew.maxFix
    -- unify patternIn's type with target's type
    let patternInType = infer gammaRew mempty patternIn
    let alpha = infer gamma g a
    sigma1 <- unify gammaRew g (norm patternInType) (norm alpha)
    -- unify patternIn with target
    sigma2 <- unify (substitute sigma1 gammaRew)
                    (substitute sigma1 g)
                    (substitute sigma1 patternIn)
                    (substitute sigma1 a)
    return (patternIn, patternOut, r, rho, sigma2 <> sigma1)

-- tryRewriteAt :: Rewrite -> HoleCtx -> VarCtx -> Fix -> Trm -> Ix -> Gen (Maybe Trm)
-- tryRewriteAt rew gamma g fix a Here = do
--   -- renew holes in rewrite patterns
--   rho   <- renewHoles rew.gamma
--   gammaRew   <- return $ rename rho rew.gamma
--   patternIn  <- return $ rename rho rew.patternIn
--   patternOut <- return $ rename rho rew.patternOut
--   -- renew variables
--   r <- renewVars [patternIn, patternOut, a]
--   -- rename variables in rewrite pattern
--   gammaRew   <- return $ rename r gammaRew
--   patternIn  <- return $ rename r patternIn
--   patternOut <- return $ rename r patternOut
--   -- rename variables in target
--   gamma      <- return $ rename r gamma
--   g          <- return $ rename r g
--   a          <- return $ rename r a
--   --
--   return do
--     -- check maximum fix
--     guard $ fix <= rew.maxFix
--     -- unify patternIn's type with target's type
--     let patternInType = infer gammaRew mempty patternIn
--     let alpha = infer gamma g a
--     sigma1 <- unify gammaRew g (norm patternInType) (norm alpha)
--     -- unify patternIn with target
--     sigma2 <- unify (substitute sigma1 gammaRew)
--                     (substitute sigma1 g)
--                     (substitute sigma1 patternIn)
--                     (substitute sigma1 a)
--     return (patternIn, patternOut, r, rho, sigma2 <> sigma1)


rewrites :: Map.Map String Rewrite
rewrites = Map.fromList
  [ ( "fill Π"
    , makeRewriteRule
        (Ctx $ Map.fromList
          [ (0, readTrm "U")
          , (1, readTrm "?0")
          , (2, readTrm "U")
          , (3, readTrm "U")
          , (4, readTrm "?3")
          ])
        (readTrm "?1")
        (readTrm "(Π #0 : ?2 . ?4)") )
  , ( "η-reduce"
      , makeRewriteRule
          (Ctx $ Map.fromList
            [ (0, readTrm "U") -- alpha
            , (1, readTrm "U") -- beta
            , (2, readTrm "(Π #0 : ?0 . ?1)") -- f
            , (3, readTrm "?0") -- x
            ])
          (readTrm "(λ #0 : ?0 . (?2 #0))")
          (readTrm "?2") )
  , ( "β-reduce"
    , makeRewriteRule
        (Ctx $ Map.fromList
          [ (0, readTrm "U") -- alpha
          , (1, readTrm "U") -- beta
          , (2, readTrm "?0") -- b
          , (3, readTrm "?1") -- a
          ])
        (readTrm "((λ #0 : ?0 . ?2) ?3)")
        (readTrm "?2[#0 = ?3]") )
  , ( "swap parameters"
    , makeRewriteRule
        (Ctx $ Map.fromList 
          [ (0, readTrm "U") -- alpha
          , (1, readTrm "U") -- beta
          , (2, readTrm "U") -- epsilon
          , (3, readTrm "?2") -- e
          ])
        (readTrm "(λ #0 : ?0 . (λ #1 : ?1 . ?3))")
        (readTrm "(λ #2 : ?1 . (λ #3 : ?0 . ?3))") )
  , ( "dig parameter"
    , makeRewriteRule
        (Ctx $ Map.fromList
          [ (0, readTrm "U") -- alpha
          , (1, readTrm "U") -- beta
          , (2, readTrm "?0") -- a
          , (3, readTrm "?1") -- b
          ])
        (readTrm "(λ #0 : ?0 . ?3)")
        (readTrm "?3[?0 = ?2]") )
  , ( "let-wrap"
    , makeRewriteRule 
        (Ctx $ Map.fromList
          [ (0, readTrm "U")
          , (1, readTrm "U")
          , (2, readTrm "?0")
          , (3, readTrm "?1") ])
        (readTrm "?3")
        (readTrm "(let #0 : ?1 = ?2 in ?3)") )
  ]

getMaxVarId :: VarId -> Trm -> VarId
getMaxVarId varId = \case
  Uni -> varId
  Pi x alpha beta -> maximum [varId, x, getMaxVarId varId alpha, getMaxVarId varId beta]
  Lam x alpha b -> maximum [varId, x, getMaxVarId varId alpha, getMaxVarId varId b]
  App f a -> maximum [varId, getMaxVarId varId f, getMaxVarId varId a]
  Var x -> maximum [varId, x]
  Let x alpha a b -> maximum [varId, x, getMaxVarId varId alpha, getMaxVarId varId a, getMaxVarId varId b]
  Hole _ s w -> maximum (foldl max varId ((getMaxVarId varId <$> s)) : w)

getMaxHoleId :: HoleId -> Trm -> HoleId
getMaxHoleId holeId = \case
  Uni -> holeId
  Pi x alpha beta -> maximum [holeId, getMaxHoleId holeId alpha, getMaxHoleId holeId beta]
  Lam x alpha b -> maximum [holeId, getMaxHoleId holeId alpha, getMaxHoleId holeId b]
  App f a -> maximum [holeId, getMaxHoleId holeId f, getMaxHoleId holeId a]
  Var x -> holeId
  Let x alpha a b -> maximum [holeId, getMaxHoleId holeId alpha, getMaxHoleId holeId a, getMaxHoleId holeId b]
  Hole h s w -> foldl max (holeId `max` h) (getMaxHoleId holeId <$> s)

makeGenState :: Trm -> GenState
makeGenState a = GenState
  { holeId = getMaxHoleId 0 a
  , varId = getMaxVarId 0 a
  , stdGen = Random.mkStdGen 0 }

run_rewrite_test :: String -> HoleCtx -> VarCtx -> Fix -> Trm -> IO ()
run_rewrite_test rewName gamma g fix a = do
  let rew = rewrites Map.! rewName
  (res, _) <- runStateT (tryRewrite rew gamma g fix a) (makeGenState a)
  case res of
    Just (patternIn, patternOut, r, rho, sigma) -> do
      let a' = substitute sigma patternOut
      let g' = substitute sigma . rename r . rename rho $ g
      putStrLn $ unlines
        [ "[SUCCEEDED]"
        , "rewrite rule: " ++ rewName
        , "  " ++ show patternIn ++ " ~~>"
        , "  " ++ show patternOut
        , "rewrite:"
        , "  " ++ show a ++ " ~~>"
        , "  " ++ show a'
        , "  " ++ "in context:   " ++ show g'
        , "  " ++ "via var ren:  " ++ show r
        , "  " ++ "via hole ren  " ++ show rho
        , "  " ++ "via hole sub: " ++ show sigma ]
    Nothing ->
      putStrLn $ "\nfailed test for rewrite rule '" ++ rewName ++ "'"

rewrite_test1 :: IO ()
rewrite_test1 = run_rewrite_test
  "β-reduce"
  mempty
  mempty
  Free
  (readTrm "((λ #0 : U . #0) U)")

rewrite_test2 :: IO ()
rewrite_test2 = run_rewrite_test
  "β-reduce"
  mempty
  mempty
  Free
  (readTrm "((λ #0 : U . #0) (λ #1 : U . #1))")

rewrite_test3 :: IO ()
rewrite_test3 = run_rewrite_test
  "η-reduce"
  mempty
  (Ctx $ Map.fromList 
    [(0, VarCtxItem{ typ = readTrm "(Π #2 : U . U)", val = mzero })])
  Free
  (readTrm "(λ #1 : U . (#0 #1))")

rewrite_test4 :: IO ()
rewrite_test4 = run_rewrite_test -- TODO
  "fill Π"
  (Ctx $ Map.fromList
    [(0, readTrm "U")])
  mempty
  Free
  (readTrm "?0")

-- |
-- == Generation

data GenState = GenState
  { holeId :: HoleId
  , varId :: VarId
  , stdGen :: Random.StdGen }
  deriving (Show)

type Gen a = StateT GenState IO a

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

-- |
-- === Renewable

renewHoles :: HoleCtx -> Gen (RenHole)
renewHoles (Ctx ctx) =
  Ren . Map.fromList <$> traverse
    (\h -> (h,) <$> nextHoleId)
    (Map.keys ctx)

-- instance RenewableHoles (HoleCtx, [Trm]) where
--   -- accumulate a hole renaming from old holes to new holes
--   -- apply renaming to hole context and term
--   renewHoles (gamma@(Ctx ctx), as) = do
--     ren <- Ren . Map.fromList <$> traverse
--             (\h -> (h,) <$> nextHoleId)
--             (Map.keys ctx)
--     return (rename ren gamma, rename ren <$> as)

-- |
-- === RenewableVars

renewVars :: [Trm] -> Gen (RenVar)
renewVars = fmap (Ren . Map.fromList) . foldM (flip go) [] where
  go :: Trm -> [(VarId, VarId)] -> Gen [(VarId, VarId)]
  go a ren = case a of
    Uni -> return ren
    Pi x alpha beta -> go alpha ren >>=  go beta
    Lam x alpha b -> do x' <- nextVarId
                        go alpha ((x, x') : ren) >>= go b
    App f a -> go f ren >>= go a
    Var x -> return ren
    Hole h s w -> return ren
    Let x alpha a b -> do x' <- nextVarId
                          go alpha ((x, x') : ren) >>= go a >>= go b

-- class RenewableVars a where
--   renewVars :: a -> Gen a

-- instance RenewableVars Trm where
--   renewVars = \case
--     Uni -> return Uni
--     Pi x alpha beta -> do
--       x' <- nextVarId
--       Pi x' <$> renewVars (renameSingle x x' alpha)
--             <*> renewVars (renameSingle x x' beta)
--     Lam x alpha b -> do
--       x' <- nextVarId
--       Lam x' <$> renewVars (renameSingle x x' alpha)
--              <*> renewVars (renameSingle x x' b)
--     App f a -> App <$> renewVars f <*> renewVars a
--     Var x -> return $ Var x
--     Hole h s -> Hole h <$> renewVars s
--     Let x alpha a b -> do
--       x' <- nextVarId
--       Let x' <$> renewVars (renameSingle x x' alpha)
--              <*> renewVars (renameSingle x x' a)
--              <*> renewVars (renameSingle x x' b)

-- instance RenewableVars VarCtx where
--   renewVars = traverse \item -> do
--     typ <- renewVars item.typ 
--     val <- maybe (return Nothing) (fmap Just . renewVars) item.val
--     -- case item.val of Just val -> Just <$> renewVars val; Nothing -> return Nothing
--     return VarCtxItem{ typ, val }

-- instance RenewableVars HoleCtx where
--   renewVars = traverse renewVars

-- instance RenewableVars VarSub where
--   renewVars = traverse renewVars

-- instance RenewableVars HoleSub where
--   renewVars = traverse renewVars


-- |
-- == Parsing

readTrm :: String -> Trm
readTrm = unsafeEvalParser parseTrm

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
-- === Parsing Trmtax

parseTrm :: Parser Trm
parseTrm = do
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
    Nothing -> throwError $ "Attempted to parseTrm but failed all cases"

parseUni, parsePi, parseLam, parseApp, parseVar, parseHole, parseLet :: Parser Trm

parseUni = do
  lexeme $ parseString "U"
  return $ Uni 

parsePi = do
  lexeme $ parseString "("
  lexeme $ parseString "Π"
  x     <- lexeme $ parseVarId
  lexeme $ parseString ":"
  alpha <- lexeme $ parseTrm
  lexeme $ parseString "."
  beta  <- lexeme $ parseTrm
  lexeme $ parseString ")"
  return $ Pi x alpha beta 

parseLam = do
  lexeme $ parseString "("
  lexeme $ parseString "λ"
  x     <- lexeme $ parseVarId
  lexeme $ parseString ":"
  alpha <- parseTrm
  lexeme $ parseString "."
  b     <- lexeme $ parseTrm
  lexeme $ parseString ")"
  return $ Lam x alpha b 

parseApp = do
  lexeme $ parseString "("
  f     <- lexeme $ parseTrm
  a     <- lexeme $ parseTrm
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
  alpha <- parseTrm
  lexeme $ parseString "="
  a     <- lexeme $ parseTrm
  lexeme $ parseString "in"
  b     <- lexeme $ parseTrm
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

parseVarSubItem :: Parser (VarId, Trm)
parseVarSubItem = do
  x <- lexeme $ parseVarId
  lexeme $ parseString "="
  a <- lexeme $ parseTrm
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
