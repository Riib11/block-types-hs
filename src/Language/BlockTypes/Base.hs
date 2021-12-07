{-# LANGUAGE LambdaCase, BlockArguments, OverloadedRecordDot, UndecidableInstances, NamedFieldPuns, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveTraversable, GeneralizedNewtypeDeriving, DuplicateRecordFields #-}
module Language.BlockTypes.Base where 

{-

ASSUMPTIONS
- unique variable names

-}

import qualified System.IO.Unsafe as Unsafe
import qualified System.Random as Random
import Control.Monad as Monad
import Control.Monad.State as State
import Control.Monad.Except as Except
import Control.Monad.Trans as Trans
import Data.Maybe as Maybe 
import Data.Either as Either
import qualified Data.Map as Map
import qualified Data.List as List
import Prelude hiding (lookup)

-- |
-- == Syntax

data Syn
  = Uni
  | Pi VarId Syn Syn
  | Lam VarId Syn Syn
  | App Syn Syn
  | Var VarId
  | Hole HoleId VarSub
  | Let VarId Syn Syn Syn
  deriving (Eq)

newtype VarId = VarId Int deriving (Eq, Ord, Num) -- x
newtype HoleId = HoleId Int deriving (Eq, Ord, Num) -- h

instance Show Syn where
  show = \case
    Uni -> "U"
    Pi x alpha beta -> "(Π " ++ show x ++ " : " ++ show alpha ++ " . " ++ show beta ++ ")"
    Lam x alpha b -> "(λ " ++ show x ++ " : " ++ show alpha ++ " . " ++ show b ++ ")"
    App f a -> "(" ++ show f ++ " " ++ show a ++ ")"
    Var x -> "#" ++ show x
    Hole h s -> "?" ++ show h ++ if s == mempty then "" else show s
    Let x alpha a b -> "(let " ++ show x ++ " : " ++ show alpha ++ " = " ++ show a ++ " in " ++ show b ++ ")"

alphabet = [[c] | c <- ['a'..'z']]

instance Show VarId where
  show (VarId i)
    | i < length alphabet = alphabet!!i
    | otherwise = alphabet!!(i `mod` length alphabet) ++ show (i `div` length alphabet)

instance Show HoleId where
  show (HoleId i) = show i

-- |
-- === Ctx

type VarCtx = Ctx VarId VarCtxItem -- g :: var |-> type, value?
type HoleCtx = Ctx HoleId Syn -- gamma :: hole => type

data VarCtxItem = VarCtxItem { typ :: Syn, val :: Maybe Syn }

instance Show VarCtxItem where
  show item = show item.typ ++ case item.val of Nothing -> ""; Just a -> " = " ++ show a

newtype Ctx k v = Ctx (Map.Map k v)
  deriving (Eq, Semigroup, Monoid, Functor, Foldable, Traversable)

instance (Show k, Show v) => Show (Ctx k v) where
  show (Ctx ctx)
    | Map.null ctx = "{}"
    | otherwise =
        "{" ++
        ( List.intercalate ", " .
          List.map (\(k, v) -> show k ++ " : " ++ show v) .
          Map.toList
        $ ctx )
        ++ "}"

-- |
-- === Sub

type VarSub = Sub VarId Syn
type HoleSub = Sub HoleId Syn

newtype Sub k v = Sub (Map.Map k v)
  deriving (Eq, Functor, Foldable, Traversable)

instance (Ord k, Substitutable k v v) => Semigroup (Sub k v) where
  -- sigma2 after sigma1
  Sub sigma2 <> Sub sigma1 =
    case fmap (substitute (Sub sigma2)) (Sub sigma1) of
      Sub sigma1 -> Sub (sigma2 <> sigma1)

instance (Ord k, Substitutable k v v) => Monoid (Sub k v) where
  mempty = Sub mempty

instance (Show k, Show v) => Show (Sub k v) where
  show (Sub sub) 
    | Map.null sub = "[]"
    | otherwise =
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

instance Ord k => Indexable (Ctx k v) k v where
  index k (Ctx ctx) = ctx Map.! k

-- |
-- === Lookupable

class Lookupable c k v where
  lookup :: k -> c -> Maybe v

instance Ord k => Lookupable (Sub k v) k v where
  lookup k (Sub sub) = sub Map.!? k

-- |
-- === Insertable

class Insertable c k v where
  insert :: k -> v -> c -> c

instance Ord k => Insertable (Ctx k v) k v where
  insert k v (Ctx ctx) = Ctx $ Map.insert k v ctx

instance Ord k => Insertable (Sub k v) k v where
  insert k v (Sub sub) = Sub $ Map.insert k v sub

-- |
-- === Deletable

class Deletable c k where
  delete :: k -> c -> c

instance Ord k => Deletable (Ctx k v) k where
  delete k (Ctx ctx) = Ctx $ Map.delete k ctx

instance Ord k => Deletable (Sub k v) k where
  delete k (Sub sub) = Sub $ Map.delete k sub

-- |
-- == Normalization

-- | inputs/output are normal
-- `a [x |-> b]`
sub :: Syn -> VarId -> Syn -> Syn 
sub a x b = case a of 
  Uni -> Uni
  Pi y alpha beta -> Pi x (sub alpha x b) (sub beta x b)
  Lam y alpha c -> Lam x (sub alpha x b) (sub c x b)
  App f a -> app (sub f x b) (sub a x b)
  Var y -> if x == y then b else Var y
  Hole h s -> Hole h (insert x b s)

-- | inputs/output is normal
app :: Syn -> Syn -> Syn
app f a = case f of
  Lam x alpha b -> sub b x a
  App f' a' -> App (App f' a') a
  Var x -> App (Var x) a
  Hole h s -> App (Hole h s) a

-- | output is normal
norm :: Syn -> Syn
norm = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (norm alpha) (norm beta)
  Lam x alpha b -> Lam x (norm alpha) (norm b)
  App f a -> app (norm f) (norm a)
  Var x -> Var x
  Hole h s -> Hole h s
  Let x alpha a b -> sub b x (norm a)

norm_test1 :: Syn
norm_test1 = norm . readSyn $
  "(let x : U = U in x)"

norm_test2 :: Syn
norm_test2 = norm . readSyn $
  "((λ x : U . x) y)"

-- |
-- == Renaming

class Renamable id a where
  rename :: id -> id -> a -> a

instance Renamable VarId Syn where
  rename x y = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (rename x y alpha) (rename x y beta)
    Lam x alpha b -> Lam x (rename x y alpha) (rename x y b)
    App f a -> App (rename x y f) (rename x y a)
    Var x' -> if x == x' then Var y else Var x'
    Hole h s' -> Hole h (rename x y s')
    Let x alpha a b -> Let x (rename x y alpha) (rename x y a) (rename x y b)

instance Renamable VarId VarSub where
  rename x y (Sub s) =
    Sub .
    Map.mapKeys (\x' -> if x == x' then y else x') .
    Map.map (rename x y)
    $ s

-- |
-- == Substitution

class Substitutable k v a where
  substitute :: Sub k v -> a -> a

instance Substitutable VarId Syn Syn where
  -- | Doesn't normalize things
  substitute s = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (substitute s alpha) (substitute s beta)
    Lam x alpha b -> Lam x (substitute s alpha) (substitute s b)
    App f a -> App (substitute s f) (substitute s a)
    Var x -> case lookup x s of
      Just a -> a
      Nothing -> Var x
    Hole h s' -> Hole h (s' <> s)
    Let x alpha a b -> Let x (substitute s alpha) (substitute s a) (substitute s b)

instance Substitutable HoleId Syn Syn where
  substitute sigma = \case
    Uni -> Uni
    Pi x alpha beta -> Pi x (substitute sigma alpha) (substitute sigma beta)
    Lam x alpha b -> Lam x (substitute sigma alpha) (substitute sigma b)
    App f a -> App (substitute sigma f) (substitute sigma a)
    Var x -> Var x
    Hole h s -> case lookup h sigma of 
      Just a -> substitute (substitute sigma s) (substitute sigma a)
      Nothing -> Hole h (substitute sigma s)

instance Substitutable HoleId Syn HoleCtx where
  substitute (Sub sigma) =
    fmap (substitute (Sub sigma)) .
    (flip $ foldl (flip delete)) (Map.keys sigma)

instance Substitutable HoleId Syn VarCtx where
  substitute sigma = fmap (\item ->
    VarCtxItem{ typ  = substitute sigma item.typ
              , val = substitute sigma <$> item.val })

instance Substitutable HoleId Syn VarSub where
  substitute sigma s = fmap (substitute sigma) s

-- |
-- == Unification

unify :: HoleCtx -> VarCtx -> Syn -> Syn -> Maybe HoleSub
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
                (rename x' x (substitute sigma1 beta'))
    return $ sigma2 <> sigma1
  (Lam x alpha b, Lam x' alpha' b') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify
                (substitute sigma1 gamma)
                (insert x
                  VarCtxItem{typ = substitute sigma1 alpha, val = mzero}
                  (substitute sigma1 g))
                (substitute sigma1 b)
                (rename x' x (substitute sigma1 b'))
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
                (substitute (sigma2 <> sigma1) (rename x' x b'))
    return $ sigma3 <> sigma2 <> sigma1
  (Hole h s, a') | not (isHole a') ->
    return $ Sub $ Map.singleton h (substitute s a')
  (a, Hole h' sigma') | not (isHole a) ->
    return $ Sub $ Map.singleton h' (substitute sigma' a)
  _ -> mzero
  
-- |
-- == Inference

-- | Returns a type in normal form
infer :: HoleCtx -> VarCtx -> Syn -> Syn
infer gamma g = \case
  Uni -> Uni
  Pi x alpha beta -> Uni
  Lam x alpha b -> Pi x alpha beta where
    beta = infer gamma (insert x VarCtxItem{ typ = alpha , val = mzero} g) b
  App f a -> sub beta x (norm a) where
    Pi x alpha beta = infer gamma g f
  Var x -> norm (typ $ index x g)
  Hole h s -> norm $ index h gamma
  Let x alpha a b -> infer gamma beta b where
    beta = insert x VarCtxItem{ typ = alpha, val = Just a } g

-- |
-- == Fixity

-- | free < type < term
-- `fix1 < fix2` implies that `fix1` is "less fixed" than `fix2`.
data Fix = Free | FixType | FixTerm deriving (Eq, Ord, Show)

-- TODO: where do variables get term-fixed?
fixIn :: VarId -> Syn -> Fix -> Fix
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
  Hole h s -> Free
  Let y alpha a b -> maximum [fixIn x alpha fixAlpha, fixIn x a fixA, fixIn x b fixB] where
    fixAlpha | fix >= FixTerm = FixTerm
             | fixIn x b fixB >= FixType = FixTerm
             | otherwise = FixType
    fixA | fixIn x b fixB >= FixTerm = FixTerm 
         | fixIn x b fixB >= FixType = FixType
         | fixAlpha >= FixTerm = FixType
         | otherwise = Free
    fixB = fix

isHole :: Syn -> Bool
isHole = \case 
  Hole _ _ -> True
  _ -> False

-- |
-- == Rewriting

-- | `gamma |- inPattern{maxFix} ~> outPattern{maxFix}`
-- TODO: how to keep track of the local bindings in the contexts of some holes?
data Rewrite = Rewrite
  { gamma :: HoleCtx
  , maxFix :: Fix
  , inPattern :: Syn
  , outPattern :: Syn }
  deriving (Show)

-- | Makes a rewrite rule in this form:
-- `gamma |- inPattern{fix <= maxFix} ~> outPattern{fix <= maxFix}`
makeRewriteRule :: HoleCtx -> Syn -> Syn -> Rewrite
makeRewriteRule gamma inPattern outPattern = Rewrite
  { gamma
  , maxFix = inferMaxFix gamma inPattern outPattern
  , inPattern
  , outPattern }

-- | Infers the maximumity of for the inPattern/outPattern of a rewrite rule.
inferMaxFix :: HoleCtx -> Syn -> Syn -> Fix
inferMaxFix gamma inPattern outPattern = FixTerm -- TODO

-- | Tries to rewrite the term `a`, of fixness `fix`, in contexts `gamma` and `g`, with rewrite `rew`.
-- Requires that the `rew`, `gamma`, and `g` have been refreshed.
tryRewrite :: Rewrite -> HoleCtx -> VarCtx -> Fix -> Syn -> Maybe HoleSub
tryRewrite rew gamma g fix a = do
  let inPatternType = infer rew.gamma mempty rew.inPattern
  let alpha = infer gamma g a
  let gamma' = gamma <> rew.gamma
  -- check maximum fix
  guard $ fix <= rew.maxFix
  -- unify inPattern's type with target's type
  sigma1 <- unify gamma' g (norm inPatternType) (norm alpha)
  -- unify inPattern with target
  sigma2 <- unify
              (substitute sigma1 gamma')
              (substitute sigma1 g)
              (substitute sigma1 rew.inPattern)
              (substitute sigma1 a)
  return (sigma2 <> sigma1)

rewrites :: Map.Map String Rewrite
rewrites = Map.fromList
  [ ( "fill Π"
    , makeRewriteRule
        (Ctx $ Map.fromList
          [ (0, readSyn "U")
          , (1, readSyn "?0")
          , (2, readSyn "U")
          , (3, readSyn "U")
          , (4, readSyn "?3")
          ])
        (readSyn "?1")
        (readSyn "(Π 0 : ?2 . ?4)") )
  , ( "η-reduce"
      , makeRewriteRule
          (Ctx $ Map.fromList
            [ (0, readSyn "U") -- alpha
            , (1, readSyn "U") -- beta
            , (2, readSyn "(Π 0 : ?0 . ?1)") -- f
            , (3, readSyn "?0") -- x
            ])
          (readSyn "(λ 0 : ?0 . (?2 #0))")
          (readSyn "?2") )
  , ( "β-reduce"
    , makeRewriteRule
        (Ctx $ Map.fromList
          [ (0, readSyn "U") -- alpha
          , (1, readSyn "U") -- beta
          , (2, readSyn "?0") -- b
          , (3, readSyn "?1") -- a
          ])
        (readSyn "((λ 0 : ?0 . ?2) ?3)")
        (readSyn "?2[0 = ?3]") )
  , ( "swap parameters"
    , makeRewriteRule
        (Ctx $ Map.fromList 
          [ (0, readSyn "U") -- alpha
          , (1, readSyn "U") -- beta
          , (2, readSyn "U") -- epsilon
          , (3, readSyn "?2") -- e
          ])
        (readSyn "(λ 0 : ?0 . (λ 1 : ?1 . ?3))")
        (readSyn "(λ 2 : ?1 . (λ 3 : ?0 . ?3))") )
  , ( "dig parameter"
    , makeRewriteRule
        (Ctx $ Map.fromList
          [ (0, readSyn "U") -- alpha
          , (1, readSyn "U") -- beta
          , (2, readSyn "?0") -- a
          , (3, readSyn "?1") -- b
          ])
        (readSyn "(λ 0 : ?0 . ?3)")
        (readSyn "?3[0 = ?2]") )
  , ( "let-wrap"
    , makeRewriteRule 
        (Ctx $ Map.fromList
          [ (0, readSyn "U")
          , (1, readSyn "U")
          , (2, readSyn "?0")
          , (3, readSyn "?1") ])
        (readSyn "?3")
        (readSyn "(let 0 : ?1 = ?2 in ?3)") )
  ]

run_rewrite_test :: String -> HoleCtx -> VarCtx -> Fix -> Syn -> IO ()
run_rewrite_test rewName gamma g fix a = do
  let rew = rewrites Map.! rewName
  case tryRewrite rew gamma g fix a of
    Just sigma -> do
      let a' = substitute sigma rew.outPattern
      putStrLn $ unlines
        [ "passed test for rewrite rule '" ++ rewName ++ "':"
        , "  " ++ show a ++ " ~~> " ++ show a'
        , "  " ++ "via " ++ show sigma ]
    Nothing ->
      putStrLn $ "failed test for rewrite rule '" ++ rewName ++ "'"


rewrite_test1 :: IO ()
rewrite_test1 = run_rewrite_test
  "β-reduce"
  mempty
  mempty
  Free
  (readSyn "((λ 0 : U . #0) U)")

rewrite_test2 :: IO ()
rewrite_test2 = run_rewrite_test
  "β-reduce"
  mempty
  mempty
  Free
  (readSyn "((λ 0 : U . #0) (λ 1 : U . #1))")

rewrite_test3 :: IO ()
rewrite_test3 = run_rewrite_test
  "η-reduce"
  mempty
  (Ctx $ Map.fromList 
    [(0, VarCtxItem{ typ = readSyn "(Π 2 : U . U)", val = mzero })])
  Free
  (readSyn "(λ 1 : U . (#0 #1))")

rewrite_test4 :: IO ()
rewrite_test4 = run_rewrite_test
  "fill Π"
  (Ctx $ Map.fromList
    [(0, readSyn "U")])
  mempty
  Free
  (readSyn "?0")

-- |
-- == Generation

data GenState = GenState
  { holeId :: HoleId
  , varId :: VarId
  , stdGen :: Random.StdGen }

type Gen a = State GenState a

nextHoleId :: Gen HoleId
nextHoleId = do
  h <- gets holeId
  modify $ \st -> st { holeId = h + 1 }
  return h

nextVarId :: Gen VarId
nextVarId = do
  x <- gets varId
  modify $ \st -> st { varId = x + 1 }
  return x

nextRandR :: Int -> Int -> Gen Int
nextRandR iMin iMax = do
  g <- gets stdGen
  let (i, g') = Random.randomR (iMin, iMax) g
  modify $ \st -> st { stdGen = g' }
  return i

-- |
-- === Refreshable

class Num id => Refreshable id a where
  refresh :: id -> a -> Gen a

-- |
-- ==== Refreshable HoleId *

instance Refreshable HoleId Syn where
  refresh holeId = \case
    Uni -> return Uni 
    Pi x alpha beta -> Pi x <$> refresh holeId alpha <*> refresh holeId beta
    Lam x alpha b -> Lam x <$> refresh holeId alpha <*> refresh holeId b
    App f a -> App <$> refresh holeId f <*> refresh holeId a
    Var x -> return $ Var x
    Hole h s -> Hole (h + holeId) <$> refresh holeId s
    Let x alpha a b -> Let x <$> refresh holeId alpha <*> refresh holeId a <*> refresh holeId b

instance Refreshable HoleId HoleCtx where
  refresh holeId (Ctx ctx) =
    Ctx . Map.fromList <$>
    traverse
      (\(h, a) -> (h + holeId,) <$> refresh holeId a)
      (Map.toList ctx)

instance Refreshable HoleId VarCtx where
  refresh holeId (Ctx ctx) =
    Ctx . Map.fromList <$>
    traverse
      (\(x, item) -> do
        typ <- refresh holeId item.typ
        val <- case item.val of 
                Just v -> Just <$> refresh holeId v
                Nothing -> return Nothing
        return (x, item { typ, val }))
      (Map.toList ctx)

-- instance Refreshable HoleId HoleSub where
--   refresh holeId = undefined

instance Refreshable HoleId VarSub where
  refresh holeId = undefined

-- |
-- ==== Refreshable VarId *

instance Refreshable VarId Syn where
  refresh varId = \case
    Uni -> return Uni
    Pi x alpha beta -> Pi (x + varId) <$> refresh varId alpha <*> refresh varId beta
    Lam x alpha b -> Lam (x + varId) <$> refresh varId alpha <*> refresh varId b
    App f a -> App <$> refresh varId f <*> refresh varId a
    Var x -> return $ Var (x + varId)
    Hole h s -> Hole h <$> refresh varId s
    Let x alpha a b -> Let (x + varId) <$> refresh varId alpha <*> refresh varId a <*> refresh varId b

-- instance Refreshable VarId VarCtx where
--   refresh varId = undefined

-- instance Refreshable VarId HoleCtx where
--   refresh varId = undefined

instance Refreshable VarId VarSub where
  refresh varId = undefined

-- instance Refreshable VarId HoleSub where
--   refresh varId = undefined


-- |
-- == Parsing

readSyn :: String -> Syn
readSyn = unsafeEvalParser parseSyn

type Parser a = StateT String (Except String) a

runParser :: Parser a -> String -> Either String (a, String)
runParser p s = runExcept . flip runStateT s $ p

evalParser :: Parser a -> String -> Either String a
evalParser p = fmap fst . runParser p

unsafeEvalParser :: Parser a -> String -> a
unsafeEvalParser p s = a where Right a = evalParser p s

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
-- === Parsing Syntax

parseSyn :: Parser Syn
parseSyn = do
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
    Nothing -> throwError $ "Attempted to parseSyn but failed all cases"

parseUni, parsePi, parseLam, parseApp, parseVar, parseHole, parseLet :: Parser Syn

parseUni = do
  lexeme $ parseString "U"
  return $ Uni 

parsePi = do
  lexeme $ parseString "("
  lexeme $ parseString "Π"
  x     <- lexeme $ parseVarId
  lexeme $ parseString ":"
  alpha <- lexeme $ parseSyn
  lexeme $ parseString "."
  beta  <- lexeme $ parseSyn
  lexeme $ parseString ")"
  return $ Pi x alpha beta 

parseLam = do
  lexeme $ parseString "("
  lexeme $ parseString "λ"
  x     <- lexeme $ parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "."
  b     <- lexeme $ parseSyn
  lexeme $ parseString ")"
  return $ Lam x alpha b 

parseApp = do
  lexeme $ parseString "("
  f     <- lexeme $ parseSyn
  a     <- lexeme $ parseSyn
  lexeme $ parseString ")"
  return $ App f a 

parseVar = do
  lexeme $ parseString "#"
  x     <- lexeme $ parseVarId
  return $ Var x 

parseLet = do
  lexeme $ parseString "("
  lexeme $ parseString "let"
  x     <- lexeme $ parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "="
  a     <- lexeme $ parseSyn
  lexeme $ parseString "in"
  b     <- lexeme $ parseSyn
  lexeme $ parseString ")"
  return $ Let x alpha a b 

parseHole = do
  lexeme $ parseString "?"
  h     <- parseHoleId
  parseTry parseVarSub >>= \case
    Just s  -> return $ Hole h s 
    Nothing -> return $ Hole h mempty

parseVarId :: Parser VarId
parseVarId = VarId <$> parseNextInt

parseHoleId :: Parser HoleId
parseHoleId = HoleId <$> parseNextInt

parseVarSub :: Parser VarSub
parseVarSub = do
  lexeme $ parseString "["
  subList <- lexeme $ parseManySeparated (lexeme $ parseString ",") parseVarSubItem
  lexeme $ parseString "]"
  return $ Sub $ Map.fromList subList
  
parseVarSubItem :: Parser (VarId, Syn)
parseVarSubItem = do
  x <- lexeme $ parseVarId
  lexeme $ parseString "="
  a <- lexeme $ parseSyn
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
