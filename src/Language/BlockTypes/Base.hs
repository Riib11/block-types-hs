{-# LANGUAGE LambdaCase, BlockArguments, OverloadedRecordDot, UndecidableInstances, NamedFieldPuns, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Language.BlockTypes.Base where 

{-

ASSUMPTIONS
- unique variable names

-}

import qualified System.IO.Unsafe as Unsafe
import Control.Monad as Monad
import Data.Maybe as Maybe 
import qualified Data.Map as Map
import qualified Data.List as List
import Prelude hiding (lookup)

-- |
-- == Syntax

data Syn
  = Uni Fix
  | Pi VarId Syn Syn Fix
  | Lam VarId Syn Syn Fix
  | App Syn Syn Fix
  | Var VarId Fix
  | Hole HoleId VarSub Fix
  | Let VarId Syn Syn Syn Fix
  deriving (Eq)

newtype VarId = VarId String deriving (Eq, Ord) -- x
newtype HoleId = HoleId Int deriving (Eq, Ord) -- h

instance Show Syn where
  show = \case
    Uni fix -> "U"
    Pi x alpha beta fix -> "(Π " ++ show x ++ " : " ++ show alpha ++ " . " ++ show beta ++ ")"
    Lam x alpha b fix -> "(λ " ++ show x ++ " : " ++ show alpha ++ " . " ++ show b ++ ")"
    App f a fix -> "(" ++ show f ++ " " ++ show a ++ ")"
    Var x fix -> show x
    Hole h s fix -> "?" ++ show h ++ if s == mempty then "" else show s
    Let x alpha a b fix -> "(let " ++ show x ++ " : " ++ show alpha ++ " = " ++ show a ++ " in " ++ show b ++ ")"

instance Show VarId where
  show (VarId x) = x

instance Show HoleId where
  show (HoleId h) = show h

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
  Uni fix -> Uni fix
  Pi y alpha beta fix -> Pi x (sub alpha x b) (sub beta x b) fix
  Lam y alpha c fix -> Lam x (sub alpha x b) (sub c x b) fix
  App f a fix -> app (sub f x b) (sub a x b)
  Var y fix -> if x == y then b else Var y fix
  Hole h s fix -> Hole h (insert x b s) fix

-- | inputs/output is normal
app :: Syn -> Syn -> Syn
app f a = case f of
  Lam x alpha b fix -> sub b x a
  App f' a' fix -> App (App f' a' fix) a fix
  Var x fix -> App (Var x fix) a fix
  Hole h s fix -> App (Hole h s fix) a fix

-- | output is normal
norm :: Syn -> Syn
norm = \case
  Uni fix -> Uni fix
  Pi x alpha beta fix -> Pi x (norm alpha) (norm beta) fix
  Lam x alpha b fix -> Lam x (norm alpha) (norm b) fix
  App f a fix -> app (norm f) (norm a)
  Var x fix -> Var x fix
  Hole h s fix -> Hole h s fix
  Let x alpha a b fix -> sub b x (norm a)

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
    Uni fix -> Uni fix
    Pi x alpha beta fix -> Pi x (rename x y alpha) (rename x y beta) fix
    Lam x alpha b fix -> Lam x (rename x y alpha) (rename x y b) fix
    App f a fix -> App (rename x y f) (rename x y a) fix
    Var x' fix -> if x == x' then Var y fix else Var x' fix
    Hole h s' fix -> Hole h (rename x y s') fix
    Let x alpha a b fix -> Let x (rename x y alpha) (rename x y a) (rename x y b) fix

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
    Uni fix -> Uni fix
    Pi x alpha beta fix -> Pi x (substitute s alpha) (substitute s beta) fix
    Lam x alpha b fix -> Lam x (substitute s alpha) (substitute s b) fix
    App f a fix -> App (substitute s f) (substitute s a) fix
    Var x fix -> case lookup x s of
      Just a -> a
      Nothing -> Var x fix
    Hole h s' fix -> Hole h (s' <> s) fix
    Let x alpha a b fix -> Let x (substitute s alpha) (substitute s a) (substitute s b) fix

instance Substitutable HoleId Syn Syn where
  substitute sigma = \case
    Uni fix -> Uni fix
    Pi x alpha beta fix -> Pi x (substitute sigma alpha) (substitute sigma beta) fix
    Lam x alpha b fix -> Lam x (substitute sigma alpha) (substitute sigma b) fix
    App f a fix -> App (substitute sigma f) (substitute sigma a) fix
    Var x fix -> Var x fix
    Hole h s fix -> case lookup h sigma of 
      Just a -> substitute s a
      Nothing -> Hole h s fix

instance Substitutable HoleId Syn HoleCtx where
  substitute (Sub sigma) =
    fmap (substitute (Sub sigma)) .
    (flip $ foldl (flip delete)) (Map.keys sigma)

instance Substitutable HoleId Syn VarCtx where
  substitute sigma = fmap (\item ->
    VarCtxItem{ typ  = substitute sigma item.typ
              , val = substitute sigma <$> item.val })

-- |
-- == Unification

unify :: HoleCtx -> VarCtx -> Syn -> Syn -> Maybe HoleSub
-- unify gamma g a a' = (return $! debug $ show a ++ " ~ " ++ show a') >> case (a, a') of 
unify gamma g a a' = case (a, a') of 
  (Uni fix, Uni fix') -> return mempty
  (Pi x alpha beta fix, Pi x' alpha' beta' fix') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify
                (substitute sigma1 gamma)
                (insert x
                  VarCtxItem{typ=substitute sigma1 alpha, val=mzero}
                  (substitute sigma1 g))
                (substitute sigma1 beta)
                (rename x' x (substitute sigma1 beta'))
    return $ sigma2 <> sigma1
  (Lam x alpha b fix, Lam x' alpha' b' fix') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify
                (substitute sigma1 gamma)
                (insert x
                  VarCtxItem{typ=substitute sigma1 alpha, val=mzero}
                  (substitute sigma1 g))
                (substitute sigma1 b)
                (rename x' x (substitute sigma1 b'))
    return $ sigma2 <> sigma1
  (App f a fix, App f' a' fix') -> do
    sigma1 <- unify gamma g f f'
    sigma2 <- unify gamma g a a'
    return $ sigma1 <> sigma2
  (Var x fix, Var x' fix') ->
    if x == x' then return mempty else mzero
  (Let x alpha a b fix, Let x' alpha' a' b' fix') -> do
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
  (Hole h s fix, a') | not (isHole a') ->
    return $ Sub $ Map.singleton h (substitute s a')
  (a, Hole h' sigma' fix') | not (isHole a) ->
    return $ Sub $ Map.singleton h' (substitute sigma' a)
  _ -> mzero
  
-- |
-- == Inference

-- | Returns a type in normal form
infer :: HoleCtx -> VarCtx -> Syn -> Syn
infer gamma g = \case
  Uni fix -> Uni fix
  Pi x alpha beta fix -> Uni fix
  Lam x alpha b fix -> Pi x alpha beta fix where
    beta = infer gamma (insert x VarCtxItem{ typ = alpha , val = Nothing} g) b
  App f a fix -> sub beta x (norm a) where
    Pi x alpha beta fix = infer gamma g f
  Var x fix -> norm (typ $ index x g)
  Hole h s fix -> norm $ index h gamma
  Let x alpha a b fix -> infer gamma beta b where
    beta = insert x VarCtxItem{ typ = alpha, val = Just a } g

-- |
-- == Fixity

-- | free < type < term
data Fix = Free | FixType | FixTerm deriving (Eq, Ord, Show)

getFix :: Syn -> Fix
getFix = \case
  Uni fix -> fix
  Pi x alpha beta fix -> fix
  Lam x alpha b fix -> fix
  App f a fix -> fix
  Var x fix -> fix
  Hole h s fix -> fix
  Let x alpha a b fix -> fix

getFixIn :: VarId -> Syn -> Fix
getFixIn x = \case
  Uni _ -> Free
  Pi _ alpha beta _ -> getFixIn x alpha `max` getFixIn x beta
  Lam _ alpha b _ -> getFixIn x alpha `max` getFixIn x b
  App f a _ -> getFixIn x f `max` getFixIn x a
  Var y fix -> if x == y then fix else Free
  Hole _ _ _ -> Free
  Let _ alpha a beta _ -> getFixIn x alpha `max` getFixIn x a `max` getFixIn x beta

-- | Updates the fixity of subterms.
updateFix :: Fix -> Syn -> Syn
updateFix fix = \case
  Uni _ -> Uni fix
  Pi x alpha beta _ -> Pi x (updateFix fix_alpha alpha) beta' fix where
    fix_alpha | fix == FixTerm = FixTerm
              | getFixIn x beta' >= FixType = FixTerm
              | otherwise = FixType
    fix_beta | fix == FixTerm = FixTerm
             | otherwise = FixType
    beta' = updateFix fix_beta beta
  Lam x alpha b _ -> Lam x (updateFix fix_alpha alpha) b' fix where
    fix_alpha | fix >= FixType = FixTerm
              | getFixIn x b' >= FixType = FixTerm
              | otherwise = FixType
    fix_b = fix
    b' = updateFix fix_b b
  App f a _ -> App (updateFix fix f) (updateFix fix a) fix
  Var x _ -> Var x fix -- TODO: depends if type is a hole?
  Hole h s _ -> Hole h s fix -- TODO: depends if substitution is empty or not?
  Let x alpha a b _ -> Let x (updateFix fix_alpha alpha) (updateFix fix_a a) b' fix where
    fix_alpha | getFixIn x b' >= FixType = FixTerm
              | otherwise = FixType
    fix_a | getFixIn x b' == FixTerm = FixTerm
          | getFixIn x b' == FixType = FixType
          | otherwise = Free
    fix_b = fix
    b' = updateFix fix_b b

isHole :: Syn -> Bool
isHole = \case 
  Hole _ _ _ -> True
  _ -> False

-- |
-- == Rewriting

-- | `gamma |- input{maxFix} ~> output{maxFix}`
data Rewrite = Rewrite
  { gamma :: HoleCtx
  , maxFix :: Fix
  , input :: Syn
  , inputType :: Syn
  , output :: Syn }
  deriving (Show)

-- | Makes a rewrite rule in this form:
-- `gamma |- input{fix <= maxFix} ~> output{fix <= maxFix}`
makeRewriteRule :: HoleCtx -> Syn -> Syn -> Rewrite
makeRewriteRule gamma input output = Rewrite
  { gamma
  , maxFix = inferMaxFix gamma input output
  , input
  , inputType = infer gamma mempty input
  , output }

-- | Infers the maximumity of for the input/output of a rewrite rule.
inferMaxFix :: HoleCtx -> Syn -> Syn -> Fix
inferMaxFix gamma input output = FixTerm -- TODO

-- | Unifies a rewrite rule's input with the given term (if valid), then returns
-- the unifying hole substitution.
tryRewrite :: Rewrite -> HoleCtx -> VarCtx -> Syn -> Maybe HoleSub
tryRewrite rew gamma g a = do
  -- check maximum
  guard $ getFix a <= rew.maxFix
  -- unity rewrite input type with term's type
  sigma1 <- unify (gamma <> rew.gamma) g (norm rew.inputType) (norm $ infer gamma g a)
  -- unify rewrite input with term
  sigma2 <- unify
              (substitute sigma1 $ gamma <> rew.gamma)
              (substitute sigma1 g)
              (substitute sigma1 rew.input)
              (substitute sigma1 a)
  return (sigma2 <> sigma1)

rewrites :: [Rewrite]
rewrites =
  [ -- eta-conversion
    makeRewriteRule
      (Ctx $ Map.fromList
        [ (HoleId 0, readSyn "U")
        , (HoleId 1, readSyn "U")
        , (HoleId 2, readSyn "(Π x : ?0 . ?1)")
        , (HoleId 3, readSyn "?0")
        ])
      (readSyn "(λ x : ?0 . (?2 ?3))")
      (readSyn "f")
  ]

-- |
-- == Parsing

readSyn :: String -> Syn
readSyn = unsafeEvalParser parseSyn

newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }

evalParser :: Parser a -> String -> Maybe a
evalParser p = fmap fst . runParser p

unsafeEvalParser :: Parser a -> String -> a
unsafeEvalParser p = fromJust . evalParser p

instance Functor Parser where
  f `fmap` pa = Parser \str0 -> do
    (a, str1) <- runParser pa str0
    return (f a, str1)

instance Applicative Parser where
  pure a = Parser \str -> Just (a, str)
  pf <*> pa = Parser \str0 -> do
    (f, str1) <- runParser pf str0
    (a, str2) <- runParser pa str1
    return (f a, str2)

instance Monad Parser where
  pa >>= k = Parser \str0 -> do
    (a, str1) <- runParser pa str0
    runParser (k a) str1

parseFail :: Parser a
parseFail = Parser \_ -> Nothing

get :: Parser String
get = Parser \str -> return (str, str)

put :: String -> Parser ()
put str = Parser \_ -> return ((), str)

-- |
-- === Parsing Utilities

parseNextChar :: Parser Char
parseNextChar =
  get >>= \case
    [] -> parseFail
    (c : cs) -> put cs >> return c

parseChar :: Char -> Parser ()
parseChar c = do
  c' <- parseNextChar
  unless (c == c') parseFail

parsePredicatedChar :: (Char -> Bool) -> Parser Char
parsePredicatedChar p = do
  c <- parseNextChar
  if p c then return c else parseFail

parseString :: String -> Parser ()
parseString = mapM_ parseChar

parseWhitespace :: Parser ()
parseWhitespace = do
  str0 <- get
  parseTry (parseChar ' ') >>= \case
    Just _ -> parseWhitespace
    Nothing -> put str0 >> return ()

parseNextNonemptyWord :: Parser String
parseNextNonemptyWord = (:) <$> parsePredicatedChar (not . (`elem` separators)) <*> parseNextWord

separators :: [Char]
separators = " ().:="

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
    _ -> parseFail

lexeme :: Parser a -> Parser a
lexeme p = do
  a <- p
  parseWhitespace
  return a

-- | Tries to do a given parser. If the attempts succeeds, then modifies state. Otherwise, resets to the state before attempt.
parseTry :: Parser a -> Parser (Maybe a)
parseTry p = do
  str0 <- get
  case runParser p str0 of
    Just (a, str1) -> put str1 >> return (Just a)
    Nothing -> return Nothing 

-- | Tries each parser in list until one succeeds. If none succeed, then returns Nothing.
parseFirstOf :: [Parser a] -> Parser (Maybe a)
parseFirstOf [] = return Nothing
parseFirstOf (p : ps) = do
  str0 <- get
  parseTry p >>= \case
    Just a -> return $ Just a
    Nothing -> put str0 >> parseFirstOf ps

-- |
-- === Parsing Syntax

parseSyn :: Parser Syn
parseSyn = do
  mb_a <- parseFirstOf 
    [ parseUni
    , parsePi
    , parseLam
    , parseLet
    , parseApp
    , parseHole
    , parseVar ]
  case mb_a of
    Just a -> return a
    Nothing -> parseFail

parseUni, parsePi, parseLam, parseApp, parseVar, parseHole, parseLet :: Parser Syn
parseUni = lexeme do
  parseString "U"
  return $ Uni FixTerm
parsePi = lexeme do
  lexeme $ parseString "("
  lexeme $ parseString "Π"
  x <- parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "."
  beta <- parseSyn
  lexeme $ parseString ")"
  return $ Pi x alpha beta FixTerm
parseLam = do
  lexeme $ parseString "("
  lexeme $ parseString "λ"
  x <- parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "."
  b <- parseSyn
  lexeme $ parseString ")"
  return $ Lam x alpha b FixTerm
parseApp = do
  lexeme $ parseString "("
  f <- parseSyn
  a <- parseSyn
  parseString ")"
  return $ App f a FixTerm
parseVar = do
  x <- parseVarId
  return $ Var x FixTerm
parseLet = do
  lexeme $ parseString "("
  lexeme $ parseString "let"
  x <- parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "="
  a <- parseSyn
  lexeme $ parseString "in"
  b <- parseSyn
  lexeme $ parseString ")"
  return $ Let x alpha a b FixTerm
parseHole = do
  parseString "?"
  h <- parseHoleId
  return $ Hole h mempty FixTerm

parseVarId :: Parser VarId
parseVarId = lexeme $ VarId <$> parseNextNonemptyWord

parseHoleId :: Parser HoleId
parseHoleId = lexeme $ HoleId <$> parseNextInt

-- |
-- == Debugging

debug :: String -> ()
debug = Unsafe.unsafePerformIO . putStrLn
