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
  = Uni
  | Pi VarId Syn Syn
  | Lam VarId Syn Syn
  | App Syn Syn
  | Var VarId
  | Hole HoleId VarSub
  | Let VarId Syn Syn Syn
  deriving (Eq)

newtype VarId = VarId String deriving (Eq, Ord) -- x
newtype HoleId = HoleId Int deriving (Eq, Ord, Num) -- h

instance Show Syn where
  show = \case
    Uni -> "U"
    Pi x alpha beta -> "(Π " ++ show x ++ " : " ++ show alpha ++ " . " ++ show beta ++ ")"
    Lam x alpha b -> "(λ " ++ show x ++ " : " ++ show alpha ++ " . " ++ show b ++ ")"
    App f a -> "(" ++ show f ++ " " ++ show a ++ ")"
    Var x -> show x
    Hole h s -> "?" ++ show h ++ if s == mempty then "" else show s
    Let x alpha a b -> "(let " ++ show x ++ " : " ++ show alpha ++ " = " ++ show a ++ " in " ++ show b ++ ")"

instance Show VarId where
  show (VarId x) = x

instance Show HoleId where
  show (HoleId h) = show h

-- |
-- === Holes

refreshHoles :: HoleId -> Syn -> Syn
refreshHoles h = \case
  Uni -> Uni
  Pi x alpha beta -> Pi x (refreshHoles h alpha) (refreshHoles h beta)
  Lam x alpha b -> Lam x (refreshHoles h alpha) (refreshHoles h b)
  App f a -> App (refreshHoles h f) (refreshHoles h a)
  Var x -> Var x
  Hole h' s -> Hole (h + h') s
  Let x alpha a b -> Let x (refreshHoles h alpha) (refreshHoles h a) (refreshHoles h b)

refreshHoleCtx :: HoleId -> HoleCtx -> HoleCtx
refreshHoleCtx h (Ctx ctx) =
  Ctx .
  Map.fromList .
  List.map (\(h', a) -> (h + h', refreshHoles h a)) .
  Map.toList 
  $ ctx

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
                  VarCtxItem{typ=substitute sigma1 alpha, val=mzero}
                  (substitute sigma1 g))
                (substitute sigma1 beta)
                (rename x' x (substitute sigma1 beta'))
    return $ sigma2 <> sigma1
  (Lam x alpha b, Lam x' alpha' b') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <- unify
                (substitute sigma1 gamma)
                (insert x
                  VarCtxItem{typ=substitute sigma1 alpha, val=mzero}
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
    beta = infer gamma (insert x VarCtxItem{ typ = alpha , val = Nothing} g) b
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

-- | `gamma |- input{maxFix} ~> output{maxFix}`
-- TODO: how to keep track of the local bindings in the contexts of some holes?
data Rewrite = Rewrite
  { gamma :: HoleCtx
  , maxFix :: Fix
  , input :: Syn
  , output :: Syn }

-- | Makes a rewrite rule in this form:
-- `gamma |- input{fix <= maxFix} ~> output{fix <= maxFix}`
makeRewriteRule :: HoleCtx -> Syn -> Syn -> Rewrite
makeRewriteRule gamma input output = Rewrite
  { gamma
  , maxFix = inferMaxFix gamma input output
  , input
  , output }

-- | Infers the maximumity of for the input/output of a rewrite rule.
inferMaxFix :: HoleCtx -> Syn -> Syn -> Fix
inferMaxFix gamma input output = FixTerm -- TODO

-- | Unifies a rewrite rule's input with the given term (if valid), then returns
-- the unifying hole substitution.
tryRewrite :: HoleId -> Rewrite -> HoleCtx -> VarCtx -> Fix -> Syn -> Maybe HoleSub
tryRewrite h rew gamma g fix a = do
  -- check maximum
  guard $ fix <= rew.maxFix
  -- unity rewrite input type with term's type
  let inputType = infer rew.gamma mempty (refreshHoles h rew.input)
  let alpha = infer gamma g a
  sigma1 <- unify (gamma <> refreshHoleCtx h rew.gamma) g (norm inputType) (norm $ alpha)
  -- unify rewrite input with term
  sigma2 <- unify
              (substitute sigma1 $ gamma <> refreshHoleCtx h rew.gamma)
              (substitute sigma1 g)
              (substitute sigma1 $ refreshHoles h rew.input)
              (substitute sigma1 a)
  return (sigma2 <> sigma1)

rewrites :: [Rewrite]
rewrites =
  [ -- η-conversion
    makeRewriteRule
      (Ctx $ Map.fromList
        [ (0, readSyn "U")
        , (1, readSyn "U")
        , (2, readSyn "(Π x : ?0 . ?1)")
        , (3, readSyn "?0")
        ])
      (readSyn "(λ x : ?0 . (?2 ?3))")
      (readSyn "f")
  , -- β-conversion
    makeRewriteRule
      (Ctx $ Map.fromList
        [ (0, readSyn "U") -- A
        , (1, readSyn "U") -- B
        , (2, readSyn "?0") -- a
        , (3, readSyn "?1") -- b
        ])
      (readSyn "((λ x : ?0 . ?2) ?3)")
      (readSyn "?2[x = ?3]")
  ]

rewrite_test1 :: (Syn, HoleSub, Syn)
rewrite_test1 = 
  let a = readSyn "((λ x : U . x) U)"
      Just sigma = tryRewrite 0 (rewrites!!1) mempty mempty Free a
      a' = substitute sigma (rewrites!!1).output
  in (a, sigma, a')

rewrite_test2 :: (Syn, HoleSub, Syn)
rewrite_test2 = 
  let a = readSyn "((λ x : U . x) (λ y : U . y))"
      Just sigma = tryRewrite 0 (rewrites!!1) mempty mempty Free a
      a' = substitute sigma (rewrites!!1).output
  in (a, sigma, a')

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
  return $ Uni 
parsePi = lexeme do
  lexeme $ parseString "("
  lexeme $ parseString "Π"
  x <- parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "."
  beta <- parseSyn
  lexeme $ parseString ")"
  return $ Pi x alpha beta 
parseLam = do
  lexeme $ parseString "("
  lexeme $ parseString "λ"
  x <- parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "."
  b <- parseSyn
  lexeme $ parseString ")"
  return $ Lam x alpha b 
parseApp = do
  lexeme $ parseString "("
  f <- parseSyn
  a <- parseSyn
  parseString ")"
  return $ App f a 
parseVar = do
  x <- parseVarId
  return $ Var x 
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
  return $ Let x alpha a b 
parseHole = do
  parseString "?"
  h <- parseHoleId
  parseTry parseVarSub >>= \case
    Just s -> return $ Hole h s 
    Nothing -> return $ Hole h mempty

parseVarId :: Parser VarId
parseVarId = lexeme $ VarId <$> parseNextNonemptyWord

parseHoleId :: Parser HoleId
parseHoleId = lexeme $ HoleId <$> parseNextInt

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
