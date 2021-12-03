{-# LANGUAGE LambdaCase, BlockArguments, OverloadedRecordDot #-}
module Language.BlockTypes.Omega where 

{-
ASSUMPTIONS
- unique variable names
-}

import Control.Monad as Monad
import Data.Map as Map

-- |
-- == Syntax

data Syn
  = Uni Fix
  | Pi VarId Syn Syn Fix
  | Lam VarId Syn Syn Fix
  | App Syn Syn Fix
  | Var VarId Fix
  | Hole HoleId Sub Fix
  | Let VarId Syn Syn Syn Fix
  deriving (Eq)

newtype VarId = VarId String deriving (Eq, Ord) -- x
newtype HoleId = HoleId Int deriving (Eq, Ord) -- h

type Ctx = Map VarId (Syn, Maybe Syn) -- g :: var => type, value?
type Sub = Map VarId Syn -- s :: var => value

type HoleCtx = Map HoleId Syn -- gamma :: hole => type
type HoleSub = Map HoleId Syn -- sigma :: hole => value

-- |
-- == Show

instance Show Syn where
  show = \case
    Uni fix -> "U"
    Pi x alpha beta fix -> "(Π " ++ show x ++ " : " ++ show alpha ++ " . " ++ show beta ++ ")"
    Lam x alpha b fix -> "(λ " ++ show x ++ " : " ++ show alpha ++ " . " ++ show b ++ ")"
    App f a fix -> "(" ++ show f ++ " " ++ show a ++ ")"
    Var x fix -> show x
    Hole h sigma fix -> "?" ++ show h ++ "[" ++ show sigma ++ "]"
    Let x alpha a b fix -> "(let " ++ show x ++ " : " ++ show alpha ++ " = " ++ show a ++ " in " ++ show b ++ ")"

instance Show VarId where
  show (VarId x) = x

instance Show HoleId where
  show (HoleId h) = show h

-- |
-- == Parsing

-- type Parser a = String -> Maybe (String, a)

newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }

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

parseString :: String -> Parser ()
parseString = mapM_ parseChar

parseWhitespace :: Parser ()
parseWhitespace = do
  str0 <- get
  parseTry (parseChar ' ') >>= \case
    Just _ -> parseWhitespace
    Nothing -> put str0 >> return ()

parseNextNonemptyWord :: Parser String
parseNextNonemptyWord = (:) <$> parseNextChar <*> parseNextWord

parseNextWord :: Parser String
parseNextWord = do
  parseTry parseNextChar >>= \case
    Nothing -> return ""
    Just ' ' -> return ""
    Just c -> (c :) <$> parseNextWord

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

-- Tries to do a given parser. If the attempts succeeds, then modifies state. Otherwise, resets to the state before attempt.
parseTry :: Parser a -> Parser (Maybe a)
parseTry p = do
  str0 <- get
  case runParser p str0 of
    Just (a, str1) -> put str1 >> return (Just a)
    Nothing -> return Nothing 

-- Tries each parser in list until one succeeds. If none succeed, then returns Nothing.
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
  return $ Uni Free
parsePi = lexeme do
  lexeme $ parseString "("
  lexeme $ parseString "Π"
  x <- parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "."
  beta <- parseSyn
  lexeme $ parseString ")"
  return $ Pi x alpha beta Free
parseLam = do
  lexeme $ parseString "("
  lexeme $ parseString "λ"
  x <- parseVarId
  lexeme $ parseString ":"
  alpha <- parseSyn
  lexeme $ parseString "."
  b <- parseSyn
  lexeme $ parseString ")"
  return $ Lam x alpha b Free
parseApp = do
  lexeme $ parseString "("
  f <- parseSyn
  a <- parseSyn
  parseString ")"
  return $ App f a Free
parseVar = do
  x <- parseVarId
  return $ Var x Free
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
  return $ Let x alpha a b Free
parseHole = do
  parseString "?"
  h <- parseHoleId
  return $ Hole h mempty Free

parseVarId :: Parser VarId
parseVarId = lexeme $ VarId <$> parseNextNonemptyWord

parseHoleId :: Parser HoleId
parseHoleId = lexeme $ HoleId <$> parseNextInt

test :: Maybe (Syn, String)
test = runParser parseSyn "(Π x : alpha . beta)"

-- |
-- == Normalization

-- inputs/output is normal
-- a [x |-> b]
sub :: Syn -> VarId -> Syn -> Syn 
sub a x b = case a of 
  Uni fix -> Uni fix
  Pi y alpha beta fix -> Pi x (sub alpha x b) (sub beta x b) fix
  Lam y alpha c fix -> Lam x (sub alpha x b) (sub c x b) fix
  App f a fix -> app (sub f x b) (sub a x b)
  Var y fix -> if x == y then b else Var y fix
  Hole h sigma fix -> Hole h (Map.insert x b sigma) fix

-- inputs/output is normal
app :: Syn -> Syn -> Syn
app f a = case f of
  Lam x alpha b fix -> sub b x a
  App f' a' fix -> App (App f' a' fix) a fix
  Var x fix -> App (Var x fix) a fix
  Hole h sigma fix -> App (Hole h sigma fix) a fix

-- output is normal
norm :: Syn -> Syn
norm = \case
  Uni fix -> Uni fix
  Pi x alpha beta fix -> Pi x (norm alpha) (norm beta) fix
  Lam x alpha b fix -> Lam x (norm alpha) (norm b) fix
  App f a fix -> app (norm f) (norm a)
  Var x fix -> Var x fix
  Hole h sigma fix -> Hole h sigma fix
  Let x alpha a b fix -> sub b x (norm a)

-- TODO: use parsing

-- norm_test1 :: Syn
-- norm_test1 = norm $
--   Let (VarId "x") (Uni FixTerm) (Uni FixTerm) 
--     (Var (VarId "x") FixTerm)
--     FixTerm

-- norm_test2 :: Syn
-- norm_test2 = norm $
--   App (Lam "x" (Uni FixTerm) (Var "x" FixTerm) FixTerm)
--       (Var "y" FixTerm) FixTerm

-- |
-- == Renaming

-- Rename x to y in a
rename :: VarId -> VarId -> Syn -> Syn
rename x y = \case
  Uni fix -> Uni fix
  Pi x alpha beta fix -> Pi x (rename x y alpha) (rename x y beta) fix
  Lam x alpha b fix -> Lam x (rename x y alpha) (rename x y b) fix
  App f a fix -> App (rename x y f) (rename x y a) fix
  Var x' fix -> if x == x' then Var y fix else Var x' fix
  Hole h sigma' fix -> Hole h (renameSub x y sigma') fix
  Let x alpha a b fix -> Let x (rename x y alpha) (rename x y a) (rename x y b) fix

renameSub :: VarId -> VarId -> Sub -> Sub
renameSub x y =
  Map.mapKeys (\x' -> if x == x' then y else x') .
  Map.map (rename x y)

-- |
-- == Substitution

-- Doesn't normalize things..
applySub :: Sub -> Syn -> Syn
applySub s = \case
  Uni fix -> Uni fix
  Pi x alpha beta fix -> Pi x (applySub s alpha) (applySub s beta) fix
  Lam x alpha b fix -> Lam x (applySub s alpha) (applySub s b) fix
  App f a fix -> App (applySub s f) (applySub s a) fix
  Var x fix -> case s !? x of
    Just a -> a
    Nothing -> Var x fix
  Hole h s' fix -> Hole h (s' <> s) fix
  Let x alpha a b fix -> Let x (applySub s alpha) (applySub s a) (applySub s b) fix

applyHoleSub :: HoleSub -> Syn -> Syn 
applyHoleSub sigma = \case
  Uni fix -> Uni fix
  Pi x alpha beta fix -> Pi x (applyHoleSub sigma alpha) (applyHoleSub sigma beta) fix
  Lam x alpha b fix -> Lam x (applyHoleSub sigma alpha) (applyHoleSub sigma b) fix
  App f a fix -> App (applyHoleSub sigma f) (applyHoleSub sigma a) fix
  Var x fix -> Var x fix
  Hole h s fix -> case sigma !? h of 
    Just a -> applySub s a
    Nothing -> Hole h s fix

applyHoleSubToHoleCtx :: HoleSub -> HoleCtx -> HoleCtx
applyHoleSubToHoleCtx sigma gamma = 
  Map.map (applyHoleSub sigma) $
  Prelude.foldl (flip Map.delete) gamma (Map.keys sigma)

applyHoleSubToCtx :: HoleSub -> Ctx -> Ctx
applyHoleSubToCtx sigma = Map.map \(alpha, mb_a) ->
  (applyHoleSub sigma alpha, applyHoleSub sigma <$> mb_a)

-- None of the keys in sigma1 appear in the keys or values of sigma2
joinHoleSub :: HoleSub -> HoleSub -> HoleSub
joinHoleSub sigma2 sigma1 = Map.map (applyHoleSub sigma2) sigma1 <> sigma2

-- |
-- == Unification

unify :: HoleCtx -> Ctx -> Syn -> Syn -> Maybe HoleSub
unify gamma g a a' = case (a, a') of 
  (Uni fix, Uni fix') -> return mempty
  (Pi x alpha beta fix, Pi x' alpha' beta' fix') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <-
      unify
        gamma
        (Map.insert x (applyHoleSub sigma1 alpha, mzero) g)
        beta
        (rename x' x beta')
    return $ sigma1 `joinHoleSub` sigma2
  (Lam x alpha b fix, Lam x' alpha' b' fix') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <-
      unify
        gamma
        (Map.insert x (applyHoleSub sigma1 alpha, mzero) g)
        b
        (rename x' x b')
    return $ sigma1 `joinHoleSub` sigma2
  (App f a fix, App f' a' fix') -> do
    sigma1 <- unify gamma g f f'
    sigma2 <- unify gamma g a a'
    return $ sigma1 `joinHoleSub` sigma2
  (Var x fix, Var x' fix') ->
    if x == x' then return mempty else mzero
  (Let x alpha a b fix, Let x' alpha' a' b' fix') -> do
    sigma1 <- unify gamma g alpha alpha'
    sigma2 <-
      unify
        (applyHoleSubToHoleCtx sigma1 gamma)
        (applyHoleSubToCtx sigma1 g)
        (applyHoleSub sigma1 a)
        (applyHoleSub sigma1 a')
    sigma3 <-
      unify
        (applyHoleSubToHoleCtx (sigma2 `joinHoleSub` sigma1) gamma)
        (applyHoleSubToCtx (sigma2 `joinHoleSub` sigma1) g)
        (applyHoleSub (sigma2 `joinHoleSub` sigma1) b)
        (applyHoleSub (sigma2 `joinHoleSub` sigma1) (rename x' x b'))
    return $ sigma1 `joinHoleSub` sigma2 `joinHoleSub` sigma3
  (Hole h sigma fix, a') | Map.null sigma -> return $ Map.singleton h a'
  (a, Hole h' sigma' fix') | Map.null sigma' -> return $ Map.singleton h' a
  _ -> mzero
  
  -- |
  -- == Inference

-- Returns a type in normal form
infer :: HoleCtx -> Ctx -> Syn -> Syn
infer gamma g = \case
  Uni fix -> Uni fix
  Pi x alpha beta fix -> Uni fix
  Lam x alpha b fix -> Pi x alpha (infer gamma (Map.insert x (alpha, Nothing) g) b) fix
  App f a fix -> case infer gamma g f of Pi x alpha beta fix -> sub beta x (norm a)
  Var x fix -> norm (fst (g ! x))
  Hole h sigma fix -> norm $ gamma ! h
  Let x alpha a b fix -> infer gamma (Map.insert x (alpha, Just a) g) b

-- |
-- == Fixity

-- free < type < term
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

-- Updates the fixity of subterms.
updateFix :: Fix -> Syn -> Syn
updateFix fix = \case
  Uni _ -> Uni fix
  Pi x alpha beta _ ->
    let
      fix_alpha = if fix == FixTerm || getFixIn x beta' >= FixType then FixTerm else FixType
      fix_beta = if fix == FixTerm then FixTerm else FixType
      beta' = updateFix fix_beta beta
    in
      Pi x (updateFix fix_alpha alpha) beta' fix
  Lam x alpha b _ ->
    let
      fix_alpha = if fix >= FixType || getFixIn x b' >= FixType then FixTerm else FixType
      fix_b = fix
      b' = updateFix fix_b b
    in
      Lam x (updateFix fix_alpha alpha) b' fix
  App f a _ -> App (updateFix fix f) (updateFix fix a) fix
  Var x _ -> Var x fix -- TODO: depends if type is a hole
  Hole h s _ -> Hole h s fix -- TODO: depends if substitution is empty or not
  Let x alpha a b _ ->
    let
      fix_alpha = if getFixIn x b' >= FixType then FixTerm else FixType
      fix_a = if getFixIn x b' == FixTerm then FixTerm else
              if getFixIn x b' == FixType then FixType
              else Free
      fix_b = fix
      b' = updateFix fix_b b
    in
      Let x (updateFix fix_alpha alpha) (updateFix fix_a a) b' fix

isHole :: Syn -> Bool
isHole = \case 
  Hole _ _ _ -> True
  _ -> False

-- |
-- == Rewriting

-- `gamma |- input{maxFix} ~> output{maxFix}`
data Rewrite = Rewrite
  { gamma :: HoleCtx
  , maxFix :: Fix
  , input :: Syn
  , inputType :: Syn
  , output :: Syn }
  deriving (Show)

-- Makes a rewrite rule in this form:
-- `gamma |- input{fix <= maxFix} ~> output{fix <= maxFix}`
makeRewriteRule :: HoleCtx -> Syn -> Syn -> Rewrite
makeRewriteRule gamma input output = Rewrite
  { gamma
  , maxFix = inferMaxFix gamma input output
  , input
  , inputType = infer gamma mempty input
  , output }

-- Infers the maximumity of for the input/output of a rewrite rule.
inferMaxFix :: HoleCtx -> Syn -> Syn -> Fix
inferMaxFix gamma input output = FixTerm -- TODO

-- Unifies a rewrite rule's input with the given term (if valid), then returns
-- the unifying hole substitution.
tryRewrite :: Rewrite -> HoleCtx -> Ctx -> Syn -> Maybe HoleSub
tryRewrite rew gamma g a = do
  -- check maximum
  guard $ getFix a <= rew.maxFix
  -- unity rewrite input type with term's type
  sigma1 <- unify (gamma <> rew.gamma) g rew.inputType (infer gamma g a)
  -- unify rewrite input with term
  sigma2 <-
    unify
      (applyHoleSubToHoleCtx sigma1 $ gamma <> rew.gamma)
      (applyHoleSubToCtx sigma1 g)
      (applyHoleSub sigma1 rew.input)
      (applyHoleSub sigma1 a)
  return (sigma1 `joinHoleSub` sigma2)

-- rewrites :: [Rewrite]
-- rewrites =
--   [ makeRewriteRule


--   ]