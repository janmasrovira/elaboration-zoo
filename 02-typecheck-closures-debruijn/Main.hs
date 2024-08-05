{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Use <$>" #-}
module Main where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L
import Text.Printf
import Prelude hiding (lookup)

-- examples
--------------------------------------------------------------------------------

ex0 :: IO ()
ex0 =
  main' "nf" $
    unlines
      [ "let id : (A : Type) -> A -> A",
        "     = \\A x. x;",
        "let foo : Type = Type;",
        "let bar : Type = id id;", -- we cannot apply any function to itself (already true in simple TT)
        "id"
      ]

-- basic polymorphic functions
ex1 :: IO ()
ex1 =
  main' "nf" $
    unlines
      [ "let id : (A : Type) -> A -> A",
        "      = \\A x. x;",
        "let const : (A B : Type) -> A -> B -> A",
        "      = \\A B x y. x;",
        "id ((A B : Type) -> A -> B -> A) const"
      ]

-- Church-coded natural numbers (standard test for finding eval bugs)
ex2 :: IO ()
ex2 =
  main' "nf" $
    unlines
      [ "let Nat  : Type = (N : Type) -> (N -> N) -> N -> N;",
        "let five : Nat = \\N s z. s (s (s (s (s z))));",
        "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);",
        "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z;",
        "let ten      : Nat = add five five;",
        "let hundred  : Nat = mul ten ten;",
        "let thousand : Nat = mul ten hundred;",
        "thousand"
      ]

-- syntax
--------------------------------------------------------------------------------

-- Minimal bidirectional elaboration
--   surface syntax vs core syntax
--      (intermediate: raw syntax -->(scope checking) -->raw syntax with indices
--   (our case: difference: no de Bruijn indices in surface syntax, but they're in core syntax)

-- | De Bruijn index.
newtype Ix = Ix Int deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

type Name = String

data Raw
  = RVar Name -- x
  | RLam Name Raw -- \x. t
  | RApp Raw Raw -- t u
  | RU -- Type
  | RPi Name Raw Raw -- (x : A) -> B
  | RLet Name Raw Raw Raw -- let x : A = t; u
  | RSrcPos SourcePos Raw -- source position for error reporting
  deriving stock (Show)

-- core syntax
------------------------------------------------------------

data Term
  = Var Ix
  | Lam Name Term
  | App Term Term
  | Type
  | Pi Name Term Term
  | Let Name Term Term Term

-- values
------------------------------------------------------------

type Env = [Value]

data Closure = Closure Env Term

type ValueType = Value

data Value
  = VVar Lvl
  | VApp Value Value
  | VLam Name {-# UNPACK #-} !Closure
  | VPi Name ValueType {-# UNPACK #-} !Closure
  | VType

--------------------------------------------------------------------------------

infixl 8 $$

($$) :: Closure -> Value -> Value
($$) (Closure env t) u = eval (u : env) t

eval :: Env -> Term -> Value
eval env = \case
  Var (Ix x) -> env !! x
  App t u -> case (eval env t, eval env u) of
    (VLam _ t', u') -> t' $$ u'
    (t', u') -> VApp t' u'
  Lam x t -> VLam x (Closure env t)
  Pi x a b -> VPi x (eval env a) (Closure env b)
  Let _ _ t u -> eval (eval env t : env) u
  Type -> VType

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quote :: Lvl -> Value -> Term
quote l = \case
  VVar x -> Var (lvl2Ix l x)
  VApp t u -> App (quote l t) (quote l u)
  VLam x t -> Lam x (quote (l + 1) (t $$ VVar l))
  VPi x a b -> Pi x (quote l a) (quote (l + 1) (b $$ VVar l))
  VType -> Type

nf :: Env -> Term -> Term
nf env t = quote (Lvl (length env)) (eval env t)

-- | Beta-eta conversion checking. Precondition: both values have the same type.
conversion :: Lvl -> Value -> Value -> Bool
conversion l t u = case (t, u) of
  (VType, VType) -> True
  (VPi _ a b, VPi _ a' b') ->
    conversion l a a'
      && conversion (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VLam _ t1, VLam _ t2) ->
    conversion (l + 1) (t1 $$ VVar l) (t2 $$ VVar l)
  (VLam _ t', u') ->
    conversion (l + 1) (t' $$ VVar l) (VApp u' (VVar l))
  (u', VLam _ t') ->
    conversion (l + 1) (VApp u' (VVar l)) (t' $$ VVar l)
  (VVar x, VVar x') -> x == x'
  (VApp t1 u1, VApp t2 u2) -> conversion l t1 t2 && conversion l u1 u2
  (VType, VVar {}) -> False
  (VType, VApp {}) -> False
  (VType, VPi {}) -> False
  (VPi {}, VVar {}) -> False
  (VPi {}, VApp {}) -> False
  (VPi {}, VType {}) -> False
  (VVar {}, VApp {}) -> False
  (VVar {}, VPi {}) -> False
  (VVar {}, VType {}) -> False
  (VApp {}, VPi {}) -> False
  (VApp {}, VType {}) -> False
  (VApp {}, VVar {}) -> False
  -- _ -> False

-- Elaboration
--------------------------------------------------------------------------------

-- type of every variable in scope
type Types = [(Name, ValueType)]

-- | Elaboration context.
data Cxt = Cxt
  { env :: Env,
    types :: Types,
    lvl :: Lvl,
    pos :: SourcePos
  }

-- "unzipped" Cxt definition, for performance reason (also for convenience)

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] [] 0

-- | Extend Cxt with a bound variable.
bind :: Name -> ValueType -> Cxt -> Cxt
bind var varTy (Cxt env types l pos) =
  Cxt (VVar l : env) ((var, varTy) : types) (l + 1) pos

-- | Extend Cxt with a definition.
define :: Name -> Value -> ValueType -> Cxt -> Cxt
define var varDef varTy (Cxt env types l pos) =
  Cxt (varDef : env) ((var, varTy) : types) (l + 1) pos

-- | Typechecking monad. We annotate the error with the current source position.
type M = Either (String, SourcePos)

report :: Cxt -> String -> M a
report cxt msg = Left (msg, pos cxt)

showVal :: Cxt -> Value -> String
showVal cxt v = prettyTm 0 (map fst (types cxt)) (quote (lvl cxt) v) []

-- bidirectional algorithm:
--   use check when the type is already known
--   use infer if the type is unknown
-- (original Hindley-Milner does not use bidirectionality)
-- (even if you don't strictly need bidir, it's faster and has better errors)

check :: Cxt -> Raw -> ValueType -> M Term
check cxt ttop tytop = case (ttop, tytop) of
  -- setting the source pos
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a
  -- checking Lam with Pi type (canonical checking case)
  -- (\x. t) : ((x : A) -> B)
  (RLam x t, VPi _ a b) ->
    Lam x <$> check (bind x a cxt) t (b $$ VVar (lvl cxt))
  -- go under a binder as usual

  -- fall-through checking
  (RLet var lty varBody body, a') -> do
    -- let x : lty = t in body
    lty' <- check cxt lty VType
    let valLty' = eval (env cxt) lty'
    varBody' <- check cxt varBody valLty'
    let varBodyVal' = eval (env cxt) varBody'
    body' <- check (define var varBodyVal' valLty' cxt) body a'
    pure (Let var lty' varBody' body')

  -- only Lam and Let is checkable
  -- if the term is not checkable, we switch to infer (change of direction)
  _ -> do
    (ttop', inferredTy) <- infer cxt ttop
    unless (conversion (lvl cxt) inferredTy tytop) $
      report
        cxt
        ( printf
            "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
            (showVal cxt tytop)
            (showVal cxt inferredTy)
        )
    return ttop'

infer :: Cxt -> Raw -> M (Term, ValueType)
infer cxt = \case
  RSrcPos pos t -> infer (cxt {pos = pos}) t
  RVar x -> do
    let go i = \case
          [] -> report cxt ("variable out of scope: " ++ x)
          (x', a) : tys
            | x == x' -> pure (Var i, a)
            | otherwise -> go (i + 1) tys
    go 0 (types cxt)
  RU -> pure (Type, VType) -- Type : Type rule
  RApp appl appr -> do
    (l', lty) <- infer cxt appl
    case lty of
      VPi _ a b -> do
        appr' <- check cxt appr a
        pure (App l' appr', b $$ eval (env cxt) appr') -- t u : B[x |-> u]
      tty ->
        report cxt $ "Expected a function type, instead inferred:\n\n  " ++ showVal cxt tty
  RLam {} -> report cxt "Can't infer type for lambda expression"
  RPi x pil pir -> do
    pil' <- check cxt pil VType
    pir' <- check (bind x (eval (env cxt) pil') cxt) pir VType
    pure (Pi x pil' pir', VType)
  RLet var varType varTerm body -> do
    varType' <- check cxt varType VType
    let valVarType = eval (env cxt) varType'
    t <- check cxt varTerm valVarType
    let vt = eval (env cxt) t
    (u, uty) <- infer (define var vt valVarType cxt) body
    pure (Let var varType' t u, uty)

-- printing
--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns = \case
  "_" -> "_"
  x
    | elem x ns -> fresh ns (x ++ "'")
    | otherwise -> x

-- printing precedences
atomp :: Int
atomp = 3 -- Type, var

appp :: Int
appp = 2 -- application

pip :: Int
pip = 1 -- pi

letp :: Int
letp = 0 -- let, lambda

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Term -> ShowS
prettyTm prec = go prec
  where
    piBind ns x a =
      showParen True ((x ++) . (" : " ++) . go letp ns a)

    goLam :: [Name] -> Term -> ShowS
    goLam ns = \case
      Lam (fresh ns -> x) t -> (' ' :) . (x ++) . goLam (x : ns) t
      t -> (". " ++) . go letp ns t

    goPi :: [Name] -> Term -> ShowS
    goPi ns = \case
      Pi "_" a b -> (" → " ++) . go appp ns a . (" → " ++) . go pip ("_" : ns) b
      Pi (fresh ns -> x) a b -> piBind ns x a . goPi (x : ns) b
      b -> (" → " ++) . go pip ns b

    go :: Int -> [Name] -> Term -> ShowS
    go p goNames = \case
      Var (Ix x) -> ((goNames !! x) ++)
      App t u -> par p appp $ go appp goNames t . (' ' :) . go atomp goNames u
      Lam (fresh goNames -> x) t -> par p letp $ ("λ " ++) . (x ++) . goLam (x : goNames) t
      Type -> ("Type" ++)
      Pi "_" a b -> par p pip $ go appp goNames a . (" → " ++) . go pip ("_" : goNames) b
      Pi (fresh goNames -> x) a b -> par p pip $ piBind goNames x a . goPi (x : goNames) b
        where
      Let (fresh goNames -> x) a t u ->
        par p letp $
          ("let " ++)
            . (x ++)
            . (" : " ++)
            . go letp goNames a
            . ("\n    = " ++)
            . go letp goNames t
            . ("\n;\n" ++)
            . go letp (x : goNames) u

instance Show Term where showsPrec p = prettyTm p []

-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

lexeme :: Parser a -> Parser a
lexeme = L.lexeme ws

symbol :: String -> Parser String
symbol s = lexeme (C.string s)

char :: Char -> Parser Char
char c = lexeme (C.char c)

parens :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'

pArrow ::Parser String
pArrow = symbol "→" <|> symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "Type"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  void (C.string kw)
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Raw
pAtom =
  withPos ((RVar <$> pIdent) <|> (RU <$ symbol "Type"))
    <|> parens pRaw

pBinder :: Parser Name
pBinder = pIdent <|> symbol "_"

pSpine :: Parser Raw
pSpine = foldl1 RApp <$> some pAtom

pLam :: Parser Raw
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RLam t xs)

pPi :: Parser Raw
pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

funOrSpine :: Parser Raw
funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _ -> RPi "_" sp <$> pRaw

pLet :: Parser Raw
pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol "="
  t <- pRaw
  symbol ";"
  u <- pRaw
  pure $ RLet x a t u

pRaw :: Parser Raw
pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)

pSrc :: Parser Raw
pSrc = ws *> pRaw <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm <- parseString file
  pure (tm, file)

-- main
--------------------------------------------------------------------------------

displayError :: String -> (String, SourcePos) -> IO ()
displayError file (msg, SourcePos path (unPos -> linum) (unPos -> colnum)) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n" lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

helpMsg :: String
helpMsg =
  unlines
    [ "usage: elabzoo-typecheck-closures-debruijn [--help|nf|type]",
      "  --help : display this message",
      "  nf     : read & typecheck expression from stdin, print its normal form and type",
      "  type   : read & typecheck expression from stdin, print its type"
    ]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err -> displayError file err
        Right (term, ty) -> do
          print $ nf [] term
          putStrLn "  :"
          print $ quote 0 ty
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err -> displayError file err
        Right (_, ty) -> print $ quote 0 ty
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
