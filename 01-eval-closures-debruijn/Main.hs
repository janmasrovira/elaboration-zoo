{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Main where

import Control.Applicative hiding (many, some)
import Data.Char
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L
import Prelude hiding (length, lookup)
import Data.Functor

-- | De Bruijn index.
newtype Ix = Ix Int
  deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

data Tm
  = Var Ix
  | Lam Tm -- lam (x.t)
  | App Tm Tm
  | Let Tm Tm -- let t (x.u)

data Env
  = Nil
  | Define Env Val -- list of lazy value

data Closure
  = Closure Env Tm

data Val
  = VVar Lvl
  | VApp Val Val
  | VLam {-# UNPACK #-} !Closure

--------------------------------------------------------------------------------

length :: Env -> Lvl
length = go 0
  where
    go :: Lvl -> Env -> Lvl
    go acc Nil = acc
    go acc (Define env _) = go (acc + 1) env

lookup :: Env -> Ix -> Val
lookup e n = case e of
  Define env v
   | n == 0 -> v
   | otherwise -> lookup env (n - 1)
  Nil -> error "index out of scope"

applyClosure :: Closure -> Val -> Val
applyClosure (Closure env t) u = eval (Define env u) t

eval :: Env -> Tm -> Val
eval env = \case
  Var x -> lookup env x
  App t u -> case (eval env t, eval env u) of -- eval-apply
    (VLam t', u') -> applyClosure t' u'
    (t', u') -> VApp t' u'
  Lam t -> VLam (Closure env t)
  Let t u -> eval (Define env (eval env t)) u

-- Normalization
--------------------------------------------------------------------------------

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl l) (Lvl x) = Ix (l - x - 1)

 -- normalization-by-evaulation
quote :: Lvl -> Val -> Tm
quote l = \case
  VVar x -> Var (lvlToIx l x)
  VApp t u -> App (quote l t) (quote l u)
  VLam closure -> Lam (quote (l + 1) (applyClosure closure (VVar l)))

nf :: Env -> Tm -> Tm
nf env t =
  let t' = eval env t
  in quote (length env) t'

-- ("\\" works for lambda as well)
ex :: IO ()
ex =
  main' "nf" $
    unlines
      [ "let λ λ 1 (1 (1 (1 (1 0))));", -- five = λ s z. s (s (s (s (s z))))
        "let λ λ λ λ 3 1 (2 1 0);", -- add  = λ a b s z. a s (b s z)
        "let λ λ λ λ 3 (2 1) 0;", -- mul  = λ a b s z. a (b s) z
        "let 1 2 2;", -- ten  = add five five
        "let 1 0 0;", -- hundred = mul ten ten
        "let 2 1 0;", -- thousand = mul ten hundred
        "0" -- thousand
      ]

-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme ws

symbol :: String -> Parser String
symbol s = lexeme (C.string s)

char :: Char -> Parser Char
char c = lexeme (C.char c)

parens :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'

pKeyword :: String -> Parser ()
pKeyword kw = do
  void (C.string kw)
  (takeWhile1P Nothing isDigit *> empty) <|> ws

pIx :: Parser Ix
pIx = lexeme L.decimal

pAtom :: Parser Tm
pAtom = (Var <$> pIx) <|> parens pTm

pSpine :: Parser Tm
pSpine = foldl1 App <$> some pAtom

pLam :: Parser Tm
pLam = do
  void (char 'λ' <|> char '\\')
  Lam <$> pTm

pLet :: Parser Tm
pLet = do
  pKeyword "let"
  t <- pTm
  pKeyword ";"
  u <- pTm
  pure $ Let t u

pTm :: Parser Tm
pTm = pLam
  <|> pLet
  <|> pSpine

pSrc :: Parser Tm
pSrc = ws *> pTm <* eof

parseString :: String -> IO Tm
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO Tm
parseStdin = parseString =<< getContents

-- printing
--------------------------------------------------------------------------------

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0)
  where
    goArg = go True

    goLam (Lam t) = ("λ " ++) . goLam t
    goLam t = go False t

    go :: Bool -> Tm -> ShowS
    go p = \case
      Var x -> (show x ++)
      App (App t u) u' -> showParen p (go False t . (' ' :) . goArg u . (' ' :) . goArg u')
      App t u -> showParen p (go True t . (' ' :) . goArg u)
      Lam t -> showParen p (("λ " ++) . goLam t)
      Let t u -> ("let " ++) . go False t . ("\n;\n" ++) . go False u

instance Show Tm where showsPrec = prettyTm

-- main
--------------------------------------------------------------------------------

helpMsg :: String
helpMsg =
  unlines
    [ "usage: elabzoo-eval [--help|nf]",
      "  --help : display this message",
      "  nf     : read expression from stdin, print its normal form"
    ]

mainWith :: IO [String] -> IO Tm -> IO ()
mainWith getOpt getTm = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> print . nf Nil =<< getTm
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) (parseString src)
