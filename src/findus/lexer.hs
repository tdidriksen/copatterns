module Lexer where

import Text.Parsec
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Language (haskellStyle)

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where ops = ["->", "|", "=", ":", "(", ")", ",", "{", "}"]
        style = haskellStyle{
                             Tok.reservedOpNames = ops,
                             Tok.reservedNames = keywords,
                             Tok.commentLine = "--"
                            }
keywords = ["let", "in", "end", "case", "of", "observe", "as", "data", "codata"]

lexeme :: Parser a -> Parser a
lexeme = Tok.lexeme lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

braces :: Parser a -> Parser a
braces = Tok.braces lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

identifier :: Parser String
identifier = Tok.identifier lexer

reservedKw :: Parser ()
reservedKw = foldr1 (<|>) (map reserved keywords)