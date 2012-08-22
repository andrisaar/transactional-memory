
module Parser (parseProgram) where

import Language
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Combinator
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Prim
import Text.ParserCombinators.Parsec.Error

whileDef = javaStyle {
	     reservedNames = ["skip", "while", "do", "if", "then", "else", "spawn", "atomic", "true", "false"],
	     reservedOpNames = ["&&", "||", "==", "<=", "+", "-", "*", ":="]
	   }

while = P.makeTokenParser whileDef

integer = P.integer while
identifier = P.identifier while
reservedOp = P.reservedOp while
parens = P.parens while
reserved = P.reserved while
semiSep1 = P.semiSep1 while
braces = P.braces while
symbol = P.symbol while
whiteSpace = P.whiteSpace while

aexpTable   = [[Infix (do { reservedOp "*"; return (:*) }) AssocLeft],
               [Infix (do { reservedOp "+"; return (:+) }) AssocLeft, 
	        Infix (do { reservedOp "-"; return (:-) }) AssocLeft]
              ]

aexpr :: Parser AExp
aexpr    = buildExpressionParser aexpTable aexpTerm
         <?> "expression"

aexpTerm    =  parens aexpr
            <|> do { n <- integer; return $ N n }
	    <|> do { v <- identifier; return $ V v }
            <?> "arithmetic expression"

bexpTable = [[Prefix (do { reservedOp "!"; return Not })],
             [Infix (do { reservedOp "&&"; return (:&&) }) AssocLeft],
             [Infix (do { reservedOp "||"; return (:||) }) AssocLeft]
            ]

bexpr :: Parser BExp
bexpr = buildExpressionParser bexpTable bexpTerm

bexpTerm = parens bexpr
         <|> do a1 <- aexpr
	        op <- try (do {reservedOp "=="; return (:==) }) <|> do {reservedOp "<="; return (:<=) }
		a2 <- aexpr
		return $ op a1 a2
	 <|> do { reserved "true"; return TT }
	 <|> do { reserved "false"; return FF }
	 <?> "boolean expression"

stmtParser :: Parser Stmt
stmtParser = choice [ 
		try spawnParser,
  	        do { reserved "skip"; return Skip },
		ifParser,
		whileParser,
		atomicParser,
		seqParser,
		try assgnParser
	     ]

assgnParser :: Parser Stmt
assgnParser = do v <- identifier
                 symbol ":="
		 a <- aexpr
		 return $ v := a
              <?> "assignment"

ifParser :: Parser Stmt
ifParser = do reserved "if"
              b <- bexpr
              reserved "then"
              s1 <- stmtParser
              reserved "else"
              s2 <- stmtParser
              return $ If b s1 s2

whileParser :: Parser Stmt
whileParser = do reserved "while"
                 b <- bexpr
		 reserved "do"
		 stmt <- stmtParser
		 return $ While b stmt

atomicParser :: Parser Stmt
atomicParser = do reserved "atomic"
                  stmt <- stmtParser
		  return $ Atomic stmt

spawnParser :: Parser Stmt
spawnParser = do reserved "spawn"
                 stmts <- sepBy stmtParser whiteSpace
		 return $ Spawn stmts

seqParser :: Parser Stmt
seqParser = do stmts <- braces $ semiSep1 stmtParser
               return $ foldl1 (:\) stmts
	    <?> "nested block"


programParser :: Parser Stmt
programParser = do whiteSpace
                   stmts <- semiSep1 stmtParser
		   eof
                   return $ foldl1 (:\) stmts



--parseProgram :: String -> Stmt
--parseProgram s = either (error . show) id $ parse programParser "" s
--
parseProgram = parse programParser
