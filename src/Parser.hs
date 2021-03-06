--The MIT License (MIT)
--
--Copyright (c) 2016-2017 Steffen Michels (mail@steffen-michels.de)
--
--Permission is hereby granted, free of charge, to any person obtaining a copy of
--this software and associated documentation files (the "Software"), to deal in
--the Software without restriction, including without limitation the rights to use,
--copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the
--Software, and to permit persons to whom the Software is furnished to do so,
--subject to the following conditions:
--
--The above copyright notice and this permission notice shall be included in all
--copies or substantial portions of the Software.
--
--THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
--FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
--COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
--IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
--CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Parser
    ( parsePclp
    , rational
    , Exception(..)
    ) where
import AST (AST)
import qualified AST
import qualified Data.HashMap as Map
import IdNrMap (IdNrMap)
import qualified IdNrMap
import Text.Parsec (Parsec)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Exception
import Numeric
import Data.Ratio ((%))
import qualified Statistics.Distribution as Dist
import qualified Statistics.Distribution.Normal as Norm
import Probability
import TextShow
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy.Builder as TB

newtype Exception = InvalidSyntax ParseError
instance TextShow Exception where
    showb (InvalidSyntax err) = TB.fromString $ show err

type P a = Parsec String (IdNrMap Text) a

-- LEXER
languageDef =
    emptyDef { Token.commentStart    = "/*"
             , Token.commentEnd      = "*/"
             , Token.commentLine     = "//"
             , Token.identStart      = lower
             , Token.identLetter     = alphaNum
             , Token.reservedNames   = [ "query", "evidence", "flip"
                                       , "norm", "true", "false"
                                       ]
             , Token.reservedOpNames = [ "~", "+", "<", "<=", ">", ">="
                                       ]
             }

lexer      = Token.makeTokenParser languageDef
identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
braces     = Token.braces     lexer
colon      = Token.colon      lexer
hash       = Token.lexeme     lexer $ string "#"
rational   = Token.lexeme     lexer parseRat
    where
    parseRat :: Parsec String st Rational
    parseRat = do
        neg <- (string "-" >> return True) <|> return False
        rat <- try parseDecimal <|> parseFraction
        spaces
        return $ if neg then -rat else rat
        where
        parseDecimal = do
            int <- decimal
            _ <- string "."
            nFrac <- length <$> lookAhead (many1 digit)
            frac <- decimal
            return $ (fromIntegral int :: Rational) + frac % (10^(fromIntegral nFrac :: Integer))
        parseFraction = do
            num <- integer
            _ <- string "/"
            den <- integer
            return $ num % den
realIneqOp = Token.lexeme lexer parseRealIneqOp
    where
    parseRealIneqOp :: P AST.IneqOp
    parseRealIneqOp =     try (reservedOp "<"  >> return AST.Lt)
                      <|>     (reservedOp "<=" >> return AST.LtEq)
                      <|> try (reservedOp ">"  >> return AST.Gt)
                      <|>     (reservedOp ">=" >> return AST.GtEq)
pFuncL = Token.lexeme     lexer parseUserPFuncLabel
    where
    parseUserPFuncLabel :: P AST.PFuncLabel
    parseUserPFuncLabel = string "~" >> AST.PFuncLabel <$> identifierNumber
decimal    = Token.decimal       lexer
integer    = Token.integer       lexer
stringLit  = Token.stringLiteral lexer
dot        = Token.dot           lexer
comma      = Token.comma         lexer
whiteSpace = Token.whiteSpace    lexer
variable   = Token.lexeme        lexer parseVar
    where
    parseVar = do
        first <- upper
        rest  <- many alphaNum
        return (first:rest)

identifierNumber :: P Int
identifierNumber = do
    ident <- identifier
    (idNr, idMap) <- IdNrMap.getIdNr (T.pack ident) <$> getState
    setState idMap
    return idNr

-- PARSER
parsePclp :: String -> Exceptional Exception (AST, IdNrMap Text)
parsePclp src =
    let initialState = AST.AST
            { AST.pFuncDefs = Map.empty
            , AST.rules     = Map.empty
            , AST.queries   = []
            , AST.evidence  = []
            }
    in mapException InvalidSyntax (fromEither (runParser (theory initialState) IdNrMap.empty "PCLP theory" src))

theory :: AST -> P (AST, IdNrMap Text)
theory ast = whiteSpace >>
    (     try ( do -- query
            q <- query
            let ast' = ast {AST.queries = q : AST.queries ast}
            theory ast'
          )
      <|> try (do --evidence
            e <- evidence
            let ast' = ast {AST.evidence = e : AST.evidence ast}
            theory ast'
          )
      <|> ( do -- probabilistic function definition
            (lbl, args, def) <- pFuncDef
            -- put together defs with same signature
            let ast' = ast {AST.pFuncDefs = Map.insertWith (++) (lbl, length args) [(args, def)] (AST.pFuncDefs ast)}
            theory ast'
          )
      <|> ( do -- rule
            (lbl, args, body) <- rule
            -- put together rules with same head
            let ast' = ast {AST.rules = Map.insertWith (\[x] -> (x :)) (lbl, length args) [(args, body)] (AST.rules ast)}
            theory ast'
          )
      <|> ( do -- end of input
                eof
                (ast,) <$> getState
          )
    )

-- rules
rule :: P (AST.PredicateLabel, [AST.HeadArgument], AST.RuleBody)
rule = do
    (lbl, args) <- userPred headArgument
    body <- option
        []
        (do reservedOp "<-"
            sepBy bodyElement comma
        )
    _ <- dot
    return (lbl, args, AST.RuleBody body)

bodyElement :: P AST.RuleBodyElement
bodyElement =
        AST.BuildInPredicate      <$> try buildInPredicate
    <|> uncurry AST.UserPredicate <$> userPred expression

userPred :: P arg -> P (AST.PredicateLabel, [arg])
userPred argument = do
    lbl  <- predicateLabel
    args <- option [] $ parens $ sepBy argument comma
    return (lbl, args)

predicateLabel :: P AST.PredicateLabel
predicateLabel = AST.PredicateLabel <$> identifierNumber

buildInPredicate :: P AST.BuildInPredicate
buildInPredicate = do
    exprX <- expression
    constr <-     (reservedOp "="  >>         return (AST.Equality True))
              <|> (reservedOp "/=" >>         return (AST.Equality False))
              <|> (realIneqOp      >>= \op -> return $ AST.Ineq op)
    exprY <- expression
    return $ constr exprX exprY

-- pfunc defs
pFuncDef :: P (AST.PFuncLabel, [AST.HeadArgument], AST.PFuncDef)
pFuncDef = do
    (lbl, args) <- pFunc headArgument
    reservedOp "~"
    def <- flipDef <|> normDef <|> strDef <|> objDef <|> objDefUniformOtherObject
    return (lbl, args, def)

pFunc :: P arg -> P (AST.PFuncLabel, [arg])
pFunc argument = do
    lbl  <- pFuncL
    args <- option [] $ parens $ sepBy argument comma
    return (lbl, args)

flipDef :: P AST.PFuncDef
flipDef = do
    reserved "flip"
    prob <- parens $ fromRational <$> rational
    _ <- dot
    return $ AST.Flip prob

normDef :: P AST.PFuncDef
normDef = do
    reserved "norm"
    (m, d) <- parens $ do
         m <- rational
         _ <- comma
         d <- rational
         return (m, d)
    _ <- dot
    return $ AST.RealDist
        (doubleToProb . Dist.cumulative (Norm.normalDistr (fromRat m) (fromRat d)) . fromRat)
        (toRational   . Dist.quantile   (Norm.normalDistr (fromRat m) (fromRat d)) . probToDouble)

strDef :: P AST.PFuncDef
strDef = const <$> braces (AST.StrDist <$> sepBy choicesElement comma) <*> dot
    where
        choicesElement :: P (Probability, Text)
        choicesElement =     ((\p _ s -> (p, T.pack s)) . fromRational <$> rational)
                         <*> colon
                         <*> stringConstant

objDef :: P AST.PFuncDef
objDef = do
    reserved "uniformObjects"
    nr <- parens integer
    _ <- dot
    return $ AST.UniformObjDist nr

objDefUniformOtherObject :: P AST.PFuncDef
objDefUniformOtherObject = do
    reserved "uniformOtherObject"
    (lbl, args) <- parens $ pFunc expression
    _ <- dot
    return $ AST.UniformOtherObjDist lbl args

headArgument :: P AST.HeadArgument
headArgument =     AST.ArgConstant                          <$> constantExpression
               <|> (AST.ArgVariable . AST.VarName . T.pack) <$> variable
               <|> const AST.ArgDontCareVariable            <$> string "_"

-- expressions
expression :: P AST.Expr
expression = buildExpressionParser operators term

operators = [ [Infix  (reservedOp "+" >> return AST.Sum) AssocLeft] ]

term =     AST.ConstantExpr                    <$> constantExpression
       <|> uncurry AST.PFunc                   <$> pFunc expression
       <|> AST.Variable . AST.VarName . T.pack <$> variable

constantExpression :: P AST.ConstantExpr
constantExpression =     const (AST.BoolConstant True)  <$> reserved "true"
                     <|> const (AST.BoolConstant False) <$> reserved "false"
                     <|> AST.StrConstant . T.pack       <$> stringConstant
                     <|> AST.RealConstant               <$> try rational
                     <|> AST.IntConstant                <$> integer
                     <|> AST.ObjConstant                <$> objectConstant

stringConstant = identifier <|> stringLit

objectConstant = hash >> integer

-- queries
query :: P AST.RuleBodyElement
query = do
    reserved "query"
    q <- bodyElement
    _ <- dot
    return q

-- evidence
evidence :: P AST.RuleBodyElement
evidence = do
    reserved "evidence"
    e <- bodyElement
    _ <- dot
    return e
