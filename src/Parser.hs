--The MIT License (MIT)
--
--Copyright (c) 2016 Steffen Michels (mail@steffen-michels.de)
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
    ) where
import AST (AST)
import qualified AST
import qualified Data.HashMap.Lazy as Map
import qualified Data.HashSet as Set
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Exception
import Numeric
import Text.Printf (printf)
import BasicTypes
import Data.Ratio ((%))
import qualified Statistics.Distribution as Dist
import qualified Statistics.Distribution.Normal as Norm
--import Interval (Interval, IntervalLimit(..))

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
rational   = Token.lexeme     lexer parseRat
    where
    parseRat :: Parser Rational
    parseRat = do
        neg <- (string "-" >> return True) <|> return False
        rat <- try parseDecimal <|> parseFraction
        spaces
        return $ if neg then -rat else rat
        where
        parseDecimal = do
            before <- decimal
            _ <- string "."
            after <- many1 digit
            return $ (fst . head . readFloat) (printf "%i.%s" before after)
        parseFraction = do
            before <- integer
            _ <- string "/"
            after <- integer
            return $ before % after
realIneqOp = Token.lexeme     lexer parseRealIneqOp
    where
    parseRealIneqOp :: Parser AST.IneqOp
    parseRealIneqOp =     try (reservedOp "<"  >> return AST.Lt)
                      <|>     (reservedOp "<=" >> return AST.LtEq)
                      <|> try (reservedOp ">"  >> return AST.Gt)
                      <|>     (reservedOp ">=" >> return AST.GtEq)
rFuncL = Token.lexeme     lexer parseUserRFuncLabel
    where
    parseUserRFuncLabel :: Parser AST.RFuncLabel
    parseUserRFuncLabel = string "~" >> AST.RFuncLabel <$> identifier
decimal    = Token.decimal    lexer
integer    = Token.integer    lexer
dot        = Token.dot        lexer
comma      = Token.comma      lexer
whiteSpace = Token.whiteSpace lexer
variable   = Token.lexeme     lexer parseVar
    where
    parseVar = do
        first <- upper
        rest  <- many alphaNum
        return (first:rest)

-- PARSER
parsePclp :: String -> Exceptional String AST
parsePclp src =
    let initialState = AST.AST
            { AST.rFuncDefs = Map.empty
            , AST.rules     = Map.empty
            , AST.queries   = Set.empty
            , AST.evidence  = Nothing
            }
    in mapException show (fromEither (parse (parseTheory initialState) "PCLP theory" src))

parseTheory :: AST -> Parser AST
parseTheory ast = whiteSpace >>
    (     try ( do -- query
            query <- parseQuery
            let ast' = ast {AST.queries = Set.insert query $ AST.queries ast}
            parseTheory ast'
          )
      <|> try (do --evidence
            evidence <- parseEvidence
            -- TODO: handle multiple evidence statements
            let ast' = ast {AST.evidence = Just evidence}
            parseTheory ast'
          )
      <|> ( do -- random function definition
            (lbl, args, def) <- parseRFuncDef
            -- put together defs with same signature
            let ast' = ast {AST.rFuncDefs = Map.insertWith (++) (lbl, length args) [(args, def)] (AST.rFuncDefs ast)}
            parseTheory ast'
          )
      <|> ( do -- rule
            (lbl, args, body) <- parseRule
            -- put together rules with same head
            let ast' = ast {AST.rules = Map.insertWith Set.union (lbl, length args) (Set.singleton (args, body)) (AST.rules ast)}
            parseTheory ast'
          )
      <|> ( do -- end of input
                eof
                return ast
          )
    )

-- rules
parseRule :: Parser (AST.PredicateLabel, [AST.Argument], AST.RuleBody)
parseRule = do
    (lbl, args) <- parseUserPred
    reservedOp "<-"
    body <- sepBy parseBodyElement comma
    _ <- dot
    return (lbl, args, AST.RuleBody body)

parseBodyElement :: Parser AST.RuleBodyElement
parseBodyElement =
        uncurry AST.UserPredicate <$> parseUserPred
    <|>
        AST.BuildInPredicate <$> parseBuildInPredicate

parseUserPred :: Parser (AST.PredicateLabel, [AST.Argument])
parseUserPred = do
    lbl <- parsePredicateLabel
    args  <- option [] $ parens $ sepBy parseArg comma
    return (lbl, args)

parsePredicateLabel :: Parser AST.PredicateLabel
parsePredicateLabel = AST.PredicateLabel <$> identifier

parseBuildInPredicate :: Parser AST.BuildInPredicate
parseBuildInPredicate = try parseBoolPredicate <|> parseRealPredicate

parseBoolPredicate :: Parser AST.BuildInPredicate
parseBoolPredicate = do
    exprX <- bExpression
    reservedOp "="
    exprY <- bExpression
    return (AST.BoolEq True exprX exprY)

parseRealPredicate :: Parser AST.BuildInPredicate
parseRealPredicate = do
    exprX <- rExpression
    op    <- realIneqOp
    exprY <- rExpression
    return $ AST.RealIneq op exprX exprY

-- rfunc defs
parseRFuncDef :: Parser (AST.RFuncLabel, [AST.Argument], AST.RFuncDef)
parseRFuncDef = do
    (lbl, args) <- parseRFunc
    reservedOp "~"
    def <- parseFlip <|> parseNorm
    return (lbl, args, def)

parseRFunc :: Parser (AST.RFuncLabel, [AST.Argument])
parseRFunc = do
    lbl  <- rFuncL
    args <- option [] $ parens $ sepBy parseArg comma
    return (lbl, args)

parseFlip :: Parser AST.RFuncDef
parseFlip = do
    reserved "flip"
    prob <- parens $ fromRational <$> rational
    _ <- dot
    return $ AST.Flip prob

parseNorm :: Parser AST.RFuncDef
parseNorm = do
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

parseArg :: Parser AST.Argument
parseArg = AST.Object   . AST.ObjectStr <$> identifier
           <|>
           AST.Object   . AST.ObjectInt <$> integer
           <|>
           AST.Variable . AST.VarName   <$> variable

-- expressions
bExpression :: Parser (AST.Expr Bool)
bExpression = buildExpressionParser bOperators bTerm

bOperators = []

bTerm =  (reserved "true"  >> return (AST.BoolConstant True))
     <|> (reserved "false" >> return (AST.BoolConstant False))
     <|> uncurry AST.RFunc <$> parseRFunc

rExpression :: Parser (AST.Expr RealN)
rExpression = buildExpressionParser rOperators rTerm

rOperators = [ [Infix  (reservedOp "+"   >> return AST.RealSum) AssocLeft] ]

rTerm =  AST.RealConstant <$> rational
     <|> uncurry AST.RFunc <$> parseRFunc

-- queries
parseQuery :: Parser (AST.PredicateLabel, [AST.Argument])
parseQuery = do
    reserved "query"
    query <- parseUserPred
    _ <- dot
    return query

-- evidence
parseEvidence :: Parser (AST.PredicateLabel, [AST.Argument])
parseEvidence = do
    reserved "evidence"
    evidence <- parseUserPred
    _ <- dot
    return evidence
