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

lexer = Token.makeTokenParser languageDef
identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
rational   = Token.lexeme     lexer parseRat
realIneqOp = Token.lexeme     lexer parseRealIneqOp
userRFuncL = Token.lexeme     lexer parseUserRFuncLabel
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

parseRat :: Parser Rational
parseRat = do
    neg <- (string "-" >> return True) <|> return False
    rat <- try parseDecimal <|> parseFraction
    spaces
    return $ if neg then -rat else rat
    where
    parseDecimal = do
        before <- decimal
        string "."
        after <- many1 digit
        return $ (fst . head . readFloat) (printf "%i.%s" before after)
    parseFraction = do
        before <- integer
        string "/"
        after <- integer
        return $ before % after

parseRealIneqOp :: Parser AST.IneqOp
parseRealIneqOp =     try (reservedOp "<"  >> return AST.Lt)
                  <|>     (reservedOp "<=" >> return AST.LtEq)
                  <|> try (reservedOp ">"  >> return AST.Gt)
                  <|>     (reservedOp ">=" >> return AST.GtEq)

parseUserRFuncLabel :: Parser RFuncLabel
parseUserRFuncLabel = string "~" >> identifier

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
            (signature, def) <- parseRFuncDef
            -- put together defs with same signature
            let ast' = ast {AST.rFuncDefs = Map.insertWith (++) signature [def] (AST.rFuncDefs ast)}
            parseTheory ast'
          )
      <|> ( do -- rule
            (label, args, body) <- parseRule
            -- put together rules with same head
            let ast' = ast {AST.rules = Map.insertWith Set.union (label, length args) (Set.singleton (args, body)) (AST.rules ast)}
            parseTheory ast'
          )
      <|> ( do -- end of input
                eof
                return ast
          )
    )

-- rules
parseRule :: Parser (PredicateLabel, [AST.PredArgument], AST.RuleBody)
parseRule = do
    (label,args) <- parseUserPred
    reservedOp "<-"
    body <- sepBy parseBodyElement comma
    dot
    return (label, args, AST.RuleBody body)

parseBodyElement :: Parser AST.RuleBodyElement
parseBodyElement =
        uncurry AST.UserPredicate <$> parseUserPred
    <|>
        AST.BuildInPredicate <$> parseBuildInPredicate

parseUserPred :: Parser (PredicateLabel, [AST.PredArgument])
parseUserPred = do
    label <- parsePredicateLabel
    args  <- option [] $ parens $ sepBy parseArg comma
    return (label, args)

parsePredicateLabel :: Parser PredicateLabel
parsePredicateLabel = identifier

parseArg :: Parser AST.PredArgument
parseArg = AST.ObjectLabel <$> identifier <|> AST.Variable <$> variable

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
    op    <- parseRealIneqOp
    exprY <- rExpression
    return $ AST.RealIneq op exprX exprY

-- rfunc defs
parseRFuncDef :: Parser (RFuncLabel, AST.RFuncDef)
parseRFuncDef = do
    label <- parseUserRFuncLabel
    reservedOp "~"
    def <- parseFlip <|> parseNorm
    return (label, def)

parseFlip :: Parser AST.RFuncDef
parseFlip = do
    reserved "flip"
    prob <- parens $ ratToProb <$> rational
    dot
    return $ AST.Flip prob

parseNorm :: Parser AST.RFuncDef
parseNorm = do
    reserved "norm"
    (m, d) <- parens $ do
         m <- rational
         comma
         d <- rational
         return (m, d)
    dot
    return $ AST.RealDist
        (doubleToProb . Dist.cumulative (Norm.normalDistr (fromRat m) (fromRat d)) . fromRat)
        (toRational   . Dist.quantile   (Norm.normalDistr (fromRat m) (fromRat d)) . probToDouble)

-- expressions
bExpression :: Parser (AST.Expr Bool)
bExpression = buildExpressionParser bOperators bTerm

bOperators = []

bTerm =  (reserved "true"  >> return (AST.BoolConstant True))
     <|> (reserved "false" >> return (AST.BoolConstant False))
     <|> fmap AST.UserRFunc parseUserRFuncLabel

rExpression :: Parser (AST.Expr AST.RealN)
rExpression = buildExpressionParser rOperators rTerm

rOperators = [ [Infix  (reservedOp "+"   >> return AST.RealSum) AssocLeft] ]

rTerm =  fmap AST.RealConstant rational
     <|> fmap AST.UserRFunc parseUserRFuncLabel

-- queries
parseQuery :: Parser (PredicateLabel, [AST.PredArgument])
parseQuery = do
    reserved "query"
    query <- parseUserPred
    dot
    return query

-- evidence
parseEvidence :: Parser (PredicateLabel, [AST.PredArgument])
parseEvidence = do
    reserved "evidence"
    evidence <- parseUserPred
    dot
    return evidence
