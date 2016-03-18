-----------------------------------------------------------------------------
--
-- Module      :  Parser
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

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
import Interval (Interval, IntervalLimit(..))

-- LEXER
languageDef =
    emptyDef { Token.commentStart    = "/*"
             , Token.commentEnd      = "*/"
             , Token.commentLine     = "//"
             , Token.identStart      = letter
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
            after <- decimal
            return $ (fst . head . readFloat) (printf "%i.%i" before after)
        parseFraction = do
            before <- integer
            string "/"
            after <- integer
            return $ before % after

parseRealIneqOp :: Parser AST.IneqOp
parseRealIneqOp =   try (reservedOp "<"  >> return AST.Lt)
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
            (label, body) <- parseRule
            -- put together rules with same head
            let ast' = ast {AST.rules = Map.insertWith Set.union label (Set.singleton body) (AST.rules ast)}
            parseTheory ast'
          )
      <|> ( do -- end of input
                eof
                return ast
          )
    )

-- rules
parseRule :: Parser (PredicateLabel, AST.RuleBody)
parseRule = do
    label <- parsePredicateLabel
    reservedOp "<-"
    body <- sepBy parseBodyElement comma
    dot
    return (label, AST.RuleBody body)

parseBodyElement :: Parser AST.RuleBodyElement
parseBodyElement =
        fmap AST.UserPredicate parsePredicateLabel
    <|>
        fmap AST.BuildInPredicate parseBuildInPredicate

parsePredicateLabel :: Parser PredicateLabel
parsePredicateLabel = do
    first <- lower
    rest  <- many alphaNum
    spaces
    return (first:rest)

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
    return $ case (exprX, op, exprY) of
        (AST.UserRFunc rf, AST.Lt,   AST.RealConstant c) -> AST.RealIn rf (Inf, Open c)
        (AST.UserRFunc rf, AST.LtEq, AST.RealConstant c) -> AST.RealIn rf (Inf, Closed c)
        (AST.UserRFunc rf, AST.Gt,   AST.RealConstant c) -> AST.RealIn rf (Open c, Inf)
        (AST.UserRFunc rf, AST.GtEq, AST.RealConstant c) -> AST.RealIn rf (Closed c, Inf)
        (AST.RealConstant c, AST.Lt,   AST.UserRFunc rf) -> AST.RealIn rf (Open c, Inf)
        (AST.RealConstant c, AST.LtEq, AST.UserRFunc rf) -> AST.RealIn rf (Closed c, Inf)
        (AST.RealConstant c, AST.Gt,   AST.UserRFunc rf) -> AST.RealIn rf (Inf, Open c)
        (AST.RealConstant c, AST.GtEq, AST.UserRFunc rf) -> AST.RealIn rf (Inf, Closed c)
        _                                                -> AST.RealIneq op exprX exprY

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
parseQuery :: Parser PredicateLabel
parseQuery = do
    reserved "query"
    query <- parsePredicateLabel
    dot
    return query

-- evidence
parseEvidence :: Parser PredicateLabel
parseEvidence = do
    reserved "evidence"
    evidence <- parsePredicateLabel
    dot
    return evidence
