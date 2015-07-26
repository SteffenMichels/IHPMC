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
import qualified Data.Map as Map
import qualified Data.HashSet as Set
import Text.ParserCombinators.Parsec
import Exception
import Numeric
import Text.Printf (printf)
import BasicTypes
import Data.Ratio ((%))
import qualified Statistics.Distribution as Dist
import qualified Statistics.Distribution.Normal as Norm

parsePclp :: String -> Exceptional String AST
parsePclp src =
    let initialState = AST.AST
            { AST.rFuncDefs = Map.empty
            , AST.rules     = Map.empty
            , AST.queries   = Set.empty
            }
    in mapException show (fromEither (parse (parseTheory initialState) "PCLP theory" src))

parseTheory :: AST -> Parser AST
parseTheory ast = spaces >>
                (     try ( do -- query
                        query <- parseQuery
                        let ast' = ast {AST.queries = Set.insert query $ AST.queries ast}
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
    stringAndSpaces "<-"
    body <- sepBy parseBodyElement (stringAndSpaces ",")
    stringAndSpaces "."
    return (label, AST.RuleBody body)

parseBodyElement :: Parser AST.RuleBodyElement
parseBodyElement = do
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
    exprX <- parseBoolExpr
    stringAndSpaces "="
    exprY <- parseBoolExpr
    return (AST.BoolEq exprX exprY)

parseRealPredicate :: Parser AST.BuildInPredicate
parseRealPredicate = do
    exprX <- parseRealExpr
    op    <- parseRealIneqOp
    exprY <- parseRealExpr
    return (AST.RealIneq op exprX exprY)

-- rfunc defs
parseRFuncDef :: Parser (RFuncLabel, AST.RFuncDef)
parseRFuncDef = do
    label <- parseUserRFuncLabel
    stringAndSpaces "~"
    def <- try parseFlip <|> parseNorm
    return (label, def)

parseFlip :: Parser AST.RFuncDef
parseFlip = do
    stringAndSpaces "flip("
    prob <- parseRat
    stringAndSpaces ")"
    stringAndSpaces "."
    return $ AST.Flip prob

parseNorm :: Parser AST.RFuncDef
parseNorm = do
    stringAndSpaces "norm("
    m <- parseRat
    stringAndSpaces ","
    d <- parseRat
    stringAndSpaces ")"
    stringAndSpaces "."
    return $ AST.RealDist (\x -> toRational $ Dist.cumulative (Norm.normalDistr (fromRat m) (fromRat d)) $ fromRat x)

-- expressions
parseBoolExpr :: Parser (AST.Expr Bool)
parseBoolExpr =   fmap AST.BoolConstant parseBoolConstant
              <|> fmap AST.UserRFunc parseUserRFuncLabel

parseBoolConstant :: Parser Bool
parseBoolConstant =
        string "#"
    >>
        (   (stringAndSpaces "true"  >> return True)
        <|>
            (stringAndSpaces "false" >> return False)
        )

parseRealExpr :: Parser (AST.Expr AST.RealN)
parseRealExpr =   fmap AST.RealConstant parseRat
              <|> fmap AST.UserRFunc parseUserRFuncLabel

parseRealIneqOp :: Parser AST.IneqOp
parseRealIneqOp =   (try $ stringAndSpaces "<"  >> return AST.Lt)
                <|> (try $ stringAndSpaces "<=" >> return AST.LtEq)
                <|> (try $ stringAndSpaces ">"  >> return AST.Gt)
                <|> (try $ stringAndSpaces ">=" >> return AST.GtEq)

parseUserRFuncLabel :: Parser RFuncLabel
parseUserRFuncLabel = do
    string "~"
    first <- lower
    rest  <- many alphaNum
    spaces
    return (first:rest)

-- queries
parseQuery :: Parser PredicateLabel
parseQuery = do
    stringAndSpaces "query"
    query <- parsePredicateLabel
    stringAndSpaces "."
    return query

-- common

parseRat :: Parser Rational
parseRat = do
    neg <- (try $ string "-" >> return True) <|> return False
    rat <- try parseDecimal <|> parseFraction
    spaces
    return $ if neg then -rat else rat
    where
        parseDecimal = do
            before <- many digit
            string "."
            after <- many1 digit
            return $ (fst . head . readFloat) (printf "%s.%s" before after)
        parseFraction = do
            before <- many digit
            string "/"
            after <- many1 digit
            return $ (read before) % (read after)

stringAndSpaces :: String -> Parser ()
stringAndSpaces str = string str >> spaces
