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
import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import Exception
import Numeric
import Text.Printf (printf)
import BasicTypes
import Data.Ratio ((%))

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
parseBuildInPredicate = do
    exprX <- parseBoolExpr
    stringAndSpaces "="
    exprY <- parseBoolExpr
    return (AST.BoolEq exprX exprY)

-- rfunc defs
parseRFuncDef :: Parser (RFuncLabel, AST.RFuncDef)
parseRFuncDef = do
    label <- parseUserRFuncLabel
    stringAndSpaces "~"
    stringAndSpaces "flip("
    prob <- parseProb
    spaces
    stringAndSpaces ")"
    stringAndSpaces "."
    return (label, AST.Flip prob)

parseProb :: Parser Probability
parseProb = try parseDecimal <|> parseFraction where
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

-- expressions
parseBoolExpr :: Parser (AST.Expr Bool)
parseBoolExpr = do
        fmap AST.BoolConstant parseBoolConstant
    <|>
        fmap AST.UserRFunc parseUserRFuncLabel

parseBoolConstant :: Parser Bool
parseBoolConstant = do
        string "#"
    >>
        (    (stringAndSpaces "true" >> return True)
        <|>
            (stringAndSpaces "false" >> return False)
        )

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

-- util

stringAndSpaces :: String -> Parser ()
stringAndSpaces str = string str >> spaces
