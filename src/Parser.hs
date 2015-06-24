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
import AST
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec
import Control.Monad.Exception.Synchronous
import Numeric

parsePclp :: String -> Exceptional String AST
parsePclp src =
    let initialState = AST
            { rFuncDefs = Map.empty
            , rules     = Map.empty
            , queries   = []
            }
    in mapException show (fromEither (parse (parseTheory initialState) "PCLP theory" src))

parseTheory :: AST -> Parser AST
parseTheory ast = spaces >>
                (     try ( do -- query
                        query <- parseQuery
                        let ast' = ast {queries = query:queries ast}
                        parseTheory ast'
                      )
                  <|> ( do -- random function definition
                        (signature, def) <- parseRFuncDef
                        -- put together defs with same signature
                        let ast' = ast {rFuncDefs = Map.insertWith (++) signature [def] (rFuncDefs ast)}
                        parseTheory ast'
                      )
                  <|> ( do -- rule
                        (label, body) <- parseRule
                        -- put together rules with same head
                        let ast' = ast {rules = Map.insertWith (++) label [body] (rules ast)}
                        parseTheory ast'
                      )
                  <|> ( do -- end of input
                            eof
                            return ast
                      )
                )

-- rules
parseRule :: Parser (PredicateLabel, RuleBody)
parseRule = do
    label <- parsePredicateLabel
    stringAndSpaces "<-"
    body <- sepBy parseBodyElement (stringAndSpaces ",")
    stringAndSpaces "."
    return (label, RuleBody body)

parseBodyElement :: Parser RuleBodyElement
parseBodyElement = do
        fmap UserPredicate parsePredicateLabel
    <|>
        fmap BuildInPredicate parseBuildInPredicate

parsePredicateLabel :: Parser PredicateLabel
parsePredicateLabel = do
    first <- lower
    rest  <- many letter
    spaces
    return (first:rest)

parseBuildInPredicate :: Parser BuildInPredicate
parseBuildInPredicate = do
    exprX <- parseBoolExpr
    stringAndSpaces "="
    exprY <- parseBoolExpr
    return (BoolEq exprX exprY)

-- rfunc defs
parseRFuncDef :: Parser (RFuncLabel, RFuncDef)
parseRFuncDef = do
    label <- parseUserRFuncLabel
    stringAndSpaces "~"
    stringAndSpaces "flip("
    prob <- fmap (fst . head . readFloat) ( do
            before <- many digit
            string "."
            after <- many1 digit
            return (before ++ "." ++ after)
        )
    spaces
    stringAndSpaces ")"
    stringAndSpaces "."
    return (label, Flip prob)

-- expressions
parseBoolExpr :: Parser (Expr Bool)
parseBoolExpr = do
        fmap BoolConstant parseBoolConstant
    <|>
        fmap UserRFunc parseUserRFuncLabel

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
    rest  <- many letter
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
