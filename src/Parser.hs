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

parsePclp :: String -> AST
parsePclp src =
    let initialState = AST
            { rFuncDefs = Map.empty
            , rules     = Map.empty
            , query     = ""
            }
    in case parse (parseTheory initialState) "PCLP theory" src of
        Left err  -> AST
            { rFuncDefs = Map.empty
            , rules     = Map.empty
            , query     = show err
            }
        Right val -> val

parseTheory :: AST -> Parser AST
parseTheory ast = spaces >>
                (   ( do -- rules
                        (label, body) <- parseRule
                        -- put together rules with same head
                        let ast' = ast {rules = Map.insertWith (++) label [body] (rules ast)}
                        parseTheory ast'
                      )
                  <|> ( do
                            eof
                            return ast
                      )
                )

parseRule :: Parser (PredicateLabel, RuleBody)
parseRule = do
    label <- parsePredicateLabel
    stringAndSpaces "<-"
    body <- sepBy parseBodyElement (stringAndSpaces ",")
    stringAndSpaces "."
    return (label, RuleBody body)

parsePredicateLabel :: Parser PredicateLabel
parsePredicateLabel = do
    first <- lower
    rest  <- many letter
    spaces
    return (first:rest)

parseBodyElement :: Parser RuleBodyElement
parseBodyElement = do
    userPred <- parsePredicateLabel
    spaces
    return (UserPredicate userPred)

stringAndSpaces :: String -> Parser ()
stringAndSpaces str = string str >> spaces
