--The MIT License (MIT)
--
--Copyright (c) 2017 Steffen Michels (mail@steffen-michels.de)
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

module AstPreprocessor
    ( substitutePfsWithPfArgs
    ) where
import AST (AST)
import qualified AST
import IdNrMap (IdNrMap)
import qualified IdNrMap
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import Data.Text (Text)
import TextShow
import Data.Monoid ((<>))
import qualified Data.List as List
import Data.Traversable (mapAccumR)

substitutePfsWithPfArgs :: AST -> IdNrMap Text -> (AST, IdNrMap Text)
substitutePfsWithPfArgs ast identIds = (ast', identIds')
    where
    (ast', identIds') = Map.foldWithKey addUsagePreds (ast2, identIds2) pfsWithPfArgsUsages
        where
        -- add predicates for each usage of predicates, of which at least one arg is a PF in at least one usage
        addUsagePreds :: (AST.PFuncLabel, Int) -> Map [AST.Expr] AST.PredicateLabel -> (AST, IdNrMap Text) -> (AST, IdNrMap Text)
        addUsagePreds (_, nArgs) uses ast'' = res
            where
            (res, _, _, _) = Map.foldWithKey addUsagePreds' (ast'', 0, [], []) uses
            addUsagePreds' :: [AST.Expr]
                           -> AST.PredicateLabel
                           -> ((AST, IdNrMap Text), Int, [(AST.PredicateLabel, [AST.Expr])], [[(AST.Expr, AST.Expr)]])
                           -> ((AST, IdNrMap Text), Int, [(AST.PredicateLabel, [AST.Expr])], [[(AST.Expr, AST.Expr)]])
            addUsagePreds' args usagePred ((ast''', identIds''), n, prevUsages, conditions) = ((ast'''', identIds''), succ n, prevUsages', conditions')
                where
                ast'''' = ast'''{AST.rules = Map.insert (usagePred, nArgs) (bodies prevUsages []) $ AST.rules ast'''}
                conditions' = conditions
                prevUsages' = (usagePred, args) : prevUsages

                bodies :: [(AST.PredicateLabel, [AST.Expr])]
                       -> [([AST.HeadArgument], AST.RuleBody)]
                       -> [([AST.HeadArgument], AST.RuleBody)]
                bodies ((prevUsagePred, prevUsageArgs) : prevUsages'') acc =
                    bodies prevUsages'' (body : acc)
                    where
                    body = (usagePredArgsHead, AST.RuleBody (AST.UserPredicate prevUsagePred usagePredArgs : equalToPrev))
                    usagePredArgsHead = [AST.ArgVariable $ AST.TempVar $ -x | x <- [1..nArgs]]
                    usagePredArgs     = [AST.Variable    $ AST.TempVar $ -x | x <- [1..nArgs]]
                    equalToPrev       = [ AST.BuildInPredicate $ AST.Equality True arg argPrev
                                        | arg <- args, argPrev <- prevUsageArgs
                                        ]
                bodies [] acc = ([AST.ArgVariable $ AST.TempVar $ -x | x <- [1..nArgs]], AST.RuleBody body) : acc
                    where
                    body = concat (argValueEqs : unequalToPrev)
                    argValueEqs = [ AST.BuildInPredicate $ AST.Equality True (AST.Variable $ AST.TempVar $ -v) (pfs2placeh arg)
                                  | v <- [1..nArgs], arg <- args
                                  ]
                    unequalToPrev = [ [ AST.BuildInPredicate $ AST.Equality False arg argPrev
                                      | arg <- args, argPrev <- prevUsageArgs
                                      ]
                                    | (_, prevUsageArgs) <- prevUsages
                                    ]
                    pfs2placeh (AST.PFunc (AST.PFuncLabel pf) []) = AST.ConstantExpr $
                        AST.StrConstant ("_" <> Map.findWithDefault undefined pf (IdNrMap.fromIdNrMap identIds''))
                    pfs2placeh arg = arg

    -- predicates for which pfsWithPfArgs are used -> all usages with generated predicate label to compute arguments of that usage
    pfsWithPfArgsUsages :: Map (AST.PFuncLabel, Int) (Map [AST.Expr] AST.PredicateLabel)
    pfsWithPfArgsUsages = pfsWithPfArgsUsages'

    ((pfsWithPfArgsUsages', identIds2, _), ast2) = mapAccumAddRuleElemsPfs pfsWithPfArgsUsages'' (Map.empty, identIds, 0) ast
        where
        pfsWithPfArgsUsages'' :: (Map (AST.PFuncLabel, Int) (Map [AST.Expr] AST.PredicateLabel), IdNrMap Text, Int)
                              -> ((AST.PFuncLabel, Int), [AST.Expr])
                              -> ([AST.Expr], (Map (AST.PFuncLabel, Int) (Map [AST.Expr] AST.PredicateLabel), IdNrMap Text, Int), [AST.RuleBodyElement])
        pfsWithPfArgsUsages'' st@(pfUses, identIds'', tmpVarCounter) (sign@(AST.PFuncLabel pfId, _), args)
            | Set.member sign pfsWithPfArgs =
                let usesArgs = Map.findWithDefault Map.empty sign pfUses
                in  case Map.lookup args usesArgs of
                    Just prd -> (argsWithSubstPfs, st, [AST.UserPredicate prd argsWithSubstPfs])
                    Nothing ->
                        let (prdId, identIds''') = IdNrMap.getIdNr (predIdent $ Map.size usesArgs) identIds''
                            prdLabel             = AST.PredicateLabel prdId
                        in  ( argsWithSubstPfs
                            , (Map.insert sign (Map.insert args prdLabel usesArgs) pfUses, identIds''', tmpVarCounter')
                            , [AST.UserPredicate prdLabel argsWithSubstPfs]
                            )
            | otherwise = (args, st, [])
            where
            -- substitute all Pfs used as args with fresh variables
            (tmpVarCounter', argsWithSubstPfs) = mapAccumR substPfs tmpVarCounter args
                where
                substPfs counter (AST.PFunc _ _) = (succ counter, AST.Variable $ AST.TempVar $ -counter)
                substPfs counter a               = (counter,      a)

            predIdent n = toText $
                          "~" <>
                          fromText (Map.findWithDefault undefined pfId (IdNrMap.fromIdNrMap identIds)) <>
                          "@" <>
                          showb n
    -- all pfs which have pfs as args
    pfsWithPfArgs :: Set (AST.PFuncLabel, Int)
    pfsWithPfArgs = fst $ mapAccumAddRuleElemsPfs pfsWithPfArgs' Set.empty ast
        where
        pfsWithPfArgs' :: Set (AST.PFuncLabel, Int)
                       -> ((AST.PFuncLabel, Int), [AST.Expr])
                       -> ([AST.Expr], Set (AST.PFuncLabel, Int), [a])
        pfsWithPfArgs' pfs (sign, args)
            | any (AST.foldExpr (\b e -> b || AST.exprIsPFunc e) False) args = (args, Set.insert sign pfs, [])
            | otherwise                                                      = (args, pfs, [])

mapAccumAddRuleElemsPfs :: (a -> ((AST.PFuncLabel, Int), [AST.Expr]) -> ([AST.Expr], a, [AST.RuleBodyElement])) -> a -> AST -> (a, AST)
mapAccumAddRuleElemsPfs f acc ast = (acc', ast{AST.rules = rules})
    where
    (acc', rules) = Map.mapAccumWithKey
        (\acc'' _ -> List.mapAccumL mapAccumAddRuleElemsPfs' acc'')
        acc
        (AST.rules ast)

    mapAccumAddRuleElemsPfs' acc'' (args, AST.RuleBody body) = (acc''', (args, AST.RuleBody $ concat body'))
        where
        (acc''', body') = List.mapAccumL mapAccumAddRuleElemsPfs'' acc'' body

    mapAccumAddRuleElemsPfs'' acc'' el@(AST.UserPredicate _ _) = (acc'', [el])
    mapAccumAddRuleElemsPfs'' acc'' (AST.BuildInPredicate bip) = case bip of
        AST.Equality op exprX exprY -> mapAccumAddRuleElemsPfs''' (AST.Equality op) exprX exprY
        AST.Ineq     op exprX exprY -> mapAccumAddRuleElemsPfs''' (AST.Ineq     op) exprX exprY
        where
        mapAccumAddRuleElemsPfs''' constr exprX exprY = (acc'''', AST.BuildInPredicate (constr exprX' exprY') : toAdd)
            where
            (acc''',  exprX')          = AST.mapAccExpr mapAccumAddRuleElemsPfs'''' (acc'', []) exprX
            ((acc'''', toAdd), exprY') = AST.mapAccExpr mapAccumAddRuleElemsPfs'''' acc'''      exprY

    mapAccumAddRuleElemsPfs'''' (acc'', toAdd) (AST.PFunc label args) = ((acc''', toAdd ++ toAdd'), AST.PFunc label args')
        where
        (args', acc''', toAdd') = f acc'' ((label, length args), args)
    mapAccumAddRuleElemsPfs'''' acc'' expr = (acc'', expr)

