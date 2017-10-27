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

module GrounderPhase2
    ( substitutePfsWithPfArgs
    ) where
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
import Data.Foldable (foldl')
import qualified GroundedASTPhase1 as GAST1
import qualified GroundedASTPhase2 as GAST2

substitutePfsWithPfArgs :: GAST1.GroundedAST
                        -> IdNrMap (Int, [AST.ConstantExpr])
                        -> (GAST2.GroundedAST, IdNrMap (Int, [AST.ConstantExpr]))
substitutePfsWithPfArgs GAST1.GroundedAST{GAST1.rules, GAST1.queries, GAST1.evidence} lIds =
    (GAST2.GroundedAST {GAST2.rules = rules', GAST2.queries = queries', GAST2.evidence = evidence'}, lIds''')
    where
    (lIds', rules')      = Map.mapAccum toRuleBodies2 lIds rules
    (queries',  lIds'')  = toRuleBodyElements2 queries lIds'
    (evidence', lIds''') = toRuleBodyElements2 evidence lIds''

toRuleBodies2 :: IdNrMap (Int, [AST.ConstantExpr])
              -> Set GAST1.RuleBody
              -> (IdNrMap (Int, [AST.ConstantExpr]), Set GAST2.RuleBody)
toRuleBodies2 lIds ruleBodies = (lIds', Set.fromList ruleBodies')
    where
    (lIds', ruleBodies') = mapAccumR toRuleBody2 lIds $ Set.toList ruleBodies

    toRuleBody2 :: IdNrMap (Int, [AST.ConstantExpr])
                -> GAST1.RuleBody
                -> (IdNrMap (Int, [AST.ConstantExpr]), GAST2.RuleBody)
    toRuleBody2 lIds'' (GAST1.RuleBody ruleBody) = (lIds''', GAST2.RuleBody ruleBody') 
        where
        (ruleBody', lIds''') = toRuleBodyElements2 ruleBody lIds''

toRuleBodyElements2 :: Set GAST1.RuleBodyElement
                    -> IdNrMap (Int, [AST.ConstantExpr])
                    -> (Set GAST2.RuleBodyElement, IdNrMap (Int, [AST.ConstantExpr]))
toRuleBodyElements2 queries lIds = (Set.fromList qs, lIds')
    where
    (lIds', qs) = mapAccumR toRuleBodyElement2 lIds $ Set.toList queries    

    toRuleBodyElement2 :: IdNrMap (Int, [AST.ConstantExpr])
                       -> GAST1.RuleBodyElement
                       -> (IdNrMap (Int, [AST.ConstantExpr]), GAST2.RuleBodyElement)
    toRuleBodyElement2 lIds'' (GAST1.UserPredicate prd) = (lIds'', GAST2.UserPredicate prd)
    toRuleBodyElement2 lIds'' (GAST1.BuildInPredicate prd) = (lIds''', GAST2.BuildInPredicate prd')
        where
        (prd', lIds''') = toBuildInPred2 prd lIds''

    toBuildInPred2 :: GAST1.BuildInPredicate
                   -> IdNrMap (Int, [AST.ConstantExpr])
                   -> (GAST2.BuildInPredicate, IdNrMap (Int, [AST.ConstantExpr]))
    toBuildInPred2 (GAST1.BuildInPredicateBool prd) = toTypedBuildInPred2' GAST2.BuildInPredicateBool prd
    toBuildInPred2 (GAST1.BuildInPredicateReal prd) = toTypedBuildInPred2' GAST2.BuildInPredicateReal prd
    toBuildInPred2 (GAST1.BuildInPredicateStr  prd) = toTypedBuildInPred2' GAST2.BuildInPredicateStr  prd
    toBuildInPred2 (GAST1.BuildInPredicateInt  prd) = toTypedBuildInPred2' GAST2.BuildInPredicateInt  prd
    toBuildInPred2 (GAST1.BuildInPredicateObj  prd) = toTypedBuildInPred2' GAST2.BuildInPredicateObj  prd
    toBuildInPred2 (GAST1.BuildInPredicatePh   prd) = toTypedBuildInPred2' GAST2.BuildInPredicatePh   prd

    toTypedBuildInPred2' :: (GAST2.TypedBuildInPred a -> GAST2.BuildInPredicate)
                         -> GAST1.TypedBuildInPred a
                         -> IdNrMap (Int, [AST.ConstantExpr])
                         -> (GAST2.BuildInPredicate, IdNrMap (Int, [AST.ConstantExpr]))
    toTypedBuildInPred2' constr prd lIds'' = (constr prd', lIds''')
        where
        (prd', lIds''') = toTypedBuildInPred2 prd lIds''

    toTypedBuildInPred2 :: GAST1.TypedBuildInPred a
                        -> IdNrMap (Int, [AST.ConstantExpr])
                        -> (GAST2.TypedBuildInPred a, IdNrMap (Int, [AST.ConstantExpr]))
    toTypedBuildInPred2 (GAST1.Equality eq exprX exprY) lIds'' = (GAST2.Equality eq exprX' exprY', lIds'''')
        where
        (exprX', lIds''')  = toExpr2 exprX lIds''
        (exprY', lIds'''') = toExpr2 exprY lIds'''
    toTypedBuildInPred2 (GAST1.Ineq op exprX exprY) lIds'' = (GAST2.Ineq op exprX' exprY', lIds'''')
        where
        (exprX', lIds''')  = toExpr2 exprX lIds''
        (exprY', lIds'''') = toExpr2 exprY lIds'''
    toTypedBuildInPred2 (GAST1.Constant cnst) lIds'' = (GAST2.Constant cnst, lIds'')

    toExpr2 :: GAST1.Expr a -> IdNrMap (Int, [AST.ConstantExpr]) -> (GAST2.Expr a, IdNrMap (Int, [AST.ConstantExpr]))
    toExpr2 (GAST1.ConstantExpr expr) lIds'' = (GAST2.ConstantExpr expr, lIds'')
    toExpr2 (GAST1.PFuncExpr pf)      lIds'' = (GAST2.PFuncExpr pf', lIds''')
        where
        (pf', lIds''') = toPFunc2 pf lIds''
    toExpr2 (GAST1.Sum exprX exprY)   lIds'' = (GAST2.Sum exprX' exprY', lIds'''')
        where
        (exprX', lIds''')  = toExpr2 exprX lIds''
        (exprY', lIds'''') = toExpr2 exprY lIds'''

    toPFunc2 :: GAST1.PFunc a -> IdNrMap (Int, [AST.ConstantExpr]) -> (GAST2.PFunc a, IdNrMap (Int, [AST.ConstantExpr]))
    toPFunc2 (GAST1.PFunc label def) lIds'' = (GAST2.PFunc label' def', lIds'''')
        where
        (label', lIds''')  = toPFuncLabel2 label lIds''
        (def',   lIds'''') = toPFuncDef2 def lIds'''

    toPFuncLabel2 :: GAST1.PFuncLabel
                  -> IdNrMap (Int, [AST.ConstantExpr])
                  -> (GAST2.PFuncLabel, IdNrMap (Int, [AST.ConstantExpr]))
    toPFuncLabel2 (GAST1.PFuncLabel (AST.PFuncLabel lbl) args) lIds'' = (GAST2.PFuncLabel idNr, lIds''')
        where
        (idNr, lIds''') = IdNrMap.getIdNr (lbl, args) lIds''

    toPFuncDef2 :: GAST1.PFuncDef a
                -> IdNrMap (Int, [AST.ConstantExpr])
                -> (GAST2.PFuncDef a, IdNrMap (Int, [AST.ConstantExpr]))
    toPFuncDef2 (GAST1.Flip p)                      lIds'' = (GAST2.Flip p, lIds'')
    toPFuncDef2 (GAST1.RealDist cdf cdf')           lIds'' = (GAST2.RealDist cdf cdf', lIds'')
    toPFuncDef2 (GAST1.StrDist dist)                lIds'' = (GAST2.StrDist dist, lIds'')
    toPFuncDef2 (GAST1.UniformObjDist objId)        lIds'' = (GAST2.UniformObjDist objId, lIds'')
    toPFuncDef2 (GAST1.UniformOtherObjDist otherPf) lIds'' = (GAST2.UniformOtherObjDist otherPf', lIds''')
        where
        (otherPf', lIds''') = toPFunc2 otherPf lIds''

{-substitutePfsWithPfArgs :: AST -> IdNrMap Text -> (AST, IdNrMap Text)
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
            addUsagePreds' args usagePred ((ast''', identIds''), n, prevUsages, conditions) = ((ast'''', identIds'''), succ n, prevUsages', conditions')
                where                
                ast'''' = ast'''
                    { AST.rules =
                        foldl'
                            (\x (head', bodies'') -> Map.insert (head', 0) (([],) <$> bodies'') x)
                            (Map.insert (usagePred, nArgs) bodies' $ AST.rules ast''')
                            auxRules
                    }
                (bodies', auxRules, identIds''') = bodies prevUsages ([], []) identIds''
                conditions' = conditions
                prevUsages' = (usagePred, args) : prevUsages

                bodies :: [(AST.PredicateLabel, [AST.Expr])]
                       -> ([([AST.HeadArgument], AST.RuleBody)], [(AST.PredicateLabel, [AST.RuleBody])])
                       -> IdNrMap Text
                       -> ([([AST.HeadArgument], AST.RuleBody)], [(AST.PredicateLabel, [AST.RuleBody])], IdNrMap Text)
                -- handle cases that usage actually equals one of previous usage
                bodies ((prevUsagePred, prevUsageArgs) : prevUsages'') (accBodies, accAuxRules) identIds'''' =
                    bodies prevUsages'' (body : accBodies, unequalAuxRule : accAuxRules) identIds'''''
                    where
                    body = (usagePredArgsHead, AST.RuleBody (AST.UserPredicate prevUsagePred usagePredArgs : equalToPrev))
                    usagePredArgsHead = [AST.ArgVariable $ AST.TempVar $ -x | x <- [1..nArgs]]
                    usagePredArgs     = [AST.Variable    $ AST.TempVar $ -x | x <- [1..nArgs]]
                    equalToPrev       = [ AST.BuildInPredicate $ AST.Equality True arg argPrev
                                        | arg <- args | argPrev <- prevUsageArgs
                                        ]
                    -- add aux rule, which is negation of 'equalToPrev', used to restrict last body to cases no rules matches
                    unequalAuxRule = ( unequalAuxRuleHead
                                     , [ AST.RuleBody [AST.BuildInPredicate $ AST.Equality False arg argPrev]
                                       | arg <- args | argPrev <- prevUsageArgs
                                       ]
                                     )
                    unequalAuxRuleHead = AST.PredicateLabel unequalAuxRuleLabel
                    (unequalAuxRuleLabel, identIds''''') = IdNrMap.getIdNr usagePredAuxLabel identIds''''
                        where
                        AST.PredicateLabel pfId = usagePred
                        usagePredAuxLabel = toText $ fromText (Map.findWithDefault undefined pfId (IdNrMap.fromIdNrMap identIds'')) <>
                                                     "_" <> showb (length accBodies)
                -- add last case: no previous usage equals current one
                bodies [] (accBodies, accAuxRules) identIds'''' =
                    ( ([AST.ArgVariable $ AST.TempVar $ -x | x <- [1..nArgs]], AST.RuleBody body) : accBodies
                    , accAuxRules
                    , identIds''''
                    )
                    where
                    body = argValueEqs ++ uneqPrevious
                    argValueEqs = [ AST.BuildInPredicate $ AST.Equality True (AST.Variable $ AST.TempVar $ -v) (pfs2placeh arg)
                                  | v <- [1..nArgs] | arg <- args
                                  ]

                    uneqPrevious = [AST.UserPredicate label [] | (label, _) <- accAuxRules]

                    pfs2placeh (AST.PFunc (AST.PFuncLabel pf) []) = AST.ConstantExpr $
                        AST.Placeholder (Map.findWithDefault undefined pf (IdNrMap.fromIdNrMap identIds''))
                    pfs2placeh arg = arg

    -- predicates for which pfsWithPfArgs are used -> all usages with generated predicate label to compute arguments of that usage
    pfsWithPfArgsUsages :: Map (AST.PFuncLabel, Int) (Map [AST.Expr] AST.PredicateLabel)
    pfsWithPfArgsUsages = pfsWithPfArgsUsages'

    ((pfsWithPfArgsUsages', identIds2, _), ast2) = mapAccumAddRuleElemsPfs pfsWithPfArgsUsages'' (Map.empty, identIds, 1) ast
        where
        pfsWithPfArgsUsages'' :: (Map (AST.PFuncLabel, Int) (Map [AST.Expr] AST.PredicateLabel), IdNrMap Text, Int)
                              -> ((AST.PFuncLabel, Int), [AST.Expr])
                              -> ([AST.Expr], (Map (AST.PFuncLabel, Int) (Map [AST.Expr] AST.PredicateLabel), IdNrMap Text, Int), [AST.RuleBodyElement])
        pfsWithPfArgsUsages'' st@(pfUses, identIds'', tmpVarCounter) (sign@(AST.PFuncLabel pfId, _), args)
            | Set.member sign pfsWithPfArgs =
                let usesArgs = Map.findWithDefault Map.empty sign pfUses
                in  case Map.lookup args usesArgs of
                    Just prd -> (argsWithSubstPfs, (pfUses, identIds'', tmpVarCounter'), [AST.UserPredicate prd argsWithSubstPfs])
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
    mapAccumAddRuleElemsPfs'''' acc'' expr = (acc'', expr)-}

