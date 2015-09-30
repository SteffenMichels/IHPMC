-----------------------------------------------------------------------------
--
-- Module      :  GWMC
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

module GWMC
    ( gwmc
    , gwmcEvidence
    , gwmcDebug
    ) where
import Formula (Formula)
import qualified Formula
import PST (PST, PSTNode)
import qualified PST
import BasicTypes
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import qualified AST
import Text.Printf (printf)
import GHC.Exts (sortWith)
import Debug.Trace (trace)
import qualified Data.List as List
import Interval (Interval, IntervalLimit(..), LowerUpper(..))
import qualified Interval
import Numeric (fromRat)
import Data.Maybe (mapMaybe, fromJust)
import Control.Arrow (first)
import Control.Applicative ((<$>))

gwmc :: Formula.NodeRef -> HashMap RFuncLabel [AST.RFuncDef] -> Formula -> [ProbabilityBounds]
gwmc query rfuncDefs f = fmap (\(pst,_) -> PST.bounds pst) results where
    results = gwmcDebug query rfuncDefs f

gwmcDebug :: Formula.NodeRef -> HashMap RFuncLabel [AST.RFuncDef] -> Formula -> [(PST, Formula)]
gwmcDebug query rfuncDefs f = gwmc' f $ PST.initialNode query
    where
        gwmc' :: Formula -> PSTNode -> [(PST, Formula)]
        gwmc' f pstNode = case GWMC.iterate f pstNode Map.empty 1.0 rfuncDefs of
            (f', pst@(PST.Finished _))              -> [(pst,f')]
            (f', pst@(PST.Unfinished pstNode' _ _)) -> let results = gwmc' f' pstNode'
                                                         in  (pst,f') : results

gwmcEvidence :: Formula.NodeRef -> Formula.NodeRef -> HashMap RFuncLabel [AST.RFuncDef] -> Formula -> [ProbabilityBounds]
gwmcEvidence query evidence rfuncDefs f = probBounds <$> gwmc' (initPST queryAndEvidence) (initPST negQueryAndEvidence) f''
    where
        gwmc' :: PST -> PST -> Formula -> [(PST, PST, Formula)]
        gwmc' (PST.Finished _) (PST.Finished _) _ = []
        gwmc' qe nqe f
            | PST.maxError qe > PST.maxError nqe =let (PST.Unfinished pstNode _ _) = qe
                                                      (f', qe')  = GWMC.iterate f pstNode Map.empty 1.0 rfuncDefs
                                                      rest = gwmc' qe' nqe f'
                                                   in (qe', nqe, f') : rest
            | otherwise                          = let (PST.Unfinished pstNode _ _) = nqe
                                                       (f', nqe') = GWMC.iterate f pstNode Map.empty 1.0 rfuncDefs
                                                       rest = gwmc' qe nqe' f'
                                                   in  (qe, nqe', f') : rest

        probBounds (qe, nqe, _) = (lqe/(lqe+unqe), uqe/(uqe+lnqe)) where
            (lqe,  uqe)  = PST.bounds qe
            (lnqe, unqe) = PST.bounds nqe

        initPST nwr = PST.Unfinished (PST.initialNode $ Formula.entryRef nwr) (0.0,1.0) undefined
        (queryAndEvidence,    f')  = Formula.insert Nothing True Formula.And (Set.fromList [queryRef True,  evidence]) f
        (negQueryAndEvidence, f'') = Formula.insert Nothing True Formula.And (Set.fromList [queryRef False, evidence]) f'
        queryRef sign = case query of
            Formula.RefComposed qSign label  -> Formula.RefComposed (sign == qSign) label
            Formula.RefBuildInPredicate pred -> Formula.RefBuildInPredicate $ if sign then pred else AST.negatePred pred

iterate :: Formula -> PSTNode -> HashMap RFuncLabel (Interval, Int) -> Double -> HashMap RFuncLabel [AST.RFuncDef] -> (Formula, PST)
iterate f pstNode previousChoicesReal partChoiceProb rfuncDefs
    | l == u    = (f', PST.Finished l)
    | otherwise = (f', PST.Unfinished pstNode' bounds score)
    where
        (f', pstNode', bounds@(l,u), score) = iterateNode f pstNode previousChoicesReal partChoiceProb

        iterateNode :: Formula -> PSTNode -> HashMap RFuncLabel (Interval, Int) -> Double -> (Formula, PSTNode, ProbabilityBounds, Double)
        iterateNode f (PST.ChoiceBool rFuncLabel p left right) previousChoicesReal partChoiceProb =
            (f', PST.ChoiceBool rFuncLabel p left' right', combineProbsChoice p left' right', combineScoresChoice left' right')
            where
                (f', left', right') = case (left,right) of
                        (PST.Unfinished pstNode _ _, _) | PST.score left > PST.score  right ->
                            let (f'', left'') = GWMC.iterate f pstNode previousChoicesReal (probToDouble p * partChoiceProb) rfuncDefs
                            in  (f'', left'', right)
                        (_, PST.Unfinished pstNode _ _) ->
                            let (f'', right'') = GWMC.iterate f pstNode previousChoicesReal (probToDouble (1-p) * partChoiceProb) rfuncDefs
                            in  (f'', left, right'')
                        _ -> error "finished node should not be selected for iteration"
        iterateNode f (PST.ChoiceReal rf p splitPoint left right) previousChoicesReal partChoiceProb =
            (f', PST.ChoiceReal rf p splitPoint left' right', combineProbsChoice p left' right', combineScoresChoice left' right')
            where
                (f', left', right') = case (left,right) of
                        (PST.Unfinished pstNode _ _, _) | PST.score  left > PST.score  right ->
                            let (f'', left'') = GWMC.iterate f pstNode (Map.insert rf ((curLower, Open splitPoint), curCount+1) previousChoicesReal) (probToDouble p * partChoiceProb) rfuncDefs
                            in  (f'', left'', right)
                        (_, PST.Unfinished pstNode _ _) ->
                            let (f'', right'') = GWMC.iterate f pstNode (Map.insert rf ((Open splitPoint, curUpper), curCount+1) previousChoicesReal) (probToDouble (1-p) * partChoiceProb) rfuncDefs
                            in  (f'', left, right'')
                        _ -> error "finished node should not be selected for iteration"
                ((curLower, curUpper), curCount) = Map.lookupDefault ((Inf, Inf), 0) rf previousChoicesReal
        iterateNode f (PST.Decomposition op dec) previousChoicesReal partChoiceProb =
            (f', PST.Decomposition op dec', combineProbsDecomp op dec', combineScoresDecomp dec')
            where
                sortedChildren = sortWith (\c -> -PST.score  c) dec
                selectedChild  = head sortedChildren
                selectedChildNode = case selectedChild of
                    PST.Unfinished pstNode _ _ -> pstNode
                    _                          -> error "finished node should not be selected for iteration"
                (f', selectedChild') = GWMC.iterate f selectedChildNode previousChoicesReal partChoiceProb rfuncDefs
                dec' = selectedChild':tail sortedChildren
        iterateNode f (PST.Leaf ref) previousChoicesReal partChoiceProb = case decompose ref f of
            Nothing -> case Map.lookup rf rfuncDefs of
                    Just (AST.Flip p:_) -> (f'', PST.ChoiceBool rf p left right, combineProbsChoice p left right, combineScoresChoice left right)
                        where
                            (leftEntry,  f')  = Formula.conditionBool fEntry rf True f
                            (rightEntry, f'') = Formula.conditionBool fEntry rf False f'
                            left  = toPSTNode p leftEntry
                            right = toPSTNode (1-p) rightEntry
                    Just (AST.RealDist cdf icdf:_) -> (f'', PST.ChoiceReal rf p splitPoint left right, combineProbsChoice p left right, combineScoresChoice left right)
                        where
                            p = (pUntilSplit-pUntilLower)/(pUntilUpper-pUntilLower)
                            pUntilLower = cdf' cdf True curLower
                            pUntilUpper = cdf' cdf False curUpper
                            pUntilSplit = cdf splitPoint
                            (leftEntry,  f')  = Formula.conditionReal fEntry rf (curLower, Open splitPoint) previousChoicesReal f
                            (rightEntry, f'') = Formula.conditionReal fEntry rf (Open splitPoint, curUpper) previousChoicesReal f'
                            left  = toPSTNode p leftEntry
                            right = toPSTNode (1-p) rightEntry
                            splitPoint = determineSplitPoint rf curInterv pUntilLower pUntilUpper icdf previousChoicesReal fEntry f
                            curInterv@(curLower, curUpper) = fst $ Map.lookupDefault ((Inf, Inf), undefined) rf previousChoicesReal
                    _  -> error ("undefined rfunc " ++ rf)
                    where
                        rf = fst $ head xxx
                        xxx = sortWith rfScore $ Map.toList $ snd $ Formula.entryScores $ Formula.augmentWithEntry ref f
                        --xxxy = trace (foldl (\str x@(rf,_) -> str ++ "\n" ++ show (rfScore x) ++ " " ++ rf) ("\n" ++ show ref) xxx) xxx
                        rfScore (rf, s) = case Map.lookup rf previousChoicesReal of
                            Just (_, count) -> (count, -s)
                            _               -> (case Map.lookup rf rfuncDefs of Just (AST.Flip p:_) -> -1; _ -> 0, -s)

                        fEntry = Formula.augmentWithEntry ref f
                        toPSTNode p entry = case Formula.entryNode entry of
                            Formula.Deterministic val -> PST.Finished $ if val then 1.0 else 0.0
                            _                     -> PST.Unfinished (PST.Leaf $ Formula.entryRef entry) (0.0,1.0) (probToDouble p * partChoiceProb)
                        cdf' _ lower Inf      = if lower then 0.0 else 1.0
                        cdf' cdf _ (Open x)   = cdf x
                        cdf' cdf _ (Closed x) = cdf x
            Just (origOp, decOp, sign, decomposition) -> (f', PST.Decomposition decOp psts, (0.0,1.0), combineScoresDecomp psts)
                where
                    (psts, f') = Set.foldr
                        (\dec (psts, f) ->
                            let (fresh, f') = if Set.size dec > 1 then
                                                    first Formula.entryRef $ Formula.insert Nothing sign origOp dec f
                                                else
                                                    let single = getFirst dec
                                                    in  (if sign then single else negate single, f)
                            in  (PST.Unfinished (PST.Leaf fresh) (0.0,1.0) partChoiceProb:psts, f')
                        )
                        ([], f)
                        decomposition

                    negate (Formula.RefComposed sign label)   = Formula.RefComposed (not sign) label
                    negate (Formula.RefBuildInPredicate pred) = Formula.RefBuildInPredicate (AST.negatePred pred)
                    negate (Formula.RefDeterministic val)     = Formula.RefDeterministic (not val)

combineProbsChoice p left right = (p*leftLower+(1-p)*rightLower, p*leftUpper+(1-p)*rightUpper) where
    (leftLower,  leftUpper)  = PST.bounds left
    (rightLower, rightUpper) = PST.bounds right
combineProbsDecomp Formula.And dec = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l'*l,u'*u)) (1.0, 1.0) dec
combineProbsDecomp Formula.Or dec  = (1-nl, 1-nu) where
    (nl, nu) = foldr (\pst (l,u) -> let (l',u') = PST.bounds pst in (l*(1.0-l'), u*(1.0-u'))) (1.0, 1.0) dec

combineScoresChoice left right = max (PST.score left) (PST.score right)
combineScoresDecomp            = foldr (\pst score -> max score $ PST.score pst) 0.0

decompose :: Formula.NodeRef -> Formula -> Maybe (Formula.NodeType, Formula.NodeType, Bool, HashSet (HashSet Formula.NodeRef))
decompose ref f = Nothing{-case Formula.entryNode $ Formula.augmentWithEntry ref f of
    Formula.Composed op children -> let dec = decomposeChildren Set.empty $ Set.map (`Formula.augmentWithEntry` f) children
                                in  if Set.size dec == 1 then Nothing else Just (op, decOp op, sign, dec)
    _ -> Nothing
    where
        decomposeChildren :: HashSet (HashSet Formula.RefWithNode) -> HashSet Formula.RefWithNode -> HashSet (HashSet Formula.NodeRef)
        decomposeChildren dec children
            | Set.null children = Set.map (Set.map Formula.entryRef) dec
            | otherwise =
                let first               = getFirst children
                    (new, _, children') = findFixpoint (Set.singleton first) (Formula.entryRFuncs first) (Set.delete first children)
                in  decomposeChildren (Set.insert new dec) children'

        findFixpoint :: HashSet Formula.RefWithNode -> HashSet RFuncLabel -> HashSet Formula.RefWithNode -> (HashSet Formula.RefWithNode, HashSet RFuncLabel, HashSet Formula.RefWithNode)
        findFixpoint cur curRFs children
            | Set.null children || List.null withSharedRFs = (cur, curRFs, children)
            | otherwise                                    = findFixpoint cur' curRFs' children'
            where
                (withSharedRFs, withoutSharedRFs) = List.partition (not . Set.null . Set.intersection curRFs . Formula.entryRFuncs) $ Set.toList children
                cur'      = Set.union cur $ Set.fromList withSharedRFs
                curRFs'   = Set.foldr (\c curRFs -> Set.union curRFs $ Formula.entryRFuncs c) curRFs $ Set.fromList withSharedRFs
                children' = Set.fromList withoutSharedRFs
        decOp op
            | sign = op
            | otherwise = case op of
                Formula.And -> Formula.Or
                Formula.Or  -> Formula.And
        sign = case ref of
            Formula.RefComposed sign _ -> sign
            _                      -> error "nodes other than composed ones have to sign"-}

determineSplitPoint :: RFuncLabel -> Interval -> Probability -> Probability -> (Probability -> Rational) -> HashMap RFuncLabel (Interval, Int) -> Formula.RefWithNode -> Formula -> Rational
determineSplitPoint rf (lower,upper) pUntilLower pUntilUpper icdf prevChoicesReal fEntry f = fst $ head list
    where
        list = sortWith (\(point,score) -> -score) (Map.toList $ pointsWithScore fEntry)
        listTrace = trace (show list ++ show rf ++ show (Formula.entryRef fEntry)) list
        pointsWithScore entry
            | Set.member rf $ Formula.entryRFuncs entry = case Formula.entryNode entry of
                Formula.Composed op children  -> foldr combine Map.empty [pointsWithScore $ Formula.augmentWithEntry c f | c <- Set.toList children]
                Formula.BuildInPredicate pred -> Map.fromList $ points pred
                _                         -> Map.empty
            | otherwise = Map.empty

        points (AST.RealIn _ (l,u)) = mapMaybe
                                        (\x -> case x of
                                            Inf      -> Nothing
                                            Open p   -> Just (p, 1.0)
                                            Closed p -> Just (p, 1.0)
                                        ) [l,u]
        points pred = if Set.size (AST.predRandomFunctions pred) == 2 then points'' else error "determineSplitPoint: not implemented"
            where
                otherRf = let [x,y] = Set.toList $ AST.predRandomFunctions pred in if x == rf then y else x
                mbOtherInterv = Map.lookup otherRf prevChoicesReal
                points' = case mbOtherInterv of
                    Nothing -> []
                    Just ((otherLower, otherUpper), _) ->
                        -- points must be in interval and not at boundary
                        filter (\p -> Interval.PointPlus p > Interval.toPoint Lower lower && Interval.PointMinus p < Interval.toPoint Upper upper) rationalPoints
                        where
                            -- can only split at rational points
                            rationalPoints = mapMaybe Interval.pointRational [Interval.toPoint Lower otherLower, Interval.toPoint Upper otherUpper]

                -- split probability mass in two equal part if no other split is possible
                points''
                    | null points' = [(icdf ((pUntilLower + pUntilUpper)/2), 1.0/fromIntegral (Set.size $ AST.predRandomFunctions pred))]
                    | otherwise    = [(p,1.0) | p <- points']

        combine :: HashMap Rational Double -> HashMap Rational Double -> HashMap Rational Double
        combine x y = foldr (\(p,score) map -> Map.insert p (score + Map.lookupDefault 0.0 p map) map) y $ Map.toList x
