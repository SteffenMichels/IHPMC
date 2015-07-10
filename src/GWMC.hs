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
    ) where
import NNF (NNF)
import qualified NNF
import PST (PST)
import qualified PST
import BasicTypes
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified AST
import Data.Maybe (fromJust)
import Text.Printf (printf)

gwmc :: PredicateLabel -> Map RFuncLabel [AST.RFuncDef] -> NNF -> ([ProbabilityBounds], NNF)
gwmc query rfuncDefs nnf = gwmc' nnf $ PST.empty $ NNF.uncondNodeLabel query
    where
        gwmc' :: NNF -> PST -> ([ProbabilityBounds], NNF)
        gwmc' nnf pst = case iterate nnf pst of
            Nothing           -> ([], nnf)
            Just (nnf', pst') -> let (bounds, nnf'') = gwmc' nnf' pst' in (PST.bounds pst' : bounds, nnf'')

        iterate :: NNF -> PST -> Maybe (NNF, PST)
        iterate nnf (PST.Choice rFuncLabel p left right) = case iterate nnf left of
            Just (nnf', left') -> Just (nnf', PST.Choice rFuncLabel p left' right)
            Nothing -> case iterate nnf right of
                Just (nnf', right') -> Just (nnf', PST.Choice rFuncLabel p left right')
                Nothing -> Nothing
        iterate nnf (PST.Finished _) = Nothing
        iterate nnf (PST.Unfinished nnfLabel) = Just (nnf'', PST.Choice rFuncLabel falseP left right) where
            rFuncLabel = Set.findMin $ NNF.randomFunctions nnfLabel nnf
            (leftNNFLabel,  nnf')  = NNF.condition nnfLabel rFuncLabel False nnf
            (rightNNFLabel, nnf'') = NNF.condition nnfLabel rFuncLabel True nnf'
            left  = toPSTNode leftNNFLabel
            right = toPSTNode rightNNFLabel
            falseP = case Map.lookup rFuncLabel rfuncDefs of
                Just (AST.Flip p:_) -> 1-p
                _                   -> error $ printf "no definition for random function '%s'" rFuncLabel

            toPSTNode nnfLabel = case NNF.deterministicValue nnfLabel nnf'' of
                Just val -> PST.Finished val
                Nothing  -> PST.Unfinished nnfLabel
