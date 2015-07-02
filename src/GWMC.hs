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
import qualified AST

gwmc :: PredicateLabel -> NNF -> [ProbabilityBounds]
gwmc query nnf = gwmc' nnf $ PST.empty $ NNF.uncondNodeLabel query
    where
        gwmc' :: NNF -> PST -> [ProbabilityBounds]
        gwmc' nnf pst = case GWMC.iterate nnf pst of
            Nothing           -> []
            Just (nnf', pst') -> PST.bounds pst' : gwmc' nnf' pst'

iterate :: NNF -> PST -> Maybe (NNF, PST)
iterate nnf (PST.Choice rFuncLabel p left right) = case GWMC.iterate nnf left of
    Just (nnf', left') -> Just (nnf', PST.Choice rFuncLabel p left' right)
    Nothing -> case GWMC.iterate nnf right of
        Just (nnf', right') -> Just (nnf', PST.Choice rFuncLabel p left right')
        Nothing -> Nothing
iterate nnf (PST.Finished _) = Nothing
iterate nnf (PST.Unfinished nnfLabel) = Just (nnf'', PST.Choice rFuncLabel 0.5 left right) where
    rFuncLabel = Set.findMin $ NNF.randomFunctions nnfLabel nnf
    (leftNNFLabel,  nnf')  = NNF.condition nnfLabel rFuncLabel False nnf
    (rightNNFLabel, nnf'') = NNF.condition nnfLabel rFuncLabel True nnf'
    left  = toPSTNode leftNNFLabel
    right = toPSTNode rightNNFLabel

    toPSTNode nnfLabel = case NNF.deterministicValue nnfLabel of
        Just val -> PST.Finished val
        Nothing  -> PST.Unfinished nnfLabel
