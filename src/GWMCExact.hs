-----------------------------------------------------------------------------
--
-- Module      :  GWMCExact
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

module GWMCExact
    ( gwmc
    ) where
import BasicTypes
import NNF (NNF)
import qualified NNF
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import GHC.Exts (sortWith)
import qualified AST

gwmc :: PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> NNF -> (Probability, NNF)
gwmc query rfuncDefs nnf = gwmc' (NNF.augmentWithEntry (NNF.RefComposed True $ NNF.uncondNodeLabel query) nnf) nnf
    where
        gwmc' entry nnf = case NNF.entryNode entry of
            NNF.Deterministic True  -> (1.0, nnf)
            NNF.Deterministic False -> (0.0, nnf)
            _ -> case Map.lookup rf rfuncDefs of
                Just (AST.Flip p:_) -> (p*pLeft + (1-p)*pRight, nnf'''')
                    where
                        (leftEntry,  nnf')   = NNF.conditionBool entry rf True nnf
                        (pLeft, nnf'')       = gwmc' leftEntry nnf'
                        (rightEntry, nnf''') = NNF.conditionBool entry rf False nnf''
                        (pRight, nnf'''')    = gwmc' rightEntry nnf'''
                Just (AST.RealDist cdf icdf:_) -> error "not implemented"
                where
                    xxx = sortWith (\(rf, (p,n)) -> -abs (p-n)) $ Map.toList $ NNF.entryScores entry
                    --xxxy = trace (foldl (\str (rf,(p,n)) -> str ++ "\n" ++ (show (p+n)) ++ " " ++ rf) ("\n" ++ show nnfLabel) xxx) xxx
                    rf = fst $ head xxx
