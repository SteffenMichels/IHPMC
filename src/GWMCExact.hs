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
import Formula (Formula)
import qualified Formula
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as Map
import GHC.Exts (sortWith)
import qualified AST

gwmc :: PredicateLabel -> HashMap RFuncLabel [AST.RFuncDef] -> Formula -> (Probability, Formula)
gwmc query rfuncDefs f = undefined--gwmc' (Formula.augmentWithEntry (Formula.RefComposed True $ Formula.uncondNodeLabel query) Formula) Formula
    where
        gwmc' entry f = case Formula.entryNode entry of
            Formula.Deterministic True  -> (1.0, f)
            Formula.Deterministic False -> (0.0, f)
            _ -> case Map.lookup rf rfuncDefs of
                Just (AST.Flip p:_) -> (p*pLeft + (1-p)*pRight, f'''')
                    where
                        (leftEntry,  f')   = Formula.conditionBool entry rf True f
                        (pLeft, f'')       = gwmc' leftEntry f'
                        (rightEntry, f''') = Formula.conditionBool entry rf False f''
                        (pRight, f'''')    = gwmc' rightEntry f'''
                Just (AST.RealDist cdf icdf:_) -> error "not implemented"
                where
                    xxx = sortWith (\(rf, s) -> s) $ Map.toList $ snd $ Formula.entryScores entry
                    --xxxy = trace (foldl (\str (rf,(p,n)) -> str ++ "\n" ++ (show (p+n)) ++ " " ++ rf) ("\n" ++ show FormulaLabel) xxx) xxx
                    rf = fst $ head xxx
