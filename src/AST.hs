--The MIT License (MIT)
--
--Copyright (c) 2016 Steffen Michels (mail@steffen-michels.de)
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

{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE Strict #-}
#endif

module AST
    ( AST(..)
    , PredicateLabel(..)
    , PFuncLabel(..)
    , RuleBody(..)
    , RuleBodyElement(..)
    , BuildInPredicate(..)
    , HeadArgument(..)
    , PFuncDef(..)
    , Expr(..)
    , ConstantExpr(..)
    , IneqOp(..)
    , VarName(..)
    , varsInExpr
    , varsInRuleBodyElement
    , negateOp
    , mapExprsInRuleBodyElement
    , mapExprsInRuleBodyElementM
    , mapAccExpr
    , mapAccExprsInRuleBodyElement
    , predicateLabelToText
    , pFuncLabelToText
    , ruleBodyElementToText
    , exprToText
    ) where
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Text.Printf (printf)
import Data.Char (toLower)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Numeric (fromRat)
import Probability
import Util
import Control.Arrow (second)
import Data.Traversable (forM, mapAccumL)

data AST = AST
    { pFuncDefs :: HashMap (PFuncLabel, Int)     [([HeadArgument], PFuncDef)] -- first matching def applies
    , rules     :: HashMap (PredicateLabel, Int) [([HeadArgument], RuleBody)]
    , queries   :: [RuleBodyElement]
    , evidence  :: [RuleBodyElement]
    }

newtype PredicateLabel = PredicateLabel Int deriving (Eq, Generic)
predicateLabelToText :: PredicateLabel -> HashMap Int String -> String
predicateLabelToText (PredicateLabel idNr) = Map.lookupDefault undefined idNr
instance Hashable PredicateLabel

newtype PFuncLabel = PFuncLabel Int deriving (Eq, Generic)
pFuncLabelToText :: PFuncLabel -> HashMap Int String -> String
pFuncLabelToText (PFuncLabel idNr) = Map.lookupDefault undefined idNr
instance Hashable PFuncLabel

data PFuncDef = Flip     Probability
              | RealDist (Rational -> Probability) (Probability -> Rational)
              | StrDist  [(Probability, String)]

instance Show PFuncDef
    where
    show (Flip p)        = printf "flip(%s)" $ show p
    show (RealDist _ _)  = printf "realDist"
    show (StrDist pairs) = printf "{%s}" $ showLst pairs

newtype RuleBody = RuleBody [RuleBodyElement] deriving (Eq, Generic)
instance Hashable RuleBody

data RuleBodyElement = UserPredicate    PredicateLabel [Expr]
                     | BuildInPredicate BuildInPredicate
                     deriving (Eq, Generic)
ruleBodyElementToText :: RuleBodyElement -> HashMap Int String -> String
ruleBodyElementToText (UserPredicate label args) ids2str =
    printf "%s(%s)" (predicateLabelToText label ids2str) (toTextLst args (`exprToText` ids2str))
ruleBodyElementToText (BuildInPredicate prd) ids2str = buildInPredicateToText prd ids2str

instance Hashable RuleBodyElement

-- the arguments in head definitions are restricted to variables and constants
data HeadArgument = ArgVariable VarName
                  | ArgConstant ConstantExpr
                  | ArgDontCareVariable
                  deriving (Eq, Show, Generic)
instance Hashable HeadArgument

data VarName = VarName String
             | TempVar Integer
             deriving (Eq, Generic)
instance Show VarName
    where
    show (VarName str) = str
    show (TempVar i)   = printf "_%i" i
instance Hashable VarName

data BuildInPredicate = Equality Bool Expr Expr
                      | Ineq     IneqOp Expr Expr
                      deriving (Eq, Generic)
buildInPredicateToText :: BuildInPredicate -> HashMap Int String -> String
buildInPredicateToText (Equality eq exprX exprY) ids2str =
    printf "%s %s %s" (exprToText exprX ids2str) (if eq then "=" else "/=") (exprToText exprY ids2str)
buildInPredicateToText (Ineq     op exprX exprY) ids2str =
    printf "%s %s %s" (exprToText exprX ids2str) (show op) (exprToText exprY ids2str)
instance Hashable BuildInPredicate

data IneqOp = Lt | LtEq | Gt | GtEq deriving (Eq, Generic)
instance Show IneqOp
    where
    show Lt   = "<"
    show LtEq = "<="
    show Gt   = ">"
    show GtEq = ">="
instance Hashable IneqOp

data Expr = ConstantExpr ConstantExpr
          | PFunc        PFuncLabel [Expr]
          | Variable     VarName
          | Sum          Expr Expr
          deriving (Eq, Generic)

exprToText :: Expr -> HashMap Int String -> String
exprToText (ConstantExpr cnst) _ = show cnst
exprToText (PFunc pf args) ids2str =
    printf "~%s(%s)" (pFuncLabelToText pf ids2str) $ toTextLst args (`exprToText` ids2str)
exprToText (Variable var) _ = show var
exprToText (Sum x y) ids2str = printf "%s + %s" (exprToText x ids2str) (exprToText y ids2str)
instance Hashable Expr

data ConstantExpr = BoolConstant Bool
                  | RealConstant Rational
                  | StrConstant  String
                  | IntConstant  Integer
                  deriving (Eq, Generic)

instance Show ConstantExpr
    where
    show (BoolConstant cnst) = toLower <$> show cnst
    show (RealConstant cnst) = printf "%f" (fromRat cnst::Float)
    show (StrConstant  cnst) = printf "\"%s\"" cnst
    show (IntConstant  cnst) = show cnst
instance Hashable ConstantExpr

negateOp :: IneqOp -> IneqOp
negateOp Lt   = GtEq
negateOp LtEq = Gt
negateOp Gt   = LtEq
negateOp GtEq = Lt

varsInRuleBodyElement :: RuleBodyElement -> Bool
varsInRuleBodyElement (UserPredicate _ args) = any varsInExpr args
varsInRuleBodyElement (BuildInPredicate bip) = varsInBip bip

varsInBip :: BuildInPredicate -> Bool
varsInBip (AST.Equality _ exprX exprY) = varsInExpr exprX || varsInExpr exprY
varsInBip (AST.Ineq _     exprX exprY) = varsInExpr exprX || varsInExpr exprY

varsInExpr :: Expr -> Bool
varsInExpr (Variable _)      = True
varsInExpr (ConstantExpr _)  = False
varsInExpr (PFunc _ args)    = any varsInExpr args
varsInExpr (Sum exprX exprY) = varsInExpr exprX || varsInExpr exprY

-- traverses top-down
mapExprsInRuleBodyElement :: (AST.Expr -> AST.Expr) -> AST.RuleBodyElement -> AST.RuleBodyElement
mapExprsInRuleBodyElement f el = snd $ mapAccExprsInRuleBodyElement (\a e -> (a, f e)) () el

mapExprsInRuleBodyElementM :: Monad m
                           => AST.RuleBodyElement
                           -> (AST.Expr -> m AST.Expr)
                           -> (AST.Expr -> m AST.Expr)
                           -> m AST.RuleBodyElement
mapExprsInRuleBodyElementM el userPF bipF = case el of
    AST.UserPredicate label args -> do
        args' <- forM args (`mapExprM` userPF)
        return $ AST.UserPredicate label args'
    AST.BuildInPredicate bip -> do
        bip' <- case bip of
            AST.Equality eq exprX exprY -> do exprX' <- mapExprM exprX bipF
                                              exprY' <- mapExprM exprY bipF
                                              return $ AST.Equality eq exprX' exprY'
            AST.Ineq op exprX exprY     -> do exprX' <- mapExprM exprX bipF
                                              exprY' <- mapExprM exprY bipF
                                              return $ AST.Ineq op exprX' exprY'
        return $ AST.BuildInPredicate bip'

mapExprM :: Monad m => AST.Expr -> (AST.Expr -> m AST.Expr) -> m AST.Expr
mapExprM expr f = do
    expr' <- f expr
    case expr' of
        AST.Sum exprX exprY -> do exprX' <- mapExprM exprX f
                                  exprY' <- mapExprM exprY f
                                  return $ AST.Sum exprX' exprY'
        AST.PFunc label args -> do
            args' <- forM args (`mapExprM` f)
            return $ AST.PFunc label args'
        _ -> return expr'

mapAccExprsInRuleBodyElement :: (a -> AST.Expr -> (a, AST.Expr)) -> a -> AST.RuleBodyElement -> (a, AST.RuleBodyElement)
mapAccExprsInRuleBodyElement f acc el = case el of
    AST.UserPredicate label args -> second (AST.UserPredicate label) $ mapAccumL (mapAccExpr f) acc args
    AST.BuildInPredicate bip -> second AST.BuildInPredicate $ case bip of
        AST.Equality eq exprX exprY -> let (acc',  exprX') = mapAccExpr f acc  exprX
                                           (acc'', exprY') = mapAccExpr f acc' exprY
                                       in  (acc'', AST.Equality eq exprX' exprY')
        AST.Ineq op exprX exprY     -> let (acc',  exprX') = mapAccExpr f acc  exprX
                                           (acc'', exprY') = mapAccExpr f acc' exprY
                                       in  (acc'', AST.Ineq op exprX' exprY')

mapAccExpr :: (a -> AST.Expr -> (a, AST.Expr)) -> a -> AST.Expr -> (a, AST.Expr)
mapAccExpr f acc expr = case expr' of
    AST.Sum exprX exprY -> let (acc'',  exprX') = mapAccExpr f acc'  exprX
                               (acc''', exprY') = mapAccExpr f acc'' exprY
                           in (acc''', AST.Sum exprX' exprY')
    AST.PFunc label args -> second (AST.PFunc label) $ mapAccumL (mapAccExpr f) acc' args
    _ -> (acc', expr')
    where
    (acc', expr') = f acc expr
