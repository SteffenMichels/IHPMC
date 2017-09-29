--The MIT License (MIT)
--
--Copyright (c) 2016-2017 Steffen Michels (mail@steffen-michels.de)
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
{-# LANGUAGE Strict#-}
#endif

module GroundedASTCommon ( GroundedASTCommon(..)
                         , BuildInPredicateCommon(..)
                         , TypedBuildInPredCommon(..)
                         , PFunc(..)
                         , ExprCommon(..)
                         , PredicateLabel(..)
                         , ConstantExpr(..)
                         , PFuncDefCommon(..)
                         , Addition
                         , Ineq
                         , AST.IneqOp(..)
                         , RealN
                         , Object
                         , Placeholder
                         , RuleBodyCommon(..)
                         , RuleBodyElementCommon(..)
                         , deterministicValue
                         , deterministicValueTyped
                         , groundedAstToText
                         , exprToText
                         , typedBuildInPredToText
                         , pFuncToText
                         , ruleBodyElementToText
                         , predicateLabelToText
                         ) where
import qualified AST
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import GHC.Generics (Generic)
import Interval ((~<), (~>), (~<=), (~>=))
import qualified Interval
import Data.Char (toLower)
import Numeric (fromRat)
import Util
import Probability
import TextShow
import Data.Text (Text)
import Data.Monoid ((<>))
import qualified Data.Text.Lazy.Builder as TB
import qualified Data.Text.Lazy as LT

-- use sets here to avoid duplicate elements
data GroundedASTCommon pFuncLabel = GroundedAST
    { rules     :: Map PredicateLabel (Set (RuleBodyCommon pFuncLabel))
    , queries   :: Set (RuleBodyElementCommon pFuncLabel)
    , evidence  :: Set (RuleBodyElementCommon pFuncLabel)
    }

groundedAstToText :: GroundedASTCommon pFuncLabel
                  -> (pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder)
                  -> Map Int Text
                  -> Map Int (Int, [AST.ConstantExpr])
                  -> Builder
groundedAstToText ast pFuncLabelToText ids2str ids2label = rulesStr <> queryStr <> evStr
    where
    rulesStr     = mconcat $ mconcat [
                        let lStr = predicateLabelToText label ids2str ids2label
                        in  [lStr <> " <- " <> ruleBodyToText body pFuncLabelToText ids2str ids2label <> ".\n" | body <- Set.toList bodies]
                   | (label, bodies) <- Map.toList $ rules ast]
    queryStr     = mconcat ["query "    <> ruleBodyElementToText query pFuncLabelToText ids2str ids2label <> ".\n" | query <- Set.toList $ queries  ast]
    evStr        = mconcat ["evidence " <> ruleBodyElementToText ev    pFuncLabelToText ids2str ids2label <> ".\n" | ev    <- Set.toList $ evidence ast]

-- propositional version of data types, similarly present in AST (without argument, after grounding)
newtype PredicateLabel = PredicateLabel Int deriving (Eq, Generic, Ord)

predicateLabelToText :: PredicateLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
predicateLabelToText (PredicateLabel idNr) ids2str ids2label =
    AST.predicateLabelToText (AST.PredicateLabel label) ids2str <>
    if null args then "" else "(" <> showbLst args <> ")"
    where (label, args) = Map.findWithDefault undefined idNr ids2label
instance Hashable PredicateLabel

data PFunc pFuncLabel a = PFunc pFuncLabel (PFuncDefCommon pFuncLabel a)
-- there should never be more than one PF with the same label, so compare/hash only label and ignore definition
instance Eq pFuncLabel => Eq (PFunc pFuncLabel a) where
    PFunc x _ == PFunc y _ = x == y
instance Ord pFuncLabel => Ord (PFunc pFuncLabel a) where
    PFunc x _ <= PFunc y _ = x <= y
instance Hashable pFuncLabel => Hashable (PFunc pFuncLabel a) where
    hashWithSalt salt (PFunc label _) = Hashable.hashWithSalt salt label

pFuncToText :: PFunc pFuncLabel a
            -> (pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder)
            -> Map Int Text
            -> Map Int (Int, [AST.ConstantExpr])
            -> Builder
pFuncToText (PFunc l _) pFuncLabelToText = pFuncLabelToText l

data PFuncDefCommon pFuncLabel a where
    Flip                :: Probability                                            -> PFuncDefCommon pFuncLabel Bool
    RealDist            :: (Rational -> Probability) -> (Probability -> Rational) -> PFuncDefCommon pFuncLabel RealN
    StrDist             :: [(Probability, Text)]                                  -> PFuncDefCommon pFuncLabel Text
    UniformObjDist      :: Integer                                                -> PFuncDefCommon pFuncLabel Object
    UniformOtherObjDist :: PFunc pFuncLabel Object                                -> PFuncDefCommon pFuncLabel Object

newtype RuleBodyCommon pFuncLabel = RuleBody (Set (RuleBodyElementCommon pFuncLabel)) deriving (Eq, Generic, Ord)

ruleBodyToText :: RuleBodyCommon pFuncLabel
               -> (pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder)
               -> Map Int Text
               -> Map Int (Int, [AST.ConstantExpr])
               -> Builder
ruleBodyToText (RuleBody elements) pFuncLabelToText ids2str ids2label =
    toTextLst (Set.toList elements) (\x -> ruleBodyElementToText x pFuncLabelToText ids2str ids2label)
instance (Generic pFuncLabel, Hashable pFuncLabel) => Hashable (RuleBodyCommon pFuncLabel)

data RuleBodyElementCommon pFuncLabel = UserPredicate    PredicateLabel
                                      | BuildInPredicate (BuildInPredicateCommon pFuncLabel)
                                      deriving (Eq, Generic, Ord)

ruleBodyElementToText :: RuleBodyElementCommon pFuncLabel
                      -> (pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder)
                      -> Map Int Text
                      -> Map Int (Int, [AST.ConstantExpr])
                      -> Builder
ruleBodyElementToText (UserPredicate label)  _                = predicateLabelToText label
ruleBodyElementToText (BuildInPredicate prd) pFuncLabelToText = buildInPredToText    prd   pFuncLabelToText
instance (Generic pFuncLabel, Hashable pFuncLabel) => Hashable (RuleBodyElementCommon pFuncLabel)

data BuildInPredicateCommon pFuncLabel = BuildInPredicateBool (TypedBuildInPredCommon pFuncLabel Bool)
                                       | BuildInPredicateReal (TypedBuildInPredCommon pFuncLabel RealN)
                                       | BuildInPredicateStr  (TypedBuildInPredCommon pFuncLabel Text)
                                       | BuildInPredicateInt  (TypedBuildInPredCommon pFuncLabel Integer)
                                       | BuildInPredicateObj  (TypedBuildInPredCommon pFuncLabel Object)
                                       | BuildInPredicatePh   (TypedBuildInPredCommon pFuncLabel Placeholder)

deriving instance Eq      pFuncLabel => Eq      (BuildInPredicateCommon pFuncLabel)
deriving instance Generic pFuncLabel => Generic (BuildInPredicateCommon pFuncLabel)
deriving instance Ord     pFuncLabel => Ord     (BuildInPredicateCommon pFuncLabel)
instance (Generic pFuncLabel, Hashable pFuncLabel) => Hashable (BuildInPredicateCommon pFuncLabel)
buildInPredToText :: BuildInPredicateCommon pFuncLabel
                  -> (pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder)
                  -> Map Int Text
                  -> Map Int (Int, [AST.ConstantExpr])
                  -> Builder
buildInPredToText (BuildInPredicateBool b) = typedBuildInPredToText b
buildInPredToText (BuildInPredicateReal r) = typedBuildInPredToText r
buildInPredToText (BuildInPredicateStr  s) = typedBuildInPredToText s
buildInPredToText (BuildInPredicateInt  i) = typedBuildInPredToText i
buildInPredToText (BuildInPredicateObj  o) = typedBuildInPredToText o
buildInPredToText (BuildInPredicatePh   p) = typedBuildInPredToText p

data TypedBuildInPredCommon pFuncLabel a
    where
    Equality ::           Bool       -> ExprCommon pFuncLabel a -> ExprCommon pFuncLabel a -> TypedBuildInPredCommon pFuncLabel a
    Ineq     :: Ineq a => AST.IneqOp -> ExprCommon pFuncLabel a -> ExprCommon pFuncLabel a -> TypedBuildInPredCommon pFuncLabel a
    Constant ::           Bool                                                 -> TypedBuildInPredCommon pFuncLabel a

deriving instance Eq pFuncLabel  => Eq  (TypedBuildInPredCommon pFuncLabel a)
deriving instance Ord pFuncLabel => Ord (TypedBuildInPredCommon pFuncLabel a)

typedBuildInPredToText :: TypedBuildInPredCommon pFuncLabel a
                       -> (pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder)
                       -> Map Int Text
                       -> Map Int (Int, [AST.ConstantExpr])
                       -> Builder
typedBuildInPredToText (Equality eq exprX exprY) pFuncLabelToText ids2str ids2label =
    exprToText exprX pFuncLabelToText ids2str ids2label <> " " <> (if eq then "=" else "/=") <> " " <> exprToText exprY pFuncLabelToText ids2str ids2label
typedBuildInPredToText (Ineq     op exprX exprY) pFuncLabelToText ids2str ids2label =
    exprToText exprX pFuncLabelToText ids2str ids2label <> " " <> showb op <> " " <> exprToText exprY pFuncLabelToText ids2str ids2label
typedBuildInPredToText (Constant cnst) _ _ _ = showb cnst
instance Hashable pFuncLabel => Hashable (TypedBuildInPredCommon pFuncLabel a)
    where
    hashWithSalt salt (Equality eq exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt eq) exprX) exprY
    hashWithSalt salt (Ineq     op exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt op) exprX) exprY
    hashWithSalt salt (Constant b)              = Hashable.hashWithSalt salt b

data ExprCommon pFuncLabel a
    where
    ConstantExpr ::               ConstantExpr a                                     -> ExprCommon pFuncLabel a
    PFuncExpr    ::               PFunc pFuncLabel a                                 -> ExprCommon pFuncLabel a
    Sum          :: Addition a => ExprCommon pFuncLabel a -> ExprCommon pFuncLabel a -> ExprCommon pFuncLabel a

deriving instance Eq pFuncLabel  => Eq  (ExprCommon pFuncLabel a)
deriving instance Ord pFuncLabel => Ord (ExprCommon pFuncLabel a)

exprToText :: ExprCommon pFuncLabel a
           -> (pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder)
           -> Map Int Text
           -> Map Int (Int, [AST.ConstantExpr])
           -> Builder
exprToText (ConstantExpr cExpr) _                _       _         = showb cExpr
exprToText (PFuncExpr pf)       pFuncLabelToText ids2str ids2label = pFuncToText pf pFuncLabelToText ids2str ids2label
exprToText (Sum x y)            pFuncLabelToText ids2str ids2label =
    exprToText x pFuncLabelToText ids2str ids2label <> " + " <> exprToText y pFuncLabelToText ids2str ids2label
instance Hashable pFuncLabel => Hashable (ExprCommon pFuncLabel a)
    where
    hashWithSalt salt (ConstantExpr cExpr) = Hashable.hashWithSalt salt cExpr
    hashWithSalt salt (PFuncExpr r)        = Hashable.hashWithSalt salt r
    hashWithSalt salt (Sum x y)            = Hashable.hashWithSalt (Hashable.hashWithSalt salt x) y

data ConstantExpr a
    where
    BoolConstant :: Bool     -> ConstantExpr Bool
    RealConstant :: Rational -> ConstantExpr RealN
    StrConstant  :: Text     -> ConstantExpr Text
    IntConstant  :: Integer  -> ConstantExpr Integer
    ObjConstant  :: Integer  -> ConstantExpr Object
    Placeholder  :: Text     -> ConstantExpr Placeholder

deriving instance Eq (ConstantExpr a)
instance TextShow (ConstantExpr a) where
    showb (BoolConstant cnst) = TB.fromLazyText $ LT.map toLower $ TB.toLazyText $ showb cnst
    showb (RealConstant cnst) = showb (fromRat cnst::Float)
    showb (StrConstant  cnst) = TB.fromText cnst
    showb (IntConstant  cnst) = showb cnst
    showb (ObjConstant  cnst) = "#" <> showb cnst
    showb (Placeholder  ph)   = "_" <> TB.fromText ph
instance Hashable (ConstantExpr a)
    where
    hashWithSalt salt (BoolConstant b) = Hashable.hashWithSalt salt b
    hashWithSalt salt (RealConstant r) = Hashable.hashWithSalt salt r
    hashWithSalt salt (StrConstant  s) = Hashable.hashWithSalt salt s
    hashWithSalt salt (IntConstant  i) = Hashable.hashWithSalt salt i
    hashWithSalt salt (ObjConstant  o) = Hashable.hashWithSalt salt o
    hashWithSalt salt (Placeholder  p) = Hashable.hashWithSalt salt p
instance Ord (ConstantExpr a)
    where
    BoolConstant x <= BoolConstant y = x <= y
    RealConstant x <= RealConstant y = x <= y
    StrConstant  x <= StrConstant  y = x <= y
    IntConstant  x <= IntConstant  y = x <= y
    ObjConstant  x <= ObjConstant  y = x <= y
    Placeholder  x <= Placeholder  y = x <= y
#if __GLASGOW_HASKELL__ < 800
    _              <= _              = undefined
#endif

data RealN       -- phantom for real numbered expression etc.
data Object      -- phantom for expressions about objects
data Placeholder -- phantom type for placeholder expressions in AstPreprocessor

class Addition a
instance Addition Integer
instance Addition RealN

class Ineq a
instance Ineq Integer
instance Ineq RealN

deterministicValue :: Eq pFuncLabel => BuildInPredicateCommon pFuncLabel -> Maybe Bool
deterministicValue (BuildInPredicateBool b) = deterministicValueTyped b
deterministicValue (BuildInPredicateReal r) = deterministicValueTyped r
deterministicValue (BuildInPredicateStr  s) = deterministicValueTyped s
deterministicValue (BuildInPredicateInt  i) = deterministicValueTyped i
deterministicValue (BuildInPredicateObj  o) = deterministicValueTyped o
deterministicValue (BuildInPredicatePh   p) = deterministicValueTyped p

deterministicValueTyped :: Eq pFuncLabel => TypedBuildInPredCommon pFuncLabel a -> Maybe Bool
deterministicValueTyped (Equality eq (ConstantExpr left) (ConstantExpr right))              = Just $ (if eq then (==) else (/=)) left right
deterministicValueTyped (Equality eq (PFuncExpr left)    (PFuncExpr right)) | left == right = Just eq
deterministicValueTyped (Ineq     op (ConstantExpr left) (ConstantExpr right))              = Just evalPred
    where
    evalPred = case op of
        AST.Lt   -> left <  right
        AST.LtEq -> left <= right
        AST.Gt   -> left >  right
        AST.GtEq -> left >= right
deterministicValueTyped (Constant val) = Just val
deterministicValueTyped _              = Nothing

