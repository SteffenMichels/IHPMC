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

module GroundedAST ( GroundedASTCommon(..)
                   , BuildInPredicateCommon(..)
                   , TypedBuildInPredCommon(..)
                   , PFunc(..)
                   , probabilisticFuncLabel
                   , probabilisticFuncDef
                   , objectPfNrObjects
                   , ExprCommon(..)
                   , PredicateLabel(..)
                   , ConstantExpr(..)
                   , PFuncDef(..)
                   , Addition
                   , Ineq
                   , AST.IneqOp(..)
                   , RealN
                   , Object
                   , Placeholder
                   , RuleBodyCommon(..)
                   , RuleBodyElementCommon(..)
                   , negatePred
                   , deterministicValue
                   , deterministicValueTyped
                   , possibleValuesStr
                   , simplifiedBuildInPred
                   , simplifiedExpr
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

groundedAstToText :: GroundedASTCommon pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
groundedAstToText ast ids2str ids2label = ""{-rulesStr <> queryStr <> evStr
    where
    rulesStr     = mconcat $ mconcat [
                        let lStr = predicateLabelToText label ids2str ids2label
                        in  [lStr <> " <- " <> ruleBodyToText body ids2str ids2label <> ".\n" | body <- Set.toList bodies]
                   | (label, bodies) <- Map.toList $ rules ast]
    queryStr     = mconcat ["query "    <> ruleBodyElementToText query ids2str ids2label <> ".\n" | query <- Set.toList $ queries  ast]
    evStr        = mconcat ["evidence " <> ruleBodyElementToText ev    ids2str ids2label <> ".\n" | ev    <- Set.toList $ evidence ast]-}

-- propositional version of data types, similarly present in AST (without argument, after grounding)
newtype PredicateLabel = PredicateLabel Int deriving (Eq, Generic, Ord)
--2
predicateLabelToText :: PredicateLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
predicateLabelToText (PredicateLabel idNr) ids2str ids2label =
    AST.predicateLabelToText (AST.PredicateLabel label) ids2str <>
    if null args then "" else "(" <> showbLst args <> ")"
    where (label, args) = Map.findWithDefault undefined idNr ids2label
instance Hashable PredicateLabel

data PFunc pFuncLabel a = PFunc pFuncLabel (PFuncDef a)
-- there should never be more than one PF with the same label, so compare/hash only label and ignore definition
instance Eq pFuncLabel => Eq (PFunc pFuncLabel a) where
    PFunc x _ == PFunc y _ = x == y
instance Ord pFuncLabel => Ord (PFunc pFuncLabel a) where
    PFunc x _ <= PFunc y _ = x <= y
instance Hashable pFuncLabel => Hashable (PFunc pFuncLabel a) where
    hashWithSalt salt (PFunc label _) = Hashable.hashWithSalt salt label

pFuncToText :: PFunc pFuncLabel a -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
pFuncToText (PFunc l _) = undefined--pFuncLabelToText l

data PFuncDef a where
    Flip                :: Probability                                            -> PFuncDef Bool
    RealDist            :: (Rational -> Probability) -> (Probability -> Rational) -> PFuncDef GroundedAST.RealN
    StrDist             :: [(Probability, Text)]                                  -> PFuncDef Text
    UniformObjDist      :: Integer                                                -> PFuncDef Object
    UniformOtherObjDist :: Int{-PFuncPhase2 Object-}                                     -> PFuncDef Object

-- 2
objectPfNrObjects :: PFunc pFuncLabel Object -> Integer
objectPfNrObjects pf = case GroundedAST.probabilisticFuncDef pf of
    GroundedAST.UniformObjDist n        -> n
    GroundedAST.UniformOtherObjDist pf' -> undefined--objectPfNrObjects pf'

--2
probabilisticFuncLabel :: PFunc pFuncLabel a -> pFuncLabel
probabilisticFuncLabel (PFunc label _) = label

--2
probabilisticFuncDef :: PFunc pFuncLabel a -> PFuncDef a
probabilisticFuncDef (PFunc _ def) = def

newtype RuleBodyCommon pFuncLabel = RuleBody (Set (RuleBodyElementCommon pFuncLabel)) deriving (Eq, Generic, Ord)

ruleBodyToText :: RuleBodyCommon pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
ruleBodyToText (RuleBody elements) ids2str ids2label = ""
    --toTextLst (Set.toList elements) (\x -> ruleBodyElementToText x ids2str ids2label)
instance (Generic pFuncLabel, Hashable pFuncLabel) => Hashable (RuleBodyCommon pFuncLabel)

data RuleBodyElementCommon pFuncLabel = UserPredicate    PredicateLabel
                                      | BuildInPredicate (BuildInPredicateCommon pFuncLabel)
                                      deriving (Eq, Generic, Ord)

--2
ruleBodyElementToText :: RuleBodyElementCommon pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
ruleBodyElementToText (UserPredicate label)  ids2str ids2label = ""--predicateLabelToText label ids2str ids2label
ruleBodyElementToText (BuildInPredicate prd) ids2str ids2label = ""--buildInPredToText    prd   ids2str ids2label
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
buildInPredToText :: BuildInPredicateCommon pFuncLabel -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
buildInPredToText (BuildInPredicateBool b) = undefined--typedBuildInPredToText b
buildInPredToText (BuildInPredicateReal r) = undefined--typedBuildInPredToText r
buildInPredToText (BuildInPredicateStr  s) = undefined--typedBuildInPredToText s
buildInPredToText (BuildInPredicateInt  i) = undefined--typedBuildInPredToText i
buildInPredToText (BuildInPredicateObj  o) = undefined--typedBuildInPredToText o
buildInPredToText (BuildInPredicatePh   p) = undefined--typedBuildInPredToText p

data TypedBuildInPredCommon pFuncLabel a
    where
    Equality ::           Bool       -> ExprCommon pFuncLabel a -> ExprCommon pFuncLabel a -> TypedBuildInPredCommon pFuncLabel a
    Ineq     :: Ineq a => AST.IneqOp -> ExprCommon pFuncLabel a -> ExprCommon pFuncLabel a -> TypedBuildInPredCommon pFuncLabel a
    Constant ::           Bool                                                 -> TypedBuildInPredCommon pFuncLabel a

deriving instance Eq pFuncLabel  => Eq  (TypedBuildInPredCommon pFuncLabel a)
deriving instance Ord pFuncLabel => Ord (TypedBuildInPredCommon pFuncLabel a)
--2
typedBuildInPredToText :: TypedBuildInPredCommon pFuncLabel a -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
typedBuildInPredToText (Equality eq exprX exprY) ids2str ids2label = ""
    --exprToText exprX ids2str ids2label <> " " <> (if eq then "=" else "/=") <> " " <> exprToText exprY ids2str ids2label
typedBuildInPredToText (Ineq     op exprX exprY) ids2str ids2label = ""
    --exprToText exprX ids2str ids2label <> " " <> showb op <> " " <> exprToText exprY ids2str ids2label
typedBuildInPredToText (Constant cnst)           _       _ = ""--showb cnst
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
--1
exprToText :: ExprCommon pFuncLabel a -> Map Int Text -> Map Int (Int, [AST.ConstantExpr]) -> Builder
exprToText (ConstantExpr cExpr) _       _         = ""--showb cExpr
exprToText (PFuncExpr pf)       ids2str ids2label = ""--pFuncToText pf ids2str ids2label
exprToText (Sum x y)            ids2str ids2label = ""
    --xprToText x ids2str ids2label <> " + " <> exprToText y ids2str ids2label
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

--2,1
data RealN       -- phantom for real numbered expression etc.
--2,1
data Object      -- phantom for expressions about objects
--1
data Placeholder -- phantom type for placeholder expressions in AstPreprocessor

--1
class Addition a
instance Addition Integer
instance Addition RealN

--1
class Ineq a
instance Ineq Integer
instance Ineq RealN

negatePred :: TypedBuildInPredCommon pFuncLabel a -> TypedBuildInPredCommon pFuncLabel a
negatePred (Equality eq exprX exprY) = Equality (not eq) exprX exprY
negatePred (Ineq     op exprX exprY) = Ineq (AST.negateOp op) exprX exprY
negatePred (Constant cnst)           = Constant $ not cnst

--1,2
deterministicValue :: Eq pFuncLabel => BuildInPredicateCommon pFuncLabel -> Maybe Bool
deterministicValue (BuildInPredicateBool b) = deterministicValueTyped b
deterministicValue (BuildInPredicateReal r) = deterministicValueTyped r
deterministicValue (BuildInPredicateStr  s) = deterministicValueTyped s
deterministicValue (BuildInPredicateInt  i) = deterministicValueTyped i
deterministicValue (BuildInPredicateObj  o) = deterministicValueTyped o
deterministicValue (BuildInPredicatePh   p) = deterministicValueTyped p

-- 2
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

--2
possibleValuesStr :: (Hashable pFuncLabel, Ord pFuncLabel) => ExprCommon pFuncLabel Text -> Map pFuncLabel (Set Text) -> Set Text
possibleValuesStr (ConstantExpr (StrConstant cnst)) _ = Set.singleton cnst
possibleValuesStr (PFuncExpr (PFunc pfLabel (StrDist elements))) sConds =
    Map.findWithDefault (Set.fromList $ snd <$> elements) pfLabel sConds
possibleValuesStr _ _ = undefined

--1
simplifiedBuildInPred :: BuildInPredicateCommon pFuncLabel -> BuildInPredicateCommon pFuncLabel
simplifiedBuildInPred (BuildInPredicateBool prd) = BuildInPredicateBool $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateReal prd) = BuildInPredicateReal $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateInt  prd) = BuildInPredicateInt  $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateStr  prd) = BuildInPredicateStr  $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateObj  prd) = BuildInPredicateObj  $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicatePh   prd) = BuildInPredicatePh   $ simplifiedTypedBuildInPred prd

simplifiedTypedBuildInPred :: TypedBuildInPredCommon pFuncLabel a -> TypedBuildInPredCommon pFuncLabel a
simplifiedTypedBuildInPred (Equality eq exprX exprY) = Equality eq (simplifiedExpr exprX) (simplifiedExpr exprY)
simplifiedTypedBuildInPred (Ineq     op exprX exprY) = Ineq     op (simplifiedExpr exprX) (simplifiedExpr exprY)
simplifiedTypedBuildInPred prd'                      = prd'
 --1
simplifiedExpr :: ExprCommon pFuncLabel a -> ExprCommon pFuncLabel a
simplifiedExpr (Sum exprX exprY) = case (simplifiedExpr exprX, simplifiedExpr exprY) of
    (ConstantExpr x, ConstantExpr y) -> ConstantExpr (add x y)
    (exprX',        exprY')          -> Sum exprX' exprY'
simplifiedExpr expr = expr

add :: Addition a => ConstantExpr a -> ConstantExpr a -> ConstantExpr a
add (RealConstant x) (RealConstant y) = RealConstant (x + y)
add (IntConstant  x) (IntConstant  y) = IntConstant  (x + y)

