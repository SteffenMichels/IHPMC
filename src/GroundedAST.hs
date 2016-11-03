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

module GroundedAST ( GroundedAST(..)
                   , BuildInPredicate(..)
                   , TypedBuildInPred(..)
                   , PFuncLabel(..)
                   , PFunc
                   , probabilisticFuncLabel
                   , probabilisticFuncDef
                   , makePFuncBool
                   , makePFuncReal
                   , makePFuncString
                   , Expr(..)
                   , PredicateLabel(..)
                   , ConstantExpr(..)
                   , PFuncDef(..)
                   , Addition
                   , Ineq
                   , RealN
                   , RuleBody(..)
                   , RuleBodyElement(..)
                   , negatePred
                   , predProbabilisticFunctions
                   , exprProbabilisticFunctions
                   , deterministicValue
                   , deterministicValueTyped
                   , possibleValues
                   , checkRealIneqPred
                   , simplifiedBuildInPred
                   , simplifiedExpr
                   , groundedAstToText
                   , exprToText
                   , typedBuildInPredToText
                   , pFuncToText
                   , pFuncLabelToText
                   , ruleBodyElementToText
                   , predicateLabelToText
                   ) where
import qualified AST
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
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
import Data.Monoid ((<>), mconcat)
import qualified Data.Text.Lazy.Builder as TB
import qualified Data.Text.Lazy as LT

-- use sets here to avoid duplicate elements
data GroundedAST = GroundedAST
    { rules     :: HashMap PredicateLabel (HashSet RuleBody)
    , queries   :: HashSet RuleBodyElement
    , evidence  :: HashSet RuleBodyElement
    }

groundedAstToText :: GroundedAST -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
groundedAstToText ast ids2str ids2label = rulesStr <> queryStr <> evStr
    where
    rulesStr     = mconcat $ mconcat [
                        let lStr = predicateLabelToText label ids2str ids2label
                        in  [lStr <> " <- " <> ruleBodyToText body ids2str ids2label <> ".\n" | body <- Set.toList bodies]
                   | (label, bodies) <- Map.toList $ rules ast]
    queryStr     = mconcat ["query " <> ruleBodyElementToText query ids2str ids2label <> ".\n" | query <- Set.toList $ queries  ast]
    evStr        = mconcat ["evidence %" <> ruleBodyElementToText ev ids2str ids2label <> ".\n" | ev <- Set.toList $ evidence ast]

-- propositional version of data types, similarly present in AST (without argument, after grounding)
newtype PredicateLabel = PredicateLabel Int deriving (Eq, Generic)
predicateLabelToText :: PredicateLabel -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
predicateLabelToText (PredicateLabel idNr) ids2str ids2label =
    AST.predicateLabelToText (AST.PredicateLabel label) ids2str <>
    if null args then "" else "(" <> showbLst args <> ")"
    where (label, args) = Map.lookupDefault undefined idNr ids2label
instance Hashable PredicateLabel

data PFunc a = PFunc PFuncLabel (PFuncDef a)
-- there should never be more than one PF with the same label, so compare/hash only label and ignore definition
instance Eq (PFunc a) where
    PFunc x _ == PFunc y _ = x == y
instance Hashable (PFunc a) where
    hashWithSalt salt (PFunc label _) = Hashable.hashWithSalt salt label

pFuncToText :: PFunc a -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
pFuncToText (PFunc l _) = pFuncLabelToText l

data PFuncDef a where
    Flip     :: Probability                                            -> PFuncDef Bool
    RealDist :: (Rational -> Probability) -> (Probability -> Rational) -> PFuncDef GroundedAST.RealN
    StrDist  :: [(Probability, Text)]                                  -> PFuncDef Text

probabilisticFuncLabel :: PFunc a -> PFuncLabel
probabilisticFuncLabel (PFunc label _) = label

probabilisticFuncDef :: PFunc a -> PFuncDef a
probabilisticFuncDef (PFunc _ def) = def

makePFuncBool :: PFuncLabel -> Probability-> PFunc Bool
makePFuncBool label p = PFunc label $ Flip p

makePFuncReal :: PFuncLabel ->  (Rational -> Probability) -> (Probability -> Rational) -> PFunc GroundedAST.RealN
makePFuncReal label cdf cdf' = PFunc label $ RealDist cdf cdf'

makePFuncString :: PFuncLabel -> [(Probability, Text)] -> PFunc Text
makePFuncString label dist = PFunc label $ StrDist dist

newtype PFuncLabel = PFuncLabel Int deriving (Eq, Generic)
pFuncLabelToText :: PFuncLabel -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
pFuncLabelToText (PFuncLabel idNr) ids2str ids2label =
    "~" <>
    TB.fromText (Map.lookupDefault undefined label ids2str) <>
    if null args then "" else "(" <> showbLst args <> ")"
    where
    (label, args) = Map.lookupDefault undefined idNr ids2label
instance Hashable PFuncLabel

newtype RuleBody = RuleBody (HashSet RuleBodyElement) deriving (Eq, Generic)

ruleBodyToText :: RuleBody -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
ruleBodyToText (RuleBody elements) ids2str ids2label =
    toTextLst (Set.toList elements) (\x -> ruleBodyElementToText x ids2str ids2label)
instance Hashable RuleBody

data RuleBodyElement = UserPredicate    PredicateLabel
                     | BuildInPredicate BuildInPredicate
                     deriving (Eq, Generic)

ruleBodyElementToText :: RuleBodyElement -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
ruleBodyElementToText (UserPredicate label)  ids2str ids2label = predicateLabelToText label ids2str ids2label
ruleBodyElementToText (BuildInPredicate prd) ids2str ids2label = buildInPredToText    prd   ids2str ids2label
instance Hashable RuleBodyElement

data BuildInPredicate = BuildInPredicateBool (TypedBuildInPred Bool)
                      | BuildInPredicateReal (TypedBuildInPred RealN)
                      | BuildInPredicateStr  (TypedBuildInPred Text)
                      | BuildInPredicateInt  (TypedBuildInPred Integer)
                      deriving (Eq, Generic)
buildInPredToText :: BuildInPredicate -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
buildInPredToText (BuildInPredicateBool b) = typedBuildInPredToText b
buildInPredToText (BuildInPredicateReal r) = typedBuildInPredToText r
buildInPredToText (BuildInPredicateStr  s) = typedBuildInPredToText s
buildInPredToText (BuildInPredicateInt  i) = typedBuildInPredToText i
instance Hashable BuildInPredicate

data TypedBuildInPred a
    where
    Equality ::           Bool       -> Expr a -> Expr a -> TypedBuildInPred a
    Ineq     :: Ineq a => AST.IneqOp -> Expr a -> Expr a -> TypedBuildInPred a
    Constant ::           Bool                           -> TypedBuildInPred a

deriving instance Eq (TypedBuildInPred a)
typedBuildInPredToText :: TypedBuildInPred a -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
typedBuildInPredToText (Equality eq exprX exprY) ids2str ids2label =
    exprToText exprX ids2str ids2label <> " " <> if eq then "=" else "/=" <> " " <> exprToText exprY ids2str ids2label
typedBuildInPredToText (Ineq     op exprX exprY) ids2str ids2label =
    exprToText exprX ids2str ids2label <> " " <> showb op <> " " <> exprToText exprY ids2str ids2label
typedBuildInPredToText (Constant cnst)           _       _ = showb cnst
instance Hashable (TypedBuildInPred a)
    where
    hashWithSalt salt (Equality eq exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt eq) exprX) exprY
    hashWithSalt salt (Ineq     op exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt op) exprX) exprY
    hashWithSalt salt (Constant b)              = Hashable.hashWithSalt salt b

data Expr a
    where
    ConstantExpr ::               ConstantExpr a   -> Expr a
    PFuncExpr    ::               PFunc a          -> Expr a
    Sum          :: Addition a => Expr a -> Expr a -> Expr a

deriving instance Eq (Expr a)
exprToText :: Expr a -> HashMap Int Text -> HashMap Int (Int, [AST.ConstantExpr]) -> Builder
exprToText (ConstantExpr cExpr) _       _         = showb cExpr
exprToText (PFuncExpr pf)       ids2str ids2label = pFuncToText pf ids2str ids2label
exprToText (Sum x y)            ids2str ids2label =
    exprToText x ids2str ids2label <> " + " <> exprToText y ids2str ids2label
instance Hashable (Expr a)
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

deriving instance Eq (ConstantExpr a)
instance TextShow (ConstantExpr a) where
    showb (BoolConstant cnst) = TB.fromLazyText $ LT.map toLower $ TB.toLazyText $ showb cnst
    showb (RealConstant cnst) = showb (fromRat cnst::Float)
    showb (StrConstant  cnst) = TB.fromText cnst
    showb (IntConstant  cnst) = showb cnst
instance Hashable (ConstantExpr a)
    where
    hashWithSalt salt (BoolConstant b) = Hashable.hashWithSalt salt b
    hashWithSalt salt (RealConstant r) = Hashable.hashWithSalt salt r
    hashWithSalt salt (StrConstant  s) = Hashable.hashWithSalt salt s
    hashWithSalt salt (IntConstant  i) = Hashable.hashWithSalt salt i
instance Ord (ConstantExpr a)
    where
    BoolConstant x <= BoolConstant y = x <= y
    RealConstant x <= RealConstant y = x <= y
    StrConstant  x <= StrConstant  y = x <= y
    IntConstant  x <= IntConstant  y = x <= y
#if __GLASGOW_HASKELL__ < 800
    _              <= _              = undefined
#endif

data RealN -- phantom for real numbered expression etc.

class Addition a
instance Addition Integer
instance Addition RealN

class Ineq a
instance Ineq Integer
instance Ineq RealN

predProbabilisticFunctions :: TypedBuildInPred a -> HashSet (PFunc a)
predProbabilisticFunctions (Equality _ left right) = Set.union (exprProbabilisticFunctions left) (exprProbabilisticFunctions right)
predProbabilisticFunctions (Ineq     _ left right) = Set.union (exprProbabilisticFunctions left) (exprProbabilisticFunctions right)
predProbabilisticFunctions (Constant _)            = Set.empty

exprProbabilisticFunctions :: Expr a -> HashSet (PFunc a)
exprProbabilisticFunctions (PFuncExpr pf)   = Set.singleton pf
exprProbabilisticFunctions (ConstantExpr _) = Set.empty
exprProbabilisticFunctions (Sum x y)        = Set.union (exprProbabilisticFunctions x) (exprProbabilisticFunctions y)

negatePred :: TypedBuildInPred a -> TypedBuildInPred a
negatePred (Equality eq exprX exprY) = Equality (not eq) exprX exprY
negatePred (Ineq     op exprX exprY) = Ineq (AST.negateOp op) exprX exprY
negatePred (Constant cnst)           = Constant $ not cnst

deterministicValue :: BuildInPredicate -> Maybe Bool
deterministicValue (BuildInPredicateBool b) = deterministicValueTyped b
deterministicValue (BuildInPredicateReal r) = deterministicValueTyped r
deterministicValue (BuildInPredicateStr  s) = deterministicValueTyped s
deterministicValue (BuildInPredicateInt  i) = deterministicValueTyped i

deterministicValueTyped :: TypedBuildInPred a -> Maybe Bool
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

possibleValues :: Expr Text -> HashMap (PFunc Text) (HashSet Text) -> HashSet Text
possibleValues (ConstantExpr (StrConstant cnst)) _ = Set.singleton cnst
possibleValues (PFuncExpr pf@(PFunc _ (StrDist elements))) sConds =
    Map.lookupDefault (Set.fromList $ snd <$> elements) pf sConds
possibleValues _ _ = undefined

checkRealIneqPred :: AST.IneqOp
                  -> Expr RealN
                  -> Expr RealN
                  -> Map.HashMap (PFunc GroundedAST.RealN) Interval.IntervalLimitPoint
                  -> Maybe Bool -- result may be undetermined -> Nothing
checkRealIneqPred op left right point = case op of
    AST.Lt   -> evalLeft ~<  evalRight
    AST.LtEq -> evalLeft ~<= evalRight
    AST.Gt   -> evalLeft ~>  evalRight
    AST.GtEq -> evalLeft ~>= evalRight
    where
    evalLeft  = eval left  point
    evalRight = eval right point

eval :: Expr RealN -> HashMap (PFunc GroundedAST.RealN) Interval.IntervalLimitPoint -> Interval.IntervalLimitPoint
eval (PFuncExpr pf) point              = Map.lookupDefault (error "AST.checkRealIneqPred: no point") pf point
eval (ConstantExpr (RealConstant r)) _ = Interval.rat2IntervLimPoint r
eval (Sum x y) point                   = eval x point + eval y point

simplifiedBuildInPred :: BuildInPredicate -> BuildInPredicate
simplifiedBuildInPred (BuildInPredicateBool prd) = BuildInPredicateBool $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateReal prd) = BuildInPredicateReal $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateInt  prd) = BuildInPredicateInt  $ simplifiedTypedBuildInPred prd
simplifiedBuildInPred (BuildInPredicateStr  prd) = BuildInPredicateStr  $ simplifiedTypedBuildInPred prd

simplifiedTypedBuildInPred :: TypedBuildInPred a -> TypedBuildInPred a
simplifiedTypedBuildInPred (Equality eq exprX exprY) = Equality eq (simplifiedExpr exprX) (simplifiedExpr exprY)
simplifiedTypedBuildInPred (Ineq     op exprX exprY) = Ineq     op (simplifiedExpr exprX) (simplifiedExpr exprY)
simplifiedTypedBuildInPred prd'                      = prd'

simplifiedExpr :: Expr a -> Expr a
simplifiedExpr (Sum exprX exprY) = case (simplifiedExpr exprX, simplifiedExpr exprY) of
    (ConstantExpr x, ConstantExpr y) -> ConstantExpr (add x y)
    (exprX',        exprY')          -> Sum exprX' exprY'
simplifiedExpr expr = expr

add :: Addition a => ConstantExpr a -> ConstantExpr a -> ConstantExpr a
add (RealConstant x) (RealConstant y) = RealConstant (x + y)
add (IntConstant  x) (IntConstant  y) = IntConstant  (x + y)
add _                            _    = error "Formula.refBuildInPredicate"
