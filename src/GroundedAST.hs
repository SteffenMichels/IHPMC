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
                   , PredicateLabel
                   , stringNamePredicateLabel
                   , numberNamePredicateLabel
                   , setBodyNr
                   , setExcluded
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
import Text.Printf (printf)
import Data.Char (toLower)
import Numeric (fromRat)
import Util
import Probability

-- use sets here to avoid duplicate elements
data GroundedAST = GroundedAST
    { rules     :: HashMap PredicateLabel (HashSet RuleBody)
    , queries   :: HashSet RuleBodyElement
    , evidence  :: HashSet RuleBodyElement
    }

instance Show GroundedAST
    where
    show ast = rulesStr ++ queryStr ++ evStr
        where
        rulesStr     = concat $ concat [
                            [printf "%s <- %s.\n" (show label) $ show body | body <- Set.toList bodies]
                       | (label, bodies) <- Map.toList $ rules ast]
        queryStr     = concat [printf "query %s.\n"    $ show query | query <- Set.toList $ queries  ast]
        evStr        = concat [printf "evidence %s.\n" $ show ev    | ev    <- Set.toList $ evidence ast]

-- propositional version of data types, similarly present in AST (without argument, after grounding)
data PredicateLabel = PredicateLabel PredicateName [AST.ConstantExpr] (Maybe Integer) (HashSet PredicateLabel) Int deriving Eq
instance Show PredicateLabel where
    show (PredicateLabel name args mbNr excluded _) = printf
        "%s%s%s%s"
        (show name)
        (if null args then "" else printf "(%s)" (showLst args))
        (case mbNr of Just n -> printf "#%i" n; Nothing -> "")
        (if null excluded then "" else printf "-%s" $ showLst $ Set.toList excluded)
instance Hashable PredicateLabel where
    hashWithSalt salt (PredicateLabel _ _ _ _ hash) = Hashable.hashWithSalt salt hash

data PredicateName = StringName String
                   | NumberName Integer
                    deriving (Eq, Generic)
instance Show PredicateName where
    show (StringName n) = n
    show (NumberName n) = show n
instance Hashable PredicateName

stringNamePredicateLabel :: String -> [AST.ConstantExpr] -> PredicateLabel
stringNamePredicateLabel name args = PredicateLabel strName args Nothing Set.empty $ predicateLabelHash strName args Nothing Set.empty
    where
    strName = StringName name

numberNamePredicateLabel :: Integer -> [AST.ConstantExpr] -> PredicateLabel
numberNamePredicateLabel name args = PredicateLabel nrName args Nothing Set.empty $ predicateLabelHash nrName args Nothing Set.empty
    where
    nrName = NumberName name

setBodyNr :: Integer -> PredicateLabel -> PredicateLabel
setBodyNr n (PredicateLabel name args _ excluded _) = PredicateLabel name args (Just n) excluded $ predicateLabelHash name args (Just n) excluded

setExcluded :: HashSet PredicateLabel -> PredicateLabel -> PredicateLabel
setExcluded excluded (PredicateLabel name args mbNr _ _) = PredicateLabel name args mbNr excluded $ predicateLabelHash name args mbNr excluded

predicateLabelHash :: PredicateName -> [AST.ConstantExpr] -> Maybe Integer -> HashSet PredicateLabel -> Int
predicateLabelHash name args mbNr = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hash name) args) mbNr)

data PFunc a = PFunc PFuncLabel (PFuncDef a) Int -- store hash for efficiency reasons
instance Eq (PFunc a)
    where
    PFunc x _ hx == PFunc y _ hy = hx == hy && x == y
instance Show (PFunc a)
    where
    show (PFunc l _ _) = show l
instance Hashable (PFunc a)
    where
    hash = Hashable.hashWithSalt 0
    -- there should never be more than one PF with the same name, so hash only name and ignore definition
    hashWithSalt salt (PFunc _ _ hash) = Hashable.hashWithSalt salt hash

data PFuncDef a where
    Flip     :: Probability                                            -> PFuncDef Bool
    RealDist :: (Rational -> Probability) -> (Probability -> Rational) -> PFuncDef GroundedAST.RealN
    StrDist  :: [(Probability, String)]                                -> PFuncDef String

probabilisticFuncLabel :: PFunc a -> PFuncLabel
probabilisticFuncLabel (PFunc label _ _) = label

probabilisticFuncDef :: PFunc a -> PFuncDef a
probabilisticFuncDef (PFunc _ def _) = def

makePFuncBool :: PFuncLabel -> Probability-> PFunc Bool
makePFuncBool label p = PFunc label (Flip p) $ Hashable.hash label

makePFuncReal :: PFuncLabel ->  (Rational -> Probability) -> (Probability -> Rational) -> PFunc GroundedAST.RealN
makePFuncReal label cdf cdf' = PFunc label (RealDist cdf cdf') $ Hashable.hash label

makePFuncString :: PFuncLabel -> [(Probability, String)] -> PFunc String
makePFuncString label dist = PFunc label (StrDist dist) $ Hashable.hash label

data PFuncLabel = PFuncLabel AST.PFuncLabel [AST.ConstantExpr] deriving (Eq, Generic)
instance Show PFuncLabel
    where
    show (PFuncLabel label args) = printf
        "~%s%s"
        (show label)
        (if null args then "" else printf "(%s)" (showLst args))
instance Hashable PFuncLabel

newtype RuleBody = RuleBody (HashSet RuleBodyElement) deriving (Eq, Generic)

instance Show RuleBody
    where
    show (RuleBody elements) = showLst $ Set.toList elements
instance Hashable RuleBody

data RuleBodyElement = UserPredicate    PredicateLabel
                     | BuildInPredicate BuildInPredicate
                     deriving (Eq, Generic)

instance Show RuleBodyElement where
    show (UserPredicate label)  = show label
    show (BuildInPredicate prd) = show prd
instance Hashable RuleBodyElement

data BuildInPredicate = BuildInPredicateBool (TypedBuildInPred Bool)
                      | BuildInPredicateReal (TypedBuildInPred RealN)
                      | BuildInPredicateStr  (TypedBuildInPred String)
                      | BuildInPredicateInt  (TypedBuildInPred Integer)
                      deriving (Eq, Generic)
instance Show BuildInPredicate
    where
    show (BuildInPredicateBool b) = show b
    show (BuildInPredicateReal r) = show r
    show (BuildInPredicateStr  s) = show s
    show (BuildInPredicateInt  i) = show i
instance Hashable BuildInPredicate

data TypedBuildInPred a
    where
    Equality ::           Bool       -> Expr a -> Expr a -> TypedBuildInPred a
    Ineq     :: Ineq a => AST.IneqOp -> Expr a -> Expr a -> TypedBuildInPred a
    Constant ::           Bool                           -> TypedBuildInPred a

deriving instance Eq (TypedBuildInPred a)
instance Show (TypedBuildInPred a)
    where
    show (Equality eq exprX exprY) = printf "%s %s %s" (show exprX) (if eq then "=" else "/=") (show exprY)
    show (Ineq     op exprX exprY) = printf "%s %s %s" (show exprX) (show op) (show exprY)
    show (Constant cnst)           = show cnst
instance Hashable (TypedBuildInPred a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (Equality eq exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt eq) exprX) exprY
    hashWithSalt salt (Ineq     op exprX exprY) = Hashable.hashWithSalt (Hashable.hashWithSalt (Hashable.hashWithSalt salt op) exprX) exprY
    hashWithSalt salt (Constant b)              = Hashable.hashWithSalt salt b

data Expr a
    where
    ConstantExpr ::               ConstantExpr a   -> Expr a
    PFuncExpr    ::               PFunc a          -> Expr a
    Sum          :: Addition a => Expr a -> Expr a -> Expr a

deriving instance Eq (Expr a)
instance Show (Expr a)
    where
    show (ConstantExpr cExpr) = show cExpr
    show (PFuncExpr pf)       = show pf
    show (Sum x y)            = printf "%s + %s" (show x) (show y)
instance Hashable (Expr a)
    where
    hash = Hashable.hashWithSalt 0
    hashWithSalt salt (ConstantExpr cExpr) = Hashable.hashWithSalt salt cExpr
    hashWithSalt salt (PFuncExpr r)        = Hashable.hashWithSalt salt r
    hashWithSalt salt (Sum x y)            = Hashable.hashWithSalt (Hashable.hashWithSalt salt x) y

data ConstantExpr a
    where
    BoolConstant :: Bool     -> ConstantExpr Bool
    RealConstant :: Rational -> ConstantExpr RealN
    StrConstant  :: String   -> ConstantExpr String
    IntConstant  :: Integer  -> ConstantExpr Integer

deriving instance Eq (ConstantExpr a)
instance Show (ConstantExpr a)
    where
    show (BoolConstant cnst) = printf "%s" (toLower <$> show cnst)
    show (RealConstant cnst) = printf "%f" (fromRat cnst::Float)
    show (StrConstant  cnst) = cnst
    show (IntConstant  cnst) = show cnst
instance Hashable (ConstantExpr a)
    where
    hash = Hashable.hashWithSalt 0
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

possibleValues :: Expr String -> HashMap (PFunc String) (HashSet String) -> HashSet String
possibleValues (ConstantExpr (StrConstant cnst)) _ = Set.singleton cnst
possibleValues (PFuncExpr pf@(PFunc _ (StrDist elements) _)) sConds =
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
eval (PFuncExpr pf) point              = Map.lookupDefault (error $ printf "AST.checkRealIneqPred: no point for %s" $ show pf) pf point
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
