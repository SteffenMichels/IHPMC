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

module AstPreprocessor
    ( substitutePfsWithPfArgs
    ) where
import AST (AST)
import qualified AST
import IdNrMap (IdNrMap)
import qualified IdNrMap
import Data.HashMap (Map)
import qualified Data.HashMap as Map
import Data.HashSet (Set)
import qualified Data.HashSet as Set
import Data.Text (Text)
import TextShow
import Data.Monoid ((<>))
import Data.Foldable (foldl')

substitutePfsWithPfArgs :: AST -> IdNrMap Text -> (AST, IdNrMap Text)
substitutePfsWithPfArgs ast identIds = (ast', identIds')
    where
    AST.AST{AST.queries=queries, AST.evidence=evidence, AST.rules=rules, AST.pFuncDefs=pfDefs} = ast

    (ast', identIds') = Map.foldWithKey addUsagePreds (ast, identIds) pfsWithPfArgsUsages
        where
        addUsagePreds :: (AST.PFuncLabel, Int) -> Set [AST.Expr] -> (AST, IdNrMap Text) -> (AST, IdNrMap Text)
        addUsagePreds (AST.PFuncLabel pfId, nArgs) uses ast'' = fst $ Set.fold addUsagePreds' (ast'', 0) uses
            where
            addUsagePreds' :: [AST.Expr] -> ((AST, IdNrMap Text), Integer) -> ((AST, IdNrMap Text), Integer)
            addUsagePreds' args ((ast''', identIds''), n) = ((ast'''', identIds'''), succ n)
                where
                ast'''' = ast'''{AST.rules = Map.insert (AST.PredicateLabel predId, nArgs) [([AST.ArgDontCareVariable], AST.RuleBody [])] $ AST.rules ast'''}
                (predId, identIds''') = IdNrMap.getIdNr (toText predIdent) identIds''
                predIdent = "~" <>
                            fromText (Map.findWithDefault undefined pfId (IdNrMap.fromIdNrMap identIds'')) <>
                            "@" <>
                            showb n

    -- arguments for which pfsWithPfArgs are used
    pfsWithPfArgsUsages :: Map (AST.PFuncLabel, Int) (Set [AST.Expr])
    pfsWithPfArgsUsages = foldPfs pfsWithPfArgsUsages' Map.empty
        where
        pfsWithPfArgsUsages' :: Map (AST.PFuncLabel, Int) (Set [AST.Expr])
                            -> ((AST.PFuncLabel, Int), [AST.Expr])
                            -> Map (AST.PFuncLabel, Int) (Set [AST.Expr])
        pfsWithPfArgsUsages' pfUses (sign, args)
            | Set.member sign pfsWithPfArgs = Map.insert
                sign
                (Set.insert args $ Map.findWithDefault Set.empty sign pfUses)
                pfUses
            | otherwise = pfUses

    -- all pfs which have pfs as args
    pfsWithPfArgs :: Set (AST.PFuncLabel, Int)
    pfsWithPfArgs = foldPfs pfsWithPfArgs' Set.empty
        where
        pfsWithPfArgs' :: Set (AST.PFuncLabel, Int)
                       -> ((AST.PFuncLabel, Int), [AST.Expr])
                       -> Set (AST.PFuncLabel, Int)
        pfsWithPfArgs' pfs (sign, args)
            | any (AST.foldExpr (\b e -> b || AST.exprIsPFunc e) False) args = Set.insert sign pfs
            | otherwise                                                      = pfs

    foldPfs :: (a -> ((AST.PFuncLabel, Int), [AST.Expr]) -> a) -> a -> a
    foldPfs f acc = foldl'
        ( foldl' ( \pfs (_, AST.RuleBody body) ->
                     foldl' foldPfs' pfs body
                 )
        )
        acc
        (Map.elems rules)
        where
        foldPfs' pfs (AST.UserPredicate _ _) = pfs
        foldPfs' pfs (AST.BuildInPredicate bip) = case bip of
            AST.Equality _ exprX exprY -> AST.foldExpr foldPfs'' (AST.foldExpr foldPfs'' pfs exprX) exprY
            AST.Ineq     _ exprX exprY -> AST.foldExpr foldPfs'' (AST.foldExpr foldPfs'' pfs exprX) exprY

        foldPfs'' acc' (AST.PFunc label args) = f acc' ((label, length args), args)
        foldPfs'' acc' _                      = acc'
