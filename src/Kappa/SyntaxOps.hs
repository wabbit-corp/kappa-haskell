-- | Generic operations over the surface AST used by the §21
-- metaprogramming elaborator: quote grafting (hole substitution),
-- hygienic renaming of captured variable occurrences, free/bound name
-- queries, and a rough source-like rendering for 'renderSyntax'
-- (§21.10.1 permits a stable fallback form).
--
-- The traversals are written with @Data.Data@ generics so they stay
-- total over the whole 'Expr' family without fifty-constructor
-- boilerplate. Queries deliberately do NOT descend into nested
-- 'EQuote' payloads: an inner quote's splices, captures, and bound
-- names belong to that inner quote's own elaboration (§21.1).
module Kappa.SyntaxOps
  ( transformExprs
  , collectSplices
  , replaceSplices
  , substQuoteHoles
  , renameVarOccurrences
  , freeVarOccurrences
  , boundNamesIn
  , renderExprSrc
  ) where

import Data.Data (Data, cast, gmapQ, gmapT)
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe, maybeToList)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Source (Span)
import Kappa.Syntax
import Kappa.Token (StrFragment (..), StringLit (..))

-- | Bottom-up transform of every 'Expr' node reachable from @a@,
-- without descending into nested 'EQuote' payloads.
transformExprs :: Data a => (Expr -> Expr) -> a -> a
transformExprs f = go
  where
    go :: Data b => b -> b
    go x = case cast x :: Maybe Expr of
      Just (EQuote _ _) -> x
      Just e ->
        fromMaybe x (cast (f (gmapT go e)))
      Nothing -> gmapT go x

-- | Top-down query over every 'Expr' node reachable from @a@; the
-- function decides whether to descend into the node's children.
-- Nested 'EQuote' payloads are never entered.
queryExprs :: forall a r. Data a => (Expr -> ([r], Bool)) -> a -> [r]
queryExprs f = go
  where
    go :: forall b. Data b => b -> [r]
    go x = case cast x :: Maybe Expr of
      Just (EQuote _ _) -> []
      Just e ->
        let (rs, descend) = f e
         in rs ++ if descend then concat (gmapQ go e) else []
      Nothing -> concat (gmapQ go x)

-- | The in-quote splices @${ e }@ of a quote payload, in source order
-- (not entering nested quotes).
collectSplices :: Expr -> [(Span, Expr)]
collectSplices = queryExprs $ \case
  ESpliceInQuote inner sp -> ([(sp, inner)], False)
  _ -> ([], True)

-- | Replace each in-quote splice with its grafting slot 'EQuoteHole'.
replaceSplices :: Map Span Int -> Expr -> Expr
replaceSplices slots = transformExprs $ \case
  ESpliceInQuote _ sp
    | Just i <- Map.lookup sp slots -> EQuoteHole i sp
  e -> e

-- | Graft slot payloads into a quote payload (§21.2 splice grafting).
substQuoteHoles :: Map Int Expr -> Expr -> Expr
substQuoteHoles slots = transformExprs $ \case
  EQuoteHole i sp
    | Just e <- Map.lookup i slots -> reSpan sp e
  e -> e
  where
    -- keep the hole's source span for ascriptions that need one
    reSpan _ e = e

-- | Rename free variable occurrences (expression positions only; the
-- caller guarantees the renamed names are not rebound inside).
renameVarOccurrences :: Map Text Text -> Expr -> Expr
renameVarOccurrences m = transformExprs $ \case
  EVar (Name t sp)
    | Just t' <- Map.lookup t m -> EVar (Name t' sp)
  e -> e

-- | Every variable occurrence in expression position (not entering
-- nested quotes). Includes names that are bound inside the payload;
-- callers subtract 'boundNamesIn'.
freeVarOccurrences :: Expr -> [Name]
freeVarOccurrences = queryExprs $ \case
  EVar n -> ([n], False)
  _ -> ([], True)

-- | Every name bound anywhere inside the payload (patterns, binders,
-- local definitions, comprehension clauses, do items). Conservative
-- over-approximation: a quoted payload that rebinds a name anywhere
-- keeps every occurrence of that spelling un-captured (§21.4 hygiene
-- still holds for the fixture-relevant forms; see SPEC_COVERAGE.md).
boundNamesIn :: Expr -> [Text]
boundNamesIn e0 = nub (goAll e0)
  where
    goAll :: Data b => b -> [Text]
    goAll x = here x ++ concat (gmapQ goAll x)
    here :: Data b => b -> [Text]
    here x
      | Just (e :: Expr) <- cast x = exprBinds e
      | Just (p :: Pattern) <- cast x = patBinds p
      | Just (b :: Binder) <- cast x = maybeToList (nameText <$> bName b)
      | Just (ld :: LetDef) <- cast x = maybeToList (nameText <$> ldName ld)
      | Just (it :: DoItem) <- cast x = doBinds it
      | Just (cl :: CompClause) <- cast x = clauseBinds cl
      | otherwise = []
    exprBinds = \case
      EOpenExists _ ns _ _ _ -> map nameText ns
      _ -> []
    patBinds = \case
      PVar n -> [nameText n]
      PAs n _ -> [nameText n]
      PCtorNamed _ fields _ -> [nameText n | (n, Nothing) <- fields]
      PRecord fields rest _ ->
        [nameText n | (_, n, Nothing) <- fields]
          ++ [nameText n | Just (PatRestBind n) <- [rest]]
      PVariant mb _ _ mrest _ ->
        map nameText (maybeToList mb ++ maybeToList mrest)
      _ -> []
    doBinds = \case
      DoVar n _ _ -> [nameText n]
      DoAssign n _ _ _ -> [nameText n]
      _ -> []
    clauseBinds = \case
      CGroupBy _ aggs into _ ->
        nameText into : [nameText n | (n, _, _) <- aggs]
      CJoin _ _ _ _ minto _ -> map nameText (maybeToList minto)
      _ -> []

-- | Source-like rendering of surface syntax for 'renderSyntax'
-- (§21.10.1): faithful for the common forms, stable fallback
-- otherwise. Rendering is presentation-only; nothing semantic
-- consumes it.
renderExprSrc :: Expr -> Text
renderExprSrc = render
  where
    render = \case
      EVar n -> nameText n
      EHole Nothing _ -> "_"
      EHole (Just n) _ -> "?" <> nameText n
      EIntLit v _ _ -> T.pack (show v)
      EFloatLit v _ _ -> T.pack (show v)
      EStringLit sl _ _ ->
        "\"" <> T.concat [t | FragLit t <- slFragments sl] <> "\""
      EUnit _ -> "()"
      ETuple es _ -> "(" <> T.intercalate ", " (map render es) <> ")"
      EListLit es _ -> "[" <> T.intercalate ", " (map render es) <> "]"
      ERecordLit items _ ->
        "(" <> T.intercalate ", " (mapMaybe item items) <> ")"
        where
          item (RecItem _ n mv) = Just (nameText n <> maybe "" ((" = " <>) . render) mv)
      EApp f args -> T.unwords (render f : map renderArg args)
      EDot e (DotName n) -> render e <> "." <> nameText n
      EDot e (DotOperator n) -> render e <> ".(" <> nameText n <> ")"
      EAscription e t _ -> "(" <> render e <> " : " <> render t <> ")"
      EQuoteHole i _ -> "${__slot" <> T.pack (show i) <> "}"
      ESpliceInQuote e _ -> "${" <> render e <> "}"
      EQuote e _ -> "'{ " <> render e <> " }"
      ESplice e _ -> "$(" <> render e <> ")"
      EKindQualified _ n _ -> "type " <> nameText n
      EOpChain els -> T.unwords (map elemSrc els)
      EComprehension _ _ _ _ -> "[ ... ]"
      EMatch {} -> "(match ...)"
      ELambda {} -> "(\\...)"
      _ -> "<syntax>"
    elemSrc (ChainOperand e) = render e
    elemSrc (ChainOp n) = nameText n
    renderArg = \case
      ArgExplicit e -> atom e
      ArgImplicit e -> "@" <> atom e
      ArgInout e _ -> "~" <> atom e
      ArgNamedBlock _ _ -> "{ ... }"
    atom e = case e of
      EVar {} -> render e
      EIntLit {} -> render e
      EUnit {} -> render e
      EStringLit {} -> render e
      _ -> "(" <> render e <> ")"
