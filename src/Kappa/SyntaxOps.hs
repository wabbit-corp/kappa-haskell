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
  , queryExprs
  , collectSplices
  , replaceSplices
  , substQuoteHoles
  , renameVarOccurrences
  , renameFreeVarOccurrences
  , freeVarOccurrences
  , freeVarOccurrencesScoped
  , boundNamesIn
  , renderExprSrc
  ) where

import Data.Data (Data, cast, gmapQ, gmapT)
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe, maybeToList)
import Data.Set (Set)
import qualified Data.Set as Set
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
  ERefFacet (Name t sp) rsp
    | Just t' <- Map.lookup t m -> ERefFacet (Name t' sp) rsp
  e -> e

-- | Capture-avoiding renaming of free expression-position variables. This is
-- the declaration-schema alpha-renaming operation: ordinary binders with the
-- same spelling as a schema parameter must remain ordinary binders.
renameFreeVarOccurrences :: Map Text Text -> Expr -> Expr
renameFreeVarOccurrences renaming expression =
  let freeSites =
        Set.fromList
          [ (nameSpan occurrence, nameText occurrence)
          | occurrence <- freeVarOccurrencesScoped expression
          ]
   in transformExprs
        (\case
           EVar (Name text sourceSpan)
             | (sourceSpan, text) `Set.member` freeSites
             , Just replacement <- Map.lookup text renaming ->
                 EVar (Name replacement sourceSpan)
           ERefFacet (Name text sourceSpan) refSpan
             | (sourceSpan, text) `Set.member` freeSites
             , Just replacement <- Map.lookup text renaming ->
                 ERefFacet (Name replacement sourceSpan) refSpan
           node -> node)
        expression

-- | Every variable occurrence in expression position (not entering
-- nested quotes). Includes names that are bound inside the payload;
-- callers subtract 'boundNamesIn'.
freeVarOccurrences :: Expr -> [Name]
freeVarOccurrences = queryExprs $ \case
  EVar n -> ([n], False)
  ERefFacet n _ -> ([n], False)
  _ -> ([], True)

-- | Lexically free variable occurrences in expression position. Unlike
-- 'freeVarOccurrences', this traversal respects every surface binding form
-- needed before elaboration (local SCC discovery and declaration-schema
-- alpha-renaming). Nested quotes remain separate hygiene scopes.
freeVarOccurrencesScoped :: Expr -> [Name]
freeVarOccurrencesScoped = go Set.empty
  where
    go :: Set Text -> Expr -> [Name]
    go bound = \case
      EQuote _ _ -> []
      EVar name
        | nameText name `Set.notMember` bound -> [name]
        | otherwise -> []
      ERefFacet name _
        | nameText name `Set.notMember` bound -> [name]
        | otherwise -> []
      ELambda _ binders body _ ->
        let (binderOccurrences, bodyScope) = goBinders bound binders
         in binderOccurrences ++ go bodyScope body
      EArrow binder body ->
        let (binderOccurrences, bodyScope) = goBinders bound [binder]
         in binderOccurrences ++ go bodyScope body
      EForall binders body _ ->
        let (binderOccurrences, bodyScope) = goBinders bound binders
         in binderOccurrences ++ go bodyScope body
      EExists binders body _ ->
        let (binderOccurrences, bodyScope) = goBinders bound binders
         in binderOccurrences ++ go bodyScope body
      ELet bindings body _ ->
        let (bindingOccurrences, bodyScope) = goLetBindings bound bindings
         in bindingOccurrences ++ go bodyScope body
      EBlock declarations result _ ->
        let (declarationOccurrences, resultScope) = goDeclarations bound declarations
         in declarationOccurrences ++ maybe [] (go resultScope) result
      EDo _ items _ -> fst (goDoItems bound items)
      EMatch scrutinee cases _ ->
        go bound scrutinee ++ concatMap (goMatchCase bound) cases
      ETry body cases finalizer _ ->
        go bound body
          ++ concatMap (goExceptCase bound) cases
          ++ maybe [] (go bound) finalizer
      ETryMatch body matches cases finalizer _ ->
        go bound body
          ++ concatMap (goMatchCase bound) matches
          ++ concatMap (goExceptCase bound) cases
          ++ maybe [] (go bound) finalizer
      EHandle _ label body cases _ ->
        go bound label ++ go bound body ++ concatMap (goHandlerCase bound) cases
      EOpenExists package names pattern body _ ->
        go bound package
          ++ goData bound pattern
          ++ go (Set.union bound (Set.fromList (map nameText names) <> patternBinders pattern)) body
      EComprehension kind clauses yield _ ->
        goData bound kind
          ++ let (clauseOccurrences, yieldScope) = goClauses bound clauses
              in clauseOccurrences ++ goData yieldScope yield
      node -> concat (gmapQ (goData bound) node)

    goData :: Data a => Set Text -> a -> [Name]
    goData bound value =
      case cast value :: Maybe Expr of
        Just expression -> go bound expression
        Nothing -> concat (gmapQ (goData bound) value)

    goBinders scope [] = ([], scope)
    goBinders scope (binder : rest) =
      let here = concat (gmapQ (goData scope) binder)
          next = maybe scope ((`Set.insert` scope) . nameText) (bName binder)
          (later, finalScope) = goBinders next rest
       in (here ++ later, finalScope)

    goLetBindings scope [] = ([], scope)
    goLetBindings scope (binding : rest) =
      let here =
            maybe [] (go scope) (lbType binding)
              ++ go scope (lbExpr binding)
              ++ goData scope (lbPrefix binding)
              ++ goData scope (lbPattern binding)
          next = Set.union scope (patternBinders (lbPattern binding))
          (later, finalScope) = goLetBindings next rest
       in (here ++ later, finalScope)

    goDeclarations scope [] = ([], scope)
    goDeclarations scope (declaration : rest) =
      let declared = declarationBinders declaration
          declarationScope = Set.union scope declared
          here = goData declarationScope declaration
          (later, finalScope) = goDeclarations declarationScope rest
       in (here ++ later, finalScope)

    goDoItems scope [] = ([], scope)
    goDoItems scope (item : rest) =
      let (here, next) = case item of
            DoBind binding ->
              ( maybe [] (go scope) (lbType binding)
                  ++ go scope (lbExpr binding)
                  ++ goData scope (lbPrefix binding)
                  ++ goData scope (lbPattern binding)
              , Set.union scope (patternBinders (lbPattern binding))
              )
            DoLet binding ->
              ( maybe [] (go scope) (lbType binding)
                  ++ go scope (lbExpr binding)
                  ++ goData scope (lbPrefix binding)
                  ++ goData scope (lbPattern binding)
              , Set.union scope (patternBinders (lbPattern binding))
              )
            DoLetQ pattern rhs fallback _ ->
              ( goData scope pattern
                  ++ go scope rhs
                  ++ maybe [] (\(elsePattern, expression) ->
                        goData scope elsePattern
                          ++ go (Set.union scope (patternBinders elsePattern)) expression)
                       fallback
              , Set.union scope (patternBinders pattern)
              )
            DoVar name annotation initializer _ ->
              (maybe [] (go scope) annotation ++ go scope initializer, Set.insert (nameText name) scope)
            DoAssign _ _ rhs _ -> (go scope rhs, scope)
            DoExpr expression -> (go scope expression, scope)
            DoUsing _ pattern action _ ->
              (goData scope pattern ++ go scope action, Set.union scope (patternBinders pattern))
            DoDefer _ action _ -> (go scope action, scope)
            DoReturn _ result _ -> (maybe [] (go scope) result, scope)
            DoBreak {} -> ([], scope)
            DoContinue {} -> ([], scope)
            DoWhile _ condition body alternative _ ->
              ( go scope condition
                  ++ fst (goDoItems scope body)
                  ++ maybe [] (fst . goDoItems scope) alternative
              , scope
              )
            DoFor _ pattern source body alternative _ ->
              ( goData scope pattern
                  ++ go scope source
                  ++ fst (goDoItems (Set.union scope (patternBinders pattern)) body)
                  ++ maybe [] (fst . goDoItems scope) alternative
              , scope
              )
            DoIf branches alternative _ ->
              ( concat
                  [ go scope condition ++ fst (goDoItems scope branch)
                  | (condition, branch) <- branches
                  ]
                  ++ maybe [] (fst . goDoItems scope) alternative
              , scope
              )
            DoDecl declaration ->
              let declared = declarationBinders declaration
                  declarationScope = Set.union scope declared
               in (goData declarationScope declaration, declarationScope)
          (later, finalScope) = goDoItems next rest
       in (here ++ later, finalScope)

    goMatchCase scope = \case
      MatchImpossible _ -> []
      MatchCase pattern guard body _ ->
        let bodyScope = Set.union scope (patternBinders pattern)
         in goData scope pattern
              ++ maybe [] (go bodyScope) guard
              ++ go bodyScope body

    goExceptCase scope (ExceptCase pattern guard body _) =
      let bodyScope = Set.union scope (patternBinders pattern)
       in goData scope pattern
            ++ maybe [] (go bodyScope) guard
            ++ go bodyScope body

    goHandlerCase scope = \case
      HandlerReturn pattern body _ ->
        goData scope pattern
          ++ go (Set.union scope (patternBinders pattern)) body
      HandlerOp _ patterns continuation body _ ->
        let bodyScope =
              Set.insert (nameText continuation)
                (Set.unions (scope : map patternBinders patterns))
         in concatMap (goData scope) patterns ++ go bodyScope body

    goClauses scope [] = ([], scope)
    goClauses scope (clause : rest) =
      let (here, next) = case clause of
            CFor _ _ pattern source _ ->
              (goData scope pattern ++ go scope source, Set.union scope (patternBinders pattern))
            CLet _ pattern annotation rhs _ ->
              ( goData scope pattern ++ maybe [] (go scope) annotation ++ go scope rhs
              , Set.union scope (patternBinders pattern)
              )
            CIf condition -> (go scope condition, scope)
            COrderBy keys _ -> (concatMap (go scope . snd) keys, scope)
            CSkip count _ -> (go scope count, scope)
            CTake count _ -> (go scope count, scope)
            CDistinct key _ -> (maybe [] (go scope) key, scope)
            CGroupBy key aggregates into _ ->
              ( go scope key
                  ++ concat
                    [ go scope aggregate ++ maybe [] (go scope) using
                    | (_, aggregate, using) <- aggregates
                    ]
              , Set.insert (nameText into) scope
              )
            CJoin _ pattern source condition into _ ->
              let conditionScope = Set.union scope (patternBinders pattern)
                  nextScope =
                    maybe conditionScope ((`Set.insert` conditionScope) . nameText) into
               in ( goData scope pattern
                      ++ go scope source
                      ++ go conditionScope condition
                  , nextScope
                  )
          (later, finalScope) = goClauses next rest
       in (here ++ later, finalScope)

    patternBinders = \case
      PWild _ -> Set.empty
      PVar name -> Set.singleton (nameText name)
      PLit {} -> Set.empty
      PAs name pattern -> Set.insert (nameText name) (patternBinders pattern)
      PCtor _ patterns _ -> Set.unions (map patternBinders patterns)
      PCtorNamed _ fields _ ->
        Set.unions
          [ maybe (Set.singleton (nameText name)) patternBinders pattern
          | (name, pattern) <- fields
          ]
      PActive _ _ pattern _ -> patternBinders pattern
      PTuple patterns _ -> Set.unions (map patternBinders patterns)
      PUnit _ -> Set.empty
      PRecord fields rest _ ->
        Set.unions
          ( [ maybe (Set.singleton (nameText name)) patternBinders pattern
            | (_, name, pattern) <- fields
            ]
              ++ [case rest of
                    Just (PatRestBind name) -> Set.singleton (nameText name)
                    _ -> Set.empty]
          )
      PTyped pattern _ _ -> patternBinders pattern
      POr patterns _ -> Set.unions (map patternBinders patterns)
      POpChain pattern rest _ ->
        Set.unions (patternBinders pattern : [patternBinders rhs | (_, rhs) <- rest])
      PVariant binder _ _ rest _ ->
        Set.fromList (map nameText (maybeToList binder ++ maybeToList rest))

    declarationBinders = \case
      DSig _ name _ _ -> Set.singleton (nameText name)
      DLet _ definition _ ->
        Set.fromList (map nameText (maybeToList (ldName definition)))
          <> maybe Set.empty patternBinders (ldPattern definition)
      DData _ declaration _ -> Set.singleton (nameText (ddName declaration))
      DTypeAlias _ name _ _ _ _ -> Set.singleton (nameText name)
      DTrait _ declaration _ -> Set.singleton (nameText (trName declaration))
      DInstance {} -> Set.empty
      DDerive {} -> Set.empty
      DEffect _ declaration _ -> Set.singleton (nameText (effName declaration))
      DFixity {} -> Set.empty
      DImport {} -> Set.empty
      DExport {} -> Set.empty
      DExpect _ expected _ -> case expected of
        ExpectTerm name _ -> Set.singleton (nameText name)
        ExpectType name _ _ -> Set.singleton (nameText name)
        ExpectData name _ _ -> Set.singleton (nameText name)
        ExpectTrait name _ _ -> Set.singleton (nameText name)
      DPattern _ definition _ ->
        Set.fromList (map nameText (maybeToList (ldName definition)))
          <> maybe Set.empty patternBinders (ldPattern definition)
      DProjection _ name _ _ _ _ -> Set.singleton (nameText name)
      DTopSplice {} -> Set.empty
      DUnsafeAssert _ declaration _ -> declarationBinders declaration

-- | Every name bound anywhere inside the payload (patterns, binders,
-- local definitions, comprehension clauses, do items). Conservative
-- over-approximation: a quoted payload that rebinds a name anywhere
-- keeps every occurrence of that spelling un-captured (§21.4 hygiene
-- still holds for the fixture-relevant forms; see SPEC_COMPLIANCE.md).
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
      DoVar n _ _ _ -> [nameText n]
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
      ERefFacet n _ -> "ref " <> nameText n
      EVarRead n _ -> "readRef (ref " <> nameText n <> ")"
      EQuantityBorrowMarker _ -> "&"
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
          item it =
            let q = maybe "" (\x -> renderQuantity x <> " ") (riQuantity it)
             in Just (q <> nameText (riName it) <> maybe "" ((" = " <>) . render) (riValue it))
          renderQuantity = \case
            QZero -> "0"
            QOne -> "1"
            QOmega -> "ω"
            QAtMostOne -> "<=1"
            QAtLeastOne -> ">=1"
            QTerm e -> "(" <> render e <> ")"
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
      ERefFacet {} -> render e
      EVarRead {} -> render e
      EIntLit {} -> render e
      EUnit {} -> render e
      EStringLit {} -> render e
      _ -> "(" <> render e <> ")"
