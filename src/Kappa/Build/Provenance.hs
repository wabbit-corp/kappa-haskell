-- | Value provenance for config evaluation (§35.7). Provenance is
-- metadata (§35.7: it does not affect typing, equality, hashing, identity,
-- or backend output) that records where each config value came from, so a
-- tool can answer "which source range produced this value", "where was it
-- named", and "which earlier values contributed to it".
--
-- This builds the provenance graph from the manifest's SURFACE syntax (the
-- span-bearing AST) rather than the normalized value: §35.7's model is
-- expression-oriented (origin of the binding name, origin of the computing
-- expression, edges from a reference to the referenced value's
-- provenance), which is exactly what the surface tree expresses. It is
-- precise where the structure is directly readable (literals, named
-- application, lists) and uses 'DerivedProvenance'/'UnknownProvenance'
-- where evaluation would be needed to be exact (e.g. through @if@/@match@).
-- Per §35.7 it never fabricates precise provenance: a value computed by a
-- conditional is recorded as derived from that operation, not from a
-- guessed branch.
module Kappa.Build.Provenance
  ( Provenance (..)
  , manifestProvenance
  , renderProvenance
  ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Source (Pos (..), Span (..))
import Kappa.Syntax

-- | A §35.7 provenance record. ('PartialProvenance' from the spec is
-- represented as a 'CompositeProvenance'/'SequenceProvenance' whose
-- unknown components are 'UnknownProvenance'.)
data Provenance
  = UnknownProvenance
  | SourceProvenance !Span
  -- ^ a source origin that directly produced the value (a literal, or a
  -- schema-scope name)
  | DerivedProvenance !Span ![Provenance]
  -- ^ an operation origin (a call, a reference, a conditional) together
  -- with the provenances of the values that contributed to it
  | CompositeProvenance !Span ![(Text, Provenance)]
  -- ^ a structured value (named application / record / constructor) with
  -- per-component provenance
  | SequenceProvenance !Span ![Provenance]
  -- ^ a sequence value (list) with per-element provenance
  deriving stock (Show)

-- | The provenance of a manifest's @buildConfig@ value, computed over the
-- config unit's top-level @let@ bindings (each binding's value provenance
-- is bound for later reference edges). 'Nothing' if there is no
-- @buildConfig@ binding.
manifestProvenance :: Module -> Maybe Provenance
manifestProvenance m =
  let lets = [ld | DLet _ ld _ <- modDecls m, null (ldBinders ld)]
      step ev ld = case ldName ld of
        Just n -> Map.insert (nameText n) (provExpr ev (ldBody ld)) ev
        Nothing -> ev
      env = foldl' step Map.empty lets
   in case [ld | ld <- lets, fmap nameText (ldName ld) == Just "buildConfig"] of
        (ld : _) -> Just (provExpr env (ldBody ld))
        [] -> Nothing

-- | Provenance of an expression under a binding environment mapping each
-- earlier config binding to its value provenance.
provExpr :: Map.Map Text Provenance -> Expr -> Provenance
provExpr env e0 = case e0 of
  EIntLit {} -> SourceProvenance (exprSpan e0)
  EFloatLit {} -> SourceProvenance (exprSpan e0)
  -- a plain string is a source; an interpolated string is derived from
  -- its hole subexpressions (preserving reference edges, §35.7/§35.8),
  -- without fabricating per-slice spans.
  EStringLit _ parts _
    | null parts -> SourceProvenance (exprSpan e0)
    | otherwise -> DerivedProvenance (exprSpan e0) [provExpr env (ipExpr p) | p <- parts]
  EQuotedLit {} -> SourceProvenance (exprSpan e0)
  EUnit _ -> SourceProvenance (exprSpan e0)
  EVar n -> reference env n
  EApp _f args -> case [nb | ArgNamedBlock nb _ <- args] of
    -- §10.1.1/§16.1.7 named application: a structured value with
    -- per-field provenance (a punned field reuses a bound value). Any
    -- preceding positional argument is kept as an indexed component.
    (fields : _) ->
      CompositeProvenance (exprSpan e0)
        ( [(T.pack (show i), provExpr env a) | (i, ArgExplicit a) <- zip [1 :: Int ..] args]
            ++ [(nameText n, maybe (reference env n) (provExpr env) me) | (n, me) <- fields]
        )
    -- a positional call: derived from its explicit arguments.
    [] -> DerivedProvenance (exprSpan e0) [provExpr env a | ArgExplicit a <- args]
  EListLit es _ -> SequenceProvenance (exprSpan e0) (map (provExpr env) es)
  ETuple es _ -> CompositeProvenance (exprSpan e0) (zipWith (\i x -> (T.pack (show i), provExpr env x)) [1 :: Int ..] es)
  ERecordLit items _ ->
    CompositeProvenance (exprSpan e0)
      [(nameText (riName it), maybe (reference env (riName it)) (provExpr env) (riValue it)) | it <- items]
  EAscription e _ _ -> provExpr env e
  EIf arms mdef _ ->
    -- the value is one branch; we do not guess which (no fabricated
    -- precise provenance), recording it as derived from the conditional.
    DerivedProvenance (exprSpan e0) (concat [[provExpr env c, provExpr env t] | (c, t) <- arms] ++ maybe [] (pure . provExpr env) mdef)
  EMatch scrut cs _ ->
    DerivedProvenance (exprSpan e0)
      ( provExpr env scrut
          : concat [maybe [] (pure . provExpr env) mg ++ [provExpr env b] | MatchCase _ mg b _ <- cs]
      )
  ELet binds body _ ->
    let env' = foldl' (\ev b -> bindLet ev b) env binds
     in provExpr env' body
  EThunk e _ -> provExpr env e
  ELazy e _ -> provExpr env e
  EForce e _ -> provExpr env e
  EOptionSugar e _ -> provExpr env e
  _ -> UnknownProvenance

-- | A let-bound local: extend the env with the binding's value provenance
-- (only simple identifier bindings carry a usable reference origin).
bindLet :: Map.Map Text Provenance -> LetBind -> Map.Map Text Provenance
bindLet env (LetBind _ _ pat _ rhs _) = case pat of
  PVar n -> Map.insert (nameText n) (provExpr env rhs) env
  _ -> env

-- | The provenance of a reference to @n@: an edge from the reference
-- origin to the referenced value's provenance (§35.7); a free name (a
-- schema-scope builder) is a direct source origin.
reference :: Map.Map Text Provenance -> Name -> Provenance
reference env n = case Map.lookup (nameText n) env of
  Just p -> DerivedProvenance (nameSpan n) [p]
  Nothing -> SourceProvenance (nameSpan n)

-- ── rendering ────────────────────────────────────────────────────────

-- | Render a span as @file:line:col@.
renderSpan :: Span -> Text
renderSpan sp =
  T.pack (spanFile sp)
    <> ":" <> T.pack (show (posLine (spanStart sp)))
    <> ":" <> T.pack (show (posCol (spanStart sp)))

-- | Render a provenance graph as an indented tree (spans as file:line:col).
renderProvenance :: Provenance -> Text
renderProvenance = T.unlines . go 0
  where
    ind n = T.replicate n "  "
    go n p = case p of
      UnknownProvenance -> [ind n <> "unknown"]
      SourceProvenance sp -> [ind n <> "source " <> renderSpan sp]
      DerivedProvenance sp ps -> (ind n <> "derived " <> renderSpan sp) : concatMap (go (n + 1)) ps
      SequenceProvenance sp ps ->
        (ind n <> "sequence " <> renderSpan sp)
          : concat [(ind (n + 1) <> "[" <> T.pack (show i) <> "]") : go (n + 2) c | (i, c) <- zip [0 :: Int ..] ps]
      CompositeProvenance sp fs ->
        (ind n <> "composite " <> renderSpan sp)
          : concat [(ind (n + 1) <> field <> ":") : go (n + 2) c | (field, c) <- fs]
