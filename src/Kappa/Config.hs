-- | Config-mode checking (Spec §35): a config unit is ordinary Kappa
-- source evaluated under a loader-supplied schema scope with the
-- additional declaration and expression restrictions of Chapter 35.
-- This module provides the @config-expression@ profile used by the
-- build-manifest loader (§35.13): the structural restriction pass
-- (§35.1/§35.2.2), the schema-scope construction (§35.3) that supplies
-- @std.config@/@std.build@ names without an ordinary import, and the
-- restricted check of the unit.
--
-- Per §35.1 the restrictions are additional restrictions on ordinary
-- Kappa, not a separate parser: the caller parses with the ordinary
-- 'parseModule', and this module enforces the config restrictions over
-- the parsed 'Module' and checks it with the ordinary 'checkModule'
-- under the schema scope.
module Kappa.Config
  ( ConfigProfile (..)
  , schemaScopeFor
  , configRestrictionDiags
  , checkConfigUnit
  , manifestSchemaModules
  , configFamily
  ) where

import Data.Data (Data, cast, gmapQ)
import Data.List (foldl')
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Builtins
import Kappa.Check
import Kappa.Core (GName (..))
import Kappa.Diagnostic
import Kappa.Resolve (defaultFixities, resolveModule)
import Kappa.Source
import Kappa.Syntax
import Kappa.SyntaxOps (queryExprs)

-- | The standardized config profiles (§35.2). The build manifest is
-- checked in 'ConfigExpression' (§35.13).
data ConfigProfile = ConfigData | ConfigExpression | ConfigSchema
  deriving stock (Eq, Show)

profileName :: ConfigProfile -> Text
profileName = \case
  ConfigData -> "config-data"
  ConfigExpression -> "config-expression"
  ConfigSchema -> "config-schema"

-- | The schema modules whose config-safe names a build manifest is
-- checked under (§35.3): @std.config@ and @std.build@.
manifestSchemaModules :: [ModuleName]
manifestSchemaModules = [modConfig, modBuild]

-- | The config-admissible prelude names (§35.3): the schema scope
-- provides "only the config-safe names required for literals, records,
-- tuples, lists, booleans, options, results, ordering". These are the
-- portable-minimum config-admissible types (§35.5) and their data
-- constructors — NOT ordinary prelude functions, so a manifest cannot
-- call, e.g., @map@. The build vocabulary itself comes from
-- @std.build@/@std.config@ (the schema modules), not from this list.
configAdmissiblePreludeNames :: [Text]
configAdmissiblePreludeNames = configSafeTypeNames ++ configSafeCtorNames

-- | Build the §35.3 schema scope from a prelude 'CheckState' in which
-- the schema modules have already been checked (their config-safe names
-- are registered in 'csGlobals'/'csCtors'/'csModuleExports'). The
-- resulting unqualified scope maps each config-safe name to its 'GName';
-- the manifest references these names without an ordinary import.
--
-- Names from a later schema module shadow earlier ones; the config
-- admissible prelude subset is installed first so the build vocabulary
-- wins on any (currently nonexistent) collision.
schemaScopeFor :: CheckState -> Map.Map Text GName
schemaScopeFor st = foldl' add preludeNames manifestSchemaModules
  where
    inScope g = Map.member g (csGlobals st) || Map.member g (csCtors st)
    preludeNames =
      Map.fromList
        [ (nm, g)
        | nm <- configAdmissiblePreludeNames
        , let g = gPrel nm
        , inScope g
        ]
    add acc mn =
      foldl'
        (\m nm -> Map.insert nm (GName mn nm) m)
        acc
        [ nm
        | nm <- Map.findWithDefault [] mn (csModuleExports st)
        , inScope (GName mn nm)
        ]

-- ── §35.1/§35.2.2 restriction pass ───────────────────────────────────

declSpan :: Decl -> Span
declSpan = \case
  DSig _ _ _ s -> s
  DLet _ _ s -> s
  DData _ _ s -> s
  DTypeAlias _ _ _ _ _ s -> s
  DTrait _ _ s -> s
  DInstance _ s -> s
  DFixity _ s -> s
  DImport _ s -> s
  DExport _ s -> s
  DExpect _ _ s -> s
  d -> declSpanFallback d

-- Decls not covered above carry their own span field last; we only need
-- a best-effort location for the diagnostic. Use a zero span when the
-- shape is unknown (these forms are themselves rejected anyway).
declSpanFallback :: Decl -> Span
declSpanFallback _ = Span "<config>" (Pos 1 1) (Pos 1 1)

-- | The §35.11 config diagnostic family for a code, as a full literal
-- (the family-completeness gate scans for full family string literals,
-- so these must not be assembled by prefix concatenation). Every value
-- here is registered in "Kappa.Explain".
configFamily :: DiagnosticCode -> DiagnosticFamily
configFamily = \case
  "E_CONFIG_PARSE" -> "kappa-hs.config.parse"
  "E_CONFIG_RESTRICTED_FORM" -> "kappa-hs.config.restricted-form"
  "E_CONFIG_IMPORT_NOT_SAFE" -> "kappa-hs.config.import-not-safe"
  "E_CONFIG_TYPE" -> "kappa-hs.config.type"
  "E_CONFIG_UNRESOLVED_NAME" -> "kappa-hs.config.unresolved-name"
  "E_CONFIG_CALL_NOT_SAFE" -> "kappa-hs.config.call-not-safe"
  "E_CONFIG_PARTIAL_APPLICATION" -> "kappa-hs.config.partial-application"
  "E_CONFIG_EVAL" -> "kappa-hs.config.eval"
  "E_CONFIG_PROVENANCE_UNAVAILABLE" -> "kappa-hs.config.provenance-unavailable"
  "E_CONFIG_INTERPOLATION" -> "kappa-hs.config.interpolation"
  "E_CONFIG_EXPECTED_VALUE" -> "kappa-hs.config.expected-value"
  _ -> "kappa-hs.config.restricted-form"

cfgErr :: DiagnosticCode -> Span -> Text -> Diagnostic
cfgErr code = diag SevError StageElaborate code (Just (configFamily code))

-- | Structural + expression restriction diagnostics for a config unit
-- (§35.1, §35.2.2). The caller has already parsed the module; these are
-- the additional config-mode restrictions.
configRestrictionDiags :: ConfigProfile -> Module -> Diagnostics
configRestrictionDiags prof m =
  headerDiag ++ concatMap declDiags (modDecls m)
  where
    prof' = profileName prof
    -- §35.1: a config unit has no module header.
    headerDiag = case modHeader m of
      Just mp ->
        [ cfgErr "E_CONFIG_RESTRICTED_FORM"
            (Span "<config>" (Pos 1 1) (Pos 1 1))
            ( "a config unit (" <> prof' <> ") must have no module header; found 'module "
                <> T.intercalate "." (modPathName mp) <> "' (Spec §35.1)"
            )
        ]
      Nothing -> []

    declDiags d = case d of
      -- §35.1: config units contain only top-level value bindings.
      DLet _ ld s -> letDiags s ld
      DImport _ s ->
        [cfgErr "E_CONFIG_IMPORT_NOT_SAFE" s ("ordinary imports are not admitted in a config unit (" <> prof' <> ", Spec §35.3)")]
      DExport _ s ->
        [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("a config unit has no 'export' declarations (" <> prof' <> ", Spec §35.1)")]
      DSig _ n _ s ->
        [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("a config unit has no top-level signature separate from its definition ('" <> nameText n <> "', " <> prof' <> ", Spec §35.1)")]
      DData _ _ s ->
        [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("local 'data' declarations are not admitted in a config unit (" <> prof' <> ", Spec §35.2.2)")]
      DTypeAlias {} -> [] -- §35.2.2: nonrecursive local type aliases are admitted in config-expression
      DTrait _ _ s ->
        [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("traits are not admitted in a config unit (" <> prof' <> ", Spec §35.2.2)")]
      DInstance _ s ->
        [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("instances are not admitted in a config unit (" <> prof' <> ", Spec §35.2.2)")]
      DExpect _ _ s ->
        [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("'expect' declarations are not admitted in a config unit (" <> prof' <> ", Spec §35.2.2)")]
      _ ->
        [cfgErr "E_CONFIG_RESTRICTED_FORM" (declSpan d) ("this declaration form is not admitted in a config unit (" <> prof' <> ", Spec §35.1)")]

    -- A config binding is `let ident [: type] = configExpr`: a single
    -- simple identifier, no binders (a function definition is a
    -- user-defined function, rejected by §35.2.2), no pattern binding.
    letDiags s ld =
      nameDiag ++ binderDiag ++ patternDiag ++ exprDiags (ldBody ld)
      where
        nameDiag = case ldName ld of
          Just _ -> []
          Nothing ->
            [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("a config binding must bind a simple identifier (" <> prof' <> ", Spec §35.1)")]
        binderDiag
          | null (ldBinders ld) = []
          | otherwise =
              [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("user-defined functions are not admitted in a config unit; a config binding takes no parameters (" <> prof' <> ", Spec §35.2.2)")]
        patternDiag = case ldPattern ld of
          Nothing -> []
          Just _ ->
            [cfgErr "E_CONFIG_RESTRICTED_FORM" s ("pattern bindings are not admitted as config bindings (" <> prof' <> ", Spec §35.1)")]

    -- §35.2.2 expression admissibility (config-expression). We reject the
    -- clearly inadmissible forms anywhere in the binding body using a
    -- generic top-down Expr query (no node is missed); the schema scope
    -- plus ordinary type checking reject the rest (unresolved or
    -- non-config-safe callees surface as ordinary name/type errors).
    -- Partial application and stuck values are caught at reification.
    -- queryExprs deliberately does NOT enter quote payloads and yields
    -- nothing for a top-level 'EQuote', so syntax quotes would slip past
    -- the walk below. Catch every quote/quoted-literal node with a
    -- separate full 'Data' descent (entering quote payloads) — §35.2.2
    -- admits no first-class function/syntax values.
    exprDiags :: Expr -> Diagnostics
    exprDiags e = quoteDiags e ++ queryExprs check e
      where
        quoteDiags :: Data b => b -> Diagnostics
        quoteDiags x = hereQuote x ++ concat (gmapQ quoteDiags x)
        hereQuote x = case cast x :: Maybe Expr of
          Just (EQuote _ s) -> [cfgErr "E_CONFIG_RESTRICTED_FORM" s "syntax quotes are not admitted in a config unit (Spec §35.2.2)"]
          Just (EQuotedLit _ s) -> [cfgErr "E_CONFIG_RESTRICTED_FORM" s "quoted literals are not admitted in a config unit (Spec §35.2.2)"]
          _ -> []
        check e0 = case e0 of
          ELambda _ _ _ s -> stop s "first-class function values (lambda) are not admitted in a config unit (Spec §35.2.2)"
          EDo {} -> stop (exprSpan e0) "'do'/IO is not admitted in a config unit (Spec §35.2.2)"
          EBang _ _ s -> stop s "the unsafe/effect '!' form is not admitted in a config unit (Spec §35.2.2)"
          EHandle _ _ _ _ s -> stop s "effect handlers are not admitted in a config unit (Spec §35.2.2)"
          ETry _ _ _ s -> stop s "'try' is not admitted in a config unit (Spec §35.2.2)"
          ETryMatch _ _ _ _ s -> stop s "'try' is not admitted in a config unit (Spec §35.2.2)"
          EComprehension _ _ _ s -> stop s "comprehensions are not admitted in a config unit (Spec §35.2.2)"
          ESetLit _ s -> stop s "set literals are not admitted in a config unit (Spec §35.2.2)"
          EMapLit _ s -> stop s "map literals are not admitted in a config unit (Spec §35.2.2)"
          ECodeQuote _ s -> stop s "code quotes are not admitted in a config unit (Spec §35.2.2)"
          ECodeEscape _ s -> stop s "code escapes are not admitted in a config unit (Spec §35.2.2)"
          ESplice _ s -> stop s "macro splices are not admitted in a config unit (Spec §35.2.2)"
          ESpliceInQuote _ s -> stop s "macro splices are not admitted in a config unit (Spec §35.2.2)"
          ESeal _ _ s -> stop s "package sealing is not admitted in a config unit (Spec §35.2.2)"
          EOpenExists _ _ _ _ s -> stop s "existential opening is not admitted in a config unit (Spec §35.2.2)"
          ESealExists _ _ _ s -> stop s "existential sealing is not admitted in a config unit (Spec §35.2.2)"
          _ -> ([], True)
        stop s msg = ([cfgErr "E_CONFIG_RESTRICTED_FORM" s msg], False)

-- | Run the config-mode check of a manifest module on top of a prelude
-- state in which the schema modules are registered. Installs the §35.3
-- schema scope (no ordinary import), enforces the §35.1/§35.2.2
-- restrictions, and checks the unit with the ordinary checker. Returns
-- the resulting 'CheckState' (whose 'csCoreBodies' holds the elaborated
-- @buildConfig@ body for reification) and all diagnostics.
checkConfigUnit ::
  ConfigProfile ->
  CheckState ->
  ModuleName ->
  Module ->
  (CheckState, Diagnostics)
checkConfigUnit prof pst mn m =
  let restrictDiags = configRestrictionDiags prof m
      (m', rdiags) = resolveModule defaultFixities m
      scope = schemaScopeFor pst
      stIn =
        pst
          { csModule = mn
          , csScope = scope
          , csScopeAmbig = Map.empty
          , csModuleAliases = Map.empty
          , csDiags = []
          , csScopeNameCache = Nothing
          }
      (st1, cdiags) = checkModule stIn m'
      -- §35.11: config evaluation must report under the config diagnostic
      -- classes and identify the active profile. The ordinary checker
      -- emits its own codes (E_NAME_UNRESOLVED, type mismatches, parse
      -- errors); remap the recognized ones to their E_CONFIG_* class and
      -- annotate the profile, leaving E_CONFIG_*/E_BUILD_* (our own) and
      -- anything unrecognized untouched.
      toConfig = map (remapConfigDiag prof)
   in (st1, restrictDiags ++ toConfig (rdiags ++ cdiags))

-- | Remap an ordinary checker/parser diagnostic to its §35.11 config
-- class when it is one of the recognized kinds, appending the active
-- profile to the message. This is only ever applied to the ordinary
-- resolve/check diagnostics of a config unit (never to the config-class
-- diagnostics this module emits directly), so no config/build code can
-- appear here. Full ordinary code names are matched (not prefixes) so
-- the registry gate's code-literal scanner sees only registered codes.
remapConfigDiag :: ConfigProfile -> Diagnostic -> Diagnostic
remapConfigDiag prof d
  | dSeverity d /= SevError = d
  | Just code' <- mapped =
      d
        { dCode = code'
        , dFamily = Just (configFamily code')
        , dMessage = dMessage d <> " [" <> profileName prof <> " profile, Spec §35.11]"
        }
  | otherwise = d
  where
    c = dCode d
    mapped
      | dStage d == StageParse || dStage d == StageLex = Just "E_CONFIG_PARSE"
      | c `elem` ["E_NAME_UNRESOLVED", "E_MODULE_NAME_UNRESOLVED"] = Just "E_CONFIG_UNRESOLVED_NAME"
      | c == "E_APPLICATION_NONCALLABLE" = Just "E_CONFIG_CALL_NOT_SAFE"
      | c
          `elem` [ "E_TYPE_EQUALITY_MISMATCH"
                 , "E_NOT_A_TYPE"
                 , "E_APPLICATION_ARGUMENT_MISMATCH"
                 , "E_CONSTRUCTOR_ARITY_MISMATCH"
                 , "E_BINDER_MISMATCH"
                 ] =
          Just "E_CONFIG_TYPE"
      | otherwise = Nothing
