-- | Diagnostic code registry (Spec §3.1.2A).
--
-- A machine-readable registry of every diagnostic code this
-- implementation may emit in ordinary user-facing compilation, plus the
-- §3.1.3 standard Unicode diagnostic codes (whose spellings and
-- explanations the specification fixes for all conforming
-- implementations). Backs the @kappa explain CODE@ subcommand and the
-- §T.5.1 @assertDiagnosticExplainExists@ harness directive.
--
-- Family namespace (§3.1.2, §3.1.2A): a family spelled @kappa.…@ is
-- always one of the specification's standardized families (§3.2,
-- §3.1.5, §3.2.19), used exactly when the diagnostic corresponds to
-- that family's defined situation. Implementation-defined diagnostics
-- with no standardized family either carry no family or use the
-- implementation-reserved prefix @kappa-hs.…@, which cannot collide
-- with the reserved @kappa.@ namespace.
module Kappa.Explain
  ( ExplainEntry (..)
  , Stability (..)
  , registry
  , lookupCode
  , lookupFamily
  , familyMembers
  , explainExists
  , renderEntry
  , renderFamily
  , portableAlias
  , codeNames
  ) where

import Data.List (nub)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Diagnostic (Severity (..))

-- | §3.1.2A registry-entry stability classification.
data Stability = Stable | Experimental | Deprecated | Internal
  deriving stock (Eq, Show)

stabilityText :: Stability -> Text
stabilityText = \case
  Stable -> "stable"
  Experimental -> "experimental"
  Deprecated -> "deprecated"
  Internal -> "internal"

severityText :: Severity -> Text
severityText = \case
  SevError -> "error"
  SevWarning -> "warning"
  SevNote -> "note"
  SevInfo -> "info"

-- | A §3.1.2A machine-readable diagnostic code registry entry. The
-- conceptual shape (Spec.md:689-701) is modelled by the fields below;
-- @defaultSeverity@, @stability@, @portableAliases@, @owner@ and
-- @introducedIn@ are required registry metadata.
data ExplainEntry = ExplainEntry
  { eeCode :: !Text
  , eeFamily :: !(Maybe Text)
  , eeExplanation :: !Text
  , eeDefaultSeverity :: !Severity
  , eeStability :: !Stability
  , eePortableAliases :: ![Text]
  , eeOwner :: !Text
  , eeIntroducedIn :: !Text
  }

lookupCode :: Text -> Maybe ExplainEntry
lookupCode c = case [e | e <- registry, eeCode e == c] of
  (e : _) -> Just e
  [] -> Nothing

-- | §3.1.13: the codes registered under a standardized family, for
-- @kappa explain <family>@. The argument is a family spelling such as
-- @kappa.type.mismatch@.
familyMembers :: Text -> [ExplainEntry]
familyMembers fam = [e | e <- registry, eeFamily e == Just fam]

-- | §3.1.13: does any registry entry carry this family? Returns the
-- (non-empty) member list when so.
lookupFamily :: Text -> Maybe [ExplainEntry]
lookupFamily fam = case familyMembers fam of
  [] -> Nothing
  es -> Just es

-- | §T.5.1 @code-or-family@ matching: a spelling beginning with
-- @kappa.@ (a §3.2 standardized family) or with @kappa-hs.@ (this
-- implementation's reserved family prefix, §3.1.2/§3.1.2A:
-- implementation-defined families must use an implementation-reserved
-- prefix that cannot collide with the @kappa.@ namespace) is a family;
-- otherwise it is a code (codes win ties).
explainExists :: Text -> Bool
explainExists s
  | "kappa." `T.isPrefixOf` s || "kappa-hs." `T.isPrefixOf` s =
      any ((== Just s) . eeFamily) registry
  | otherwise = any ((== s) . eeCode) registry

-- | A rendered code's standardized comparison spelling, where one
-- applies. Every mapping here is a §3.1.4 *required* portable alias (see
-- 'requiredAliasTable'); the harness treats either spelling as
-- acceptable when matching @assertDiagnostic*@ directives. There are no
-- implementation-defined "tolerances": a code that §3.1.4 does not
-- standardize is compared verbatim, so a diagnostic that emits a
-- materially different code than a fixture pins is reported as a
-- mismatch rather than silently reconciled.
portableAlias :: Text -> Maybe Text
portableAlias c = lookup c requiredAliasTable

-- | Required portable diagnostic-code aliases (§3.1.4). Each entry maps
-- this implementation's rendered code for a §3.1.4-listed condition to
-- the standardized portable-alias spelling that subsection mandates. A
-- diagnostic "code" in the sense of §3.1 is recoverable either as the
-- rendered code or as its portable alias (§3.1.2A allows an
-- implementation to expose either spelling), so the harness accepts
-- both. Every right-hand spelling here appears in the §3.1.4 normative
-- list (Spec.md:827-896): @E_TYPE_MISMATCH@, @E_SAFE_NAV_GENERIC_AMBIGUOUS@,
-- @E_APPLICATION_NON_CALLABLE@, @E_MISSING_EXPLICIT_SIGNATURE@,
-- @E_CONSTRUCTOR_ARITY_MISMATCH@. (Codes whose rendered spelling already
-- equals the §3.1.4 portable spelling — e.g.
-- @E_NUMERIC_LITERAL_DOMAIN_MISMATCH@ — need no alias entry.)
--
-- The three @E_NAMED_ARG_*@ codes are the implementation-specific
-- spellings of a malformed *named* constructor application (a missing,
-- duplicated, or unexpected named field on a known constructor; emitted
-- only on the constructor branch of 'Check.elabNamedBlock'). §3.2
-- (Spec.md:3210-3225) classes this as a malformed constructor
-- application: the standardized family is @kappa.constructor.arity@ and
-- the diagnostic "MUST use portable alias @E_CONSTRUCTOR_ARITY_MISMATCH@"
-- (also §3.1.4 Spec.md:925-926, "too few, too many, duplicated, or
-- otherwise malformed constructor arguments after constructor identity
-- is known"). §3.1.4 (Spec.md:819) permits also exposing an
-- implementation-specific code, so the precise duplicate/missing/unknown
-- distinction is preserved in the rendered code while tooling recovers
-- the portable alias here.
--
-- §3.1.4 (Spec.md:823): "A portable diagnostic-code alias MUST NOT be
-- reused for a materially different diagnostic meaning." Accordingly
-- this table maps only codes whose condition is the *same* condition the
-- target alias standardizes; conditions §3.1.4 does not standardize
-- (e.g. a stuck @kappa.implicit.unsolved@ trait/evidence goal, §3.2.4)
-- are NOT folded onto an unrelated alias.
requiredAliasTable :: [(Text, Text)]
requiredAliasTable =
  [ ("E_TYPE_EQUALITY_MISMATCH", "E_TYPE_MISMATCH")
  , ("E_SAFE_NAVIGATION_AMBIGUOUS", "E_SAFE_NAV_GENERIC_AMBIGUOUS")
  , ("E_APPLICATION_NONCALLABLE", "E_APPLICATION_NON_CALLABLE")
  , ("E_RECURSION_REQUIRES_SIGNATURE", "E_MISSING_EXPLICIT_SIGNATURE")
  , ("E_NAMED_ARG_MISSING", "E_CONSTRUCTOR_ARITY_MISMATCH")
  , ("E_NAMED_ARG_DUPLICATE", "E_CONSTRUCTOR_ARITY_MISMATCH")
  , ("E_NAMED_ARG_UNKNOWN", "E_CONSTRUCTOR_ARITY_MISMATCH")
  ]

-- | All acceptable spellings of a diagnostic's code: the rendered code
-- plus its §3.1.2A portable alias, when defined.
codeNames :: Text -> [Text]
codeNames c = c : maybe [] (: []) (portableAlias c)

renderEntry :: ExplainEntry -> Text
renderEntry e =
  eeCode e
    <> maybe "" (\f -> " (" <> f <> ")") (eeFamily e)
    <> "\n\n"
    <> eeExplanation e
    <> "\n\n"
    <> "  default severity: " <> severityText (eeDefaultSeverity e) <> "\n"
    <> "  stability:        " <> stabilityText (eeStability e) <> "\n"
    <> "  owner:            " <> eeOwner e <> "\n"
    <> "  introduced in:    " <> eeIntroducedIn e <> "\n"
    <> ( if null (eePortableAliases e)
           then ""
           else "  portable aliases: " <> T.intercalate ", " (eePortableAliases e) <> "\n"
       )

-- | §3.1.13 @kappa explain <family>@: a short explanation of the family
-- plus the registered member codes. The family text is the shared
-- prefix of its members' explanations is not assumed; instead the
-- family lists its members so a reader can drill into a specific code.
renderFamily :: [ExplainEntry] -> Text
renderFamily es =
  fam <> "\n\n"
    <> "A standardized Kappa diagnostic family (§3.2). Diagnostics in this\n"
    <> "family share the family identifier above; tooling and portable tests\n"
    <> "match on the family rather than on a specific implementation code\n"
    <> "(§3.1.2, §3.1.2A).\n\n"
    <> "  member codes: " <> T.intercalate ", " (nub (map eeCode es)) <> "\n"
  where
    fam = case es of
      (e : _) -> maybe "(unknown family)" id (eeFamily e)
      [] -> "(unknown family)"

registry :: [ExplainEntry]
registry =
  [ ent "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument-mismatch")
      "An argument in a function application does not fit the corresponding parameter (wrong plicity, label, or form)."
  , ent "E_APPLICATION_NONCALLABLE" (Just "kappa-hs.application.non-callable")
      "The head of an application has a type that is not a function or callable value, so it cannot be applied to arguments."
  , ent "E_ASSIGN_NOT_VAR" (Just "kappa-hs.do.assign-non-var")
      "The left-hand side of a do-block assignment is not a mutable 'var' binding introduced in the same do scope."
  , ent "E_BINDER_MISMATCH" (Just "kappa-hs.type.binder")
      "A lambda or function definition binds a parameter whose plicity or label does not match the binder in the expected function type."
  , ent "E_BLOCK_NO_RESULT" Nothing
      "A block expression ends without producing a result expression, so the block has no value."
  , ent "E_BREAK_OUTSIDE_LOOP" (Just "kappa-hs.do.break-outside-loop")
      "A 'break' or 'continue' control expression appears outside any enclosing loop."
  , ent "E_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.constructor.arity")
      "A data constructor is applied to the wrong number of arguments for its declaration."
  -- §35.11 config-mode diagnostic classes. A config unit (e.g. the
  -- build manifest 'kappa.build.kp', §35.13) is ordinary Kappa checked
  -- under a loader-supplied schema scope with the additional Chapter-35
  -- restrictions; these are the required diagnostic classes for config
  -- evaluation.
  , ent "E_CONFIG_PARSE" (Just "kappa-hs.config.parse")
      "A config unit failed to parse as ordinary Kappa syntax (Spec §35.11)."
  , ent "E_CONFIG_RESTRICTED_FORM" (Just "kappa-hs.config.restricted-form")
      "A config unit uses a declaration or expression form not admitted by the active config profile (e.g. a module header, an export, a function definition, a lambda, 'do'/IO, traits/instances, or local 'data') (Spec §35.1, §35.2.2)."
  , ent "E_CONFIG_IMPORT_NOT_SAFE" (Just "kappa-hs.config.import-not-safe")
      "A config unit uses an ordinary import; portable config profiles supply names through the loader's schema scope, not by import (Spec §35.3)."
  , ent "E_CONFIG_TYPE" (Just "kappa-hs.config.type")
      "A config unit is ill-typed under config-admissible typing (Spec §35.11)."
  , ent "E_CONFIG_UNRESOLVED_NAME" (Just "kappa-hs.config.unresolved-name")
      "A config unit references a name that is neither an earlier config binding nor a name in the loader-supplied schema scope (Spec §35.3, §35.11)."
  , ent "E_CONFIG_CALL_NOT_SAFE" (Just "kappa-hs.config.call-not-safe")
      "A config unit calls a function that is not marked config-safe in the schema scope (Spec §35.2.2, §35.5)."
  , ent "E_CONFIG_PARTIAL_APPLICATION" (Just "kappa-hs.config.partial-application")
      "A config unit leaves a config-safe function partially applied; config-mode calls must supply all explicit arguments (Spec §35.2.2)."
  , ent "E_CONFIG_EVAL" (Just "kappa-hs.config.eval")
      "A config unit could not be evaluated to a config value by deterministic normalization (Spec §35.6)."
  , ent "E_CONFIG_PROVENANCE_UNAVAILABLE" (Just "kappa-hs.config.provenance-unavailable")
      "Value provenance for a config value is unavailable (the value came from an opaque config-safe function, an implementation boundary, an implementation limit, or an unknown external input) (Spec §35.11)."
  , ent "E_CONFIG_INTERPOLATION" (Just "kappa-hs.config.interpolation")
      "A config unit uses a string interpolation or prefixed-string handler not admitted by the active config profile (Spec §35.11)."
  , ent "E_CONFIG_EXPECTED_VALUE" (Just "kappa-hs.config.expected-value")
      "A config unit did not produce the value the loader required (e.g. a build manifest that does not define exactly one 'let buildConfig : BuildConfig = ...') (Spec §35.13, §35.11)."
  -- Build-manifest loading and provider diagnostics (§36, §3.2.15).
  , ent "E_BUILD_MANIFEST_NOT_FOUND" (Just "kappa-hs.build.manifest-not-found")
      "No build manifest ('kappa.build.kp') was found for the requested build (Spec §35.13, §36.3)."
  , ent "E_BUILD_TARGET_NOT_FOUND" (Just "kappa-hs.build.target-not-found")
      "The requested build target is not defined by the build manifest (Spec §36.3, §36.4)."
  , ent "E_PROVIDER_COLLISION" (Just "kappa.provider.collision")
      "More than one host-binding provider claims the same effective module name under a reserved host root; the manifest must disambiguate which provider supplies it (Spec §3.2.15, §36.28)."
  , ent "E_NATIVE_BINDING_UNPINNED" (Just "kappa.package.reproducibility")
      "A native binding selected by the manifest cannot be pinned to an immutable identity for reproducible builds (Spec §3.2.15, §36.28)."
  , ent "E_HOST_MODULE_SOURCE_DEFINED" (Just "kappa-hs.host.reserved")
      "A source module's effective name is at or under a reserved host binding root (host.jvm/host.dotnet/host.native/host.python); those modules are supplied from host metadata or ABI descriptions, not user source (Spec §8.3.5)."
  , ent "E_NATIVE_BINDING_UNSUPPORTED" (Just "kappa-hs.build.native-unsupported")
      "A manifest native binding names a host.native module, or a member of one, that the selected backend profile does not provide in its native catalog (Spec §27.1.1, §34.5.3, §36.28)."
  , ent "E_BUILD_BINDING_NOT_FOUND" (Just "kappa-hs.build.binding-not-found")
      "A build target references a host-binding name that the manifest's hostBindings does not declare (Spec §36.3, §36.28)."
  , ent "E_BUILD_ENTRY_NOT_FOUND" (Just "kappa-hs.build.entry-not-found")
      "A build target's entry (main) module could not be located as a source file under the package's source roots (Spec §36.3, §36.4)."
  , ent "E_MODULE_NAME_CASE_COLLISION" (Just "kappa-hs.module.case-collision")
      "Two source files in a compilation unit derive module names that are equal after case-folding but differ in case (Spec §8.1)."
  , ent "E_BACKEND_HOST_LINK_UNREALIZABLE" (Just "kappa-hs.backend.host-link")
      "A native binding requires a link or load mode the selected backend profile cannot realize (Spec §34.5.3, §36.28)."
  , ent "E_DUPLICATE_DECLARATION" (Just "kappa-hs.name.duplicate")
      "Two top-level declarations of the same kind in the same module bind the same name."
  , ent "E_DUPLICATE_PATTERN_BINDER" (Just "kappa-hs.pattern.duplicate-binder")
      "The same variable is bound more than once within a single pattern."
  , ent "E_EMPTY_BACKTICK_IDENT" Nothing
      "A backtick-quoted identifier is empty; backtick identifiers must contain at least one character."
  , ent "E_EXISTENTIAL_WITNESS_ESCAPE" (Just "kappa-hs.exists.escape")
      "An existential witness opened by 'open ... as exists ...' escapes in the result type of the open body (§13.2.11)."
  , ent "E_EXPLICIT_IMPLICIT_CLASSIFIER_MISMATCH" (Just "kappa.application.explicit-implicit-classifier")
      "An explicit implicit argument '@payload' cannot be elaborated against the selected implicit binder's demanded type or classifier (§16.1.7.2)."
  , ent "E_FEATURE_INACTIVE" (Just "kappa.feature.gated")
      "An identifier uses Unicode characters outside the active name profile without the corresponding feature gate enabled."
  , ent "E_HOLE_UNSOLVED" (Just "kappa.hole.unsolved")
      "A typed hole '?' or '_' in expression position was not solved by elaboration; the expected type or value remains unknown."
  , ent "E_IF_MISSING_ELSE" (Just "kappa-hs.control.if-missing-else")
      "An 'if' expression used for its value lacks an 'else' branch, so not all paths produce a result."
  , ent "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved")
      "An implicit argument (instance or value) could not be solved from the context at this application."
  , ent "E_IMPOSSIBLE_REACHABLE" (Just "kappa.pattern.unreachable")
      "A match arm marked 'impossible' is actually reachable: the scrutinee type does not rule the pattern out."
  , ent "E_INDEXED_IMPOSSIBLE_REACHABLE" (Just "kappa.proof.impossible-reachable")
      "An 'impossible' arm on an indexed family is reachable because the index constraints do not make the constructor uninhabited."
  , ent "E_INSTANCE_HEAD" (Just "kappa-hs.trait.bad-instance-head")
      "A trait instance declaration has a malformed head: the target is not a trait applied to well-formed type arguments."
  , ent "E_INSTANCE_INCOHERENT" (Just "kappa-hs.trait.incoherent")
      "Two visible instances of the same trait overlap for the same type, so instance resolution is incoherent."
  , ent "E_INSTANCE_MEMBER_MISSING" (Just "kappa-hs.trait.member-missing")
      "A trait instance does not define a required member that has no default in the trait declaration."
  , ent "KAPPA_DERIVING_SHAPE_NOT_DATA" (Just "kappa.deriving.shape")
      "A §22 derivation-shape reflection action ('inspectAdt' and relatives) was applied to a type that is not a data declaration."
  , ent "KAPPA_DERIVING_SHAPE_NOT_CLOSED_RECORD" (Just "kappa.deriving.shape")
      "A §22 record-shape reflection action requires a closed record type, but the subject type is not one."
  , ent "KAPPA_DERIVING_SHAPE_OPAQUE_REPRESENTATION" (Just "kappa.deriving.shape")
      "A §22 shape-reflection action attempted to inspect an 'opaque data' representation outside its defining module (§22.1)."
  , ent "KAPPA_DERIVING_SHAPE_MISSING_RUNTIME_FIELD_INSTANCE" (Just "kappa.deriving.shape")
      "A §22.4 field-constraint reflection action found a field with no instance satisfying the required runtime trait obligation."
  , ent "E_INTERNAL" Nothing
      "Internal compiler invariant violation. This is an implementation bug, not an error in the source program."
  , ent "E_LABEL_UNRESOLVED" (Just "kappa-hs.do.label-unresolved")
      "A labeled 'break' or 'continue' names a loop label that is not in scope."
  , ent "E_LAYOUT_BAD_DEDENT" Nothing
      "A line dedents to an indentation column that does not match any enclosing layout context."
  , ent "E_PATTERN_NON_EXHAUSTIVE" (Just "kappa.pattern.non-exhaustive")
      "A match expression does not cover every possible constructor or literal of the scrutinee type."
  , ent "E_MULTILINE_STRING_BAD_INDENT" Nothing
      "A line inside a multiline string literal is indented less than the closing delimiter's indentation baseline."
  , ent "E_NAMED_ARG_DUPLICATE" (Just "kappa.constructor.arity")
      "The same named field is supplied more than once in one constructor application (§3.2; portable alias E_CONSTRUCTOR_ARITY_MISMATCH)."
  , ent "E_NAMED_ARG_MISSING" (Just "kappa.constructor.arity")
      "A named constructor application omits a required field that has no default (§10.1.1, §3.2; portable alias E_CONSTRUCTOR_ARITY_MISMATCH)."
  , ent "E_NAMED_ARG_UNKNOWN" (Just "kappa.constructor.arity")
      "A named field does not correspond to any parameter of the applied constructor (§3.2; portable alias E_CONSTRUCTOR_ARITY_MISMATCH)."
  , ent "E_NOT_A_TYPE" (Just "kappa.type.mismatch")
      "An expression used in type position does not denote a type (its type is not 'Type')."
  , ent "E_NUMERIC_LITERAL_DOMAIN_MISMATCH" (Just "kappa.type.literal-domain-mismatch")
      "A numeric literal cannot elaborate at the surrounding expected type because that type admits no integer/float literal domain (no FromInteger/FromFloat witness is available) (§3.2.3, §6.1.5)."
  , ent "E_NUMERIC_LITERAL_MALFORMED" Nothing
      "A numeric literal is lexically malformed (bad digits for its radix, misplaced separators, or an invalid exponent)."
  , ent "E_OPERATOR_NO_FIXITY" (Just "kappa-hs.fixity.unbound")
      "An infix operator is used without any fixity declaration in scope, so the expression cannot be grouped."
  , ent "E_OPERATOR_NON_ASSOCIATIVE" (Just "kappa-hs.fixity.non-associative")
      "Two non-associative ('infix') operators of the same precedence are chained without parentheses, so the expression has no grouping (§5.5.2)."
  , ent "E_OR_PATTERN_BINDER_MISMATCH" (Just "kappa-hs.pattern.or-bindings")
      "The alternatives of an or-pattern do not bind exactly the same variables at the same types."
  , ent "E_EXPECT_AMBIGUOUS" (Just "kappa-hs.expect.ambiguous")
      "More than one definition in the compilation unit satisfies a single 'expect' declaration (Spec 9.4)."
  , ent "E_EXPECT_UNSATISFIED" (Just "kappa-hs.expect.unsatisfied")
      "An 'expect' declaration names a required external declaration, but no definition, backend intrinsic, or imported artifact in the compilation unit satisfies it (Spec 9.4)."
  , ent "E_RECURSIVE_VALUE_CYCLE" (Just "kappa.termination.failure")
      "A value-level definition refers to itself without an intervening function abstraction, so its evaluation can never terminate."
  , ent "E_DATA_NOT_STRICTLY_POSITIVE" (Just "kappa.termination.failure")
      "A data declaration is not strictly positive: the defined type occurs in a negative position (left of an arrow), as an argument of a non-admissible type former, or as a non-positive parameter of an admissible one (Spec 10.4)."
  , ent "E_SIGNATURE_UNSATISFIED" (Just "kappa-hs.signature.unsatisfied")
      "A non-expect top-level term signature has no matching definition in the same source file (Spec 9.1)."
  , ent "E_UNEXPECTED_INDENTATION" (Just "kappa-hs.parse.error")
      "A top-level declaration begins at a deeper indentation level than the module's declaration level (Spec 5.4)."
  , ent "E_EXPECTED_SYNTAX_TOKEN" (Just "kappa-hs.parse.error")
      "The source text does not conform to the Kappa grammar at this position."
  , ent "E_PATTERN_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.pattern.constructor-arity")
      "A constructor pattern has the wrong number of argument subpatterns for the constructor's declaration."
  , ent "E_PATTERN_FIELD_UNKNOWN" (Just "kappa.pattern.constructor-arity")
      "A record or constructor pattern mentions a field that the matched type does not declare."
  , ent "E_RECORD_DUPLICATE_FIELD" (Just "kappa-hs.record.duplicate-field")
      "A record literal or record type repeats a field name."
  , ent "E_RECORD_PATCH_DUPLICATE_PATH" (Just "kappa-hs.record.patch-duplicate")
      "A record patch updates the same field path more than once."
  , ent "E_RECORD_PROJECTION_MISSING_FIELD" (Just "kappa.name.unresolved")
      "A field projection names a field that the record type does not contain."
  , ent "E_RECURSION_REQUIRES_SIGNATURE" (Just "kappa.type.missing-signature")
      "A recursive definition lacks a type signature; recursion requires a declared signature for checking."
  , ent "E_RECURSIVE_TYPE_ALIAS" (Just "kappa-hs.type.recursive-alias")
      "A type alias refers to itself; recursive type aliases are not admitted — use a data declaration."
  , ent "E_URL_IMPORT_UNPINNED_IN_PACKAGE_MODE" (Just "kappa.package.reproducibility")
      "A URL module import without a #sha256:/#ref: pin is not reproducible and is rejected in package mode."
  , ent "E_URL_IMPORT_UNSUPPORTED" (Just "kappa-hs.import.url")
      "A pinned URL module import names content this implementation cannot fetch; URL module fetching is not provided."
  , ent "E_URL_IMPORT_REF_PIN_REQUIRES_LOCK" (Just "kappa.package.reproducibility")
      "A ref:-pinned URL import requires the resolved digest to be recorded in a lockfile in package mode; no lockfile machinery exists here."
  , ent "E_STATIC_OBJECT_KIND_MISMATCH" (Just "kappa-hs.static-object.kind")
      "A kind-qualified name expression's selector does not agree with the named declaration's facet (e.g. 'trait' on a data type)."
  , ent "E_QTT_BORROW_ESCAPE" (Just "kappa.borrow.escape")
      "A closure or value capturing a borrowed binding (or a reified BorrowView) escapes the borrow's scope through the result."
  , ent "E_REFUTABLE_LET_PATTERN" (Just "kappa-hs.pattern.refutable-binding")
      "A 'let' binding uses a refutable pattern; only irrefutable patterns may appear in plain let bindings."
  , ent "E_SAFE_NAVIGATION_RECEIVER_NOT_OPTION" (Just "kappa.type.mismatch")
      "The receiver of a '?.' safe-navigation expression is not an Option value."
  , ent "E_SAFE_NAVIGATION_AMBIGUOUS" (Just "kappa.type.mismatch")
      "A safe-navigation '?.' chain has an ambiguous generic receiver, so the implicit Option threading cannot be decided."
  , ent "E_SIGNATURE_ARITY" (Just "kappa-hs.type.signature-arity")
      "A definition binds more parameters than its declared signature provides function arrows for."
  , ent "E_SPLICE_OUTSIDE_DO" Nothing
      "A splice expression appears outside the do-block context that would give it meaning."
  , ent "E_STRING_ESCAPE_INVALID" Nothing
      "A string or character literal contains an invalid escape sequence."
  , ent "E_TRAIT_SUPERTRAIT_UNSATISFIED" (Just "kappa-hs.trait.supertrait-unsatisfied")
      "An instance is declared for a trait whose supertrait constraint has no visible instance for the same type."
  , ent "E_TAB_IN_INDENTATION" Nothing
      "A horizontal tab appears in the indentation of a line; Kappa layout indentation must use spaces only."
  , ent "E_TAB_IN_SOURCE" Nothing
      "A horizontal tab appears in source text where the active source profile forbids it."
  , ent "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
      "The inferred type of an expression is not definitionally equal to (or coercible to) the expected type."
  , ent "E_UNEXPECTED_CHARACTER" Nothing
      "The lexer encountered a character that cannot begin any token."
  , ent "E_UNKNOWN_FIELD" (Just "kappa.name.unresolved")
      "A record expression mentions a field that the expected record type does not declare."
  , ent "E_UNRESOLVED_MEMBER" (Just "kappa.name.unresolved")
      "A member access names a member that the receiver's type, trait, or module does not provide."
  , ent "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
      "A name is not in scope: no declaration, import, or prelude binding provides it."
  , ent "E_UNSUPPORTED" Nothing
      "The construct is recognized but not supported by this implementation (outside the implemented portable profile)."
  , ent "E_UNTERMINATED_BACKTICK_IDENTIFIER" Nothing
      "A backtick-quoted identifier is missing its closing backtick on the same line."
  , ent "E_UNTERMINATED_BLOCK_COMMENT" Nothing
      "A block comment is not closed before the end of the file."
  , ent "E_UNTERMINATED_CHARACTER_LITERAL" Nothing
      "A single-quoted scalar literal is missing its closing quote."
  , ent "E_UNTERMINATED_INTERPOLATION" Nothing
      "A string interpolation '${' is not closed before the end of the literal."
  , ent "E_UNTERMINATED_STRING_LITERAL" Nothing
      "A string literal is missing its closing delimiter."
  , ent "E_VARIANT_AMBIGUOUS" (Just "kappa-hs.variant.ambiguous")
      "A bare variant constructor could match more than one variant member in the expected type; disambiguate with an annotation."
  , ent "E_VARIANT_ARM" Nothing
      "A variant match arm is malformed or does not correspond to a member of the matched variant row."
  , ent "E_VARIANT_DUPLICATE" (Just "kappa-hs.variant.duplicate-member")
      "A variant row declares the same member name more than once."
  , ent "E_VARIANT_MEMBER" (Just "kappa-hs.variant.unknown-member")
      "A variant expression or pattern names a member that the variant row does not declare."
  , ent "E_VARIANT_PATTERN" Nothing
      "A variant pattern is malformed for the matched variant type."
  , ent "W_TERMINATION_UNVERIFIED" (Just "kappa.termination.failure")
      "The termination checker could not verify that this recursive definition terminates; it is accepted unverified."
  , -- Active patterns (§17.6)
    ent "E_ACTIVE_PATTERN_LINEARITY_VIOLATION" (Just "kappa-hs.pattern.active")
      "An active pattern's matcher demands the scrutinee at a quantity its declared linearity does not permit (§17.6)."
  , ent "E_ACTIVE_PATTERN_MATCH_RESULT_NOT_ALLOWED_IN_PLAIN_LET_QUESTION" (Just "kappa-hs.pattern.active")
      "An active pattern returning MatchResult is used in a plain 'let?' binding; MatchResult-returning matchers are only available in full match positions (§17.6)."
  , ent "E_ACTIVE_PATTERN_MONADIC_RESULT" (Just "kappa-hs.pattern.active")
      "An active pattern's matcher returns a monadic/effectful result where a pure Option or MatchResult is required (§17.6)."
  , -- Staging and macros (§21, §23)
    ent "E_CODE_ESCAPE_OUTSIDE_QUOTE" (Just "kappa-hs.staging.escape")
      "A '.~' code escape appears outside any enclosing code quotation (§23.2)."
  , ent "E_ELAB_DO_FORM" (Just "kappa-hs.do.elab")
      "A do item form is not available inside an 'Elab' do block, or the block does not end with an expression of the block's Elab type (§21.9)."
  , ent "E_ELAB_PHASE" (Just "kappa-hs.macro.phase")
      "An object-phase runtime binding is captured by an elaboration-time splice; object-phase terms enter 'Elab' only through meta-phase carriers such as 'Syntax' (§21.9)."
  , ent "E_ELAB_STUCK" (Just "kappa.macro.failure")
      "An elaboration-time action could not be executed by the Elab evaluator (§21.9)."
  , ent "E_MACRO_FAILURE" (Just "kappa.macro.failure")
      "A macro signalled failure during elaboration-time expansion (§21.4)."
  , ent "W_MACRO_DIAGNOSTIC" (Just "kappa.macro.failure")
      "A macro emitted a user-defined warning diagnostic during expansion (§21.4)."
  , ent "E_QUOTE_SPLICE_ELAB" (Just "kappa.syntax.quotation")
      "A splice inside a quotation failed to elaborate to a syntax value (§21.2)."
  , ent "E_QUOTE_SPLICE_OUTSIDE_QUOTE" (Just "kappa.syntax.quotation")
      "A '$'-splice appears outside any enclosing quotation (§21.2)."
  , ent "E_QUOTE_SPLICE_TYPE" (Just "kappa.syntax.quotation")
      "A splice's payload does not have the syntax type its quotation position requires (§21.2)."
  , ent "E_SPLICE_REQUIRES_SYNTAX" (Just "kappa-hs.syntax.splice")
      "A top-level or expression splice's operand is not an elaboration-time 'Syntax' value (§21.2)."
  , ent "E_SYNTAX_SCOPE_ESCAPE" (Just "kappa-hs.syntax.scope-escape")
      "Spliced syntax refers to a binding that is not in scope at the splice site; hygienic expansion forbids the reference from escaping its scope (§21.3)."
  , -- Do blocks and control (§18)
    ent "E_DEFER_ABRUPT_CONTROL" (Just "kappa-hs.do.defer")
      "A deferred action returns, breaks, or continues out of itself; abrupt control flow may not escape a 'defer' (§18.7)."
  , ent "E_DO_EMPTY" (Just "kappa-hs.do.empty")
      "A do block has no items or does not end with an expression item (§18.2)."
  , -- Effects and handlers (§18.1)
    ent "E_EFFECT_LABEL_NOT_IN_ROW" (Just "kappa.effect.row-mismatch")
      "The handled computation's effect row does not contain the label being handled (§18.1.21)."
  , ent "E_EFFECT_OP_SIGNATURE" (Just "kappa-hs.effect.operation")
      "An effect operation's declared signature is malformed for its effect declaration (§9.3.1.1)."
  , ent "E_HANDLER_OP_MISSING" (Just "kappa-hs.effect.handler")
      "A handler does not provide a clause for one of the handled effect's operations (§18.1.21)."
  , ent "E_HANDLER_OP_UNKNOWN" (Just "kappa-hs.effect.handler")
      "A handler clause names an operation the handled effect does not declare (§18.1.21)."
  , ent "E_HANDLER_RETURN_DUPLICATE" (Just "kappa-hs.effect.handler")
      "A handler declares more than one 'return' clause (§18.1.21)."
  , ent "E_HANDLER_RETURN_MISSING" (Just "kappa-hs.effect.handler")
      "A handler that needs a 'return' clause does not declare one (§18.1.21)."
  , -- Implicits, imports, names, modules
    ent "E_IMPLICIT_AMBIGUOUS" (Just "kappa.implicit.ambiguous")
      "More than one candidate solves an implicit argument and no ordering rule prefers one (§16.3.3)."
  , ent "E_IMPORT_CYCLE" (Just "kappa-hs.import.cycle")
      "Module imports form a cycle; the module dependency graph must be acyclic (§8.2)."
  , ent "E_IMPORT_ITEM_NOT_FOUND" (Just "kappa.name.unresolved")
      "An import list names an item the imported module does not export (§8.2)."
  , ent "E_IMPORT_ITEM_MALFORMED" (Just "kappa-hs.parse.error")
      "An import item combines the constructor wildcard '(..)' with an 'as' alias; these may not be combined (§8.3.1)."
  , ent "E_OPERATOR_FIXITY_AMBIGUOUS" (Just "kappa.name.ambiguous")
      "A bare operator reference '(op)' has more than one callable fixity in scope and no expected type selects one (§5.5.1)."
  , ent "E_MODULE_ALIAS_TYPE_COLLISION" (Just "kappa.name.module-alias-collision")
      "A qualified name resolves through a module alias that shadows an unrelated type, constructor, or other declaration of the same spelling, and the alias collision is the primary repairable cause (§8.3.1A, §3.1.4)."
  , ent "E_MODULE_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
      "A module path segment does not derive a valid module name, or a module reference does not resolve (§8.1)."
  , ent "E_MODULE_PATH_MISMATCH" (Just "kappa-hs.module.path-mismatch")
      "A module's declared name does not match the file path it was loaded from (§8.1)."
  , ent "E_NAME_AMBIGUOUS" (Just "kappa.name.ambiguous")
      "A name resolves to more than one declaration with no disambiguating rule (§7.1)."
  , ent "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
      "A kind-qualified static-object reference does not resolve to a declaration of the named facet (§22.1)."
  , -- Prefixed literals (§6.3.4)
    ent "E_PREFIX_HANDLER_TYPE" (Just "kappa.macro.failure")
      "A literal prefix resolves to a term whose type is not a valid interpolated-literal handler (§6.3.4.3)."
  , ent "E_PREFIX_RUNTIME_HANDLER" (Just "kappa.macro.failure")
      "A literal prefix resolves to an object-phase runtime value; prefixed literals require an elaboration-time handler (§6.3.4.3)."
  , -- Patterns
    ent "E_PATTERN_HEAD_NOT_CONSTRUCTOR_OR_ACTIVE_PATTERN" (Just "kappa-hs.pattern.head")
      "The head of an application pattern is neither a data constructor nor an active pattern (§17.2)."
  , -- Projections (§9.1.1, §16.1.5, §30.2.2)
    ent "E_PROJECTION_ACCESSOR_CLAUSE_DUPLICATE" (Just "kappa-hs.projection.accessor")
      "An accessor-bundle projection declares the same accessor clause more than once (§9.1.1)."
  , ent "E_PROJECTION_CAPABILITY_REQUIRED" (Just "kappa-hs.projection.capability")
      "A projection use requires an accessor capability (read/write/zip) the projection does not provide (§30.2.2)."
  , ent "E_PROJECTION_DESCRIPTOR_ROOTS_LITERAL_REQUIRED" (Just "kappa-hs.projection.roots")
      "A projector descriptor application requires a literal roots record at the call site (§16.1.5)."
  , ent "E_PROJECTION_DESCRIPTOR_VALUE_EXPECTED" (Just "kappa-hs.projection.descriptor")
      "A value position expected a projector descriptor, but the expression does not denote one (§16.1.5)."
  , ent "E_PROJECTION_EXPANDED_ACCESSOR_PLACE_BINDER_MISMATCH" (Just "kappa-hs.projection.accessor")
      "An expanded accessor clause's place binders do not match the projection's declared place binders (§9.1.1)."
  , ent "E_PROJECTION_MISSING_PLACE_BINDER" (Just "kappa-hs.projection.place-binder")
      "A projection declaration has no receiver-marked 'place' binder (§9.1.1)."
  , ent "E_PROJECTION_ROOTS_PACK_MISMATCH" (Just "kappa-hs.projection.roots")
      "The roots record supplied to a projector descriptor does not match the projection's place binders (§16.1.5)."
  , ent "E_PROJECTION_ROOT_INVALID" (Just "kappa-hs.projection.roots")
      "A projection root argument is not a stable place expression (§16.1.5)."
  , ent "E_PROJECTION_UPDATE_TARGET_UNSUPPORTED" (Just "kappa-hs.projection.update")
      "A record patch updates through a projection that does not support write access at that target (§30.2.2.4)."
  , ent "E_PROJECTION_YIELD_INVALID" (Just "kappa-hs.projection.yield")
      "A selector-form projection body does not yield a place rooted at one of its place binders (§9.1.1)."
  , -- Quantities and borrows (§12.2–§12.4, §18.9.3)
    ent "E_QTT_BORROW_CONSUME" (Just "kappa.quantity.unsatisfied")
      "A borrowed binding is moved into a consuming (quantity 1 / >=1) parameter (§12.3.1)."
  , ent "E_QTT_BORROW_OVERLAP" (Just "kappa.borrow.overlap")
      "A place is consumed while a live borrow of an overlapping path exists, or one call both borrows and consumes overlapping places (§12.4)."
  , ent "E_QTT_CONTINUATION_CAPTURE" (Just "kappa-hs.qtt.continuation-capture")
      "A handler's continuation is used at a quantity its declared resumption quantity does not permit (§18.1.16)."
  , ent "E_QTT_ERASED_RUNTIME_USE" (Just "kappa.quantity.unsatisfied")
      "An erased (quantity 0) binding is used at runtime (§12.2.1)."
  , ent "E_QTT_INOUT_MARKER_REQUIRED" (Just "kappa-hs.qtt.inout-marker")
      "An argument flowing into an 'inout' parameter is not marked '~place' at the call site (§18.9.3)."
  , ent "E_QTT_INOUT_MARKER_UNEXPECTED" (Just "kappa-hs.qtt.inout-marker")
      "A call-site '~' marker is applied to an argument whose parameter is not declared 'inout' (§18.9.3)."
  , ent "E_QTT_INOUT_THREADED_FIELD_MISSING" (Just "kappa.inout.restoration")
      "An 'inout' parameter's place is not threaded back through the declared result as a field of the same name (§18.9.3)."
  , ent "E_QTT_LINEAR_DROP" (Just "kappa.quantity.positive-lower-bound")
      "A linear or relevant (quantity 1 / >=1) binding may complete unused on some path (§12.2.5)."
  , ent "E_QTT_LINEAR_OVERUSE" (Just "kappa.quantity.unsatisfied")
      "A linear or affine (quantity 1 / <=1) binding or field path is consumed more often than its quantity permits (§12.2)."
  , ent "E_QTT_PATH_CONSUMED" (Just "kappa.path.consumed")
      "A place is borrowed or re-projected after the path was already consumed at quantity 1, without an intervening restoring record update (§12.4, §3.2.6)."
  , ent "E_QTT_USING_EXPLICIT_QUANTITY" (Just "kappa-hs.qtt.using-quantity")
      "A 'using' binding declares an explicit quantity; using-scoped resources have a fixed discipline (§19.5)."
  , -- Queries (§20)
    ent "E_QUERY_CARDINALITY_MISMATCH" (Just "kappa-hs.query.cardinality")
      "A comprehension's declared cardinality does not match what its pipeline can produce (§20.4)."
  , ent "E_QUERY_FOR_REFUTABLE" (Just "kappa-hs.query.refutable-for")
      "A 'for' generator pattern is refutable; only irrefutable patterns may bind rows (§20.2)."
  , ent "E_QUERY_GROUP_KEY_FIELD" (Just "kappa-hs.query.group")
      "A 'group by' key expression does not project a field usable as the group key (§20.6)."
  , ent "E_QUERY_ITEM_QUANTITY_MISMATCH" (Just "kappa-hs.query.item-quantity")
      "A comprehension clause uses a row at a quantity the row binder's discipline does not permit (§20.10.5)."
  , ent "E_QUERY_LEFT_JOIN_LINEAR_CAPTURE" (Just "kappa-hs.query.left-join")
      "A left join 'into' group captures a linear row; absent rows cannot satisfy the row's quantity (§20.5)."
  , ent "E_QUERY_METADATA_LOSS" (Just "kappa-hs.query.sink")
      "A comprehension sink discards collection metadata (keying or ordering) that the source guarantees (§20.9)."
  , ent "E_QUERY_MODE_MISMATCH" (Just "kappa-hs.query.mode")
      "A comprehension clause is not available in this comprehension mode (§20.1)."
  , ent "E_QUERY_ORDER_KEY_CONSUMES" (Just "kappa-hs.query.order-key")
      "An 'order by' key expression consumes the row; ordering keys must be non-consuming reads (§20.3.2)."
  , ent "E_QUERY_ROW_NOT_DROPPABLE" (Just "kappa.quantity.unsatisfied")
      "A filtering clause may drop a row whose quantity forbids dropping (§20.10.5)."
  , ent "E_QUERY_ROW_NOT_DUPLICABLE" (Just "kappa.quantity.unsatisfied")
      "A clause duplicates a row whose quantity forbids duplication (§20.10.5)."
  , ent "E_QUERY_UNORDERED_PAGING" (Just "kappa.query.orderedness")
      "'skip'/'take' paging is applied to an unordered pipeline (§20.3.3)."
  , ent "E_SINK_ITEM_MISMATCH" (Just "kappa-hs.query.sink")
      "A comprehension's yield item type does not match the sink collection's element shape (§20.9)."
  , -- Records, rows, seals (§11.3.1A, §13.2)
    ent "E_RECORD_DEPENDENCY_CYCLE" (Just "kappa-hs.record.dependency-cycle")
      "A dependent record type's 'this' field references form a cycle (§13.2.1)."
  , ent "E_RECORD_DEPENDENCY_INVALID" (Just "kappa-hs.record.dependency-invalid")
      "A dependent record field's type mentions a sibling in a form the telescope rules do not admit (§13.2.1)."
  , ent "E_RECORD_PATCH_INVALID_ITEM" (Just "kappa-hs.record.patch-invalid")
      "A record patch item form is not admitted (e.g. punning inside '.{ }', §13.2.5)."
  , ent "E_RECORD_PATCH_PREFIX_CONFLICT" (Just "kappa-hs.record.patch-prefix-conflict")
      "Two record patch paths overlap: one is a prefix of the other (§13.2.5)."
  , ent "E_RECORD_PATCH_UNKNOWN_PATH" (Just "kappa.name.unresolved")
      "A record patch path names a field the record type does not contain (§13.2.5)."
  , ent "E_ROW_EXTENSION_DUPLICATE_LABEL" (Just "kappa-hs.row.extension-duplicate")
      "A row extension ':=' introduces the same label more than once (§13.2.6)."
  , ent "E_ROW_EXTENSION_EXISTING_FIELD" (Just "kappa.row.lacks-failed")
      "A row extension ':=' introduces a label the record already has; use an update '=' instead (§13.2.6)."
  , ent "E_ROW_EXTENSION_MISSING_LACKS_CONSTRAINT" (Just "kappa.row.lacks-failed")
      "Extending an open record row with a label requires a 'LacksRec r label' constraint in scope (§11.3.1A, §13.2.6)."
  , ent "E_ROW_TAIL_QUANTITY_UNSATISFIED" (Just "kappa.row.tail-quantity")
      "An abstract residual row tail must satisfy a structural quantity demand (e.g. it is dropped by a consuming open-record receiver) but the required 'RecTailSatisfies r q' evidence is unavailable (§3.2.4, §13.2.7)."
  , ent "E_SEAL_DIRECT_LITERAL_FOR_SIGNATURE" (Just "kappa-hs.seal.direct-literal")
      "A record literal directly introduces a signature type with opaque members; use 'seal ... as ...' (§13.2.10)."
  , ent "E_SEAL_OPAQUE_UNFOLDING" (Just "kappa-hs.seal.opaque-unfolding")
      "An opaque member of a sealed signature is unfolded outside the seal (§13.2.10)."
  , ent "E_SEAL_OPEN_RECORD_ASCRIPTION" (Just "kappa-hs.seal.open-record")
      "'seal ... as ...' ascribes an open record row; sealing requires a closed signature type (§13.2.10)."
  , -- §3.1.2A portable alias spellings. The registry MUST include all
    -- portable aliases required by the specification; each resolves to
    -- the same explanation as its rendered code.
    ent "E_TYPE_MISMATCH" (Just "kappa.type.mismatch")
      "Portable alias (§3.1.2A) of E_TYPE_EQUALITY_MISMATCH: the inferred type of an expression does not fit the expected type."
  , ent "E_SAFE_NAV_GENERIC_AMBIGUOUS" (Just "kappa.type.mismatch")
      "Portable alias (§3.1.2A) of E_SAFE_NAVIGATION_AMBIGUOUS: a safe-navigation '?.' chain has an ambiguous generic receiver."
  , ent "E_APPLICATION_NON_CALLABLE" (Just "kappa-hs.application.non-callable")
      "Portable alias (§3.1.2A) of E_APPLICATION_NONCALLABLE: the head of an application is not a function or callable value."
  , ent "E_MISSING_EXPLICIT_SIGNATURE" (Just "kappa.type.missing-signature")
      "Portable alias (§3.1.2A) of E_RECURSION_REQUIRES_SIGNATURE: a recursive definition requires a declared type signature."
  , -- §3.1.3 standard Unicode diagnostic codes. The specification fixes
    -- these spellings and meanings for every conforming implementation;
    -- they are registered here with their normative explanations.
    ent "E_UNICODE_INVALID_SCALAR_LITERAL" (Just "kappa-hs.unicode.invalid-scalar-literal")
      "A single-quoted Unicode scalar literal decodes to zero scalar values, more than one scalar value, a surrogate code point, or an out-of-range code point (§3.1.3)."
  , ent "E_UNICODE_INVALID_GRAPHEME_LITERAL" (Just "kappa-hs.unicode.invalid-grapheme-literal")
      "A g-prefixed quoted literal contains zero extended grapheme clusters or more than one extended grapheme cluster (§3.1.3)."
  , ent "E_UNICODE_INVALID_BYTE_LITERAL" (Just "kappa-hs.unicode.invalid-byte-literal")
      "A b-prefixed quoted literal contains zero bytes or more than one byte (§3.1.3)."
  , ent "E_UNICODE_INVALID_UTF8" (Just "kappa-hs.unicode.invalid-utf8")
      "A source form or checked conversion requires valid UTF-8 but received invalid bytes (§3.1.3)."
  , ent "E_UNICODE_NAME_PROFILE_VIOLATION" (Just "kappa.unicode.name")
      "An identifier, operator, literal prefix, suffix, alias, or export name violates the active Unicode name profile (§3.1.3)."
  , ent "E_UNICODE_NAME_NON_NORMALIZED" (Just "kappa.unicode.name")
      "An unquoted Unicode identifier or operator token is not in the normalization form required by the active Unicode name profile (§3.1.3)."
  , ent "E_UNICODE_VISUAL_DUPLICATE_BINDING" (Just "kappa.unicode.name")
      "Two declarations in the same scope and declaration kind have distinct spellings but the same strong visual name key (§3.1.3, §5.1A)."
  , ent "W_UNICODE_CONFUSABLE_IDENTIFIER" (Just "kappa.unicode.name")
      "A name is visually confusable with another visible name under the active diagnostic skeleton policy (§3.1.3)."
  , ent "W_UNICODE_VISUAL_ALIAS_REFERENCE" (Just "kappa.unicode.name")
      "A reference resolved by strong visual name key rather than by exact strict name key (§3.1.3, §7.1)."
  , ent "W_UNICODE_MIXED_SCRIPT_IDENTIFIER" (Just "kappa.unicode.name")
      "A single identifier or operator name mixes scripts in a way prohibited or discouraged by the active Unicode name profile (§3.1.3)."
  , ent "W_UNICODE_MIXED_NUMBER_IDENTIFIER" (Just "kappa.unicode.name")
      "A name mixes decimal digits from different numbering systems or visually confusable number-like code points (§3.1.3)."
  , ent "W_UNICODE_NON_NORMALIZED_SOURCE_TEXT" (Just "kappa-hs.unicode.non-normalized-text")
      "A source file contains non-normalized text in comments, strings, or other positions not governed by E_UNICODE_NAME_NON_NORMALIZED (§3.1.3)."
  , ent "W_UNICODE_BIDI_CONTROL" (Just "kappa-hs.unicode.bidi-control")
      "Source text contains bidirectional control characters outside string literals or prefixed quoted literals (§3.1.3)."
  , -- CLI-level code (kappa run without a main definition)
    ent "E_NO_MAIN" Nothing
      "The module given to 'kappa run' does not define a 'main' entrypoint."
  , -- §27.7 native backend (profile-scoped) diagnostics
    ent "E_BACKEND_UNSUPPORTED" (Just "kappa-hs.backend.unsupported")
      "A reachable definition uses a construct or primitive the native backend does not support; it is rejected at build time rather than silently diverging from the interpreter (§27.7)."
  , ent "E_BACKEND_TOOLCHAIN" (Just "kappa-hs.backend.toolchain")
      "The native backend could not locate its runtime or a C toolchain, or the C toolchain failed while compiling or linking the generated program (§27.1)."
  , ent "E_BACKEND_INTRINSIC_SIGNATURE_MISMATCH" (Just "kappa-hs.backend.intrinsic")
      "An 'expect term' whose name matches a native backend host-binding intrinsic declares a type that does not match the intrinsic's signature up to definitional equality (Spec §9.4, §34.5)."
  ]
  where
    -- §3.1.2A registry metadata is derived uniformly from the code and
    -- family rather than restated per entry:
    --   * defaultSeverity follows the code prefix (E_→error, W_→warning,
    --     I_→info), the §3.1.2 readable-symbolic-form convention;
    --   * stability is 'stable' for the public diagnostic surface
    --     (every code here is emitted in ordinary compilation, §3.1.2A);
    --   * owner is the family-namespace owner — the specification for a
    --     reserved @kappa.@ family, otherwise this implementation;
    --   * portableAliases are read from 'requiredAliasTable' so the
    --     registry and the alias table cannot drift (§3.1.4);
    --   * introducedIn is the implementation version (single release).
    ent c f x =
      ExplainEntry
        { eeCode = c
        , eeFamily = f
        , eeExplanation = x
        , eeDefaultSeverity = sevOf c
        , eeStability = Stable
        , eePortableAliases = aliasesOf c
        , eeOwner = ownerOf f
        , eeIntroducedIn = "kappa-haskell 0.1.0.0"
        }
    sevOf c
      | "W_" `T.isPrefixOf` c = SevWarning
      | "I_" `T.isPrefixOf` c = SevInfo
      | otherwise = SevError
    ownerOf = \case
      Just fam
        | "kappa." `T.isPrefixOf` fam -> "kappa-specification"
      _ -> "kappa-haskell"
    -- the rendered codes for which this code is the §3.1.4 portable
    -- alias target (the inverse of 'portableAlias')
    aliasesOf c = nub [rendered | (rendered, target) <- requiredAliasTable, target == c]
