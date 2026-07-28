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
import Kappa.Diagnostic (Severity (..), portableAlias, requiredAliasTable)

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
      "A manifest native binding provides a module not under the host.native root, or declares no symbol surface; the selected backend profile cannot realize it (Spec §27.1.1, §34.5.3, §36.28)."
  , ent "E_BUILD_FRAGMENT_AXIS_CONFLICT" (Just "kappa-hs.build.fragment-axis")
      "A build target, or a selected source fragment, uses more than one tag from the same exclusive fragment axis (Spec §36.12)."
  , ent "E_BUILD_NATIVE_ABI" (Just "kappa-hs.build.native-abi")
      "Build-phase native ABI discovery/verification failed: a pkg-config package was missing or older than the manifest's minVersion, a declared header was not on the resolved include path, or a 'verify' C declaration disagreed with the real header's declaration (Spec §26.1.5, §27.1.1, §36.28)."
  , ent "E_BUILD_NATIVE_HEADER_GEN" (Just "kappa-hs.build.native-header-gen")
      "Mechanical native-surface generation from a header failed: the header could not be preprocessed, a requested function was not declared in it, or one of the function's C types has no conservative std.ffi correspondence (a by-value struct/enum or a callback parameter) (Spec §27.1.1, §36.28)."
  , ent "E_BUILD_BINDING_NOT_FOUND" (Just "kappa-hs.build.binding-not-found")
      "A build target references a host-binding name that the manifest's hostBindings does not declare (Spec §36.3, §36.28)."
  , ent "E_BUILD_ENTRY_NOT_FOUND" (Just "kappa-hs.build.entry-not-found")
      "A build target's entry (main) module could not be located as a source file under the package's source roots (Spec §36.3, §36.4)."
  , ent "E_BUILD_TARGET_CYCLE" (Just "kappa-hs.build.target-cycle")
      "An aggregate build target (transitively) includes itself; aggregate target membership must be acyclic (Spec §36.3)."
  , ent "E_MODULE_NAME_CASE_COLLISION" (Just "kappa-hs.module.case-collision")
      "Two source files in a compilation unit derive module names that are equal after case-folding but differ in case (Spec §8.1)."
  , ent "E_DEPENDENCY_NOT_FOUND" (Just "kappa-hs.build.dependency-not-found")
      "A build target lists a dependency name the manifest's dependencies do not declare (Spec §36.3, §36.23)."
  , ent "E_DEPENDENCY_PATH_NOT_FOUND" (Just "kappa-hs.build.dependency-path")
      "A path dependency points to a directory that does not contain a build manifest (Spec §36.23, §36.23.2)."
  , ent "E_DEPENDENCY_UNRESOLVED" (Just "kappa.package.reproducibility")
      "A dependency cannot be resolved by the selected resolver profile: this implementation resolves path, git, vendored-registry (a local KAPPA_REGISTRY root), and url (archive) dependencies; a networked-registry server/protocol and artifact (target-output) dependencies are not provided (Spec §36.23, §36.23.1)."
  , ent "E_DEPENDENCY_MODULE_COLLISION" (Just "kappa-hs.build.dependency-module-collision")
      "More than one package in the build (the target's own package and/or its dependencies) provides the same module name; cross-package module names must be distinct (Spec §8.1, §36.23)."
  , ent "E_DEPENDENCY_LOCK_MISMATCH" (Just "kappa.package.reproducibility")
      "A locked build's resolved path-dependency content identities do not match kappa.lock (a dependency changed, or the lock is missing/stale); the build is not reproducible against the lock (Spec §36.4, §36.23.2, §3.2.15)."
  , ent "E_DEPENDENCY_GIT_FAILED" (Just "kappa-hs.build.dependency-git")
      "A git dependency could not be resolved: git is unavailable, or a clone/checkout/rev-parse of the requested URL and revision failed (Spec §36.23)."
  , ent "E_DEPENDENCY_REGISTRY_NOT_FOUND" (Just "kappa-hs.build.dependency-registry")
      "A registry dependency names a package not present in the configured registry root (Spec §36.23, §36.23.1)."
  , ent "E_DEPENDENCY_VERSION_UNSATISFIED" (Just "kappa-hs.build.dependency-version")
      "No version of a registry dependency available in the configured registry satisfies the requested version constraint (Spec §36.23)."
  , ent "E_DEPENDENCY_URL_FAILED" (Just "kappa-hs.build.dependency-url")
      "A url dependency could not be resolved: curl/tar is unavailable, or the archive could not be fetched, unpacked, or did not contain a build manifest (Spec §36.23)."
  , ent "E_BACKEND_HOST_LINK_UNREALIZABLE" (Just "kappa-hs.backend.host-link")
      "A native binding requires a link or load mode the selected backend profile cannot realize (Spec §34.5.3, §36.28)."
  , ent "E_BACKEND_PROFILE_UNREALIZED" (Just "kappa-hs.backend.profile")
      "A build target selects a backend profile (jvm/dotnet) this implementation does not provide; only the native profile is realized (Spec §34.5.3, §36.4)."
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
  , ent "E_FEATURE_BACKEND_CAPABILITY_MISSING" (Just "kappa.feature.gated")
      "A reachable multi-shot effect resumption requires the 'rt-multishot-effects' runtime capability, which no targeted backend advertises; the multi-shot operation is rejected at compile time rather than executed with one-shot semantics (§18.1.17, §27.6, §34.3.3)."
  , ent "E_HOLE_UNSOLVED" (Just "kappa.hole.unsolved")
      "A typed hole '?' or '_' in expression position was not solved by elaboration; the expected type or value remains unknown."
  , ent "E_HOLE_INCONSISTENT_EXPECTED_TYPE" (Just "kappa.hole.inconsistent")
      "Repeated occurrences of the same named hole '?name' received expected types that are not definitionally equal, so the hole cannot denote one unknown (§16.3.2)."
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
  , ent "E_ASSOCIATED_MEMBER_UNDECLARED" (Just "kappa.associated.member-undeclared")
      "An instance body defines a member name that the governing trait does not declare; an associated static member must first be declared in the trait body (§14.3.4)."
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
  , ent "E_INTERNAL_REFL_GOAL" Nothing
      "The equality prover requested a reflexivity witness for a goal that is not a canonical equality application. This is an implementation bug, not an error in the source program."
  , ent "E_INTERNAL_BUILTIN_MISSING" (Just "kappa-hs.internal.builtin-missing")
      "The bundled prelude does not define a name the compiler wires in (see Kappa.Builtins). This is an implementation bug — a drift between the compiler and its prelude — not an error in the source program."
  , ent "E_INTERNAL_CTOR_TAG" (Just "kappa-hs.internal.ctor-tag")
      "The runtime-pinned constructor tag table (Kappa.Builtins.runtimeCtors) is internally inconsistent — its ids are not contiguous, or one is not below KCT_USER_BASE. This is an implementation bug — a drift between the compiler and the runtime tag enum — not an error in the source program."
  , ent "E_INTERNAL_PRIM_REGISTRY" (Just "kappa-hs.internal.prim-registry")
      "The native backend's primitive registry names a primitive the runtime-implemented set does not list. This is an implementation bug — a drift between the prim tables and the runtime — not an error in the source program."
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
  , ent "E_INSTANCE_SEARCH_NONTERMINATING" (Just "kappa.termination.failure")
      "An instance declaration's context violates the Paterson-style termination conditions: a premise is not structurally smaller than the head, or uses some type variable more often than the head, so instance resolution may not terminate (Spec 14.3.5)."
  , ent "E_SIGNATURE_UNSATISFIED" (Just "kappa-hs.signature.unsatisfied")
      "A non-expect top-level term signature has no matching definition in the same source file (Spec 9.1)."
  , ent "E_UNEXPECTED_INDENTATION" (Just "kappa-hs.parse.error")
      "A top-level declaration begins at a deeper indentation level than the module's declaration level (Spec 5.4)."
  , ent "E_EXPECTED_SYNTAX_TOKEN" (Just "kappa-hs.parse.error")
      "The source text does not conform to the Kappa grammar at this position."
  , -- §3.1.4: distinct from E_EXPECTED_SYNTAX_TOKEN so the portable alias
    -- E_RECOVERY_SKIPPED_INVALID_SYNTAX applies only to the declaration-skip
    -- recovery, not to generic expected-token errors (requiredAliasTable).
    ent "E_RECOVERY_DECLARATION_SKIPPED" (Just "kappa-hs.parse.error")
      "Declaration-level recovery skipped an invalid top-level declaration region to resynchronize at the next declaration (Spec 3.1.14A; portable alias E_RECOVERY_SKIPPED_INVALID_SYNTAX)."
  , -- §3.1.4 portable alias itself (no §3.2 family is mandated for parser
    -- recovery, so it shares the implementation parse-error family). Its
    -- portableAliases are derived from 'requiredAliasTable', so the harness
    -- accepts the portable spelling and recovers the impl code consistently.
    ent "E_RECOVERY_SKIPPED_INVALID_SYNTAX" (Just "kappa-hs.parse.error")
      "Parser recovery skipped invalid source text to resynchronize (Spec 3.1.4 portable diagnostic-code alias E_RECOVERY_SKIPPED_INVALID_SYNTAX)."
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
  , ent "E_CAPTURE_SET_MISMATCH" (Just "kappa.capture.mismatch")
      "A value's inferred hidden region environment is not contained in the demanded capture annotation (§3.2.7, §12.3.1)."
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
  , ent "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" (Just "kappa.universe.constraint")
      "A generated universe-level ordering constraint is unsatisfiable under the lexically scoped level assumptions (§11.1.2.1-§11.1.2.2)."
  , ent "E_UNIVERSE_SELF_CONTAINMENT" (Just "kappa.universe.constraint")
      "Universe checking would require a level to contain its own successor, violating predicativity (§11.1.2)."
  , ent "E_UNIVERSE_LEVEL_EXPRESSION" (Just "kappa.universe.level-expression")
      "A Type index does not normalize through compiler-owned TypeLevel operations to the canonical level grammar (§11.1.1)."
  , ent "E_UNIVERSE_SCHEMA_ARITY_MISMATCH" (Just "kappa.universe.schema-arity")
      "An explicit declaration-universe instantiation supplies a different number of levels than the declaration schema requires (§11.1.2.3A.1)."
  , ent "E_UNIVERSE_SCHEMA_SCOPE" (Just "kappa.universe.schema-scope")
      "A declaration-universe parameter is used outside a static universe-level position (§11.1.2.3A.1)."
  , ent "E_UNIVERSE_VARIANCE_TOO_PERMISSIVE" (Just "kappa.universe.variance")
      "An explicit nominal declaration-universe role is more permissive than the independently inferred role (§11.1.2.3A.2)."
  , ent "E_UNIVERSE_VARIANCE_NOT_APPLICABLE" (Just "kappa.universe.variance")
      "A declaration-universe role is written on a declaration that does not introduce a nominal signature block (§11.1.2.3A.2)."
  , ent "E_UNIVERSE_SCHEMA_LIFT_INVALID" (Just "kappa.universe.schema-lift")
      "A cumulative nominal-family use fails saturation, role, constraint, argument-alignment, or certificate verification (§30.2.1B)."
  , ent "E_UNIVERSE_NO_PRINCIPAL_SOLUTION" (Just "kappa.universe.no-principal-solution")
      "Declaration-universe inference has no unique least solution independent of traversal order (§11.1.2.4A)."
  , ent "E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION" (Just "kappa.universe.inference-requires-annotation")
      "A minimizable universe metavariable lies outside the portable principal-inference fragment and requires an explicit annotation or schema."
  , ent "E_UNIVERSE_RECURSIVE_SCHEMA_INCREASE" (Just "kappa.universe.recursive-schema")
      "A recursive declaration-schema call requests a universe instance that is not proved less than or equal to the caller's current instance."
  , ent "E_UNIVERSE_RECURSIVE_SCHEMA_IMPLICIT" (Just "kappa.universe.recursive-schema")
      "A recursive declaration-schema call changes universe instance without an explicit universe instantiation and a complete recursive signature."
  , ent "E_GENERALIZATION_PARAMETRIC_ESCAPE" (Just "kappa.generalization.parametric-escape")
      "A proposed declaration-level parametric generalization would be observed in an ordinary position."
  , ent "E_UNIVERSE_UNBOUNDED_TELESCOPE" (Just "kappa.universe.unbounded-telescope")
      "A dependent type former has no universe ceiling well-formed outside its own telescope (§11.1.2.8)."
  , ent "E_DATA_CONSTRUCTOR_FIELD_UNIVERSE" (Just "kappa.universe.constructor-size")
      "A constructor-local non-parametric binder exceeds the universe declared by its data family (§10.4.1)."
  , ent "E_PARAMETRIC_TYPE_PROMOTION" (Just "kappa.type.parametric-promotion")
      "A parametric type witness is used where an ordinary inspectable type-code value is required (§11.1.2.3A)."
  , ent "E_PROOF_RELEVANT_TRANSPORT_NOT_LOWERABLE" (Just "kappa.equality.transport-not-lowerable")
      "A runtime-relevant equality transport has no verified computational lowering rule (§11.4.1)."
  , ent "E_KCORE_TEXT_INVALID" (Just "kappa.kcore.text-invalid")
      "A KCoreText artifact is malformed or fails ordinary KCore checkpoint verification."
  , ent "E_KCORE_TEXT_UNSUPPORTED_VERSION" (Just "kappa.kcore.unsupported-version")
      "A KCoreText artifact declares a well-formed schema version that this compiler does not support."
  , ent "E_KCORE_LEVEL_CERTIFICATE_INVALID" (Just "kappa.kcore.level-certificate-invalid")
      "A KCoreText level certificate is malformed, out of scope, or does not prove its claimed universe relation."
  , ent "E_KCORE_ARITHMETIC_CERTIFICATE_INVALID" (Just "kappa.kcore.arithmetic-certificate-invalid")
      "A KCoreText arithmetic certificate is malformed, out of scope, or does not prove its claimed arithmetic relation."
  , ent "E_KCORE_SCHEMA_CERTIFICATE_INVALID" (Just "kappa.kcore.schema-certificate-invalid")
      "A KCoreText nominal action certificate is missing, stale, forged, unsupported, or fails independent replay (§30.2.1B)."
  , ent "E_UNSOLVED_METAVARIABLE" (Just "kappa.type.unsolved-metavariable")
      "A type or universe metavariable remained observable without a principal solution at its elaboration boundary (§11.1.3)."
  , ent "E_TERMINATION_INVALID_STRUCTURAL_TARGET" (Just "kappa.termination.invalid_structural_target")
      "A 'decreases structural' certificate names something that is not an explicit parameter of the recursive definition."
  , ent "E_UNEXPECTED_CHARACTER" Nothing
      "The lexer encountered a character that cannot begin any token."
  , ent "E_UNKNOWN_FIELD" (Just "kappa.name.unresolved")
      "A record expression mentions a field that the expected record type does not declare."
  , ent "E_UNRESOLVED_MEMBER" (Just "kappa.name.unresolved")
      "A member access names a member that the receiver's type, trait, or module does not provide."
  , ent "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
      "A name is not in scope: no declaration, import, or prelude binding provides it."
  , ent "E_UNSAFE_INTRINSIC_GATED" (Just "kappa.feature.gated")
      "Ordinary user code named a raw-admit proof intrinsic (such as '__eqProof', '__transport', '__absurd', or '__handleEff'). These prelude primitives inhabit an arbitrary proposition from nothing, so naming one outside the prelude would forge false proofs and break logical soundness. Use the checked proof helpers, or mark the module '@AllowUnsafeIntrinsics' to opt in (§4.5)."
  , ent "E_UNSUPPORTED" (Just "kappa.unsupported.deterministic")
      "The construct is recognized but not supported by this implementation (outside the implemented portable profile). Portable alias: E_UNSUPPORTED_DETERMINISTIC (§2.1, §3.3)."
  , ent "E_UNSUPPORTED_DETERMINISTIC" (Just "kappa.unsupported.deterministic")
      "The §3.1.4/§3.3 portable alias for a deterministic 'unsupported' result (a feature/query/backend/mode not implemented or not supported by the selected profile); this implementation's records spell it E_UNSUPPORTED with this alias exposed as portableCode."
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
  , ent "E_LOCAL_NOMINAL_SCOPE_ESCAPE" (Just "kappa-hs.local-nominal.scope-escape")
      "A block result transparently exposes a scoped local nominal family or its hidden nominal-scope token outside the lexical declaration scope (§9.3.1.1, §30.1.1)."
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
  , ent "E_EFFECT_LABEL_FORM" (Just "kappa-hs.effect.label")
      "An 'effect label l : E' declaration is malformed — E must be a named top-level effect (§18.1.15)."
  , ent "E_HANDLER_OP_ARITY" (Just "kappa-hs.effect.handler")
      "A handler operation clause binds a different number of arguments than the operation declares (§18.1.21)."
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
  , ent "E_MODULE_ATTRIBUTE_CONFLICT" (Just "kappa-hs.module.attribute-conflict")
      "Fragments of one effective module specify incompatible module-wide attributes (§8.1, §28.1)."
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
  , ent "E_QTT_INOUT_BINDER_CONTEXT" (Just "kappa-hs.qtt.inout-marker")
      "An 'inout' binder appears outside a named callable parameter context where §18.9.2 permits it."
  , ent "E_QTT_INOUT_RESIDUAL_PATTERN" (Just "kappa.inout.restoration")
      "An inout call residual pattern binds a threaded place result or is not a supported restoration record pattern (§18.9.4)."
  , ent "E_QTT_INOUT_THREADED_FIELD_MISSING" (Just "kappa.inout.restoration")
      "An 'inout' parameter's place is not threaded back through the declared result as a field of the same name (§18.9.3)."
  , ent "E_QTT_LINEAR_DROP" (Just "kappa.quantity.positive-lower-bound")
      "A linear or relevant (quantity 1 / >=1) binding may complete unused on some path (§12.2.5)."
  , ent "E_QTT_LINEAR_OVERUSE" (Just "kappa.quantity.unsatisfied")
      "A linear or affine (quantity 1 / <=1) binding or field path is consumed more often than its quantity permits (§12.2)."
  , ent "E_QTT_QUANTITY_UNSATISFIED" (Just "kappa.quantity.unsatisfied")
      "A declaration uses a quantity forbidden by the construct's static contract."
  , ent "E_QTT_PATH_CONSUMED" (Just "kappa.path.consumed")
      "A place is borrowed or re-projected after the path was already consumed at quantity 1, without an intervening restoring record update (§12.4, §3.2.6)."
  , ent "E_QTT_USING_EXPLICIT_QUANTITY" (Just "kappa-hs.qtt.using-quantity")
      "A 'using' binding declares an explicit quantity; using-scoped resources have a fixed discipline (§19.5)."
  , -- Mutable variables (§18.3.1, §18.6.1)
    ent "E_VAR_IN_STATIC_POSITION" (Just "kappa.var.mutable-binding")
      "A mutable variable current-value read appears in a type, static, proof, macro, or implicit-search position where object-phase reads are not available (§18.6.1)."
  , ent "E_VAR_READ_CROSSES_BOUNDARY" (Just "kappa.var.mutable-binding")
      "A mutable variable current-value read would have to cross a lambda, local function, quote, type, static, or macro boundary (§18.3.1)."
  , ent "E_VAR_READ_DUPLICATES_LINEAR_VALUE" (Just "kappa.var.mutable-binding")
      "Reading a mutable variable would duplicate a stored value that may contain a non-duplicable runtime component (§12.2.6, §18.6.1)."
  , ent "E_VAR_READ_OUTSIDE_DO" (Just "kappa.var.mutable-binding")
      "A mutable variable current-value read occurs outside the expression-lifting context of its enclosing do block (§18.3.1, §18.6.1)."
  , ent "E_VAR_REF_REQUIRED" (Just "kappa.var.mutable-binding")
      "A mutable variable reference cell is required; write 'ref x' to select the hidden cell instead of the current-value facet (§18.6.1)."
  , ent "W_VAR_REF_ESCAPE_DISABLES_FLOW" (Just "kappa.var.mutable-binding")
      "A mutable variable reference escapes, so current-value flow facts for that cell are no longer tracked (§18.6.2)."
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
  , ent "E_INTERNAL_PRELUDE_INTERFACE" (Just "kappa-hs.internal.prelude-interface")
      "A compiler-generated term requires a checked standard-library interface that is unavailable. This indicates an invalid or incomplete compiler environment, not a source-program type error."
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
  , ent "E_NATIVE_BINDING_ABI_UNVERIFIED" (Just "kappa-hs.build.native-abi")
      "An explicit symbolList declares a symbol with a pointer/string/handle signature whose ABI is not verified — it is neither shim-provided (force-include ABI-checked) nor covered by a 'verify' prototype checked against the real header; add a 'verify' decl, a shim, or generate the surface from a header (Spec §26.1.5, §36.28)."
  , ent "E_NATIVE_BINDING_PATH_ESCAPE" (Just "kappa-hs.build.native-path")
      "A native binding's package-relative input path (shim source, prebuilt artifact, include dir, module map, or header) escapes the package root via '..', an absolute path, or a symlink — rejected fail-closed (Spec §36.11)."
  , ent "E_BACKEND_CAPABILITY_UNREALIZED" (Just "kappa-hs.backend.capability")
      "A native binding's foreign-call classification requires a runtime capability the backend profile does not advertise (e.g. a 'blocking-cancellable' binding needs a safe-cancellation capability the native profile lacks); the binding is rejected rather than executed with weakened semantics (Spec §26.1.4, §27.6)."
  , ent "E_BACKEND_INTRINSIC_SIGNATURE_MISMATCH" (Just "kappa-hs.backend.intrinsic")
      "An 'expect term' whose name matches a native backend host-binding intrinsic declares a type that does not match the intrinsic's signature up to definitional equality (Spec §9.4, §34.5)."
  , ent "W_BACKENDIR_NON_FUNCTION_HEAD" (Just "kappa-hs.backendir.non-function-head")
      "An observe-only KBackendIR lint found a value application whose head is statically a non-function value (e.g. an erased/unit-valued term or a saturated constructor). Such a term would lower to an ill-typed 'kapp(unit, …)' call; this warning surfaces it without changing codegen."
  , -- §34.3.3 KBackendIR Stage-3 lowering-legality verifier (observe-only)
    ent "W_BACKENDIR_ERASED_REFERENCE" (Just "kappa-hs.backendir.erased-reference")
      "The observe-only KBackendIR Stage-3 verifier (§34.3.3) found a runtime term that refers to an erased entity — a manifestly-erased type form (a universe, a function/record/variant/signature type) sitting in a runtime-kept argument slot that was not reified as an ordinary runtime value (Spec §34.3.3 bullet 2, line 34688). This warning surfaces it without changing codegen."
  , ent "W_BACKENDIR_ARITY_MISMATCH" (Just "kappa-hs.backendir.arity-mismatch")
      "The observe-only KBackendIR Stage-3 verifier (§34.3.3) found a constructor application whose runtime field count does not match the constructor's fixed runtime arity (no partial application without a closure, no arity mismatch vs the resolved signature; Spec §34.3.3 bullet 3). This warning surfaces it without changing codegen."
  , ent "W_BACKENDIR_LAYOUT_INCONSISTENT" (Just "kappa-hs.backendir.layout-inconsistent")
      "The observe-only KBackendIR Stage-3 verifier (§34.3.3) found a data-layout inconsistency: two constructors of one datatype share a runtime tag id (non-injective assignment), a constructor a datatype lists does not point back to it, or a constructor declares more explicit fields than its type's runtime arity (so its layout would under-reserve slots) — Spec §34.3.3 layout-consistency, §§31.3-31.4. This warning surfaces it without changing codegen."
  , ent "E_BACKENDIR_ERASED_RUNTIME_TERM" (Just "kappa-hs.backendir.erased-runtime-term")
      "KCore-to-KBackendIR lowering found an erased source entity (type/proof term, erased binder, erased index, or unsolved compile-time meta) that would still be needed by a runtime-relevant backend value. Native emission rejects this rather than silently substituting a unit placeholder (§31.2, §34.3)."
  , ent "E_DERIVE_HEAD" (Just "kappa.derive.invalid-head")
      "A derive declaration does not name a supported derivable trait applied to exactly one target type (§14.5.1-§14.5.2)."
  , ent "E_DERIVE_UNSUPPORTED" (Just "kappa.derive.unsupported")
      "A well-formed derive declaration requests a trait or checked target shape outside the portable derivation fragment (§14.5.1-§14.5.2)."
  , ent "E_BACKENDIR_RETURN_CONTRACT" (Just "kappa-hs.backendir.return-contract")
      "KCore-to-KBackendIR lowering found a return value that does not satisfy the finalized function return contract. Native emission rejects the body rather than changing the declared result representation."
  , ent "E_BACKENDIR_OBSERVATION_ANALYSIS" (Just "kappa.internal.compiler")
      "The finalized KCore return path violates its declared observation contract: a value depending on a parametric origin would escape through an ordinary result. KBackendIR rejects the body before erasure rather than dropping the dependency (§30.2.0, §31.2)."
  , ent "E_BACKENDIR_BINDER_METADATA" (Just "kappa-hs.backendir.binder-metadata")
      "KCore-to-KBackendIR lowering could not reconcile a runtime binder with its typed ownership metadata. Native emission rejects the body rather than guessing a quantity, access mode, or ownership convention (§30.2.5, §31.2, §34.3)."
  , ent "E_BACKENDIR_CONSTRUCTOR_INTERFACE" (Just "kappa.internal.compiler")
      "Finalized Core references a constructor whose exact semantic telescope is unavailable or whose compiler-owned intrinsic telescope failed validation."
  , ent "E_BACKENDIR_CONSTRUCTOR_ARITY" (Just "kappa.internal.compiler")
      "A finalized constructor application does not match the arity or explicitness of its semantic telescope."
  , ent "E_BACKENDIR_CONSTRUCTOR_PATTERN_ALIGNMENT" (Just "kappa.internal.compiler")
      "A finalized constructor pattern cannot be aligned with the checked constructor telescope and scrutinee type."
  , ent "E_BACKENDIR_CONSTRUCTOR_SCOPE" (Just "kappa.internal.compiler")
      "A finalized constructor argument is outside the local telescope recorded for its occurrence."
  , ent "E_INTERNAL_CONSTRUCTOR_ARITY" (Just "kappa.internal.compiler")
      "A compiler-generated constructor application supplies an argument spine inconsistent with the declared constructor interface."
  , ent "E_INTERNAL_CONSTRUCTOR_INTERFACE" (Just "kappa.internal.compiler")
      "A compiler-generated constructor occurrence has no declared constructor interface."
  , ent "E_INTERNAL_GENERATED_APPLICATION" (Just "kappa.internal.compiler")
      "A compiler-generated application does not match the checked dependent telescope from which its argument spine was derived."
  , ent "E_INTERNAL_ARITHMETIC_PROOF" (Just "kappa.internal.compiler")
      "The value-arithmetic elaborator selected evidence whose checked law does not prove the equality required by a generated transport."
  , ent "E_INTERNAL_ARITHMETIC_TRANSPORT" (Just "kappa.internal.compiler")
      "The value-arithmetic elaborator could not check a generated equality transport against its indexed source and target types."
  , ent "E_INTERNAL_ANONYMOUS_REGION" (Just "kappa.internal.compiler")
      "The compiler could not construct the typed lexical-region witness required for an anonymous borrow."
  , ent "E_INTERNAL_MISSING_PRELUDE_DECLARATION" (Just "kappa.internal.compiler")
      "A compiler-generated use requires a checked prelude declaration or trait member that is absent from the semantic environment."
  , ent "E_INTERNAL_EFFECT_PURE_TYPE" (Just "kappa.internal.compiler")
      "The compiler attempted to construct an effect-tree pure node without an Eff result type."
  , ent "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
      "A resolved trait member has a parameter or dictionary telescope that cannot be specialized according to its checked trait interface."
  , ent "E_TERMINATION_UNVERIFIED" (Just "kappa.termination.failure")
      "The termination checker could not verify a recursive declaration-schema SCC that requires a checked strict static decrease or an ordinary well-founded measure."
  , ent "E_LOCAL_DECLARATION_CAPTURE_INTERFACE" (Just "kappa.internal.compiler")
      "A finalized local declaration interface does not contain the implicit binder required for one of its semantic captures."
  , ent "E_LOCAL_DECLARATION_CAPTURE_SCOPE" (Just "kappa.name.unresolved")
      "A local declaration reference requires a declaration-site capture that is no longer in lexical scope."
  , ent "W_BACKENDIR_MISSING_BINDER" (Just "kappa-hs.backendir.missing-binder")
      "The KBackendIR tree validator found a runtime binder or parameter without the ownership binder metadata that backend emitters require once they consume KBackendIR directly (§31.2, §34.3)."
  , ent "W_BACKENDIR_MISSING_USE" (Just "kappa-hs.backendir.missing-use")
      "The KBackendIR tree validator found a runtime variable occurrence without node-local ownership-use metadata; the backend must not fall back to a structural path lookup for this occurrence (§31.2, §34.3)."
  , ent "W_BACKENDIR_CTOR_FIELD_MISMATCH" (Just "kappa-hs.backendir.ctor-field-mismatch")
      "The KBackendIR tree validator found a constructor node whose recorded runtime field count does not match the number of lowered runtime fields on the node (§34.3.3 fixed-runtime-arity, §34.3.7 representation data)."
  , ent "W_BACKENDIR_CTOR_LAYOUT_INCONSISTENT" (Just "kappa-hs.backendir.ctor-layout-inconsistent")
      "The KBackendIR tree validator found constructor layout metadata whose arity, field representations, layout class, or boxed footprint disagrees with the node's runtime-kept field list. Native emission rejects this because S5 reuse will trust these layout facts for same-size checks (§34.3.7)."
  , ent "W_BACKENDIR_DUPLICATE_NODE_ID" (Just "kappa-hs.backendir.duplicate-node-id")
      "The KBackendIR tree validator found a backend node identity reused within a single lowered body; node identities must be stable and unique enough to carry ownership/representation facts without structural path keys (§30.2.5, §31.2)."
  , ent "W_BACKENDIR_DUPLICATE_BINDER_ID" (Just "kappa-hs.backendir.duplicate-binder-id")
      "The KBackendIR tree validator found a backend binder identity reused within a single lowered body; binder identities must be unique so ownership and branch-drop metadata cannot overwrite or alias each other (§30.2.5, §31.2)."
  , ent "W_BACKENDIR_DUPLICATE_USE_ID" (Just "kappa-hs.backendir.duplicate-use-id")
      "The KBackendIR tree validator found a backend use identity reused within a single lowered body; use identities must be unique so future graph and reuse passes can key facts without ambiguity (§30.2.5, §31.2)."
  , ent "W_BACKENDIR_BRANCH_DROP_OUT_OF_SCOPE" (Just "kappa-hs.backendir.branch-drop-out-of-scope")
      "The KBackendIR tree validator found branch-dead-drop metadata naming a backend binder that is not in scope at that branch node. Native emission rejects this rather than silently omitting an ownership drop or attaching it to the wrong runtime binder (§31.2, §34.3)."
  , ent "W_BACKENDIR_BRANCH_DROP_MISMATCH" (Just "kappa-hs.backendir.branch-drop-mismatch")
      "The KBackendIR tree validator found branch-dead-drop metadata whose binder identity is in scope but whose ownership payload does not match the canonical in-scope backend binder. Native emission rejects this so stale or forged metadata cannot change drop ownership semantics (§31.2, §34.3)."
  , ent "W_BACKENDIR_BRANCH_DROP_DUPLICATE" (Just "kappa-hs.backendir.branch-drop-duplicate")
      "The KBackendIR tree validator found branch-dead-drop metadata naming the same binder more than once at one branch site. Native emission rejects this rather than risking a duplicated ownership drop (§31.2, §34.3)."
  , ent "W_BACKENDIR_CTOR_PATTERN_FIELD_MISMATCH" (Just "kappa-hs.backendir.ctor-pattern-field-mismatch")
      "The KBackendIR tree validator found a constructor pattern whose lowered runtime payload pattern count does not equal the constructor layout's runtime field count. Constructor pattern offsets must index the same runtime-kept field list that constructor allocation built (§31.2, §34.3.3, §34.3.7)."
  , ent "W_BACKENDIR_CTOR_PATTERN_LAYOUT_MISSING" (Just "kappa-hs.backendir.ctor-pattern-layout-missing")
      "The KBackendIR tree validator found a constructor pattern without a matching layout metadata entry on its enclosing match. Match-side constructor layout facts must be present before S5 reuse can trust destructuring offsets (§31.2, §34.3.3, §34.3.7)."
  , ent "W_BACKENDIR_PATTERN_FIELD_INDEX_INVALID" (Just "kappa-hs.backendir.pattern-field-index-invalid")
      "The KBackendIR tree validator found a positional record or tuple pattern field index outside its runtime-kept field arity. Native emission rejects this because pattern offsets must index the same erased layout that allocation produced (§31.2, §34.3.3)."
  , ent "W_BACKENDIR_PATTERN_FIELD_INDEX_DUPLICATE" (Just "kappa-hs.backendir.pattern-field-index-duplicate")
      "The KBackendIR tree validator found a positional record or tuple pattern that binds the same runtime-kept field index more than once. Native emission rejects the ambiguous physical layout rather than reading one payload slot through multiple source positions (§31.2, §34.3.3)."
  , ent "W_BACKENDIR_BRANCH_DROP_UNEMITTED_ITEM" (Just "kappa-hs.backendir.branch-drop-unemitted-item")
      "The KBackendIR tree validator found branch-dead-drop metadata attached to a do-item node. Native emission drains branch drops only from term and alternative emission points, so item-level branch-drop metadata is rejected fail-closed rather than silently ignored (§31.2, §34.3)."
  , ent "W_BACKENDIR_BRANCH_DROP_UNRESOLVED" (Just "kappa-hs.backendir.branch-drop-unresolved")
      "The KBackendIR lowering validator found branch-dead-drop metadata naming a binder that cannot be resolved to node-local backend binder metadata. Native emission rejects this rather than silently omitting an ownership drop (§31.2, §34.3)."
  , ent "W_BACKENDIR_BRANCH_DROP_UNVISITED" (Just "kappa-hs.backendir.branch-drop-unvisited")
      "The KBackendIR lowering validator found branch-dead-drop metadata for a branch site that no lowered backend node owns. Native emission rejects this stale metadata so path-to-node drift cannot silently suppress ownership drops (§31.2, §34.3)."
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
