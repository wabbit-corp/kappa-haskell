-- | Diagnostic code registry (Spec §3.1.2A).
--
-- A machine-readable registry of every diagnostic code this
-- implementation may emit in ordinary user-facing compilation, plus the
-- §3.1.3 standard Unicode diagnostic codes (whose spellings and
-- explanations the specification fixes for all conforming
-- implementations). Backs the @kappa explain CODE@ subcommand and the
-- §T.5.1 @assertDiagnosticExplainExists@ harness directive.
module Kappa.Explain
  ( ExplainEntry (..)
  , registry
  , lookupCode
  , explainExists
  , renderEntry
  , portableAlias
  , codeNames
  ) where

import Data.Text (Text)
import qualified Data.Text as T

data ExplainEntry = ExplainEntry
  { eeCode :: !Text
  , eeFamily :: !(Maybe Text)
  , eeExplanation :: !Text
  }

lookupCode :: Text -> Maybe ExplainEntry
lookupCode c = case [e | e <- registry, eeCode e == c] of
  (e : _) -> Just e
  [] -> Nothing

-- | §T.5.1 @code-or-family@ matching: a spelling beginning with
-- @kappa.@ is a family; otherwise it is a code (codes win ties).
explainExists :: Text -> Bool
explainExists s
  | "kappa." `T.isPrefixOf` s = any ((== Just s) . eeFamily) registry
  | otherwise = any ((== s) . eeCode) registry

-- | Required portable diagnostic-code alias (§3.1.2A) for a rendered
-- code, where one is defined. A diagnostic "code" in the sense of §3.1
-- is recoverable either as the rendered code or as its portable alias
-- (§3.1.2A allows an implementation to expose either spelling), so the
-- harness accepts both when matching @assertDiagnostic*@ directives.
portableAlias :: Text -> Maybe Text
portableAlias c = lookup c table
  where
    table =
      [ ("E_TYPE_EQUALITY_MISMATCH", "E_TYPE_MISMATCH")
      , ("E_SAFE_NAVIGATION_AMBIGUOUS", "E_SAFE_NAV_GENERIC_AMBIGUOUS")
      , ("E_UNSOLVED_IMPLICIT", "E_TYPE_MISMATCH")
      , ("E_APPLICATION_NONCALLABLE", "E_APPLICATION_NON_CALLABLE")
      , ("E_RECURSION_REQUIRES_SIGNATURE", "E_MISSING_EXPLICIT_SIGNATURE")
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
    <> "\n"

registry :: [ExplainEntry]
registry =
  [ ent "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument")
      "An argument in a function application does not fit the corresponding parameter (wrong plicity, label, or form)."
  , ent "E_APPLICATION_NONCALLABLE" (Just "kappa.application.non-callable")
      "The head of an application has a type that is not a function or callable value, so it cannot be applied to arguments."
  , ent "E_ASSIGN_NOT_VAR" (Just "kappa.do.assign-non-var")
      "The left-hand side of a do-block assignment is not a mutable 'var' binding introduced in the same do scope."
  , ent "E_BINDER_MISMATCH" (Just "kappa.type.binder")
      "A lambda or function definition binds a parameter whose plicity or label does not match the binder in the expected function type."
  , ent "E_BLOCK_NO_RESULT" Nothing
      "A block expression ends without producing a result expression, so the block has no value."
  , ent "E_BREAK_OUTSIDE_LOOP" (Just "kappa.do.break-outside-loop")
      "A 'break' or 'continue' control expression appears outside any enclosing loop."
  , ent "E_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.application.arity")
      "A data constructor is applied to the wrong number of arguments for its declaration."
  , ent "E_DUPLICATE_DECLARATION" (Just "kappa.name.duplicate")
      "Two top-level declarations of the same kind in the same module bind the same name."
  , ent "E_DUPLICATE_PATTERN_BINDER" (Just "kappa.pattern.duplicate-binder")
      "The same variable is bound more than once within a single pattern."
  , ent "E_EMPTY_BACKTICK_IDENT" Nothing
      "A backtick-quoted identifier is empty; backtick identifiers must contain at least one character."
  , ent "E_FEATURE_INACTIVE" (Just "kappa.feature.gated")
      "An identifier uses Unicode characters outside the active name profile without the corresponding feature gate enabled."
  , ent "E_HOLE_UNSOLVED" (Just "kappa.hole.unsolved")
      "A typed hole '?' or '_' in expression position was not solved by elaboration; the expected type or value remains unknown."
  , ent "E_IF_MISSING_ELSE" (Just "kappa.control.if-missing-else")
      "An 'if' expression used for its value lacks an 'else' branch, so not all paths produce a result."
  , ent "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved")
      "An implicit argument (instance or value) could not be solved from the context at this application."
  , ent "E_IMPOSSIBLE_REACHABLE" (Just "kappa.match.impossible-reachable")
      "A match arm marked 'impossible' is actually reachable: the scrutinee type does not rule the pattern out."
  , ent "E_INDEXED_IMPOSSIBLE_REACHABLE" (Just "kappa.match.impossible-reachable")
      "An 'impossible' arm on an indexed family is reachable because the index constraints do not make the constructor uninhabited."
  , ent "E_INSTANCE_HEAD" (Just "kappa.trait.bad-instance-head")
      "A trait instance declaration has a malformed head: the target is not a trait applied to well-formed type arguments."
  , ent "E_INSTANCE_INCOHERENT" (Just "kappa.trait.incoherent")
      "Two visible instances of the same trait overlap for the same type, so instance resolution is incoherent."
  , ent "E_INSTANCE_MEMBER_MISSING" (Just "kappa.trait.member-missing")
      "A trait instance does not define a required member that has no default in the trait declaration."
  , ent "E_INTERNAL" Nothing
      "Internal compiler invariant violation. This is an implementation bug, not an error in the source program."
  , ent "E_LABEL_UNRESOLVED" (Just "kappa.do.label-unresolved")
      "A labeled 'break' or 'continue' names a loop label that is not in scope."
  , ent "E_LAYOUT_BAD_DEDENT" Nothing
      "A line dedents to an indentation column that does not match any enclosing layout context."
  , ent "E_PATTERN_NON_EXHAUSTIVE" (Just "kappa.match.nonexhaustive")
      "A match expression does not cover every possible constructor or literal of the scrutinee type."
  , ent "E_MULTILINE_STRING_BAD_INDENT" Nothing
      "A line inside a multiline string literal is indented less than the closing delimiter's indentation baseline."
  , ent "E_NAMED_ARG_DUPLICATE" (Just "kappa.application.named")
      "The same named argument is supplied more than once in one application."
  , ent "E_NAMED_ARG_MISSING" (Just "kappa.application.named")
      "A named-argument application omits a required parameter of the function."
  , ent "E_NAMED_ARG_UNKNOWN" (Just "kappa.application.named")
      "A named argument does not correspond to any parameter of the applied function."
  , ent "E_NOT_A_TYPE" (Just "kappa.type.expected-type")
      "An expression used in type position does not denote a type (its type is not 'Type')."
  , ent "E_NUMERIC_LITERAL_MALFORMED" Nothing
      "A numeric literal is lexically malformed (bad digits for its radix, misplaced separators, or an invalid exponent)."
  , ent "E_OPERATOR_NO_FIXITY" (Just "kappa.fixity.unbound")
      "An infix operator is used without any fixity declaration in scope, so the expression cannot be grouped."
  , ent "E_OR_PATTERN_BINDER_MISMATCH" (Just "kappa.pattern.or-bindings")
      "The alternatives of an or-pattern do not bind exactly the same variables at the same types."
  , ent "E_EXPECT_AMBIGUOUS" (Just "kappa.expect.ambiguous")
      "More than one definition in the compilation unit satisfies a single 'expect' declaration (Spec 9.4)."
  , ent "E_EXPECT_UNSATISFIED" (Just "kappa.expect.unsatisfied")
      "An 'expect' declaration names a required external declaration, but no definition, backend intrinsic, or imported artifact in the compilation unit satisfies it (Spec 9.4)."
  , ent "E_RECURSIVE_VALUE_CYCLE" (Just "kappa.termination.cycle")
      "A value-level definition refers to itself without an intervening function abstraction, so its evaluation can never terminate."
  , ent "E_SIGNATURE_UNSATISFIED" (Just "kappa.signature.unsatisfied")
      "A non-expect top-level term signature has no matching definition in the same source file (Spec 9.1)."
  , ent "E_UNEXPECTED_INDENTATION" (Just "kappa.parse.error")
      "A top-level declaration begins at a deeper indentation level than the module's declaration level (Spec 5.4)."
  , ent "E_EXPECTED_SYNTAX_TOKEN" (Just "kappa.parse.error")
      "The source text does not conform to the Kappa grammar at this position."
  , ent "E_PATTERN_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.pattern.arity")
      "A constructor pattern has the wrong number of argument subpatterns for the constructor's declaration."
  , ent "E_PATTERN_FIELD_UNKNOWN" (Just "kappa.pattern.field")
      "A record or constructor pattern mentions a field that the matched type does not declare."
  , ent "E_RECORD_DUPLICATE_FIELD" (Just "kappa.record.duplicate-field")
      "A record literal or record type repeats a field name."
  , ent "E_RECORD_PATCH_DUPLICATE_PATH" (Just "kappa.record.patch-duplicate")
      "A record patch updates the same field path more than once."
  , ent "E_RECORD_PROJECTION_MISSING_FIELD" (Just "kappa.record.unknown-field")
      "A field projection names a field that the record type does not contain."
  , ent "E_RECURSION_REQUIRES_SIGNATURE" (Just "kappa.termination.recursion-needs-signature")
      "A recursive definition lacks a type signature; recursion requires a declared signature for checking."
  , ent "E_RECURSIVE_TYPE_ALIAS" (Just "kappa.type.recursive-alias")
      "A type alias refers to itself; recursive type aliases are not admitted — use a data declaration."
  , ent "E_URL_IMPORT_UNPINNED_IN_PACKAGE_MODE" (Just "kappa.import.url")
      "A URL module import without a #sha256:/#ref: pin is not reproducible and is rejected in package mode."
  , ent "E_URL_IMPORT_UNSUPPORTED" (Just "kappa.import.url")
      "A pinned URL module import names content this implementation cannot fetch; URL module fetching is not provided."
  , ent "E_URL_IMPORT_REF_PIN_REQUIRES_LOCK" (Just "kappa.import.url")
      "A ref:-pinned URL import requires the resolved digest to be recorded in a lockfile in package mode; no lockfile machinery exists here."
  , ent "E_STATIC_OBJECT_KIND_MISMATCH" (Just "kappa.static-object.kind")
      "A kind-qualified name expression's selector does not agree with the named declaration's facet (e.g. 'trait' on a data type)."
  , ent "E_QTT_BORROW_ESCAPE" (Just "kappa.qtt.borrow-escape")
      "A closure or value capturing a borrowed binding (or a reified BorrowView) escapes the borrow's scope through the result."
  , ent "E_REFUTABLE_LET_PATTERN" (Just "kappa.pattern.refutable-binding")
      "A 'let' binding uses a refutable pattern; only irrefutable patterns may appear in plain let bindings."
  , ent "E_SAFE_NAVIGATION_RECEIVER_NOT_OPTION" (Just "kappa.type.mismatch")
      "The receiver of a '?.' safe-navigation expression is not an Option value."
  , ent "E_SAFE_NAVIGATION_AMBIGUOUS" (Just "kappa.type.mismatch")
      "A safe-navigation '?.' chain has an ambiguous generic receiver, so the implicit Option threading cannot be decided."
  , ent "E_SIGNATURE_ARITY" (Just "kappa.type.signature-arity")
      "A definition binds more parameters than its declared signature provides function arrows for."
  , ent "E_SPLICE_OUTSIDE_DO" Nothing
      "A splice expression appears outside the do-block context that would give it meaning."
  , ent "E_STRING_ESCAPE_INVALID" Nothing
      "A string or character literal contains an invalid escape sequence."
  , ent "E_TRAIT_SUPERTRAIT_UNSATISFIED" (Just "kappa.trait.supertrait-unsatisfied")
      "An instance is declared for a trait whose supertrait constraint has no visible instance for the same type."
  , ent "E_TAB_IN_INDENTATION" Nothing
      "A horizontal tab appears in the indentation of a line; Kappa layout indentation must use spaces only."
  , ent "E_TAB_IN_SOURCE" Nothing
      "A horizontal tab appears in source text where the active source profile forbids it."
  , ent "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
      "The inferred type of an expression is not definitionally equal to (or coercible to) the expected type."
  , ent "E_UNEXPECTED_CHARACTER" Nothing
      "The lexer encountered a character that cannot begin any token."
  , ent "E_UNKNOWN_FIELD" (Just "kappa.record.unknown-field")
      "A record expression mentions a field that the expected record type does not declare."
  , ent "E_UNRESOLVED_MEMBER" (Just "kappa.name.unresolved-member")
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
  , ent "E_VARIANT_AMBIGUOUS" (Just "kappa.variant.ambiguous")
      "A bare variant constructor could match more than one variant member in the expected type; disambiguate with an annotation."
  , ent "E_VARIANT_ARM" Nothing
      "A variant match arm is malformed or does not correspond to a member of the matched variant row."
  , ent "E_VARIANT_DUPLICATE" (Just "kappa.variant.duplicate-member")
      "A variant row declares the same member name more than once."
  , ent "E_VARIANT_MEMBER" (Just "kappa.variant.unknown-member")
      "A variant expression or pattern names a member that the variant row does not declare."
  , ent "E_VARIANT_PATTERN" Nothing
      "A variant pattern is malformed for the matched variant type."
  , ent "W_TERMINATION_UNVERIFIED" (Just "kappa.termination.unverified")
      "The termination checker could not verify that this recursive definition terminates; it is accepted unverified."
  , -- §3.1.3 standard Unicode diagnostic codes. The specification fixes
    -- these spellings and meanings for every conforming implementation;
    -- they are registered here with their normative explanations.
    ent "E_UNICODE_INVALID_SCALAR_LITERAL" (Just "kappa.unicode.invalid-scalar-literal")
      "A single-quoted Unicode scalar literal decodes to zero scalar values, more than one scalar value, a surrogate code point, or an out-of-range code point (§3.1.3)."
  , ent "E_UNICODE_INVALID_GRAPHEME_LITERAL" (Just "kappa.unicode.invalid-grapheme-literal")
      "A g-prefixed quoted literal contains zero extended grapheme clusters or more than one extended grapheme cluster (§3.1.3)."
  , ent "E_UNICODE_INVALID_BYTE_LITERAL" (Just "kappa.unicode.invalid-byte-literal")
      "A b-prefixed quoted literal contains zero bytes or more than one byte (§3.1.3)."
  , ent "E_UNICODE_INVALID_UTF8" (Just "kappa.unicode.invalid-utf8")
      "A source form or checked conversion requires valid UTF-8 but received invalid bytes (§3.1.3)."
  , ent "E_UNICODE_NAME_PROFILE_VIOLATION" (Just "kappa.unicode.name-profile")
      "An identifier, operator, literal prefix, suffix, alias, or export name violates the active Unicode name profile (§3.1.3)."
  , ent "E_UNICODE_NAME_NON_NORMALIZED" (Just "kappa.unicode.name-non-normalized")
      "An unquoted Unicode identifier or operator token is not in the normalization form required by the active Unicode name profile (§3.1.3)."
  , ent "E_UNICODE_VISUAL_DUPLICATE_BINDING" (Just "kappa.unicode.visual-duplicate")
      "Two declarations in the same scope and declaration kind have distinct spellings but the same strong visual name key (§3.1.3, §5.1A)."
  , ent "W_UNICODE_CONFUSABLE_IDENTIFIER" (Just "kappa.unicode.confusable")
      "A name is visually confusable with another visible name under the active diagnostic skeleton policy (§3.1.3)."
  , ent "W_UNICODE_VISUAL_ALIAS_REFERENCE" (Just "kappa.unicode.visual-alias")
      "A reference resolved by strong visual name key rather than by exact strict name key (§3.1.3, §7.1)."
  , ent "W_UNICODE_MIXED_SCRIPT_IDENTIFIER" (Just "kappa.unicode.mixed-script")
      "A single identifier or operator name mixes scripts in a way prohibited or discouraged by the active Unicode name profile (§3.1.3)."
  , ent "W_UNICODE_MIXED_NUMBER_IDENTIFIER" (Just "kappa.unicode.mixed-number")
      "A name mixes decimal digits from different numbering systems or visually confusable number-like code points (§3.1.3)."
  , ent "W_UNICODE_NON_NORMALIZED_SOURCE_TEXT" (Just "kappa.unicode.non-normalized-text")
      "A source file contains non-normalized text in comments, strings, or other positions not governed by E_UNICODE_NAME_NON_NORMALIZED (§3.1.3)."
  , ent "W_UNICODE_BIDI_CONTROL" (Just "kappa.unicode.bidi-control")
      "Source text contains bidirectional control characters outside string literals or prefixed quoted literals (§3.1.3)."
  , -- CLI-level code (kappa run without a main definition)
    ent "E_NO_MAIN" Nothing
      "The module given to 'kappa run' does not define a 'main' entrypoint."
  ]
  where
    ent c f x = ExplainEntry c f x
