-- | Verified runtime-representation evidence (§30.2.7B-C).
--
-- Source traits describe user-visible equivalences. These records are a
-- separate compiler-owned trust boundary: an optimization may consume them
-- only after replaying the structural encoding and contextual type identity.
module Kappa.Representation
  ( RepresentationContext (..)
  , BackendProfileRestriction (..)
  , ConstructorFieldPath (..)
  , ConstructorOrdinalEncoding (..)
  , OrdinalEncoding (..)
  , OrdinalRepresentationCertificate (..)
  , ExactNaturalRepresentationCertificate (..)
  , RefinementRepresentationCertificate (..)
  , representationTypeIdentity
  , representationEvidenceIdentity
  , ordinalRepresentationCertificateIdentity
  , exactNaturalRepresentationCertificateIdentity
  , refinementRepresentationCertificateIdentity
  , canonicalOrdinalRepresentationCertificate
  , canonicalExactNaturalRepresentationCertificate
  , canonicalRefinementRepresentationCertificate
  , ordinalEncodingCardinality
  , verifyOrdinalRepresentationCertificate
  , verifyExactNaturalRepresentationCertificate
  , verifyRefinementRepresentationCertificate
  ) where

import Data.List (nub, sort)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Cardinality
  ( CardConstraint (..)
  , CardExpr (..)
  , cardAdd
  , cardGuardedSub
  , cardIf
  , cardLiteral
  , cardMul
  , normalizeCardExpr
  , renderCardExpr
  )
import Kappa.Core (GName, Literal (..), Term (..), gKey)
import Kappa.Pretty (renderTerm)
import Kappa.SemanticHash (canonicalIdentityHex)
import Numeric.Natural (Natural)

-- | The contextual part of a §30.2.7B hard type identity. Binder types are
-- ordered outermost-first and use De Bruijn references into preceding
-- binders. Universe constraints are already normalized by the checker.
data RepresentationContext = RepresentationContext
  { rcBinderTypes :: ![Term]
  , rcUniverseConstraints :: ![Text]
  }
  deriving stock (Eq, Show)

data BackendProfileRestriction
  = InternalValuesOnly
  | ExcludeDynamicBoundary
  | ExcludeForeignBoundary
  | ExcludeExportedAbi
  | RequireCompactFiniteOrdinal
  | RequireUnboxedRefinement
  deriving stock (Eq, Ord, Show)

data ConstructorFieldPath = ConstructorFieldPath
  { cfpConstructor :: !GName
  , cfpSourceIndex :: !Int
  }
  deriving stock (Eq, Ord, Show)

-- | One constructor arm in a dense sum encoding. The offset is recorded and
-- replayed rather than trusted: it must equal the sum of all preceding arms.
data ConstructorOrdinalEncoding = ConstructorOrdinalEncoding
  { coeConstructor :: !GName
  , coeOffset :: !CardExpr
  , coeFields :: ![OrdinalEncoding]
  }
  deriving stock (Eq, Show)

-- | A total rank/unrank program in a small structural algebra. Each node has a
-- direct executable interpretation: products use mixed radix, sums use the
-- recorded constructor offset, ranges translate by their lower bound, and a
-- filtered base stores the exact accepted base ordinals. This is the
-- compiler-generated internal law bundle permitted by §30.2.7B; it is not
-- published to source instance search.
data OrdinalEncoding
  = OrdinalFin !CardExpr
  | OrdinalContractible
  | OrdinalRecord ![OrdinalEncoding]
  | OrdinalVariant ![OrdinalEncoding]
  | OrdinalData ![ConstructorOrdinalEncoding]
  | OrdinalInclusiveRange !Term !Term
  | OrdinalFiltered !OrdinalEncoding ![Natural]
  deriving stock (Eq, Show)

data OrdinalRepresentationCertificate = OrdinalRepresentationCertificate
  { orcContext :: !RepresentationContext
  , orcRepresentedType :: !Term
  , orcTypeIdentity :: !Text
  , orcSourceEvidenceIdentity :: !(Maybe Text)
  , orcCardinalityExpression :: !CardExpr
  , orcEncoding :: !OrdinalEncoding
  , orcErasedFields :: ![ConstructorFieldPath]
  , orcProfileRestrictions :: ![BackendProfileRestriction]
  , orcCertificateVersion :: !Natural
  , orcCheckerVersion :: !Natural
  }
  deriving stock (Eq, Show)

data ExactNaturalRepresentationCertificate = ExactNaturalRepresentationCertificate
  { enrcContext :: !RepresentationContext
  , enrcRepresentedType :: !Term
  , enrcTypeIdentity :: !Text
  , enrcEvidenceIdentity :: !Text
  , enrcZeroConstructor :: !GName
  , enrcSuccessorConstructor :: !GName
  , enrcRecursiveField :: !ConstructorFieldPath
  , enrcErasedFields :: ![ConstructorFieldPath]
  , enrcProfileRestrictions :: ![BackendProfileRestriction]
  , enrcCertificateVersion :: !Natural
  , enrcCheckerVersion :: !Natural
  }
  deriving stock (Eq, Show)

data RefinementRepresentationCertificate = RefinementRepresentationCertificate
  { rrcContext :: !RepresentationContext
  , rrcRepresentedType :: !Term
  , rrcTypeIdentity :: !Text
  , rrcRefinementEvidenceIdentity :: !Text
  , rrcBaseType :: !Term
  , rrcBaseTypeIdentity :: !Text
  , rrcConstructor :: !GName
  , rrcRetainedBaseField :: !ConstructorFieldPath
  , rrcErasedEvidenceFields :: ![ConstructorFieldPath]
  , rrcProfileRestrictions :: ![BackendProfileRestriction]
  , rrcCertificateVersion :: !Natural
  , rrcCheckerVersion :: !Natural
  }
  deriving stock (Eq, Show)

representationTypeIdentity :: RepresentationContext -> Term -> Text
representationTypeIdentity context representedType =
  canonicalIdentityHex
    "TypeNF"
    (contextualIdentityPayload context "type" representedType)

representationEvidenceIdentity :: RepresentationContext -> Term -> Text
representationEvidenceIdentity context evidence =
  canonicalIdentityHex
    "TraitEvidence"
    (contextualIdentityPayload context "evidence" evidence)

ordinalRepresentationCertificateIdentity
  :: OrdinalRepresentationCertificate
  -> Text
ordinalRepresentationCertificateIdentity =
  canonicalIdentityHex "OrdinalRepresentationCertificate"
    . canonicalOrdinalRepresentationCertificate

exactNaturalRepresentationCertificateIdentity
  :: ExactNaturalRepresentationCertificate
  -> Text
exactNaturalRepresentationCertificateIdentity =
  canonicalIdentityHex "ExactNaturalRepresentationCertificate"
    . canonicalExactNaturalRepresentationCertificate

refinementRepresentationCertificateIdentity
  :: RefinementRepresentationCertificate
  -> Text
refinementRepresentationCertificateIdentity =
  canonicalIdentityHex "RefinementRepresentationCertificate"
    . canonicalRefinementRepresentationCertificate

-- | Canonical artifact payloads are explicit and versioned. They do not
-- depend on derived Haskell constructor rendering, record field order, or
-- delimiter conventions. Every nested value is length-framed, so arbitrary
-- readable names and rendered terms remain unambiguous.
canonicalOrdinalRepresentationCertificate
  :: OrdinalRepresentationCertificate
  -> Text
canonicalOrdinalRepresentationCertificate certificate =
  record
    "ordinal-v1"
    [ contextPayload (orcContext certificate)
    , termPayload (orcRepresentedType certificate)
    , textPayload (orcTypeIdentity certificate)
    , maybePayload textPayload (orcSourceEvidenceIdentity certificate)
    , cardinalityPayload (orcCardinalityExpression certificate)
    , ordinalEncodingPayload (orcEncoding certificate)
    , listPayload fieldPathPayload (orcErasedFields certificate)
    , listPayload restrictionPayload (orcProfileRestrictions certificate)
    , naturalPayload (orcCertificateVersion certificate)
    , naturalPayload (orcCheckerVersion certificate)
    ]

canonicalExactNaturalRepresentationCertificate
  :: ExactNaturalRepresentationCertificate
  -> Text
canonicalExactNaturalRepresentationCertificate certificate =
  record
    "exact-natural-v1"
    [ contextPayload (enrcContext certificate)
    , termPayload (enrcRepresentedType certificate)
    , textPayload (enrcTypeIdentity certificate)
    , textPayload (enrcEvidenceIdentity certificate)
    , globalPayload (enrcZeroConstructor certificate)
    , globalPayload (enrcSuccessorConstructor certificate)
    , fieldPathPayload (enrcRecursiveField certificate)
    , listPayload fieldPathPayload (enrcErasedFields certificate)
    , listPayload restrictionPayload (enrcProfileRestrictions certificate)
    , naturalPayload (enrcCertificateVersion certificate)
    , naturalPayload (enrcCheckerVersion certificate)
    ]

canonicalRefinementRepresentationCertificate
  :: RefinementRepresentationCertificate
  -> Text
canonicalRefinementRepresentationCertificate certificate =
  record
    "refinement-v1"
    [ contextPayload (rrcContext certificate)
    , termPayload (rrcRepresentedType certificate)
    , textPayload (rrcTypeIdentity certificate)
    , textPayload (rrcRefinementEvidenceIdentity certificate)
    , termPayload (rrcBaseType certificate)
    , textPayload (rrcBaseTypeIdentity certificate)
    , globalPayload (rrcConstructor certificate)
    , fieldPathPayload (rrcRetainedBaseField certificate)
    , listPayload fieldPathPayload (rrcErasedEvidenceFields certificate)
    , listPayload restrictionPayload (rrcProfileRestrictions certificate)
    , naturalPayload (rrcCertificateVersion certificate)
    , naturalPayload (rrcCheckerVersion certificate)
    ]

contextualIdentityPayload :: RepresentationContext -> Text -> Term -> Text
contextualIdentityPayload context label term =
  record
    "contextual-identity-v1"
    [ contextPayload context
    , textPayload label
    , termPayload term
    ]

contextPayload :: RepresentationContext -> Text
contextPayload context =
  record
    "context-v1"
    [ listPayload termPayload (rcBinderTypes context)
    , listPayload textPayload (sort (rcUniverseConstraints context))
    ]

ordinalEncodingPayload :: OrdinalEncoding -> Text
ordinalEncodingPayload = \case
  OrdinalFin cardinality ->
    record "fin" [cardinalityPayload cardinality]
  OrdinalContractible ->
    record "contractible" []
  OrdinalRecord fields ->
    record "record" [listPayload ordinalEncodingPayload fields]
  OrdinalVariant members ->
    record "variant" [listPayload ordinalEncodingPayload members]
  OrdinalData constructors ->
    record "data" [listPayload constructorEncodingPayload constructors]
  OrdinalInclusiveRange lower upper ->
    record "inclusive-range" [termPayload lower, termPayload upper]
  OrdinalFiltered base ordinals ->
    record
      "filtered"
      [ ordinalEncodingPayload base
      , listPayload naturalPayload ordinals
      ]

constructorEncodingPayload :: ConstructorOrdinalEncoding -> Text
constructorEncodingPayload constructor =
  record
    "constructor"
    [ globalPayload (coeConstructor constructor)
    , cardinalityPayload (coeOffset constructor)
    , listPayload ordinalEncodingPayload (coeFields constructor)
    ]

fieldPathPayload :: ConstructorFieldPath -> Text
fieldPathPayload field =
  record
    "field-path"
    [ globalPayload (cfpConstructor field)
    , integerPayload (toInteger (cfpSourceIndex field))
    ]

restrictionPayload :: BackendProfileRestriction -> Text
restrictionPayload =
  textPayload . \case
    InternalValuesOnly -> "internal-values-only"
    ExcludeDynamicBoundary -> "exclude-dynamic-boundary"
    ExcludeForeignBoundary -> "exclude-foreign-boundary"
    ExcludeExportedAbi -> "exclude-exported-abi"
    RequireCompactFiniteOrdinal -> "require-compact-finite-ordinal"
    RequireUnboxedRefinement -> "require-unboxed-refinement"

cardinalityPayload :: CardExpr -> Text
cardinalityPayload =
  record "cardinality" . pure . textPayload . renderCardExpr . normalizeCardExpr

termPayload :: Term -> Text
termPayload = record "term" . pure . textPayload . renderTerm

globalPayload :: GName -> Text
globalPayload = record "global" . pure . textPayload . gKey

textPayload :: Text -> Text
textPayload = frame

naturalPayload :: Natural -> Text
naturalPayload = integerPayload . toInteger

integerPayload :: Integer -> Text
integerPayload = frame . T.pack . show

maybePayload :: (a -> Text) -> Maybe a -> Text
maybePayload _ Nothing = record "none" []
maybePayload encode (Just value) = record "some" [encode value]

listPayload :: (a -> Text) -> [a] -> Text
listPayload encode values =
  record
    ("list-" <> T.pack (show (length values)))
    (map encode values)

record :: Text -> [Text] -> Text
record tag fields =
  frame tag <> T.concat (map frame fields)

frame :: Text -> Text
frame value =
  T.pack (show (T.length value)) <> ":" <> value

ordinalEncodingCardinality :: OrdinalEncoding -> Maybe CardExpr
ordinalEncodingCardinality = \case
  OrdinalFin cardinality -> Just (normalizeCardExpr cardinality)
  OrdinalContractible -> Just (cardLiteral 1)
  OrdinalRecord fields ->
    foldr combineProduct (Just (cardLiteral 1)) fields
  OrdinalVariant members ->
    foldr combineSum (Just (cardLiteral 0)) members
  OrdinalData constructors ->
    validateConstructorOffsets constructors
  OrdinalInclusiveRange lower upper ->
    let lowerCardinality = termCardinality lower
        upperCardinality = termCardinality upper
     in Just
          ( cardIf
              (CardLe lowerCardinality upperCardinality)
              (cardAdd (cardGuardedSub upperCardinality lowerCardinality) (cardLiteral 1))
              (cardLiteral 0)
          )
  OrdinalFiltered base ordinals -> do
    baseCardinality <- ordinalEncodingCardinality base
    case normalizeCardExpr baseCardinality of
      CardLiteral bound
        | strictlyIncreasing ordinals
        , all (< bound) ordinals ->
            Just (cardLiteral (fromIntegral (length ordinals)))
      _ -> Nothing
  where
    termCardinality = \case
      CLit (LitInt value)
        | value >= 0 -> cardLiteral (fromInteger value)
      term -> CardIndex term
    combineProduct encoding accumulated =
      cardMul <$> ordinalEncodingCardinality encoding <*> accumulated
    combineSum encoding accumulated =
      cardAdd <$> ordinalEncodingCardinality encoding <*> accumulated

validateConstructorOffsets :: [ConstructorOrdinalEncoding] -> Maybe CardExpr
validateConstructorOffsets = go (cardLiteral 0)
  where
    go offset [] = Just offset
    go offset (constructor : rest)
      | normalizeCardExpr (coeOffset constructor) /= normalizeCardExpr offset =
          Nothing
      | otherwise = do
          arm <-
            foldr
              (\field accumulated -> cardMul <$> ordinalEncodingCardinality field <*> accumulated)
              (Just (cardLiteral 1))
              (coeFields constructor)
          go (cardAdd offset arm) rest

verifyOrdinalRepresentationCertificate
  :: OrdinalRepresentationCertificate
  -> Either Text ()
verifyOrdinalRepresentationCertificate certificate = do
  requireCurrentVersions
    (orcCertificateVersion certificate)
    (orcCheckerVersion certificate)
  requireCanonicalRestrictions (orcProfileRestrictions certificate)
  require
    ( orcTypeIdentity certificate
        == representationTypeIdentity
          (orcContext certificate)
          (orcRepresentedType certificate)
    )
    "represented type identity does not match its contextual normal form"
  cardinality <-
    maybe
      (Left "ordinal encoding is not a total canonical finite encoding")
      Right
      (ordinalEncodingCardinality (orcEncoding certificate))
  require
    (normalizeCardExpr cardinality
      == normalizeCardExpr (orcCardinalityExpression certificate))
    "ordinal encoding cardinality does not match the recorded cardinality"
  requireUniqueFields (orcErasedFields certificate)

verifyExactNaturalRepresentationCertificate
  :: ExactNaturalRepresentationCertificate
  -> Either Text ()
verifyExactNaturalRepresentationCertificate certificate = do
  requireCurrentVersions
    (enrcCertificateVersion certificate)
    (enrcCheckerVersion certificate)
  requireCanonicalRestrictions (enrcProfileRestrictions certificate)
  require
    ( enrcTypeIdentity certificate
        == representationTypeIdentity
          (enrcContext certificate)
          (enrcRepresentedType certificate)
    )
    "represented type identity does not match its contextual normal form"
  require
    (enrcZeroConstructor certificate /= enrcSuccessorConstructor certificate)
    "zero and successor constructor identities must differ"
  require
    (cfpConstructor (enrcRecursiveField certificate)
      == enrcSuccessorConstructor certificate)
    "recursive field does not belong to the successor constructor"
  require (not (T.null (enrcEvidenceIdentity certificate)))
    "exact-natural evidence identity is empty"
  requireUniqueFields
    (enrcRecursiveField certificate : enrcErasedFields certificate)

verifyRefinementRepresentationCertificate
  :: RefinementRepresentationCertificate
  -> Either Text ()
verifyRefinementRepresentationCertificate certificate = do
  requireCurrentVersions
    (rrcCertificateVersion certificate)
    (rrcCheckerVersion certificate)
  requireCanonicalRestrictions (rrcProfileRestrictions certificate)
  require
    ( rrcTypeIdentity certificate
        == representationTypeIdentity
          (rrcContext certificate)
          (rrcRepresentedType certificate)
    )
    "represented type identity does not match its contextual normal form"
  require
    ( rrcBaseTypeIdentity certificate
        == representationTypeIdentity
          (rrcContext certificate)
          (rrcBaseType certificate)
    )
    "base type identity does not match its contextual normal form"
  require
    (cfpConstructor (rrcRetainedBaseField certificate)
      == rrcConstructor certificate)
    "retained base field does not belong to the refinement constructor"
  require
    (all ((== rrcConstructor certificate) . cfpConstructor)
      (rrcErasedEvidenceFields certificate))
    "an erased evidence field belongs to another constructor"
  require (not (T.null (rrcRefinementEvidenceIdentity certificate)))
    "refinement evidence identity is empty"
  requireUniqueFields
    (rrcRetainedBaseField certificate : rrcErasedEvidenceFields certificate)

requireCurrentVersions :: Natural -> Natural -> Either Text ()
requireCurrentVersions certificateVersion checkerVersion = do
  require (certificateVersion == 1) "unsupported representation-certificate version"
  require (checkerVersion == 1) "unsupported representation-certificate checker version"

requireCanonicalRestrictions
  :: [BackendProfileRestriction]
  -> Either Text ()
requireCanonicalRestrictions restrictions =
  require
    (restrictions == sort (nub restrictions))
    "profile restrictions are not canonical"

requireUniqueFields :: [ConstructorFieldPath] -> Either Text ()
requireUniqueFields fields =
  require
    (length fields == length (nub fields))
    "constructor field paths are not unique"

strictlyIncreasing :: Ord a => [a] -> Bool
strictlyIncreasing values = and (zipWith (<) values (drop 1 values))

require :: Bool -> Text -> Either Text ()
require True _ = Right ()
require False message = Left message
