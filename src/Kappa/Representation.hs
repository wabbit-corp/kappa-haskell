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
  )
import Kappa.Core (GName, Literal (..), Term (..))
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

contextualIdentityPayload :: RepresentationContext -> Text -> Term -> Text
contextualIdentityPayload context label term =
  T.intercalate
    "\n"
    [ "binders=" <> T.intercalate ";" (map renderTerm (rcBinderTypes context))
    , "constraints=" <> T.intercalate ";" (sort (rcUniverseConstraints context))
    , label <> "=" <> renderTerm term
    ]

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
