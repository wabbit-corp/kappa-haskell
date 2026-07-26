-- | Declaration-universe roles and source-free nominal cumulativity metadata
-- (Spec §11.1.2.3A.2, §30.2.1B).  This module deliberately contains no Core
-- terms: role inference consumes normalized clause requirements produced by
-- the typed checker, and certificate replay consumes the same requirements.
module Kappa.NominalVariance
  ( UniverseVariance (..)
  , RoleRequirement (..)
  , NominalClauseKind (..)
  , NominalExplicitness (..)
  , NominalQuantity (..)
  , NominalBinderContract (..)
  , NominalRoleAction (..)
  , NominalRepresentationAction (..)
  , NominalEvidenceDependency (..)
  , NominalMonotoneWitness (..)
  , NominalClosureClause (..)
  , NominalSignatureClosure (..)
  , SchemaActionCertificateId (..)
  , TypeLevelSemanticVersions (..)
  , currentTypeLevelSemanticVersions
  , NominalCumulativitySummary (..)
  , rolePermitsAnnotation
  , inferUniverseRoles
  , makeNominalSignatureClosure
  , withNominalMonotoneWitnesses
  , nominalEvidenceDependencies
  , nominalClosureRequirements
  , makeNominalCumulativitySummary
  , verifyNominalCumulativitySummary
  , stableNominalHash
  ) where

import Data.Data (Data)
import Data.List (nub, sort, sortOn)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Level
  ( Level (..)
  , NeutralLevelAtom (..)
  , NeutralLevelTerm (..)
  , UniverseConstraint (..)
  , mapNeutralLevelTermLevels
  , neutralLevelTermLevels
  , normalizeLevel
  )
import Kappa.Observation (FormationMode, ObservationMode)
import Kappa.SemanticHash (sha256Hex)

-- | Ordered from least to most permissive.  A written role is accepted only
-- when it is no more permissive than the role inferred from the signature.
data UniverseVariance = Invariant | Covariant | Irrelevant
  deriving stock (Eq, Ord, Show, Enum, Bounded, Data)

data RoleRequirement
  = RequireCovariant !Int !Text
  | RequireInvariant !Int !Text
  deriving stock (Eq, Ord, Show)

data NominalClauseKind
  = ClauseSortDeclaration
  | ClausePointConstructor
  | ClausePathConstructor
  | ClauseHigherBoundary
  | ClauseQuotientEquation
  | ClauseRecursiveOperation
  | ClauseRecursiveEquation
  | ClauseGeneratedProjection
  | ClauseEliminator
  | ClauseComputationRule
  | ClauseTruncationRule
  | ClauseExtension
  deriving stock (Eq, Ord, Show)

data NominalExplicitness = NominalExplicit | NominalImplicit
  deriving stock (Eq, Ord, Show)

data NominalQuantity
  = NominalZero
  | NominalOne
  | NominalOmega
  | NominalAtMostOne
  | NominalAtLeastOne
  deriving stock (Eq, Ord, Show)

-- | Presentation-free contract for one binder in a normalized nominal
-- signature clause. The domain fingerprint is over resolved Core identity and
-- alpha-normalized binders; source binder names and diagnostic prose are not
-- represented here.
data NominalBinderContract = NominalBinderContract
  { nbcObservation :: !ObservationMode
  , nbcFormation :: !FormationMode
  , nbcExplicitness :: !NominalExplicitness
  , nbcQuantity :: !NominalQuantity
  , nbcBorrowed :: !Bool
  , nbcLevelAssumption :: !(Maybe (Text, Text))
  , nbcDomainFingerprint :: !Text
  }
  deriving stock (Eq, Ord, Show)

-- | Replayable semantic actions for one normalized clause.  Diagnostic prose
-- is deliberately absent: a certificate derives role requirements from these
-- actions rather than trusting a second caller-supplied requirement list.
data NominalRoleAction
  = NominalCovariantUse !Int
  | NominalInvariantUse !Int
  deriving stock (Eq, Ord, Show)

-- | Runtime action of a normalized clause.  Schema lifting is erasable only
-- when every clause preserves representation; there is no detached boolean
-- for a producer to assert independently of the closure.
data NominalRepresentationAction
  = NominalPreserveRepresentation
  | NominalTransformRepresentation
  deriving stock (Eq, Ord, Show)

-- | One semantic dependency of selected ordinary monotonicity evidence.
-- Local dependencies use binder levels, not names or de Bruijn indices, so
-- alpha-renaming and telescope presentation do not change certificate
-- identity. Global and constructor dependencies retain resolved identities.
data NominalEvidenceDependency
  = NominalLocalDependency !Int
  | NominalGlobalDependency ![Text] !Text
  | NominalConstructorDependency ![Text] !Text
  | NominalFieldDependency !Text
  deriving stock (Eq, Ord, Show)

-- | Frozen evidence for one neutral one-hole level operator. The goal and
-- evidence are source-free Core artifacts. Proof-object identity is retained
-- for independent replay but is deliberately excluded from the closure hash;
-- the normalized goal and canonical dependency closure are semantic.
data NominalMonotoneWitness = NominalMonotoneWitness
  { nmwParameter :: !Int
  , nmwOperator :: !NeutralLevelTerm
  , nmwGoal :: !NeutralLevelTerm
  , nmwEvidence :: !NeutralLevelTerm
  , nmwDependencies :: ![NominalEvidenceDependency]
  }
  deriving stock (Eq, Ord, Show)

-- | One typed clause in the normalized closure. 'nccIdentity' is the resolved
-- semantic owner identity, not a source label.  Role and representation
-- actions are the certificate replay authority.
data NominalClosureClause = NominalClosureClause
  { nccKind :: !NominalClauseKind
  , nccIdentity :: !Text
  , nccBinders :: ![NominalBinderContract]
  , nccResultFingerprint :: !Text
  , nccRoleActions :: ![NominalRoleAction]
  , nccRepresentationAction :: !NominalRepresentationAction
  }
  deriving stock (Eq, Ord, Show)

-- | Single authority consumed by role inference, certificate replay, closure
-- hashing, and interface validation for current ordinary nominal signatures.
data NominalSignatureClosure = NominalSignatureClosure
  { nscUniverseArity :: !Int
  , nscConstraints :: ![UniverseConstraint]
  , nscSaturationArity :: !Int
  , nscClauses :: ![NominalClosureClause]
  , nscMonotoneWitnesses :: ![NominalMonotoneWitness]
  }
  deriving stock (Eq, Ord, Show)

newtype SchemaActionCertificateId = SchemaActionCertificateId {unSchemaActionCertificateId :: Text}
  deriving stock (Eq, Ord, Show)

-- | Independently versioned semantic layers which make a universe artifact
-- replayable. These are part of every interface and certificate identity;
-- changing any one invalidates the artifact before its evidence is trusted.
data TypeLevelSemanticVersions = TypeLevelSemanticVersions
  { tlsvAlgebra :: !Int
  , tlsvConstructorNormalizer :: !Int
  , tlsvRigidEntailment :: !Int
  , tlsvPrincipalInference :: !Int
  , tlsvCertificate :: !Int
  }
  deriving stock (Eq, Ord, Show)

currentTypeLevelSemanticVersions :: TypeLevelSemanticVersions
currentTypeLevelSemanticVersions = TypeLevelSemanticVersions 1 1 1 1 1

-- | Verified interface fact for one nominal family.  Requirements are kept
-- so a consumer can replay role validity instead of trusting the role vector.
data NominalCumulativitySummary = NominalCumulativitySummary
  { ncsFamilyIdentity :: !Text
  , ncsRoles :: ![UniverseVariance]
  , ncsInferredRoles :: ![UniverseVariance]
  , ncsExplicitRoles :: ![Bool]
  , ncsSaturationArity :: !Int
  , ncsConstraints :: ![UniverseConstraint]
  , ncsRequirements :: ![RoleRequirement]
  , ncsClosureHash :: !Text
  , ncsCertificateId :: !SchemaActionCertificateId
  , ncsCheckerVersion :: !Int
  , ncsSemanticVersions :: !TypeLevelSemanticVersions
  , ncsClauseKinds :: ![NominalClauseKind]
  , ncsRepresentationIdentity :: !Bool
  , ncsExtensionGate :: !(Maybe Text)
  , ncsClosure :: !NominalSignatureClosure
  }
  deriving stock (Eq, Ord, Show)

rolePermitsAnnotation :: UniverseVariance -> UniverseVariance -> Bool
rolePermitsAnnotation written inferred = written <= inferred

inferUniverseRoles :: Int -> [RoleRequirement] -> [UniverseVariance]
inferUniverseRoles parameterCount = foldl' tighten (replicate parameterCount Irrelevant)
  where
    tighten roles = \case
      RequireCovariant index _ -> update index (min Covariant) roles
      RequireInvariant index _ -> update index (const Invariant) roles
    update index f roles
      | index < 0 || index >= length roles = roles
      | otherwise = case splitAt index roles of
          (before, role : after) -> before ++ f role : after
          _ -> roles

verifyNominalCumulativitySummary :: NominalCumulativitySummary -> Bool
verifyNominalCumulativitySummary summary =
  not (T.null (ncsFamilyIdentity summary))
    && ncsCheckerVersion summary == 1
    && ncsSemanticVersions summary == currentTypeLevelSemanticVersions
    && ncsRepresentationIdentity summary
    && length effective == length inferred
    && length effective == length (ncsExplicitRoles summary)
    && ncsConstraints summary == canonicalConstraints (ncsConstraints summary)
    && ncsClosure summary == canonicalClosure (ncsClosure summary)
    && all validMonotoneWitness (nscMonotoneWitnesses (ncsClosure summary))
    && ncsConstraints summary == nscConstraints (ncsClosure summary)
    && ncsSaturationArity summary == nscSaturationArity (ncsClosure summary)
    && length effective == nscUniverseArity (ncsClosure summary)
    && canonicalRequirements (ncsRequirements summary) == canonicalRequirements (nominalClosureRequirements (ncsClosure summary))
    && ncsClauseKinds summary == closureClauseKinds (ncsClosure summary)
    && ncsRepresentationIdentity summary == closurePreservesRepresentation (ncsClosure summary)
    && inferred == inferUniverseRoles (length inferred) (ncsRequirements summary)
    && and (zipWith rolePermitsAnnotation effective inferred)
    && ncsClosureHash summary == stableNominalHash (summaryPayload summary)
    && ncsCertificateId summary == certificateIdFor (ncsClosureHash summary)
  where
    effective = ncsRoles summary
    inferred = ncsInferredRoles summary
    validMonotoneWitness witness =
      nmwParameter witness >= 0
        && nmwParameter witness < length effective
        && nmwDependencies witness
          == nominalEvidenceDependencies [nmwGoal witness, nmwEvidence witness]

makeNominalSignatureClosure
  :: Int
  -> [UniverseConstraint]
  -> Int
  -> [NominalClosureClause]
  -> NominalSignatureClosure
makeNominalSignatureClosure universeArity constraints saturation clauses =
  canonicalClosure
    (NominalSignatureClosure universeArity constraints saturation clauses [])

withNominalMonotoneWitnesses
  :: [NominalMonotoneWitness]
  -> NominalSignatureClosure
  -> NominalSignatureClosure
withNominalMonotoneWitnesses witnesses closure =
  canonicalClosure closure {nscMonotoneWitnesses = witnesses}

makeNominalCumulativitySummary
  :: Text
  -> [UniverseVariance]
  -> [Bool]
  -> NominalSignatureClosure
  -> Maybe Text
  -> NominalCumulativitySummary
makeNominalCumulativitySummary familyIdentity effective explicit closure0 extensionGate = summary
  where
    closure = canonicalClosure closure0
    saturation = nscSaturationArity closure
    constraints = nscConstraints closure
    requirements = nominalClosureRequirements closure
    clauseKinds = closureClauseKinds closure
    inferred = inferUniverseRoles (length effective) requirements
    skeleton =
      NominalCumulativitySummary
        { ncsFamilyIdentity = familyIdentity
        , ncsRoles = effective
        , ncsInferredRoles = inferred
        , ncsExplicitRoles = explicit
        , ncsSaturationArity = saturation
        , ncsConstraints = canonicalConstraints constraints
        , ncsRequirements = requirements
        , ncsClosureHash = ""
        , ncsCertificateId = SchemaActionCertificateId ""
        , ncsCheckerVersion = 1
        , ncsSemanticVersions = currentTypeLevelSemanticVersions
        , ncsClauseKinds = clauseKinds
        , ncsRepresentationIdentity = closurePreservesRepresentation closure
        , ncsExtensionGate = extensionGate
        , ncsClosure = closure
        }
    digest = stableNominalHash (summaryPayload skeleton)
    summary = skeleton {ncsClosureHash = digest, ncsCertificateId = certificateIdFor digest}

certificateIdFor :: Text -> SchemaActionCertificateId
certificateIdFor digest = SchemaActionCertificateId ("schema:certificate.h" <> digest)

summaryPayload :: NominalCumulativitySummary -> Text
summaryPayload summary =
  T.pack
    ( show
        ( ncsFamilyIdentity summary
        , ncsInferredRoles summary
        , ncsRoles summary
        , ncsExplicitRoles summary
        , ncsSaturationArity summary
        , ncsConstraints summary
        , canonicalRequirements (ncsRequirements summary)
        , ncsCheckerVersion summary
        , ncsSemanticVersions summary
        , ncsClauseKinds summary
        , ncsRepresentationIdentity summary
        , ncsExtensionGate summary
        , closurePayload (ncsClosure summary)
        )
    )

-- Diagnostic explanations deliberately retain source-facing names, but the
-- normalized signature identity may depend only on typed obligations.  Sort
-- and deduplicate so declaration traversal order is not an identity input.
canonicalRequirements :: [RoleRequirement] -> [(Int, Int)]
canonicalRequirements = sort . nub . map (\case
  RequireCovariant index _ -> (index, 1)
  RequireInvariant index _ -> (index, 0))

canonicalConstraints :: [UniverseConstraint] -> [UniverseConstraint]
canonicalConstraints = sort . nub . map (\constraint ->
  constraint
    { ucLower = normalizeLevel (ucLower constraint)
    , ucUpper = normalizeLevel (ucUpper constraint)
    })

canonicalClosure :: NominalSignatureClosure -> NominalSignatureClosure
canonicalClosure closure =
  closure
    { nscConstraints = canonicalConstraints (nscConstraints closure)
    , nscClauses = sort (map canonicalClause (nscClauses closure))
    , nscMonotoneWitnesses =
        sortOn monotoneWitnessSemanticKey
          (map canonicalMonotoneWitness (nscMonotoneWitnesses closure))
    }
  where
    canonicalClause clause =
      clause {nccRoleActions = sort (nub (nccRoleActions clause))}

canonicalMonotoneWitness :: NominalMonotoneWitness -> NominalMonotoneWitness
canonicalMonotoneWitness witness =
  witness
    { nmwOperator = mapNeutralLevelTermLevels normalizeLevel (nmwOperator witness)
    , nmwGoal = mapNeutralLevelTermLevels normalizeLevel (nmwGoal witness)
    , nmwEvidence = mapNeutralLevelTermLevels normalizeLevel (nmwEvidence witness)
    , nmwDependencies = sort . nub $ nmwDependencies witness
    }

monotoneWitnessSemanticKey
  :: NominalMonotoneWitness
  -> (Int, NeutralLevelTerm, NeutralLevelTerm, [NominalEvidenceDependency])
monotoneWitnessSemanticKey witness =
  ( nmwParameter witness
  , nmwOperator witness
  , nmwGoal witness
  , nominalEvidenceDependencies [nmwGoal witness]
  )

nominalEvidenceDependencies :: [NeutralLevelTerm] -> [NominalEvidenceDependency]
nominalEvidenceDependencies = sort . nub . concatMap termDependencies
  where
    termDependencies term = direct term ++ concatMap levelDependencies (neutralLevelTermLevels term)
    direct = \case
      NLTLocal level -> [NominalLocalDependency level]
      NLTLocalDeclaration level _ -> [NominalLocalDependency level]
      NLTGlobal owner name _ -> [NominalGlobalDependency owner name]
      NLTConstruct owner name _ arguments ->
        NominalConstructorDependency owner name
          : concatMap (termDependencies . snd) arguments
      NLTApply _ function argument -> termDependencies function ++ termDependencies argument
      NLTProject field receiver -> NominalFieldDependency field : termDependencies receiver
      NLTLevel level -> levelDependencies level
      NLTLiteral _ -> []
      NLTRecord fields -> concatMap (termDependencies . snd) fields
      NLTIf condition yes no ->
        termDependencies condition ++ termDependencies yes ++ termDependencies no
      NLTUnsupported _ -> []
    levelDependencies = \case
      LSucc level -> levelDependencies level
      LAdd left right -> levelDependencies left ++ levelDependencies right
      LMax left right -> levelDependencies left ++ levelDependencies right
      LNeutral (NeutralLevelTermAtom _ term) -> termDependencies term
      LNeutral (NeutralLevelSymbol _ arguments) -> concatMap levelDependencies arguments
      _ -> []

nominalClosureRequirements :: NominalSignatureClosure -> [RoleRequirement]
nominalClosureRequirements = nub . sort . concatMap clauseRequirements . nscClauses
  where
    clauseRequirements clause = map actionRequirement (nccRoleActions clause)
    actionRequirement = \case
      NominalCovariantUse index ->
        RequireCovariant index "normalized signature action requires covariance"
      NominalInvariantUse index ->
        RequireInvariant index "normalized signature action requires invariance"

closurePreservesRepresentation :: NominalSignatureClosure -> Bool
closurePreservesRepresentation closure =
  not (null (nscClauses closure))
    && all ((== NominalPreserveRepresentation) . nccRepresentationAction) (nscClauses closure)

closureClauseKinds :: NominalSignatureClosure -> [NominalClauseKind]
closureClauseKinds = nub . sort . map nccKind . nscClauses

closurePayload :: NominalSignatureClosure -> Text
closurePayload closure =
  T.pack . show $
    ( nscUniverseArity canonical
    , nscConstraints canonical
    , nscSaturationArity canonical
    , [ ( nccKind clause
        , nccIdentity clause
        , nccBinders clause
        , nccResultFingerprint clause
        , nccRoleActions clause
        , nccRepresentationAction clause
        )
      | clause <- nscClauses canonical
      ]
    , map monotoneWitnessSemanticKey (nscMonotoneWitnesses canonical)
    )
  where
    canonical = canonicalClosure closure

-- | Stable SHA-256 digest used as a semantic interface fingerprint. Semantic
-- equality is established from the canonical payload retained by the
-- interface; this digest is only an indexed lookup/check hint.
stableNominalHash :: Text -> Text
stableNominalHash =
  sha256Hex . ("KAPPA:v1:NominalSignature:" <>)
