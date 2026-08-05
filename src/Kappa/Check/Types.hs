-- | The data dictionary for elaboration: every type declaration that
-- "Kappa.Check" threads through the checker.
--
-- These live in their own module for a structural reason worth knowing before
-- you go looking in here for the rest of @Kappa.Check@. That module's
-- elaboration kernel is a single mutually-recursive cycle of roughly 285
-- definitions spanning almost every topic in the file, so its /functions/
-- cannot be split along topic lines without @.hs-boot@ seams. Its /types/
-- carry no such constraint — a data declaration can never take part in a
-- value-level cycle — so they factor out cleanly, and they give every module
-- later carved out of @Kappa.Check@ a common vocabulary to import.
--
-- The headline types, roughly in the order a reader meets them:
--
--   * 'CtxEntry' and 'Ctx' — the local typing context: what is in scope at a
--     given point, each entry carrying its type, quantity, observation mode,
--     and binder origin. The list of entries /is/ the scope.
--   * 'CheckState' — the global elaboration state threaded through
--     @'CheckM' = State CheckState@: the global, data, constructor and trait
--     tables, registered instances, the metavariable store, deferred level
--     constraints, and accumulated diagnostics.
--   * 'DataInfo', 'CtorInfo', 'TraitInfo', 'InstanceEntry' — the interface
--     facts recorded for each kind of declaration.
--   * 'GlobalDef' — one checked top-level definition.
--
-- Background on the vocabulary these assume (de Bruijn levels, quantities,
-- observation modes, universes): docs\/CONCEPTS.md.
module Kappa.Check.Types
  ( APInfo (..)
  , APResult (..)
  , AppResultPreparation (..)
  , AppSlot (..)
  , ArithmeticCertificateGoalEndpoints (..)
  , ArithmeticIndexTransportResult (..)
  , AuditRecord (..)
  , AuthenticatedLevelProofPolicy (..)
  , CAnn (..)
  , CallEdge (..)
  , CarrierPrefix
  , CaseClass (..)
  , CheckM
  , CheckState (..)
  , CompPlan (..)
  , CompareBoolMatch (..)
  , ConstructorFieldWitness (..)
  , ConstructorSourcePatternSlot (..)
  , CtorInfo (..)
  , Ctx (..)
  , CtxEntry (..)
  , DataInfo (..)
  , DeclarationUniverseRoles (..)
  , DeclarationUniverseScope (..)
  , DeferredExplicitUniverseTreatment (..)
  , DeferredTypeEquality (..)
  , DerivedEqEvidenceBinding (..)
  , DerivedEqEvidenceNames
  , DerivedEqFieldMethod (..)
  , DerivedEqFieldMethods
  , DerivedFunctionalEquality (..)
  , DerivedNominalField (..)
  , DerivedNominalShape
  , DerivedRefinementViewShape (..)
  , EffLabelInfo (..)
  , EffOpInfo (..)
  , EffectOpValueInfo (..)
  , EvidenceCacheKey (..)
  , EvidenceConstructionMode (..)
  , ExpectedImplicitSlot (..)
  , ExplicitRefOp (..)
  , FrozenMonotoneEvidence
  , FrozenMonotoneKey
  , GeneratedConstraintInterface (..)
  , GeneratedProofEnvironment (..)
  , GeneratedProofScope (..)
  , InferredMeasureShape (..)
  , InoutParamInfo (..)
  , InstanceEntry (..)
  , InstanceMemberTermination (..)
  , InstanceTrial
  , InstantiatedRefinementField (..)
  , LevelConstraintKey (..)
  , LevelConstraintProvenance (..)
  , LevelOperatorIdentity (..)
  , LocalLetItem (..)
  , LocalMetaBinder (..)
  , LocalNominalCapture (..)
  , LocalRecursiveSchemaOccurrence (..)
  , LocalRecursiveSchemaScope (..)
  , LocalUniverseInfo (..)
  , MeasureCall (..)
  , MeasureSpec (..)
  , MetaClassifier (..)
  , NamedHole (..)
  , NormCacheKey (..)
  , ObservationClassifier (..)
  , ObservationJudgment (..)
  , PartialCall (..)
  , PatKey (..)
  , PatternRefinements (..)
  , PendingDiscardedResult (..)
  , PendingEvidenceAttempt
  , PendingEvidenceDependency (..)
  , PendingEvidenceDependencyVersion (..)
  , PendingEvidenceEntry
  , PendingEvidenceGraph (..)
  , PendingLevelEvidence (..)
  , PendingNominalSummary (..)
  , PlaceDemand (..)
  , PosData (..)
  , PosField (..)
  , PreInstance (..)
  , PrincipalBoundaryFailure (..)
  , PrincipalBoundaryResult (..)
  , ProjInfo (..)
  , ProofNormalizationProvider (..)
  , PropCacheKey (..)
  , ProviderLawRole (..)
  , ProvisionalUniverseFacet (..)
  , ProvisionalUniverseInstantiation (..)
  , QCard (..)
  , RecursiveSchemaEdge (..)
  , RecursiveSchemaOccurrence (..)
  , RecursiveSchemaRelation (..)
  , RefOpEvidence (..)
  , RelationFlavor (..)
  , RelationSpec (..)
  , RootsSupply (..)
  , SccReferenceMode (..)
  , ScopedBoolFact (..)
  , SelectedUniverseEvidence (..)
  , SrcInfo (..)
  , SrcKind (..)
  , StandardArithmeticOperation (..)
  , StandardCheckedPredicate (..)
  , StandardCheckedPredicateSemantics (..)
  , StructuralOrigin (..)
  , StructuralOrigins (..)
  , StructuralShape (..)
  , StructuralStep (..)
  , SyntheticConstructorPatternLayout (..)
  , TermFun (..)
  , ThisMode (..)
  , TopLevelDataHeader (..)
  , TraitInfo (..)
  , UniverseInferenceClass (..)
  , UniverseInferenceRecord (..)
  , UniversePublicationConsumers
  , UnsafeConfig (..)
  , VarInoutRewriteMode (..)
  , VarInoutTarget (..)
  , VarInoutWriteBack (..)
  , VarReadBlock (..)
  , VarRefInfo (..)
  ) where

import Control.Monad.State.Strict
import Data.Data (Data)
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Kappa.Check.Pending
  ( DependencySnapshot
  )
import Kappa.Core
import Kappa.Diagnostic
import Kappa.Eval
import Kappa.Level
  ( Assumptions
  , ConstraintOrigin (..)
  , LevelMeta
  , LevelConstraint (..)
  , LevelAssignmentGraphBudget
  , LevelSolveError (..)
  , PrincipalNonLeastWitness (..)
  )
import Kappa.NominalVariance
import Kappa.Ownership (OwnInfo)
import Kappa.Source
import Kappa.Syntax hiding (CompClause (..), Quantity (..))
import qualified Kappa.Syntax as S
import Kappa.Termination hiding (expandedGlobalsOfTerm)

data DataInfo = DataInfo
  { diCtors :: ![GName]
  , diParamCount :: !Int
  , diLevel :: !Level
  }

data CtorInfo = CtorInfo
  { ciData :: !GName
  , ciUniverses :: !DeclarationUniverseTelescope
  , ciType :: !Term
  , ciFields :: ![(Maybe Text, Maybe Expr)] -- ^ explicit fields: name, default (§10.1.1; elaborated at the application site)
  , ciSourceFields :: ![(Icit, Maybe Text)]
  -- ^ Every source constructor field, including erased implicit proof fields.
  -- Family parameters, generated universe evidence, and trait premises are
  -- intentionally absent: they are constructor-interface binders, not fields.
  }

-- | Whether arbitrary complete evidence values of a trait application may be
-- constructed by checked source elaboration (§14.1.1/§14.1.1A).  The
-- independently-unique case is installed only after the declaration's
-- certificate has been validated; an absent or invalid clause never silently
-- upgrades sealed-coherent evidence.
data EvidenceConstructionMode
  = SealedCoherent
  | IndependentlyUnique
  deriving stock (Eq, Show)

data TraitInfo = TraitInfo
  { tiParamCount :: !Int
  , tiMembers :: ![Text]
  , tiMemberModes :: !(Map Text ObservationMode)
  , tiAssociatedStaticMembers :: !(Set Text)
  -- ^ Members classified by the independent §11.1.6.1 compile-time-type
  -- judgment. This must not be inferred from observation mode: a static
  -- predicate family may be ordinary-observed at @(n : Nat) -> Type@.
  , tiMemberQs :: !(Map Text Q)
  -- ^ Associated static members and members whose checked result is known
  -- 'RuntimeErased' are quantity-zero dictionary fields. Ordinary runtime
  -- methods retain quantity omega.
  , tiDefaults :: !(Map Text GName)
  -- ^ Ordinary defaults elaborated once in the abstract trait context
  -- (§14.2). Each identity names a hidden checked Core template with the same
  -- universe/type telescope as the member accessor. No source syntax crosses
  -- the declaration or module boundary.
  , tiSupers :: ![(Text, Term)]
  -- ^ supertrait premises as (evidence field name, @\\params -> C params@)
  -- (§14.1.4); the field carries the supertrait dictionary (§14.3.3)
  , tiDerivedMembers :: !(Set Text)
  -- ^ Members explicitly declared with @derive@. Missing instance
  -- definitions for these fields are checked derivation obligations.
  , tiDerivedSupers :: !(Set Text)
  -- ^ Supertrait dictionary fields whose declarations carry @derive@.
  , tiEvidenceConstructionMode :: !EvidenceConstructionMode
  -- ^ Compiler-validated evidence introduction authority.  Coherence of
  -- ordinary instances alone does not grant fresh construction.
  }

-- | Compiler-owned §15.8.2 proof-normalization provider metadata.  The
-- identities below are resolved semantic object identities, not source
-- spellings.  A provider is useful only after 'providerLawProof' has checked
-- the selected evidence and instantiated member telescope against the exact
-- equality goal, so this table grants no proof authority by itself.
data ProofNormalizationProvider = ProofNormalizationProvider
  { pnpIdentity :: !Text
  , pnpTheory :: !ArithmeticNormalizationTheory
  , pnpLawRole :: !ProviderLawRole
  , pnpOperationIdentities :: ![GName]
  , pnpEvidenceTrait :: !GName
  , pnpLawOwner :: !GName
  , pnpLawField :: !Text
  , pnpLawIdentity :: !GName
  , pnpNormalFormVersion :: !Integer
  , pnpProviderVersion :: !Integer
  , pnpCheckerVersion :: !Integer
  }

data ProviderLawRole
  = ProviderLeftIdentity
  | ProviderRightIdentity
  | ProviderCommutative

data ArithmeticIndexTransportResult
  = ArithmeticIndexTransportApplied !Term
  | ArithmeticIndexTransportBlocked !(Set MetaId)
  | ArithmeticIndexTransportNotApplicable

data InstanceEntry = InstanceEntry
  { ieTrait :: !GName
  , ieTraitUniverses :: ![Level]
  -- ^ Universe instantiation of the trait head, under the dictionary schema.
  , ieUniverses :: !DeclarationUniverseTelescope
  , ieTeleLen :: !Int
  , iePremises :: ![Term] -- ^ de Bruijn under the telescope
  , ieHead :: ![Term] -- ^ trait arguments under the telescope
  , ieDict :: !GName
  }

-- | A branch-local boolean fact together with the lexical depth at which its
-- Core term was checked. Facts may outlive that exact context through a
-- postponed implicit goal or through bindings introduced inside the branch.
-- Retaining the source depth lets every consumer weaken the term into its
-- current context instead of silently retargeting de Bruijn indices.
data ScopedBoolFact = ScopedBoolFact !Int !Term !Bool

-- | An instance head elaborated and registered ahead of the body pass,
-- so instance visibility within a module does not depend on
-- declaration order (§14.3: "Instance visibility is global over the
-- compilation unit's module closure"). The members are checked later,
-- in source order, by 'elabInstance'.
data PreInstance = PreInstance
  { piTrait :: !GName
  , piFvTele :: !Telescope -- ^ inferred implicitly-universalized head binders (§11.3.3)
  , piPremTms :: ![Term] -- ^ premise types, elaborated under 'piFvs'
  , piArgTms :: ![Term] -- ^ head arguments, under 'piFvs' + premises
  , piDictG :: !GName -- ^ the dictionary global (type already registered)
  }

-- | Typed semantic identity for a transparent definition proven equivalent
-- to one of the solver-admitted TypeLevel operations. Unlike the captured
-- source equation, this metadata is suitable for transport across a typed
-- module/interface boundary.
data LevelOperatorIdentity
  = LevelOperatorZero
  | LevelOperatorOne
  | LevelOperatorSucc
  | LevelOperatorAdd
  | LevelOperatorMax
  | LevelOperatorFromInteger
  | LevelOperatorLt
  | LevelOperatorLe
  deriving stock (Eq, Ord, Show)

-- | One fresh use of an inferred declaration's provisional universe
-- telescope. Header elaboration can reference a declaration before its SCC has
-- selected the principal telescope, so the use records the source-to-fresh
-- substitution. At the SCC boundary we instantiate the callee's completed
-- provisional constraints through this substitution before solving callers.
data ProvisionalUniverseFacet
  = ProvisionalGlobalFacet
  | ProvisionalConstructorFacet
  deriving stock (Eq, Ord, Show)

data ProvisionalUniverseInstantiation = ProvisionalUniverseInstantiation
  { puiIdentity :: !Int
  , puiFacet :: !ProvisionalUniverseFacet
  , puiOwner :: !GName
  , puiConsumer :: !(Maybe GName)
  , puiSourceMetas :: ![LevelMeta]
  , puiFreshLevels :: ![Level]
  , puiConstraintsMaterialized :: !Bool
  , puiMaterializedConstraintIds :: !(Set Int)
  }

-- | Provenance for a deduplicated deferred level judgment. A constraint may
-- be registered directly by source elaboration and also be reproduced by one
-- or more provisional declaration occurrences. Retiring an occurrence may
-- remove the judgment only when no ordinary registration and no surviving
-- occurrence still owns it.
data LevelConstraintProvenance = LevelConstraintProvenance
  { lcpOrdinary :: !Bool
  , lcpProvisionalOccurrences :: !(Set Int)
  }

-- | One closure-converted argument of a block/do-local nominal family
-- (§30.1.1).  The level is the declaration-site de Bruijn level, so a use in
-- any nested lexical context can recover the same binder without consulting
-- its (possibly shadowed) source spelling.
data LocalNominalCapture = LocalNominalCapture
  { lncName :: !Text
  , lncLevel :: !Int
  }
  deriving stock (Eq, Ord, Show)

-- | A nominal declaration whose universe-role summary must be built only
-- after declaration-SCC universe generalization has replaced provisional
-- level metas by the family's stable hidden telescope.  Constructing the
-- certificate in the header pass would make its role arity and closure hash
-- stale as soon as that generalization runs.
data PendingNominalSummary
  = PendingDataNominalSummary !(Maybe UniverseSchema) !Int ![GName] !Span
  | PendingTraitNominalSummary !(Maybe UniverseSchema) !Int ![Term] !Span

data RecursiveSchemaRelation
  = RecursiveSchemaIdentity
  | RecursiveSchemaLowerOrEqual
  | RecursiveSchemaStrictLower
  deriving stock (Eq, Ord, Show)

data RecursiveSchemaEdge = RecursiveSchemaEdge
  { rseCaller :: !GName
  , rseCallee :: !GName
  , rseRelation :: !RecursiveSchemaRelation
  }
  deriving stock (Eq, Ord, Show)

data RecursiveSchemaOccurrence = RecursiveSchemaOccurrence
  { rsoCaller :: !GName
  , rsoCallee :: !GName
  , rsoLevels :: ![Level]
  , rsoExplicit :: !Bool
  , rsoAssumptions :: !Assumptions
  , rsoSpan :: !Span
  }
  deriving stock (Eq, Show)

data LocalRecursiveSchemaScope = LocalRecursiveSchemaScope
  { lrssCaller :: !Int
  , lrssMembers :: !(Map Int Text)
  , lrssCurrentInstance :: ![Level]
  }
  deriving stock (Eq, Show)

data LocalRecursiveSchemaOccurrence = LocalRecursiveSchemaOccurrence
  { lrsoCaller :: !Int
  , lrsoCallee :: !Int
  , lrsoLevels :: ![Level]
  , lrsoExplicit :: !Bool
  , lrsoAssumptions :: !Assumptions
  , lrsoSpan :: !Span
  }
  deriving stock (Eq, Show)

data InstanceMemberTermination = InstanceMemberTermination
  { imtName :: !Text
  , imtType :: !Value
  , imtBinders :: ![Binder]
  , imtDecreases :: !(Maybe Decreases)
  , imtBody :: !Term
  , imtSpan :: !Span
  }

data SelectedUniverseEvidence = SelectedUniverseEvidence
  { sueGoal :: !Text
  , sueEvidence :: !GName
  }
  deriving stock (Eq, Ord, Show)

data UniverseInferenceClass
  = InferenceSolvedPrincipal
  | InferenceUnsatisfiable
  | InferenceNoPointwiseLeastSolution
  | InferenceOutsidePortableInferenceFragment
  | InferenceBlockedByUnselectedMetas
  deriving stock (Eq, Ord, Show, Data)

data UniverseInferenceRecord = UniverseInferenceRecord
  { uirClass :: !UniverseInferenceClass
  , uirPrincipalAssignments :: !(Map LevelMeta Level)
  }
  deriving stock (Eq, Ord, Show, Data)

data PendingLevelEvidence = PendingLevelEvidence
  { pleOwner :: !GName
  , pleConstraint :: !UniverseConstraint
  }
  deriving stock (Eq, Ord, Show)

data PendingEvidenceDependency
  = PendingTermMeta !MetaId
  | PendingLevelMeta !LevelMeta
  | PendingGlobal !GName
  deriving stock (Eq, Ord, Show)

data PendingEvidenceDependencyVersion
  = PendingTermMetaVersion !Int
  | PendingLevelMetaVersion !(Maybe Level)
  | PendingGlobalVersion
      !(Maybe (DeclarationUniverseTelescope, Maybe Term, Maybe Term, Bool))
      !(Maybe (DeclarationUniverseTelescope, Term))
  deriving stock (Eq, Show)

type PendingEvidenceAttempt =
  DependencySnapshot
    PendingEvidenceDependency
    PendingEvidenceDependencyVersion

-- | A top-level data family whose source header has not yet been published,
-- or whose real family classifier has been published while constructor
-- interfaces are still pending. Forward references force only the first
-- transition, so constructor elaboration always sees real family classifiers
-- without perturbing ordinary declaration ordering.
data TopLevelDataHeader
  = PendingTopLevelDataHeader !DataDecl !Span
  | PreparedTopLevelDataHeader !Telescope !Term !Level

-- | A declaration facet whose physical generated-proof prefix participates in
-- interface publication. A data/type global and a same-spelled constructor are
-- distinct facets, so 'GName' alone is not a sufficient publication identity.
data GeneratedConstraintInterface
  = GeneratedGlobalInterface !GName
  | GeneratedConstructorInterface !GName
  deriving stock (Eq, Ord, Show)

-- | The classifier known at the point an inference metavariable is created.
-- Generalization is deliberately fail-closed: only metas with an exact
-- classifier at the completed declaration's lexical depth may be abstracted.
-- Metas created as recovery holes or without a checked domain have no entry.
data MetaClassifier = MetaClassifier
  { micDepth :: !Int
  , micType :: !Term
  , micUniverseCoercion :: !(Maybe UniverseEvidence)
  -- ^ A solved kind-like meta still denotes a term at this declared
  -- classifier. NbE deliberately erases cumulative lifts, so retain the
  -- selected proof here and restore it when the solution is reified to Core.
  }
  deriving stock (Eq, Show)

-- | A constructor-field placeholder whose value occurs in a later field or
-- result. Pattern elaboration must connect that placeholder to the field's
-- branch-local binder before checking the dependent suffix. TypeLevel fields
-- live in the level solver; all other fields live in the ordinary term-meta
-- solver.
data ConstructorFieldWitness
  = ConstructorTermWitness !MetaId
  | ConstructorLevelWitness !MetaId
  deriving stock (Eq, Show)

-- | One source-field position in a constructor elimination telescope.
-- Explicit fields consume a source pattern. Implicit fields are omitted from
-- surface patterns but still introduce an erased branch binder at this exact
-- position, preserving dependencies on earlier explicit fields.
data ConstructorSourcePatternSlot
  = ConstructorExplicitPatternSlot
      !ObservationMode
      !Q
      !Value
      !(Maybe ConstructorFieldWitness)
  | ConstructorHiddenPatternSlot
      !ObservationMode
      !Q
      !Value
      !ConstructorFieldWitness
      !(Maybe (Level, Level))

-- | A compiler-generated constructor pattern together with the branch layout
-- authenticated by the constructor's instantiated source telescope.
--
-- 'scplExplicitBinderIndices' is parallel to the supplied explicit patterns.
-- An entry is present exactly when that pattern introduces one binder; the
-- index is the de Bruijn index at which the branch body reads it.  Hidden
-- source fields therefore affect the index without appearing in the surface
-- pattern list.
data SyntheticConstructorPatternLayout = SyntheticConstructorPatternLayout
  { scplPattern :: !CorePat
  , scplExplicitBinderIndices :: ![Maybe Int]
  , scplBinderCount :: !Int
  }

data LocalMetaBinder = LocalMetaBinder
  { lmbMeta :: !MetaId
  , lmbFormation :: !FormationMode
  , lmbName :: !Text
  , lmbDomain :: !Term
  }
  deriving stock (Eq, Show)

-- | One non-final do-item result whose value is discarded (§18.2).
-- Keep the checked semantic type and lexical context until declaration
-- closeout: later statements may solve its metas, and only the finalized type
-- can justify the QTT droppability decision.
data PendingDiscardedResult = PendingDiscardedResult
  { pdrSpan :: !Span
  , pdrCtx :: !Ctx
  , pdrType :: !Value
  }

-- | A type equality whose normalization is blocked by postponed evidence.
-- The checker must not accept it merely because an evidence metavariable is
-- connected, nor should it emit a derivative mismatch before the root
-- evidence obligation is settled. The declaration boundary replays the
-- equality after its dependencies resolve; a diagnosed dependency owns the
-- failure and suppresses only the redundant mismatch.
data DeferredTypeEquality = DeferredTypeEquality
  { dteSpan :: !Span
  , dteCtx :: !Ctx
  , dteActual :: !Value
  , dteExpected :: !Value
  , dteEvidenceDependencies :: !(Set MetaId)
  }

data LevelConstraintKey
  = LevelConstraintKey
      !(Maybe GName)
      !(Maybe Span)
      !Level
      !Level
      !ConstraintOrigin
      ![(Level, Level)]
  deriving stock (Eq, Ord)

data CheckState = CheckState
  { csGlobals :: !(Map GName GlobalDef)
  , csDatas :: !(Map GName DataInfo)
  , csCtors :: !(Map GName CtorInfo)
  , csTopLevelDataHeaders :: !(Map GName TopLevelDataHeader)
  , csTraits :: !(Map GName TraitInfo)
  , csBareTraitMembers :: !(Map GName (GName, Text))
  -- ^ Exact compiler-generated bare member accessor -> owning trait/member.
  -- Semantic provider decoders use this identity instead of trusting a
  -- source-level member spelling.
  , csTraitMemberOwners :: !(Map GName GName)
  -- ^ Every generated member accessor, bare or qualified, mapped to the exact
  -- owning trait identity. Universe generalization uses this relation to keep
  -- the owner-trait schema as the accessor's leading hidden prefix.
  , csInstances :: ![InstanceEntry]
  , csInstancesByTrait :: !(Map GName [InstanceEntry])
  -- ^ Deterministic trait-identity partition of 'csInstances'. Instance
  -- search is on the elaboration hot path and must not scan and sort the
  -- complete module instance set for every evidence goal. The authoritative
  -- list is retained for serialization and declaration-order-independent
  -- coherence checks; 'setCheckInstances' keeps both views synchronized.
  , csInstanceUniverseInterfaces :: !(Map GName [Term])
  -- ^ Dictionary-identity index of the normalized instance head and premises.
  -- Universe interface discovery visits every declaration in an SCC; looking
  -- each dictionary up by scanning 'csInstances' made that pass quadratic in
  -- prelude size. 'setCheckInstances' is the sole bulk-update path and keeps
  -- this derived index synchronized with the authoritative ordered list.
  , csMetas :: !MetaState
  , csSolvedMetas :: !(Set MetaId)
  -- ^ Exact derived index of solved entries in 'csMetas'. Pending-evidence
  -- fixed-point detection consults this directly instead of filtering the
  -- complete meta store on every pass. Point updates and transactional
  -- restores must keep the two fields synchronized.
  , csMetaAssignmentGenerations :: !(Map MetaId Int)
  -- ^ Monotone per-meta assignment generations. Observational inference
  -- probes compare these identities instead of re-quoting arbitrary solved
  -- values, which may have no recorded creation depth. Fresh metas are
  -- intentionally absent from the caller's domain and therefore cannot make
  -- an otherwise read-only probe look stateful.
  , csNextMeta :: !Int
  , csMetaClassifiers :: !(Map MetaId MetaClassifier)
  , csApplicationPlanningMetas :: !(Set MetaId)
  -- ^ Classifier-authenticated placeholders created while a checked
  -- application spine is being planned. The bounded higher-order unifier may
  -- abstract only these compiler-owned, scope-local identities; an arbitrary
  -- bare meta with the same shape is not planning evidence.
  , csFirstClassLevelMetas :: !(Set MetaId)
  -- ^ Checker-created term metavariables whose authenticated classifier is
  -- @TypeLevel@. They share their stable identity with 'LMeta' while the
  -- universe solver is active. Even when a bound simplifies to a tautology
  -- (for example @succ ?u <= omega@), module closeout must install the least
  -- level back into the term meta rather than leave an unsolved proof goal.
  , csLevelConstraints :: ![LevelConstraint]
  -- ^ Deferred universe inequalities. Unlike ordinary unification goals,
  -- these are solved as a set so least assignments do not depend on traversal
  -- order (§11.1.3).
  , csLevelConstraintOwners :: !(Map Int GName)
  -- ^ Declaration identity for constraints registered while checking a body.
  -- The low-level solver remains independent of Core names; this side table
  -- lets a telescope extension refresh only its own pending constraints.
  , csLevelConstraintsByOwner :: !(Map GName [LevelConstraint])
  -- ^ Derived owner partition of 'csLevelConstraints'. This is maintained at
  -- insertion and rebuilt after every bulk constraint rewrite. Universe SCC
  -- passes use it to avoid rescanning the complete module graph for each
  -- declaration component; the authoritative ordering and ownerless
  -- constraints remain in 'csLevelConstraints'.
  , csLevelConstraintSpans :: !(Map Int Span)
  -- ^ Source provenance for each deferred inequality. Locations stay outside
  -- the pure level solver, but must survive until declaration closeout so
  -- equal ownerless failures in distinct declarations are not coalesced or
  -- reported at a synthetic line.
  , csLevelConstraintIndex :: !(Map LevelConstraintKey Int)
  -- ^ Semantic deduplication index for deferred inequalities. Constraint
  -- insertion is on the declaration hot path; linearly searching the complete
  -- module constraint list made schema occurrence materialization quadratic.
  -- Owner and source provenance are part of identity because equal judgments
  -- in distinct declaration fragments must retain distinct diagnostics.
  , csLevelConstraintProvenance :: !(Map Int LevelConstraintProvenance)
  -- ^ Reference-counted semantic origin of each deduplicated judgment.
  -- Provisional occurrence constraints are discarded with their obsolete
  -- source telescope only when no ordinary or surviving occurrence owns them.
  , csUniverseDiagnosticSpan :: !(Maybe Span)
  -- ^ Nearest source conversion site while a level inequality is registered.
  -- Nested conversions replace it transactionally; generated constraints
  -- without a source occurrence deliberately retain no entry.
  , csNextLevelConstraint :: !Int
  , csLevelAssignments :: !(Map LevelMeta Level)
  , csLevelAssignmentDependents :: !(Map LevelMeta (Set LevelMeta))
  , csLevelAssignmentBudget :: !LevelAssignmentGraphBudget
  -- ^ Reverse edges for the installed substitution graph. Assignment
  -- installation follows only this affected closure, while the paired opaque
  -- budget certificate revalidates only affected roots instead of rescanning
  -- every older declaration-local assignment after each solver result.
  , csLevelGeneralizableMetas :: !(Set LevelMeta)
  -- ^ Universe metas occurring in source or generated binder domains at the
  -- moment those binders are elaborated. This is declaration-schema
  -- provenance, not a post-solve shape guess: a fresh dependency occurrence
  -- that later solves to the same level cannot acquire this role.
  , csLevelGeneralizableOwners :: !(Map LevelMeta (Set GName))
  -- ^ Declaration ownership for the same role. A level can be a source
  -- parameter of one declaration and only a specialized occurrence in
  -- another; SCC generalization must not copy the former's schema into the
  -- latter.
  , csLevelGeneralizableMetasByOwner :: !(Map GName (Set LevelMeta))
  -- ^ Reverse owner index for incremental declaration closeout. Both
  -- directions are updated at the same provenance-registration boundary.
  , csLevelInstantiationMetas :: !(Set LevelMeta)
  -- ^ Metas created solely by fresh specialization of another declaration's
  -- hidden universe telescope. They are elaboration choices, not source
  -- polymorphic positions: principal inference minimizes them from their
  -- generated bounds instead of adding them to the referencing declaration's
  -- schema.
  , csLevelInstantiationOwners :: !(Map LevelMeta (Set GName))
  -- ^ Declaration components whose elaboration introduced each occurrence
  -- meta. Metas allocated outside an active declaration remain only in the
  -- authoritative set above and are conservatively treated as unowned.
  , csLevelInstantiationMetasByOwner :: !(Map GName (Set LevelMeta))
  -- ^ Reverse owner index for occurrence metas. Incremental body solving must
  -- not transpose the complete module relation at each close event.
  , csProvisionalUniverseInstantiations :: !(Map Int ProvisionalUniverseInstantiation)
  , csProvisionalUniverseInstantiationsByOwner :: !(Map GName (Set Int))
  , csProvisionalUniverseInstantiationsByConsumer :: !(Map GName (Set Int))
  , csNextProvisionalUniverseInstantiation :: !Int
  , csProvisionalGlobalUniverseMetas :: !(Map GName [[LevelMeta]])
  , csProvisionalConstructorUniverseMetas :: !(Map GName [[LevelMeta]])
  -- ^ Original hidden spines captured before any declaration boundary
  -- principalizes them. Call sites elaborate against these arities; retaining
  -- the source metas until the owning SCC is finalized is what makes the
  -- eventual source-to-principal projection exact across split header/body
  -- boundaries.
  , csFinalizedGlobalUniverseMetaMaps :: !(Map GName (Map LevelMeta Level))
  -- ^ Exact morphism from an inferred global's provisional interface metas
  -- to its finalized hidden telescope. Late semantic artifacts (notably
  -- instance entries registered in the header pass and consumed during body
  -- checking) must cross this boundary before occurrence specialization;
  -- the module-wide level-assignment map is not a substitute because
  -- 'LParam' indices are declaration-local.
  , csUniverseInterfaceValues :: !(Set GName)
  -- ^ Type-alias declarations whose defining value is part of the exported
  -- static interface. Universe generalization must inspect these equations;
  -- ordinary term bodies remain implementation details.
  , csFinalizedUniverseInterfaces :: !(Set GName)
  -- ^ Declarations whose provisional level-meta interface has already been
  -- replaced by its stable hidden telescope. Header and body checking share
  -- one state, so the body-pass finalization may zonk residual classifier
  -- metas but must never infer another occurrence projection or append a
  -- second telescope to these declarations.
  , csNominalSummaryRequests :: !(Map GName PendingNominalSummary)
  -- ^ Persistent typed source requests for nominal role/certificate replay.
  -- A late generated family-proof binder changes the physical saturation
  -- telescope, so the request must remain available after its first summary.
  , csDirtyNominalSummaries :: !(Set GName)
  -- ^ Requests whose checked closure must be rebuilt before a schema lift or
  -- interface artifact may consume it.
  , csRecursiveSchemaEdges :: !(Set RecursiveSchemaEdge)
  -- ^ Verified same-or-lower calls within declaration-schema SCCs.  This is
  -- checker-owned semantic evidence, not a post-hoc scan of source calls.
  , csRecursiveSchemaOccurrences :: ![RecursiveSchemaOccurrence]
  -- ^ Typed body-occurrence provenance retained until the declaration
  -- dependency graph has identified recursive SCCs. Universe-bearing
  -- occurrences additionally carry finalized level facts for schema
  -- termination; ordinary occurrences retain resolved symbol identity and a
  -- source span for termination diagnostics.
  , csRecursiveSchemaOccurrencesByCaller :: !(Map GName [RecursiveSchemaOccurrence])
  -- ^ Caller-indexed view used by owner-scoped universe closeout. The ordered
  -- list remains authoritative for module-final termination diagnostics.
  , csSelectedUniverseEvidence :: !(Set SelectedUniverseEvidence)
  -- ^ Ordinary implicit evidence selected while proving universe-role goals.
  -- The normalized goal and resolved dictionary identity are frozen before
  -- the role fixed point.
  , csUniverseInferenceRecords :: !(Map Text UniverseInferenceRecord)
  -- ^ Portable principal-inference outcomes recorded at declaration
  -- boundaries. Appendix-T reflection consumes this semantic result directly;
  -- diagnostics and finalized pretty types are not an authority for it.
  , csPendingUniverseProofs :: !(Map GName [UniverseConstraint])
  -- ^ Transactional declaration-local obligations discovered while a body is
  -- checked. They are assumptions for that active body, but become ordinary
  -- erased proof binders only when the declaration boundary closes.
  , csPublishedGeneratedConstraintCounts :: !(Map GeneratedConstraintInterface Int)
  -- ^ Authenticated physical generated-proof prefix already published to
  -- retained call sites. Multiple checker boundaries may hold overlapping
  -- historical snapshots; this monotone frontier, rather than either snapshot
  -- or proof-term spelling, makes call-spine completion exactly once.
  , csActiveUniverseDefinition :: !(Maybe GName)
  -- ^ The signature-governed definition currently being checked. Its hidden
  -- declaration-universe constraints are assumptions for the implementation,
  -- and additional consistent relations among its own hidden parameters are
  -- inferred into that telescope (§11.1.2.3A). References to every other
  -- declaration still instantiate their telescope freshly.
  , csRecordRecursiveSchemaOccurrences :: !Bool
  -- ^ True only while elaborating a source term body. Signature/interface
  -- elaboration also resolves globals under an active owner, but those typed
  -- references are not recursive calls and must not enter schema termination.
  , csActiveLocalRecursiveSchemaScope :: !(Maybe LocalRecursiveSchemaScope)
  -- ^ Lexical binder identities for the local recursive declaration currently
  -- being checked. Local schema calls are recorded by de Bruijn level, never
  -- by source spelling.
  , csLocalRecursiveSchemaOccurrences :: ![LocalRecursiveSchemaOccurrence]
  -- ^ Typed local-SCC occurrence facts retained only until that local
  -- declaration boundary applies the same-or-lower schema judgment.
  , csActiveUniverseSchema :: !(Map Text Level)
  -- ^ Source names of the rigid static parameters of the declaration being
  -- elaborated. These are not term bindings and exist only while checking
  -- the declaration's level expressions.
  , csDeclaredUniverseSchemaNames :: !(Map GName [Text])
  -- ^ Source-level names authenticated by a declaration signature/header.
  -- A following definition may omit the repeated @.{...}@ syntax while its
  -- body still refers to those names; the semantic telescope arity remains in
  -- 'gdUniverses', and this map restores only the lexical spellings.
  , csActiveLocalUniverseSchemaCount :: !(Maybe Int)
  -- ^ Parameter count of the explicit local declaration schema currently
  -- being elaborated. The active name map also contains shifted enclosing
  -- parameters, so this marker identifies the complete local prefix.
  , csAllowSchemaLevelTerms :: !Bool
  -- ^ Provisional scope for elaborating a type-level proposition that may be
  -- a compiler-authenticated level comparison. The completed Core proposition
  -- is validated before this scope exits; schema parameters never become
  -- ordinary TypeLevel values.
  , csGeneralizeBareTypeLevels :: !Bool
  -- ^ True only while elaborating a source binder domain. A bare @Type@ in
  -- such a position introduces a declaration-universe choice; the same
  -- syntax in a terminal/result classifier is a least-solution obligation.
  -- Keeping this role syntactic prevents result levels from acquiring
  -- parameter provenance through later level constraints (§11.1.3).
  , csBareTypeLevels :: !(Map Span Level)
  -- ^ Bare @Type@ floats once per source annotation. Parser-expanded grouped
  -- annotations reuse their source span and therefore share this level.
  , csDiags :: !Diagnostics
  , csModule :: !ModuleName
  , csScope :: !(Map Text GName) -- ^ unqualified import scope
  , csLocalDeclScope :: !(Map Text GName)
  -- ^ Lexically scoped nominal/static declarations. These identities are
  -- compiler-minted and therefore cannot be recovered from the current
  -- module plus source spelling. Local scope must also take precedence over
  -- same-spelled module declarations (§9.3.1, §30.1.1).
  , csLocalNominalCaptures :: !(Map GName [LocalNominalCapture])
  -- ^ Exact term-capture telescopes of closure-converted local nominal
  -- families and constructors. The global interface owns the corresponding
  -- implicit Pis; source occurrences apply these lexical arguments.
  , csScopedLocalNominals :: !(Map GName Span)
  -- ^ Scoped local families whose identity is tied to the enclosing lexical
  -- nominal scope. Their exposed result types may not escape that scope.
  , csModuleAliases :: !(Map Text ModuleName)
  , csModuleExports :: !(Map ModuleName [Text])
  , csFresh :: !Int
  , csPending :: ![(MetaId, Value, Span, Ctx, [ScopedBoolFact])]
  , csPendingEvidenceAttempts :: !(Map MetaId PendingEvidenceAttempt)
  -- ^ Last failed semantic attempt for each postponed evidence identity.
  -- Declaration closeout retries an entry only after one of this snapshot's
  -- exact term-meta, level-meta, or referenced-global dependencies changes.
  -- Final module closeout still forces every survivor once.
  -- ^ postponed implicit goals with the local context they were raised
  -- in (premise dictionaries live there, §14.3.2) and the boolean
  -- branch facts active at the raise site
  , csDeferredTypeEqualities :: ![DeferredTypeEquality]
  -- ^ Type equalities blocked on entries of 'csPending'. They are replayed
  -- once those entries resolve and suppressed only when a dependency itself
  -- receives the root diagnostic.
  , csDiagnosedPendingEvidence :: !(Set MetaId)
  -- ^ Stable identities of evidence placeholders that emitted their root
  -- diagnostic, whether they were postponed or failed immediately. Meta ids
  -- are never reused within a checking run; conversions that still depend on
  -- one of these placeholders suppress only their derivative mismatch.
  , csPendingLevelEvidence :: !(Map MetaId PendingLevelEvidence)
  -- ^ Authenticated flexible level propositions postponed inside a semantic
  -- declaration. If that declaration generalizes the proposition into an
  -- erased proof binder, finalization replaces this exact meta occurrence by
  -- the binder; no source spelling or rendered goal participates.
  , csEvidenceCache :: !(Map EvidenceCacheKey Term)
  -- ^ Closed, local-candidate-free implicit/proof evidence, keyed by the
  -- current semantic epoch plus the structurally quoted goal.  The cache is
  -- populated only after local implicit evidence fails and only for closed
  -- result terms produced without branch-local facts, so local dictionaries,
  -- supertrait projections, and control-flow refinements cannot be captured
  -- across contexts.
  , csNormEpoch :: !Int
  -- ^ Semantic epoch for bounded proof/termination caches.  It advances when
  -- global lookup, trait/instance lookup, or conversion-time reducibility
  -- changes.  Metavariable-sensitive entries are admitted to the caches only
  -- after their quoted keys contain no unsolved metas, so solving the flood of
  -- evidence metas produced by checked arithmetic does not pointlessly nuke the
  -- cache after every success.  Cache keys include the epoch; old entries are
  -- discarded eagerly as a memory bound rather than a correctness requirement.
  , csNormCache :: !(Map NormCacheKey Term)
  -- ^ Bounded cache for 'normalizeTermAt'.  Termination checking and
  -- proposition solving repeatedly normalize the same arithmetic measures and
  -- checked-operation predicates; caching the semantic normal form turns those
  -- repeated obligations from accidental quadratic work into one NbE pass.
  , csPropCache :: !(Map PropCacheKey Bool)
  -- ^ Bounded cache for proposition classification.  The value records only
  -- whether compiler-owned equality/proof normalization can construct 'refl';
  -- it never caches arbitrary user evidence.
  , csScopeAmbig :: !(Map Text [GName])
  -- ^ §7.1 names provided ambiguously by several wildcard imports
  , csExpects :: !(Map GName (Span, Int))
  -- ^ §9.4 expect declarations: span and number of satisfiers seen
  , csSigPending :: !(Map GName Span)
  -- ^ §9.1 top-level signatures not yet satisfied in this file
  , csManifest :: !(Map GName ())
  -- ^ §2.8.4 manifest bindings (no widening signature): reified
  -- static-object identity is preserved through them
  , csActive :: !(Map GName APInfo)
  -- ^ §17.3 active-pattern definitions and their result classification
  , csFacts :: !(Map Int RigidFact)
  -- ^ Branch-local dependent-match facts about rigid levels (§7.4.1),
  -- consulted by conversion-time match reduction
  , csProjections :: !(Map GName ProjInfo)
  -- ^ §9.1.1 projection definitions: binder structure for the
  -- projection facet at application sites
  , csInoutParams :: !(Map GName [Maybe InoutParamInfo])
  -- ^ §18.9 named-callable inout metadata, indexed by global and explicit
  -- parameter position.  It is elaboration-only interface data; the core term
  -- remains ordinary linear state threading.
  , csAllowInoutBinderContext :: !Bool
  -- ^ True only while elaborating a named callable signature whose leading
  -- explicit parameter chain may carry §18.9 `inout` metadata. Ordinary Pi
  -- types, lambdas, constructors, and nested function types reject it.
  , csMutableBindingFields :: !(Map Span [(Text, Text)])
  -- ^ §18.6.1 mutable-binding diagnostic payload fields captured while the
  -- checker still has selected MonadRef evidence. Usage consumes these for
  -- storage-fact diagnostics that originate after elaboration.
  , csPendingDiscardedResults :: ![PendingDiscardedResult]
  -- ^ Typed non-final do-item results waiting for declaration closeout.
  , csDiscardedResultTypes :: !(Map Span Expr)
  -- ^ Finalized source-level type facts for §18.2 discard checking. Usage
  -- consumes this checker-owned table instead of reconstructing an inferred
  -- monadic result type from source spelling.
  , csRecognizedRefOps :: !(Map Span Text)
  -- ^ Explicit @readRef (ref x)@ / @writeRef (ref x)@ occurrences accepted by
  -- checker after overload and MonadRef-evidence equality. Usage consumes these
  -- by the @ref x@ span instead of re-inferring dictionary projections.
  , csRecognizedMultishotOps :: !(Map Span (GName, Text))
  -- ^ Effect-operation selections whose resolved label identity and operation
  -- metadata prove a multi-shot resumption quantity. Later flow/usage passes
  -- consume the recorded source span instead of rediscovering @label.op@ from
  -- source spelling.
  , csEffectOpValueGlobals :: !(Map GName EffectOpValueInfo)
  -- ^ Top-level globals whose definiens is a resolved effect operation value.
  -- Application-site recognition consults this checker-owned table rather than
  -- inferring operation identity from a function type or source spelling.
  , csHandlerOpQuantities :: !(Map Span Q)
  -- ^ Handler resumption binder span -> resolved operation resumption quantity.
  -- Usage consumes this after checking so scoped labels and aliases cannot be
  -- miscounted by source label text.
  , csPatternBinderQuantities :: !(Map Span Q)
  -- ^ Pattern variable source span -> checker-resolved slot quantity. This is
  -- especially important for handler arguments: their quantities live in the
  -- resolved operation telescope and cannot be reconstructed from the handler
  -- clause's surface syntax by the post-elaboration usage pass.
  , csPatternBinderBorrows :: !(Set Span)
  -- ^ Pattern variable spans whose checker-resolved producer slot has borrowed
  -- access. Kept separately from quantity because access is orthogonal.
  , csConstructorPatternLetSpans :: !(Set Span)
  -- ^ Ambiguous @let C p... = rhs@ declarations whose head was resolved to a
  -- constructor identity. Surface usage analysis consumes this checked
  -- selection instead of rediscovering constructor meaning from spelling.
  , csStaticKindBinders :: !(Set Span)
  -- ^ Source binders whose elaborated domain satisfies the parametric-kind
  -- grammar. Usage consumes this checker-owned fact so quantity-zero type-code
  -- occurrences remain static without exempting arbitrary erased values.
  , csErasedArgumentSpans :: !(Set Span)
  -- ^ Explicit source arguments accepted at a checker-resolved quantity-zero
  -- parameter. Usage consumes this typed fact for projected and aliased
  -- callables whose parameter telescope cannot be reconstructed from syntax.
  , csBorrowedArgumentDemands :: !(Map Span Q)
  -- ^ Explicit source arguments accepted at a checker-resolved borrowed
  -- parameter, paired with the selected demand. Access mode is selected from
  -- the typed Pi binder and is orthogonal to quantity; Usage consumes this
  -- occurrence-local fact instead of reconstructing trait/member parameter
  -- modes from source spellings.
  , csErasedExpressionSpans :: !(Set Span)
  -- ^ Source expressions whose checked field/member representation is erased.
  -- This is occurrence-local typed authority: Usage must not infer erasure
  -- from a field spelling or from the source quantity of the receiver.
  , csImplicitExpressionDemands :: !(Map Span Q)
  -- ^ Source expressions consumed by checker-inserted calls, keyed by source
  -- identity. Usage cannot recover these hidden application binders from the
  -- surface tree, so the checker records their selected Core quantity.
  , csNextRefCellId :: !Int
  -- ^ Fresh counter for optimization-only mutable-cell identities carried by
  -- 'RefLoweringWitness'. These ids are local to the elaborated Core body and
  -- never affect source semantics.
  , csNextLevelFieldId :: !Int
  -- ^ Stable identities for level-valued dependent-record/package fields.
  -- Labels are not identities: nested telescopes may legally reuse them.
  , csDemand :: !PlaceDemand
  -- ^ surrounding place demand of the expression being elaborated
  -- (selects the §16.1.5/§16.1.6 eliminator and accessor capability)
  , csThis :: !(Maybe ThisMode)
  -- ^ §13.2.1 sibling-reference scope: what @this@ denotes inside a
  -- dependent record type, literal, or update being elaborated
  , csTraitSupers :: ![(Text, Value)]
  -- ^ §14.1.4: while elaborating a trait member's TYPE, the current
  -- trait's supertrait premises as @(\@field, premise-value)@ pairs. A
  -- supertrait operation appearing in the member type (e.g. an 'Eq'
  -- operation referenced by a member of a 'C => D' subtrait) resolves its
  -- dictionary implicit to the matching
  -- 'this.__superN' projection — without introducing a context binder that
  -- would perturb the operation's other implicit (carrier) inference.
  , csEvidenceUniquenessStack :: ![GName]
  -- ^ Traits whose independent uniqueness certificates are currently being
  -- checked.  Compiler-generated coherence for these exact evidence types is
  -- disabled so a certificate cannot justify itself through @IsTrait@.
  , csBlockedSupertraitProjections :: !(Set (GName, Text))
  -- ^ Exact derived-supertrait facets currently being completed.  Projecting
  -- one of these slots from the incomplete self dictionary would be a
  -- circular proof, while all other supertrait paths remain available.
  , csForbidIncompleteSelfEvidence :: !Bool
  -- ^ Scoped while elaborating an explicit @summon@ request. Ordinary method
  -- dispatch may use the current instance dictionary while checking its
  -- members, but source code may not reify that incomplete dictionary as a
  -- first-class evidence value (§14.3.4A).
  , csArgIndexRetag :: !Bool
  -- ^ §16.1.8: inside explicit-argument checking, a same-head indexed
  -- type mismatch reports E_APPLICATION_ARGUMENT_MISMATCH (a failed
  -- transport at an application boundary)
  , csDefinitionalEqualityOnly :: !Bool
  -- ^ Scoped instance-head matching mode (§14.3.2). Higher-kinded instance
  -- arguments are compared by definitional equality, not ordinary function,
  -- effect-row, or nominal-schema subsumption. This flag keeps the ordinary
  -- bidirectional checker available while tightening its conversion boundary.
  , csReceivers :: !(Map GName [Int])
  -- ^ §7.4 receiver-marked explicit binder positions (indices among
  -- the explicit binders) per global, for method-call sugar
  , csExpansions :: !(Map Span Expr)
  , csUsageExpressionTypes :: !(Map Span Expr)
  -- ^ Fully checked, delaborated types for source expressions whose storage
  -- shape Usage must inspect. Facts are recorded only when no type meta
  -- remains, so absence is conservative rather than guessed.
  -- ^ §21.2 splice expansions (splice span ↦ grafted surface syntax,
  -- with captured occurrences under their original spellings) for the
  -- usage analysis to charge object-level uses at splice sites
  , csOpaqueDatas :: !(Map GName ())
  -- ^ §10 'opaque data' declarations: representation visible only in
  -- the defining module (consulted by §22.1 shape inspection)
  , csOpaqueDefs :: !(Map GName ())
  -- ^ §8.5.2 'opaque' term/type-alias definitions: the defining
  -- equation is available for definitional equality only INSIDE the
  -- defining module. Sealed at module end ('opaqueSealPass') by
  -- clearing 'gdReducible' so downstream modules cannot δ-unfold the
  -- definition during conversion (runtime evaluation is unaffected:
  -- 'ecRuntime' unfolds every valued global regardless).
  , csRecordOrders :: !(Map GName [Text])
  -- ^ Written field order of record type aliases (§22.2 shape order;
  -- core record types are canonicalized to lexicographic order)
  , csReExports :: !(Map ModuleName (Map Text GName))
  -- ^ §8.4 re-exports: per module, exported spelling ↦ the originating
  -- declaration in another module (aliased and kind-selected items)
  , csBoolFacts :: ![ScopedBoolFact]
  -- ^ boolean branch refinement: `if c …` makes `c = True` available
  -- in the then-branch and `c = False` in the else-branch as equality
  -- evidence (a §3.2.3 proof source; branch facts in the §15.6 sense)
  , csArgFlatOk :: !Bool
  -- ^ The enclosing application has a resolved ordinary function head.
  -- Nested checking preserves this semantic call-site classification so an
  -- argument written as a constructor application cannot erase the enclosing
  -- §16.1.7.1 diagnostic context.
  , csPreInstances :: !(Map Span (Maybe PreInstance))
  -- ^ instance heads registered by the §14.3 pre-pass, keyed by the
  -- declaration span ('Nothing' records a head already rejected there,
  -- so the body pass does not re-report it)
  , csDerivedDecls :: !(Map Span [Decl])
  -- ^ Compiler-owned deriving output keyed by the source @derive@ span.
  -- Every entry is an ordinary generated instance declaration. Its head is
  -- registered in the same pre-pass and its body is elaborated by
  -- 'elabInstance'; this table is planning metadata, never evidence.
  , csPositivity :: !(Map GName [Bool])
  -- ^ §10.4 parameter-positivity signatures: for each accepted data
  -- type (and each strictly-positive built-in/imported abstract type
  -- carrier whose interface declares a signature), one flag per
  -- parameter marking it positive ('True') or non-positive ('False').
  -- Consulted by the strict-positivity check when deciding whether an
  -- application 'F A1 .. An' keeps the defined type in a strictly
  -- positive position.
  , csDeclSites :: !(Map GName Span)
  -- ^ §3.1.1A: the source span where each module-scope name was first
  -- declared, so a duplicate-declaration diagnostic can cite both sites
  -- as related origins (declaration-site of the original).
  , csMultiFixOps :: !(Set Text)
  -- ^ §5.5.1: operator spellings that have more than one callable fixity
  -- in scope for this module (e.g. the prelude `-`, which is both
  -- `infix left 60` and `prefix 80`). A bare `(op)` reference whose
  -- expected type does not select exactly one fixity is ambiguous.
  , csUnsafe :: !UnsafeConfig
  -- ^ §4.2 build-level gating: which unsafe/debug facilities the build
  -- configuration permits. Defaults to all-disabled (package mode).
  , csPreludeDisabled :: !Bool
  -- ^ §28.1 effective module setting: the implicit prelude import and
  -- fixed constructor subset are disabled for the module currently being
  -- checked, either by build configuration or @NoPrelude.
  , csAllowUnsafeIntrinsics :: !Bool
  -- ^ §4.5 soundness escape: the module currently being checked may name the
  -- raw-admit proof intrinsics (@__eqProof@, @__transport@, @__absurd@,
  -- @__handleEff@, and the @__debug*@ introspection prims) that otherwise
  -- resolve only inside the prelude. These intrinsics inhabit an arbitrary
  -- proposition from nothing, so naming one from ordinary user code is a
  -- total-unsoundness hole. This flag is the SOLE exemption (see
  -- 'gateUnsafeIntrinsic'): it is set by the prelude loader for the genuine
  -- embedded prelude/std-lib, and by the pipeline for a user module carrying
  -- the @AllowUnsafeIntrinsics attribute (an explicit, audited opt-out for
  -- tests/bootstrapping). Defaults to 'False'.
  , csEmbeddedLoad :: !Bool
  -- ^ §4.7 audit hygiene: 'True' only while elaborating the genuine embedded
  -- prelude and the embedded standard-library modules (set by the prelude
  -- loader, cleared by the pipeline for every user module). The embedded
  -- modules admit the proof helpers internally as implementation machinery,
  -- not as a user opt-in, so 'gateUnsafeIntrinsic' does NOT record those uses
  -- in the audit ledger when this flag is set; an ordinary @AllowUnsafeIntrinsics
  -- user module (where the flag is 'False') IS recorded. This is an
  -- audit-only distinction with no bearing on the soundness exemption above.
  -- Defaults to 'False'.
  , csAuditLedger :: ![AuditRecord]
  -- ^ §4.7 unsafe/debug audit ledger: one record per accepted use of an
  -- unsafe/debug facility, in source order.
  , csScopeNameCache :: !(Maybe (Map Int (Set Text)))
  -- ^ §3.2.2 typo-suggestion candidate index: the module-level in-scope
  -- names (import scope + this module's own globals) bucketed by spelling
  -- length. A single dropped import can leave thousands of references
  -- unresolved, each raising a suggestion diagnostic; rebuilding and
  -- rescanning the whole scope per diagnostic is O(Nerrors * Nscope).
  , csBackendIntrinsics :: !(Map Text Term)
  -- ^ §34.5/§34.5.3 general hook: bare-name backend intrinsics (spelling ↦
  -- expected Core type) that satisfy a §9.4 'expect term' up to defeq. This
  -- is now ALWAYS seeded empty: native host bindings are supplied as
  -- @host.native.*@ modules selected by a build manifest (§8.3.5/§36.28)
  -- and satisfied by ordinary import resolution, not by a bare-name table.
  -- A bare foreign 'expect' therefore has no native provider and is
  -- honestly unsatisfied (E_EXPECT_UNSATISFIED). The hook is retained as an
  -- inert, backend-agnostic seam; see docs/BUILD_AND_NATIVE_BINDINGS.md.
  , csFoundationProviders :: !(Map GName Term)
  -- ^ Mandatory portable-foundation providers keyed by resolved declaration
  -- identity.  Unlike backend intrinsics these are backend-independent proof
  -- constants, and unlike an ordinary companion definition they have no
  -- source body.  The stored Core type is an independently seeded ABI: an
  -- @expect term@ is satisfied only when both the global identity and its
  -- complete universe-polymorphic type agree definitionally.
  , csCoreBodies :: !(Map GName Term)
  -- ^ Elaborated KCore body of each top-level term definition, captured
  -- before evaluation to a value. The native backends lower these through
  -- KBackendIR: re-deriving a body by 'quote'-ing the stored NbE 'gdValue' is
  -- unsound for do-blocks and suspensions that close over 'let'/argument
  -- bindings (quote drops the captured environment), so we keep the real
  -- elaborator output. Used only by backend/lint/analysis paths; the
  -- interpreter path ignores it.
  , csImportedCoreBodies :: !(Map GName Term)
  -- ^ Immutable implementation bodies loaded from checked module artifacts.
  -- They participate in backend reachability but never in current-unit
  -- re-zonking, ownership analysis, linting, or declaration closeout.
  , csCoreSignatures :: !(Map GName Term)
  -- ^ Checked source signatures retained until their complete declaration
  -- SCC is generalized. NbE deliberately erases cumulative-lift evidence, so
  -- this is the pre-generalization authority from which 'gdCoreType' is
  -- produced without changing the semantic interface used to check bodies.
  , csTransparentValueAliases :: !(Map GName Expr)
  -- ^ Direct, transparent, binder-free value aliases captured before the
  -- header pass. Universe annotations are themselves checked in that pass,
  -- before ordinary let bodies, so canonical TypeLevel operation aliases
  -- need access to their source equation to preserve declaration-order
  -- independence. The equation is still elaborated against its resolved
  -- global type and admitted only when it reduces to a compiler intrinsic.
  , csLevelOperatorAliases :: !(Map GName LevelOperatorIdentity)
  -- ^ Final typed identity of transparent TypeLevel operation aliases.
  -- Imported modules retain this map even when source equations are absent.
  , csOwnership :: !(Map GName OwnInfo)
  -- ^ Perceus RC Stage S1.0 (see "Kappa.Ownership"): the per-definition
  -- ownership table (owned\/borrowed\/last-use facts), currently produced in
  -- Core structural coordinates and reattached to KBackendIR nodes during
  -- lowering. Populated in "Kappa.Pipeline" right after the core bodies are
  -- finalized, beside the @lintCoreBodies@ call.
  , csTerminationNames :: !(Set GName)
  -- ^ Signature-governed top-level functions in the current module.  An
  -- edge to one of these names is potentially part of a recursive SCC until
  -- the whole body pass has seen every definition.
  , csTerminationDecls :: !(Map GName TerminationDecl)
  -- ^ Checked, zonked bodies awaiting the SCC-level termination pass.
  , csAssertTerminates :: !(Set GName)
  -- ^ Definitions admitted for acceptance by an enabled
  -- @assertTerminates@/@assertTotal@. They remain non-reducible unless the
  -- ordinary termination checker independently certifies them.
  , csModEffLabels :: !(Map Text EffLabelInfo)
  -- ^ §18.1: module-level (top-level) @effect@ declarations, keyed by name.
  -- Unlike §9.3.1.1 @scoped effect@ (which lives in 'ctxEffLabels'), a
  -- top-level effect is visible to every definition in the module; effect
  -- resolution consults this as a fallback to 'ctxEffLabels'.
  , csEffectInterfaces :: !(Map GName EffLabelInfo)
  -- ^ Canonical effect-interface metadata keyed by semantic interface
  -- identity. Unlike 'csModEffLabels', this is not a source-visibility map:
  -- it retains scoped interfaces after their lexical context closes so SCC
  -- universe generalization and artifact finalization can account for every
  -- operation header owned by the interface.
  , csMultishotOps :: !(Set Text)
  -- ^ §18.1.16/§18.1.17 the operation NAMES declared MULTI-SHOT (resumption
  -- quantity ω or 1+) across BOTH top-level @effect@ and §9.3.1.1 block-local
  -- @scoped effect@ declarations.  Recorded at effect-declaration time so the
  -- §34.3.3 native-backend capability gate (rt-multishot-effects absent) can reject a
  -- reachable multi-shot resumption even for scoped effects (whose labels do
  -- not live in 'csModEffLabels').
  , csAssertReducible :: !(Set GName)
  -- ^ §4.4 definitions explicitly wrapped in a gated `assertReducible`.
  -- The override is consumed only by the SCC termination pass.  It is not
  -- consulted by runtime evaluation and does not make `assertTerminates`
  -- conversion-reducible.
  , csImpossibleScrut :: !(Maybe Bool)
  -- ^ §17.1.4: while a match arm body is being checked, whether that arm's
  -- §30.2.7-refined fiber is provably 'Empty'. A bare @impossible@ body
  -- consults this and is accepted exactly when it is 'Just True'. 'Nothing'
  -- (the default, e.g. outside any match arm) makes @impossible@ reject as
  -- reachable. Saved/restored around each arm body, like 'csFacts'.
  , csHoles :: !(Map Text NamedHole)
  -- ^ §16.3.2 named expression holes (@?name@) in scope for the top-level
  -- declaration currently being elaborated. Every occurrence of the same
  -- spelling shares one term metavariable and one type metavariable (one
  -- @HoleId@, §16.3.2 "Repeated occurrences of a named hole MUST share one
  -- @HoleId@"), so the occurrences denote the same unknown and MUST receive
  -- definitionally equal expected types. Reset per enclosing declaration in
  -- 'elabLetDecl' (a named hole does not escape its enclosing declaration).
  -- Anonymous @_@ never enters this map: each @_@ stays a fresh hole.
  , csSignatureHoles :: !(Map GName (Map Text NamedHole))
  -- ^ Named-hole scopes whose term signature has been checked but whose
  -- matching definition body has not yet completed. A signature and its
  -- definition are one semantic declaration for inference (§9.1, §16.3.2);
  -- keying by resolved global identity prevents same-spelled holes in
  -- unrelated declarations from sharing metas.
  }

-- | §16.3.2 a named expression hole (@?name@) shared across its
-- occurrences in one enclosing declaration. All occurrences denote the
-- same unknown: they share one term metavariable ('nhTerm') and one type
-- metavariable ('nhType', kept as a 'Value' so the shared expected type
-- can be unified and re-quoted at each occurrence). 'nhOccs' records the
-- source span of each occurrence (most recent first) so an inconsistency
-- diagnostic can cite every occurrence (§3.2.4 @kappa.hole.inconsistent@).
data NamedHole = NamedHole
  { nhTerm :: !Term -- ^ the shared term metavariable (one @HoleId@)
  , nhType :: !Value -- ^ the shared type metavariable, as a value to unify
  , nhTypeTerm :: !Term -- ^ creation-site Core for a stable fallback diagnostic
  , nhDepth :: !Int -- ^ lexical depth at which 'nhTypeTerm' was created
  , nhOccs :: ![Span] -- ^ occurrence spans, most recent first
  }

-- | §4.2 build-level gating record. Each flag enables exactly one
-- unsafe/debug facility; all default to 'False' (package mode, §4.2).
data UnsafeConfig = UnsafeConfig
  { allowUnhiding :: !Bool
  , allowClarify :: !Bool
  , allowAssertTerminates :: !Bool
  , allowAssertReducible :: !Bool
  , allowUnsafeAssertProof :: !Bool
  , allowDebugIntrospection :: !Bool
  , implicitPrelude :: !Bool
  }
  deriving stock (Eq, Show)

-- | §4.7 one audit-ledger entry: the facility used, the module and origin
-- it occurred in, the build setting that permitted it, and an optional
-- reason string supplied by the source form.
data AuditRecord = AuditRecord
  { arFacility :: !Text -- ^ e.g. "unhide", "assertReducible", "unsafeAssertProof"
  , arModule :: !ModuleName
  , arOrigin :: !Span
  , arAffected :: !Text -- ^ declaration / import item identity affected
  , arBuildSetting :: !Text -- ^ the §4.2 allow_* setting that permitted it
  , arReason :: !(Maybe Text) -- ^ structured reason string, when supplied
  }
  deriving stock (Eq, Show)

-- | What @this.label@ resolves to (§13.2.1): inside a record type,
-- the telescope prefix elaborated so far; inside a record literal or
-- update, the sibling field values already elaborated.
data ThisMode
  = ThisType ![RecordField Value]
  | ThisValue ![(Text, Term)] ![RecordField Value]
  | ThisTraitSibs ![RecordField Value]
  -- ^ trait-body member scope: like 'ThisType', but sibling members
  -- shadow same-spelling globals (§14.2.1: "Inside the trait body,
  -- Item refers to the associated static member of the current trait
  -- evidence")

-- | §16.1.5/§16.1.6 surrounding demand at a descriptor application.
data PlaceDemand = DemandRead | DemandConsume | DemandOpen
  deriving stock (Eq, Show)

-- | §9.1.1 projection-facet metadata (one entry per declared name).
data ProjInfo = ProjInfo
  { pjIsPlace :: ![Bool] -- ^ per explicit binder, declaration order
  , pjPlaceNames :: ![Text] -- ^ place binder names, declaration order
  , pjSelector :: !Bool -- ^ selector form (vs expanded accessor form)
  , pjYields :: ![(Text, [Text])] -- ^ selector yield places: root binder, path
  }

-- | §18.9 callable-interface metadata for one explicit parameter position.
-- The surface form `(inout x : A)` records the formal parameter and the
-- successor record field to restore at call sites.  The current surface syntax
-- uses the same spelling for both.
data InoutParamInfo = InoutParamInfo
  { iopFormal :: !Text
  , iopSuccessor :: !Text
  }
  deriving stock (Eq, Show)

-- | Active-pattern result classification (§17.3.1).
data APResult = APOption | APMatch | APTotal
  deriving stock (Eq, Show)

newtype APInfo = APInfo
  { apResult :: APResult
  }

data NormCacheKey = NormCacheKey
  { nckEpoch :: !Int
  , nckOwner :: !(Maybe GName)
  , nckDepth :: !Int
  , nckTerm :: !Text
  }
  deriving stock (Eq, Ord, Show)

data PropCacheKey = PropCacheKey
  { pckEpoch :: !Int
  , pckOwner :: !(Maybe GName)
  , pckDepth :: !Int
  , pckGoal :: !Text
  , pckFacts :: !Text
  , pckNatLevels :: !Text
  }
  deriving stock (Eq, Ord, Show)

data EvidenceCacheKey = EvidenceCacheKey !(Maybe GName) !Text
  deriving stock (Eq, Ord, Show)

type CheckM = State CheckState

data VarRefInfo = VarRefInfo
  { vriStoredType :: !Value
  , vriStoredTypeTerm :: !Term
  , vriMonadRefDict :: !Term
  , vriMonadType :: !Value
  , vriDiagnosticRefType :: !Value
  , vriLoweringWitness :: !(Maybe RefLoweringWitness)
  }

data VarReadBlock
  = VarReadCrossesBoundary
  | VarReadStaticPosition

-- | Checker-owned interface for a universe-polymorphic local declaration.
-- The generalized type lives in 'ceType'; this telescope is the authority for
-- fresh occurrence instantiation and for KCore serialization.
data LocalUniverseInfo = LocalUniverseInfo
  { luiTelescope :: !DeclarationUniverseTelescope
  }

data LocalLetItem
  = LocalLetBinding !LetBind
  | LocalLetRecursiveGroup ![LetBind]

-- | One entry in the local typing context: a variable in scope, with its
-- type and the quantity\/borrow\/origin metadata the usage and diagnostic
-- machinery needs. The list of these (innermost first) /is/ the scope.
data CtxEntry = CtxEntry
  { ceName :: !Text
  , ceType :: !Value
  , ceLocalUniverses :: !(Maybe LocalUniverseInfo)
  , ceMode :: !ObservationMode
  , ceModeProvisional :: !Bool
  -- ^ True only while a generated binder's domain is being inferred. This
  -- covers unannotated local parameters and implicitly universalized free
  -- variables. Source-time observation checks recompute the mode from the
  -- solved domain; finalized KCore never contains provisional modes.
  , ceImplicitLocal :: !Bool
  , ceVarInfo :: !(Maybe VarRefInfo)
  -- ^ Introduced by @var@ (§18.6.1): ordinary value occurrences select the
  -- current-value facet during do-item lifting; @ref x@ and assignments use the
  -- same MonadRef evidence that created the hidden cell.
  , ceProjInfo :: !(Maybe ProjInfo)
  -- ^ Local alias of a projection declaration. This carries the projection's
  -- symbol-backed footprint through ordinary let bindings, so inout rewriting
  -- can reason about @~(proj x)@ without inspecting source spellings.
  , ceOpValueInfo :: !(Maybe EffectOpValueInfo)
  -- ^ Local alias of a resolved effect operation value. The operation's
  -- first-class type does not retain its declared resumption quantity, so flow
  -- and usage analyses must carry this checker-owned fact through simple
  -- aliases instead of rediscovering @label.op@ from source spelling.
  , ceCoreQ :: !Q
  -- ^ Elaborated quantity retained independently from observation mode.
  , ceObservationOrigin :: !(Maybe Text)
  -- ^ Diagnostic provenance for a parametric observation. This is checker
  -- metadata only; KCore identity contains the mode but never source origin.
  , ceQ :: !(Maybe S.Quantity)
  -- ^ Quantity prefix of an implicit local binder (§16.3.3).
  , ceBorrow :: !Bool
  -- ^ @\@&@-marked implicit local: may not escape into closures.
  , ceOrigin :: !Span
  -- ^ §3.1.1A binder origin: the source span where this entry was
  -- introduced, so a borrow/ownership diagnostic about it can cite its
  -- introduction site. 'noSpan' when the introduction is untracked for
  -- this binder kind.
  }

-- | A checked occurrence judgment (§30.2.0). This value is transient checker
-- state, not a KCore wrapper or interface side table: persistent mode lives on
-- the binding/projection/global fact that introduced the occurrence.
data ObservationJudgment = ObservationJudgment
  { ojMode :: !ObservationMode
  , ojOrigin :: !Text
  , ojClassifier :: !(Maybe ObservationClassifier)
  }

data ObservationClassifier
  = ObservationType !Level
  | ObservationTypeFormer

-- | The elaboration context threaded through 'infer'\/'check': everything
-- that depends on /where/ in the program we are. 'ctxEntries' is the scope
-- (and 'ctxEnv' its evaluated mirror, for NbE); the remaining fields carry
-- flow refinement, scope barriers, effect labels, hygiene, and the current
-- @return@ target. Helpers like @bindCtx@\/@pushCtxBarrier@ extend it.
data Ctx = Ctx
  { ctxEntries :: ![CtxEntry]
  , ctxEnv :: !Env
  , ctxRefines :: !(Map Text [GName])
  -- ^ §7.4.1 flow refinement: variable → possible constructors.
  , ctxAliases :: !(Map Text Text)
  -- ^ §7.4.3 stable aliases: @let q = p@ makes q transport p's refinement.
  , ctxVarCurrentVersions :: !(Map Text Int)
  -- ^ §18.6.2 tracked local mutable-cell current-value versions.
  , ctxVarCurrentEscaped :: !(Set Text)
  -- ^ §18.6.2 mutable cells whose @ref x@ has escaped flow tracking.
  , ctxBarriers :: ![Int]
  -- ^ Context lengths at which lambda bodies began (closure
  -- boundaries for §16.3.3 borrow-escape and scope grouping).
  , ctxEffLabels :: !(Map Text EffLabelInfo)
  -- ^ Lexically scoped effect labels (§9.3.1.1 @scoped effect@).
  , ctxInDo :: !Bool
  -- ^ Inside a @do@ elaboration: gates the §18.9.3 @~@ marker.
  , ctxVarReadBlock :: !(Maybe VarReadBlock)
  -- ^ Why a surface @var@ current-value occurrence cannot be lifted in
  -- this context, for the §18.3.1/§18.6.1 diagnostic split.
  , ctxHyg :: !(Map Text (Int, Value))
  -- ^ §21.4 hygienic capture references in spliced syntax: fresh
  -- spelling ↦ (binding LEVEL in this context, binder type).
  , ctxQuoteSlots :: !(Map Int Value)
  -- ^ Types of the enclosing quote's grafting slots ('EQuoteHole'),
  -- while the quote payload is being checked (§21.1).
  , ctxCodeDepth :: !Int
  -- ^ Nesting depth of enclosing §23.2 code quotes ('.~' is only
  -- meaningful inside one).
  , ctxReturnTarget :: !(Maybe Text)
  -- ^ §18.5: name/label of the innermost enclosing return target — a named
  -- function/method, an inherited-name lambda, or a labeled lambda. A
  -- @return@L@ resolves only when @L@ matches this (resolution does not
  -- cross user-written lambda boundaries); an anonymous lambda resets it to
  -- Nothing (nothing outside is reachable across it).
  , ctxLevelAssumptions :: !Assumptions
  -- ^ §11.1.2.2 lexically scoped inequalities introduced by earlier erased
  -- level-comparison proof binders in the current telescope.
  , ctxLevelFieldIds :: !(Map Text Int)
  -- ^ Scoped identities of TypeLevel-valued `this.field` siblings. Nested
  -- telescope labels shadow by map insertion without aliasing solver atoms.
  , ctxBorrowCaptureRegions :: !(Map Text (Maybe Value))
  -- ^ Explicit borrowed locals mapped to their declared region witness.
  -- 'Nothing' records an anonymous rigid borrow, which cannot be named in a
  -- source capture annotation. Entries come from resolved binder prefixes,
  -- and 'bindEntry' removes shadowed names.
  }

-- | A scoped effect's elaborated interface (§9.3.1.1, §18.1.15): label
-- identity, interface-type identity, and operation metadata.
data EffLabelInfo = EffLabelInfo
  { eliLabel :: !GName -- ^ effect-label value identity (§18.1.18)
  , eliIface :: !GName -- ^ effect-interface type constructor
  , eliParams :: !Telescope
  -- ^ §18.1.15 effect type parameters, including their independent
  -- observation mode and quantity. Domains are de Bruijn under the preceding
  -- parameters.
  , eliFixedArgs :: !(Maybe [Value])
  -- ^ A declared @effect label l : E args@ fixes the interface arguments at
  -- the declaration site. 'Nothing' is reserved for the canonical label
  -- introduced by @effect E ...@, whose operations remain polymorphic in the
  -- interface parameters; @Just []@ is an explicit alias of an
  -- unparameterized interface.
  , eliFixedUniverses :: !(Maybe [Level])
  -- ^ The exact declaration-universe occurrence selected by an effect-label
  -- alias.  Fixed interface arguments and their hidden universe spine form
  -- one semantic instance: operation selection must not freshen the owner
  -- independently and then reuse arguments elaborated at another occurrence.
  , eliOps :: ![EffOpInfo]
  }

data EffOpInfo = EffOpInfo
  { eoiName :: !Text
  , eoiQ :: !Q -- ^ declared resumption quantity (§18.1.16)
  , eoiImplicits :: !Telescope
  -- ^ §18.1.15: the operation's own implicit (forall-bound) parameters
  -- (e.g. @op : forall a. a -> a@), de Bruijn under the effect's parameters
  -- then the preceding op-implicits. Universally quantified per
  -- operation: instantiated fresh at each call and treated as skolems in the
  -- handler clause.
  , eoiArgs :: !Telescope
  -- ^ §18.1.15/§30.2.0: the operation's explicit parameter telescope. Each
  -- entry retains mode, quantity, explicitness, access, and its domain under
  -- the effect parameters, operation implicits, and preceding arguments.
  -- Non-empty.
  , eoiResT :: !Term
  -- ^ The final result type @B@, de Bruijn under the effect parameters,
  -- operation implicits, and the complete explicit-argument telescope.
  }

data EffectOpValueInfo = EffectOpValueInfo
  { eoviLabel :: !GName
  , eoviName :: !Text
  , eoviQ :: !Q
  , eoviArity :: !Int
  }

-- | Complete applications of declarations whose generated constraint prefix
-- was discovered only by the final declaration-SCC solve.  Unlike the
-- boundary repair above, this runs after the caller's complete proof-lambda
-- prefix is present, so a caller constraint at telescope position @i@ is the
-- de Bruijn variable @depth - i - 1@.  A specialized target obligation may
-- use either that exact authenticated binder or the canonical erased witness
-- when rigid entailment proves it from the caller telescope.  Blocked and
-- false obligations are deliberately left missing for typed-Core validation
-- to reject.
data GeneratedProofScope
  = GeneratedProofLambdas
  | GeneratedProofTelescope

data GeneratedProofEnvironment = GeneratedProofEnvironment
  { gpeAvailableCallerConstraints :: ![(Int, UniverseConstraint)]
  , gpeCallerAssumptions :: !Assumptions
  , gpeRigidWitness :: !(Maybe Term)
  }

-- | The only successful declaration-boundary inference path. The detailed
-- solver remains useful for ordinary unification and for recovering the
-- concrete failed constraint, but declaration completion consumes the
-- normative five-way classification directly and never defaults a residual
-- selected metavariable by inspecting 'LevelSolution'.
data PrincipalBoundaryResult
  = PrincipalBoundarySolved !(Map LevelMeta Level)
  | PrincipalBoundaryDeferred
  | PrincipalBoundaryRejected !PrincipalBoundaryFailure

data PrincipalBoundaryFailure
  = PrincipalBoundarySolveFailure !LevelSolveError
  | PrincipalBoundaryClassifierUnsatisfiable
  | PrincipalBoundaryNoPointwiseLeast !PrincipalNonLeastWitness
  | PrincipalBoundaryOutsidePortableFragment

type PendingEvidenceEntry = (MetaId, Value, Span, Ctx, [ScopedBoolFact])

data PendingEvidenceGraph = PendingEvidenceGraph
  { pegPendingIds :: !(Set MetaId)
  , pegDependencies :: !(Map MetaId (Set MetaId))
  , pegReverseIndex :: !(Map MetaId (Set MetaId))
  , pegClassifierDependencies :: !(Map MetaId (Set MetaId))
  }

data AuthenticatedLevelProofPolicy
  = ResolveAuthenticatedLevelProof
  | DeferAuthenticatedLevelProof

type InstanceTrial = (InstanceEntry, Term, CheckState)

data ArithmeticCertificateGoalEndpoints
  = GoalBooleanPredicate !Term
  | GoalArithmeticEquality !Term !Term

data StandardCheckedPredicateSemantics
  = CheckedSubtractionDomain
  | CheckedNonzeroDomain

data StandardCheckedPredicate = StandardCheckedPredicate
  { scpTrait :: !GName
  , scpMember :: !Text
  , scpDomains :: ![ArithmeticDomain]
  , scpSemantics :: !StandardCheckedPredicateSemantics
  }

data ExpectedImplicitSlot = ExpectedImplicitSlot
  !Ctx
  !Icit
  !Q
  !Term
  !Value
  !Value
  !Bool

-- | One planned argument slot of a checked application spine
-- ('elabAppChecked'): a kind-like implicit placeholder, an evidence
-- implicit resolved after result-type pre-unification, or an explicit
-- argument expression checked against its (pre-solved) domain.
data AppSlot
  = SlotKind ObservationMode Term Value
  | SlotInfer ObservationMode Term Value
  | SlotEvid ObservationMode Q Value Term Value
  | SlotImpl ObservationMode Q Bool (RuntimeErasure Value) Expr Value MetaId Value
  | -- | An explicit argument slot, carrying the placeholder meta's id
    -- and value plus a 'Bool' that records whether the function's
    -- codomain actually depends on this argument. When 'False' (a
    -- non-dependent arrow), the placeholder meta is solved directly
    -- (O(1)) instead of unified (O(size)), since it never reaches the
    -- result type — see 'step'.
    SlotExpl ObservationMode Q Bool (RuntimeErasure Value) Bool Expr Value MetaId Value Bool
  | SlotReady Icit (RuntimeErasure Term) Term

data AppResultPreparation
  = AppResultDefinitionallyReady
  | AppResultNeedsCoercion

-- | How the place arguments of a descriptor application are supplied.
data RootsSupply
  = RootsSeparate ![(Text, Expr)] -- ^ full application: place binder ↦ argument
  | RootsSingle !Expr -- ^ §16.1.5 single roots argument

data StandardArithmeticOperation
  = ArithmeticAdd
  | ArithmeticMultiply
  | ArithmeticSubtract
  | ArithmeticDivide
  | ArithmeticModulo

-- | One classified match case during active-pattern lowering.
data CaseClass
  = CPlain !MatchCase
  | CActive !Name !APInfo ![Expr] !Pattern !(Maybe Expr) !Expr !Span
  | CBad !Span

-- §17.1 exhaustiveness for nested constructor patterns, via pattern-
-- matrix usefulness (Maranget-style, over-approximating coverage for
-- record, variant and as-patterns so positives never regress): a match
-- is non-exhaustive iff the all-wildcard row is useful w.r.t. the
-- unguarded rows.
data PatKey = KCtor !GName | KTup !Int | KLit !Literal
  deriving stock (Eq)

-- | Branch-local conversion facts established while elaborating a pattern.
-- The map uses rigid de Bruijn levels, so it remains valid while the pattern
-- continuation extends the context with its binders. It is deliberately
-- opaque outside this module: callers can only install it with
-- 'withPatternRefinements', which enforces lexical save/restore.
newtype PatternRefinements = PatternRefinements (Map Int RigidFact)

data ExplicitRefOp = ExplicitRefRead | ExplicitRefWrite
  deriving (Eq)

data RefOpEvidence = RefOpBare | RefOpCarrier Term | RefOpDict Term

data VarInoutTarget = VarInoutTarget
  { vitRoot :: !Name
  , vitPath :: ![Name]
  , vitMutableRoot :: !Bool
  , vitWriteBack :: !VarInoutWriteBack
  , vitSuccessor :: !Text
  , vitTemp :: !Name
  }

data VarInoutWriteBack
  = VarInoutPath
  | VarInoutSection !Expr
  | VarInoutUnsupported !Span

data VarInoutRewriteMode = VarInoutMonadic | VarInoutPure

-- | How a generator source is iterated (§20.10.2 built-in obligations).
data SrcKind
  = SKList
  | SKArray
  | SKSet
  | SKMap
  | SKOption
  | SKQuery
  | SKRange
  | SKIntoQuery
  | SKUnknown
  deriving stock (Eq, Show)

-- | Cardinality approximation (§20.10.1).
data QCard = CZero | COne | CZeroOrOne | COneOrMore | CZeroOrMore
  deriving stock (Eq, Show)

-- | What pass 1 learned about one generator source.
data SrcInfo = SrcInfo
  { siKind :: !SrcKind
  , siItem :: !Value
  , siOrdered :: !Bool
  , siOneShot :: !Bool
  , siCard :: !QCard
  , siItemLinear :: !Bool
  }

-- | Per-clause pass-1 annotation consumed by the desugaring pass.
data CAnn = CAnn
  { caKind :: !SrcKind -- ^ generator/join source kind
  , caForceRefut :: !Bool -- ^ desugar with a wildcard fallback case
  }

-- | Pass-1 result: plan metadata plus pending diagnostics.
data CompPlan = CompPlan
  { cpAnns :: ![CAnn]
  , cpOneShot :: !Bool
  , cpCard :: !QCard
  , cpItemLinear :: !Bool
  , cpDiags :: ![(Span, Text, Maybe Text, Text)]
  }

-- | The elaborated carrier prefix of a prefixed comprehension (§20.9):
-- the prefix term and its (forced) type.
type CarrierPrefix = (Term, Value)

data DeclarationUniverseRoles = DeclarationUniverseRoles
  { durGeneralizable :: !(Set LevelMeta)
  , durMinimizable :: !(Set LevelMeta)
  }

-- | Whether an initial header-boundary pass may minimize checker-created
-- occurrence levels in source-explicit interfaces whose bodies are still
-- deferred.  Completed-body closeout must preserve every unrelated deferred
-- interface: repeating the header exception there makes elaboration
-- quadratic and lets unrelated source order participate in principalization.
data DeferredExplicitUniverseTreatment
  = MinimizeDeferredExplicitUniverses
  | PreserveDeferredExplicitUniverses
  deriving (Eq)

-- | Positive scopes are used for incremental body closeout; the ordinary
-- module boundary retains its natural negative deferral set.  Keeping the two
-- representations explicit prevents a one-owner closeout from allocating and
-- rescanning the complement of the whole current module.
data DeclarationUniverseScope
  = GeneralizeAllExcept !(Set GName)
  | GeneralizeOnly !(Set GName)

-- | Reverse identity index used while body declarations close.  Header-owned
-- interfaces are indexed once; each completed Core body contributes one
-- incremental entry.  Universe publication changes only telescope spines, not
-- referenced global identities, so the index remains valid across SCC
-- rebuilds and avoids rediscovering every consumer at each body boundary.
type UniversePublicationConsumers = Map GName (Set GName)

instance Semigroup DeclarationUniverseRoles where
  DeclarationUniverseRoles g1 m1 <> DeclarationUniverseRoles g2 m2 =
    DeclarationUniverseRoles (Set.union g1 g2) (Set.union m1 m2)

instance Monoid DeclarationUniverseRoles where
  mempty = DeclarationUniverseRoles Set.empty Set.empty

-- | Evidence authority consumed by the role fixed point.  The key includes
-- the nominal block, declaration-universe parameter, and normalized one-hole
-- operator.  It is populated exactly once before iteration; replay never
-- launches open-ended trait search (§10.4.3.4).
type FrozenMonotoneKey = (GName, Int, NeutralLevelTerm)

type FrozenMonotoneEvidence = Map FrozenMonotoneKey NominalMonotoneWitness

-- | The constructor argument (field) types of a data type, as core
-- terms, each closed over the data parameters as the OUTERMOST de Bruijn
-- binders. 'tdParamCount' leading 'CPi' binders of the elaborated
-- constructor type are the (implicit) parameters; every remaining 'CPi'
-- domain up to the result head is a field type. The returned 'pfDepth'
-- is the number of binders in scope at the field domain (parameters plus
-- the earlier fields of the same constructor), so that parameter @j@
-- (0-based, first parameter) sits at de Bruijn index @pfDepth - 1 - j@.
data PosField = PosField
  { pfDepth :: !Int
  , pfType :: !Term
  }

-- | Per-data-type positivity input gathered from the elaborated state.
data PosData = PosData
  { pdName :: !GName
  , pdParamCount :: !Int
  , pdFields :: ![PosField] -- ^ across all constructors of this type
  , pdSpan :: !Span
  }

data InferredMeasureShape
  = InferredParameter !Int
  | InferredDifference !Int !Int
  | InferredDifferencePlusOne !Int !Int
  | InferredSuccessorDifference !Int !Int
  deriving stock (Eq, Show)

data TermFun = TermFun
  { tfDecl :: !TerminationDecl
  , tfName :: !GName
  , tfCtx :: !Ctx
  , tfNatLvls :: !(Set Int)
  , tfParams :: ![(Icit, Int)]
  , tfExplParams :: ![Int]
  , tfParamNames :: ![Text]
  , tfBody :: !Term
  , tfDepth :: !Int
  , tfMeasure :: !(Maybe MeasureSpec)
  }

data MeasureSpec = MeasureSpec
  { msMeasureTerm :: !Term
  , msMeasureTypeKey :: !Term
  , msRelation :: !(Maybe RelationSpec)
  , msProof :: !(Maybe Expr)
  , msDepth :: !Int
  }

data RelationSpec = RelationSpec
  { rsTerm :: !Term
  , rsTypeKey :: !Term
  , rsFlavor :: !RelationFlavor
  , rsKey :: !Term
  , rsDepth :: !Int
  , rsWellFounded :: !Bool
  }

data RelationFlavor = RelationReturnsType | RelationReturnsBool | RelationUnknown
  deriving stock (Eq, Show)

data CallEdge = CallEdge
  { edgeFrom :: !GName
  , edgeTo :: !GName
  , edgeUniverses :: ![Level]
  , edgeDepth :: !Int
  , edgeFacts :: ![AFact]
  , edgeBoolFacts :: ![(Term, Bool)]
  , edgeArgs :: ![(Icit, Term)]
  , edgeStructuralOrigins :: !StructuralOrigins
  }
  deriving stock (Show)

data StructuralStep
  = StructuralPosition !Int
  | StructuralField !Text
  | StructuralVariant !Text
  deriving stock (Eq, Ord, Show)

data StructuralOrigin = StructuralOrigin
  { structuralRoot :: !Int
  , structuralPath :: ![StructuralStep]
  }
  deriving stock (Eq, Ord, Show)

data StructuralShape
  = StructuralCtor !GName ![Level]
  | StructuralLiteral !Literal
  deriving stock (Eq, Ord, Show)

data StructuralOrigins = StructuralOrigins
  { structuralLocals :: !(Map Int (Set StructuralOrigin))
  , structuralShapes :: !(Map StructuralShape (Set StructuralOrigin))
  }
  deriving stock (Eq, Show)

data PartialCall = PartialCall
  { pcTarget :: !GName
  , pcUniverses :: ![Level]
  , pcDepth :: !Int
  , pcArgs :: ![(Icit, Term)]
  }
  deriving stock (Show)

data SccReferenceMode
  = AnySccReference
  | IncompleteSccClosure
  deriving stock (Eq)

data MeasureCall = MeasureCall
  { mcDepth :: !Int
  , mcFacts :: ![AFact]
  , mcOldMeasure :: !Term
  , mcNewMeasure :: !Term
  , mcRelation :: !(Maybe RelationSpec)
  , mcProof :: !(Maybe Expr)
  , mcSource :: !TermFun
  }

data CompareBoolMatch = CompareLt | CompareLe | CompareGt | CompareGe
  deriving stock (Eq, Show)

-- | The exact checked shape used to generate a 'RefinementView' dictionary.
-- Field positions are source-constructor positions, but their semantic roles
-- were selected from instantiated checked types and resolved global identity.
-- Textual names are used only to emit ordinary syntax that is re-resolved by
-- the checker.
data DerivedRefinementViewShape = DerivedRefinementViewShape
  { drvsConstructor :: !GName
  , drvsFieldCount :: !Int
  , drvsFieldIcit :: ![Icit]
  , drvsBaseIndex :: !Int
  , drvsIsPropIndex :: !Int
  , drvsProofIndex :: !Int
  , drvsBaseFieldName :: !(Maybe Text)
  , drvsIsPropFieldName :: !Text
  , drvsProofFieldName :: !Text
  , drvsBaseType :: !Expr
  , drvsPredicateBody :: !Expr
  }

data InstantiatedRefinementField = InstantiatedRefinementField
  { irfSourceIndex :: !Int
  , irfArgumentIndex :: !Int
  , irfMode :: !ObservationMode
  , irfQuantity :: !Q
  , irfRuntimeErasure :: !(RuntimeErasure ())
  , irfType :: !Value
  , irfArgument :: !ConstructorArg
  }

data DerivedNominalField = DerivedNominalField
  { dnfQuantity :: !Q
  , dnfTypeTerm :: !Term
  , dnfTypeExpression :: !Expr
  }

type DerivedNominalShape = [(GName, [DerivedNominalField])]

type DerivedEqEvidenceNames = Map GName [Maybe Name]

data DerivedEqFieldMethod
  = DerivedEqFieldEvidence !(Maybe Name)
  | DerivedEqFieldRecursive
  deriving stock (Eq)

type DerivedEqFieldMethods = Map GName [DerivedEqFieldMethod]

data DerivedFunctionalEquality = DerivedFunctionalEquality
  { dfeIdentity :: !GName
  , dfeBindingName :: !Name
  , dfeTerm :: !Term
  , dfeType :: !Value
  , dfeDomain :: !Value
  , dfeDomainExpr :: !Expr
  , dfeShape :: !DerivedNominalShape
  , dfeMethods :: !DerivedEqFieldMethods
  }

data DerivedEqEvidenceBinding = DerivedEqEvidenceBinding
  { deebName :: !Name
  , deebDictionary :: !Term
  , deebDictionaryType :: !Value
  }
