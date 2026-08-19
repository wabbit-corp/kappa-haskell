{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

-- | KBackendIR Phase A: a target-neutral runtime tree.
--
-- This module is deliberately not an annotated 'Kappa.Core.Term'. The lowering
-- constructs a separate recursive datatype whose runtime children are already
-- erased: q0/kind-domain binders are not KBackendIR binders, erased call
-- arguments are not KBackendIR arguments, and type/proof-only subterms that
-- still reach runtime value position are recorded as lowering violations before
-- target emission.
module Kappa.Backend.IR
  ( BackendNodeId (..)
  , BackendBinderId (..)
  , BackendUseId (..)
  , KBackendIR (..)
  , BackendBody (..)
  , BackendParam (..)
  , BackendErasure (..)
  , ErasureSite (..)
  , ErasureProvenance (..)
  , BackendTerm (..)
  , BackendPat (..)
  , BackendAlt (..)
  , BackendItem (..)
  , BackendCond (..)
  , BackendMeta (..)
  , BackendBinder (..)
  , BackendUse (..)
  , BackendCtorLayout (..)
  , BackendSourceFieldIdentity (..)
  , BackendFieldStorage (..)
  , BackendRepresentationSubject (..)
  , BackendRepresentationDecision (..)
  , BackendExactNaturalOperation (..)
  , BackendIRViolation (..)
  , lowerKBackendIR
  , lowerKBackendIRForCapabilities
  , backendExactNaturalOperation
  , runtimeArgumentFreeGlobal
  , kbackendRepresentationCertificates
  , validateCoreCapabilities
  , validateKBackendIR
  ) where

import Control.Applicative ((<|>))
import Control.Monad (forM, forM_, guard, unless, when)
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable (toList)
import Data.List (elemIndex, find, foldl', nub, sort, zip4)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, listToMaybe, mapMaybe, maybeToList)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

import qualified Kappa.Backend.Repr as Repr
import Kappa.Backend.Repr (ArgConv, CtorLayoutInfo (..))
import Kappa.Builtins
  ( gPrel
  , preludeModule
  , prelFin
  , prelEffLabel
  , prelEffOp
  , prelHandleEff
  , prelIO
  , prelInteger
  , prelIsSet
  , prelNat
  , prelNatAdd
  , prelNatAddRightIdentity
  , prelNatCompare
  , prelNatMultiply
  , prelNatSucc
  , prelNatZero
  , prelPathInd
  , prelRefl
  , prelRefined
  , prelRuntimeErased
  , prelSTM
  , prelSubst
  , prelTypeLevel
  , prelTypeLevelAdd
  , prelTypeLevelFromInteger
  , prelTypeLevelMax
  , prelTypeLevelOmega
  , prelTypeLevelOmegaAlias
  , prelTypeLevelOne
  , prelTypeLevelSucc
  , prelTypeLevelZero
  , traitFromInteger
  )
import Kappa.Check
  ( CheckState (..)
  , DataInfo (..)
  , CtorInfo (..)
  , InstanceEntry (..)
  , LevelOperatorIdentity (..)
  , TraitInfo (..)
  , exactNaturalRepresentationForState
  , linkedCoreBodies
  , metaObservationMode
  , nominalHiddenProjectionInfo
  , ordinalRepresentationForState
  , refinementRepresentationForState
  )
import Kappa.Core
import Kappa.CoreOps
  ( authenticatedLevelAssumptionWith
  , coreToNeutralLevelTerm
  , declarationUniverseConstraints
  , finalizedSemanticSpineAfterGeneratedConstraints
  , levelMetasOfTerm
  , metaIdsOf
  , levelParamsOfTerm
  , patBindersC
  , shiftTerm
  , specializeTraitMemberProjectionType
  , specializeTraitMemberStorageType
  , spineOfTerm
  , spineOfTermWithErasure
  , substTopTermAt
  , termAsLevel
  , termScopedAt
  , zonkTermWith
  )
import Kappa.Eval
  ( EvalCtx (..)
  , GlobalDef (..)
  , Globals (..)
  , canonicalEqualityPayload
  , convertible
  , eval
  , force
  , quote
  , specializeGlobalDefinitionTypePrefix
  )
import Kappa.Level
  ( Assumptions
  , SolveResult (..)
  , abstractLocalLevelParams
  , assumptionsConsistent
  , assumptionsList
  , instantiateLocalLevelParams
  , emptyAssumptions
  , insertAssumption
  , levelAdd
  , levelFields
  , levelMax
  , levelMetas
  , neutralLevelTermAtom
  , levelParams
  , levelSucc
  , levelVars
  , normalizeLevel
  , proveLevelEq
  , proveLevelLeq
  , renderLevel
  , substituteLevelMetas
  , substituteLevelParams
  )
import Kappa.NominalVariance
  ( NominalCumulativitySummary (..)
  , UniverseVariance (..)
  , verifyNominalCumulativitySummary
  )
import Kappa.LevelEvidence
  ( coreTypeIsTypeLevel
  , scopeRecordFields
  , scopeRecordLevelAssumption
  )
import Kappa.Ownership
  ( BinderOwn (..)
  , UseKind (..)
  )
import Kappa.ObservationDeps
  ( ObservationBinding (..)
  , ObservationOracle (..)
  , ParametricOrigin (..)
  , classifierRelativeDependencies
  , dependencyBlocksFinalizedAnalysis
  , constructorPatternObservationSites
  , dependenciesMode
  , evidenceRelativeCallableDependencies
  , intrinsicEffectConstructorType
  , isParametricKindValue
  , observationDependencies
  , parametricCodomainPropagates
  , observationCallableType
  )
import Kappa.Pretty (renderTerm)
import Kappa.Representation
  ( BackendProfileRestriction
  , ConstructorFieldPath (..)
  , ExactNaturalRepresentationCertificate (..)
  , OrdinalRepresentationCertificate (..)
  , RefinementRepresentationCertificate (..)
  , RepresentationContext (..)
  , VerifiedRepresentationCertificate (..)
  , exactNaturalRepresentationCertificateIdentity
  , ordinalRepresentationCertificateIdentity
  , representationTypeIdentity
  , refinementRepresentationCertificateIdentity
  , verifyExactNaturalRepresentationCertificate
  , verifyOrdinalRepresentationCertificate
  , verifyRefinementRepresentationCertificate
  )
import Kappa.Source (ModuleName)

data ParamLowerSite = ParamLowerSite
  { plsIcit :: !Icit
  , plsMode :: !ObservationMode
  , plsQ :: !Q
  , plsBorrowed :: !Bool
  , plsErasure :: !(Maybe ErasureProvenance)
  , plsDomain :: !Value
  }
  deriving stock (Show)

newtype BackendNodeId = BackendNodeId Int
  deriving stock (Eq, Ord, Show)

newtype BackendBinderId = BackendBinderId Int
  deriving stock (Eq, Ord, Show)

newtype BackendUseId = BackendUseId Int
  deriving stock (Eq, Ord, Show)

data KBackendIR = KBackendIR
  { kbirModule :: !ModuleName
  , kbirBodies :: !(Map GName BackendBody)
  , kbirCapabilities :: !(Set Text)
  , kbirExactNaturalCertificate :: !(Maybe ExactNaturalRepresentationCertificate)
  , kbirSourceFields :: !(Map BackendSourceFieldIdentity BackendFieldStorage)
  , kbirRepresentations :: !(Map BackendRepresentationSubject BackendRepresentationDecision)
  , kbirLoweringViolations :: ![BackendIRViolation]
  }
  deriving stock (Eq, Show)

data BackendBody = BackendBody
  { bbOwner :: !GName
  , bbParams :: ![BackendParam]
  , bbErasures :: ![BackendErasure]
  , bbRoot :: !BackendTerm
  }
  deriving stock (Eq, Show)

data BackendParam = BackendParam
  { bpIcit :: !Icit
  , bpName :: !Text
  , bpBinder :: !(Maybe BackendBinder)
  }
  deriving stock (Eq, Show)

-- | Why a source-level binder is absent from runtime KBackendIR.  Keeping
-- these cases distinct is the §30.2.2.9 erasure-justification boundary: a
-- quantity-zero type witness must never be reconstructed as an ordinary type
-- code merely because both have no runtime slot.
data ErasureProvenance
  = ErasedOrdinaryTypeCode
  | ErasedIntrinsicCompileTimeValue
  | ErasedParametricTypeWitness !Level
  | ErasedParametricTypeFormer
  | ErasedProofOrTraitEvidence
  | ErasedBySelectedEvidence !Term !Term !Term
  | ErasedByQuantity
  deriving stock (Eq, Show)

data BackendErasure = BackendErasure
  { beNode :: !BackendNodeId
  , beDepth :: !Int
  , beSite :: !ErasureSite
  , beIcit :: !Icit
  , beName :: !Text
  , beProvenance :: !ErasureProvenance
  }
  deriving stock (Eq, Show)

data ErasureSite
  = ErasedParameterSite
  | ErasedLambdaSite
  | ErasedLetSite
  | ErasedApplicationArgumentSite
  | ErasedRecordFieldSite
  | ErasedConstructorFieldSite
  | ErasedPatternSlotSite
  | ErasedMatchScrutineeSite
  deriving stock (Eq, Ord, Show)

data BackendMeta = BackendMeta
  { bmNodeId :: !BackendNodeId
  , bmBranchDrops :: ![BackendBinder]
  }
  deriving stock (Eq, Show)

data BackendBinder = BackendBinder
  { bbBinderId :: !BackendBinderId
  , bbBinderOrigin :: !Text
  , bbBinderOwn :: !BinderOwn
  , bbBinderHasConsumingLastUse :: !Bool
  }
  deriving stock (Eq, Show)

data BackendUse = BackendUse
  { buUseId :: !BackendUseId
  , buUseKind :: !UseKind
  , buConsumes :: !Bool
  }
  deriving stock (Eq, Show)

data BackendCtorLayout = BackendCtorLayout
  { bclCtor :: !GName
  , bclInfo :: !(Maybe CtorLayoutInfo)
  , bclRuntimeFields :: !Int
  }
  deriving stock (Eq, Show)

-- | Stable source identity for one constructor field.  Layout verification
-- uses the nominal family and constructor identities plus the source index;
-- the readable name is presentation metadata only.
data BackendSourceFieldIdentity = BackendSourceFieldIdentity
  { bsfiOwner :: !GName
  , bsfiConstructor :: !GName
  , bsfiSourceIndex :: !Int
  , bsfiName :: !Text
  }
  deriving stock (Eq, Ord, Show)

data BackendFieldStorage
  = BackendFieldStored
  | BackendFieldErased !ErasureProvenance
  deriving stock (Eq, Show)

data BackendRepresentationSubject
  = BackendDeclarationSubject !GName
  | BackendConstructorFieldSubject !BackendSourceFieldIdentity
  deriving stock (Eq, Ord, Show)

-- | A canonical logical-'Nat' operation whose compact runtime lowering is
-- authorized by 'kbirExactNaturalCertificate'.  The constructor is selected
-- from checked global identity, never source spelling; both native emitters
-- consume this shared classification.
data BackendExactNaturalOperation
  = BackendNaturalAdd
  | BackendNaturalMultiply
  | BackendNaturalCompare
  deriving stock (Eq, Ord, Show)

-- | One final target-profile representation choice.  Certificates are kept on
-- the decision so the KBackendIR verifier replays the same evidence that
-- selected the class; identities alone are cache keys, not proof.
data BackendRepresentationDecision = BackendRepresentationDecision
  { brdTypeIdentity :: !Text
  , brdClass :: !Repr.VerifiedRepresentationClass
  , brdRequiredExactNatural :: !Bool
  , brdOrdinalCertificate :: !(Maybe OrdinalRepresentationCertificate)
  , brdExactNaturalCertificate :: !(Maybe ExactNaturalRepresentationCertificate)
  , brdRefinementCertificate :: !(Maybe RefinementRepresentationCertificate)
  , brdProfileRestrictions :: ![BackendProfileRestriction]
  , brdWrapperEliminated :: !Bool
  , brdErasedFields :: ![BackendSourceFieldIdentity]
  }
  deriving stock (Eq, Show)

data BackendIRViolation = BackendIRViolation
  { bivBody :: !GName
  , bivNode :: !BackendNodeId
  , bivCode :: !Text
  , bivMessage :: !Text
  , bivPayloadFields :: ![(Text, Text)]
  }
  deriving stock (Eq, Show)

data BackendTerm
  = BUnit !BackendMeta
  | BVar !BackendMeta !(Maybe BackendUse) !Int
  | BGlob !BackendMeta !GName
  | BLit !BackendMeta !Literal
  | BLam !BackendMeta !(Maybe BackendBinder) !Icit !Q !Text !BackendTerm
  | BApp !BackendMeta !BackendTerm ![(Icit, Maybe ArgConv, BackendTerm)]
  | BCtor !BackendMeta !BackendCtorLayout ![BackendTerm]
  | BMatch !BackendMeta !BackendTerm ![BackendAlt] ![(GName, BackendCtorLayout)]
  | BRecord !BackendMeta ![(Text, BackendTerm)]
  | BProj !BackendMeta !BackendTerm !Text !(Maybe Int)
  | BInject !BackendMeta !Text !BackendTerm
  | BLet !BackendMeta !(Maybe BackendBinder) !Q !Text !BackendTerm !BackendTerm
  | BLetRec !BackendMeta !(Maybe BackendBinder) !Q !Text !BackendTerm !BackendTerm
  | BDo !BackendMeta !(Maybe Text) ![BackendItem]
  | BSeal !BackendMeta ![Text] !BackendTerm
  | BThunk !BackendMeta !BackendTerm
  | BLazy !BackendMeta !BackendTerm
  | BForce !BackendMeta !BackendTerm
  | BIf !BackendMeta !BackendTerm !BackendTerm !BackendTerm
  deriving stock (Eq, Show)

-- | Recover a global identity only when KBackendIR proves that no runtime
-- application arguments are attached. Quantity-0 and selected evidence
-- erasure has already happened before this phase, so any surviving 'BApp'
-- child is semantically relevant regardless of its source icity.
runtimeArgumentFreeGlobal :: BackendTerm -> Maybe GName
runtimeArgumentFreeGlobal = \case
  BGlob _ global -> Just global
  BSeal _ _ term -> runtimeArgumentFreeGlobal term
  _ -> Nothing

data BackendAlt = BackendAlt
  { baMeta :: !BackendMeta
  , baPat :: !BackendPat
  , baBinders :: ![Maybe BackendBinder]
  , baGuard :: !(Maybe BackendTerm)
  , baBody :: !BackendTerm
  }
  deriving stock (Eq, Show)

data BackendPat
  = BPWild
  | BPVar !Text
  | BPLit !Literal
  | BPCtor !GName !Int ![(Int, BackendPat)]
  | BPTuple !Int ![(Int, BackendPat)]
  | BPRecord ![(Text, BackendPat)] !(Maybe Text)
  | BPInject !Text !BackendPat
  | BPInjectRest ![Text]
  | BPOr ![BackendPat] ![[Int]]
  | BPAs !Text !BackendPat
  deriving stock (Eq, Show)

data BackendItem
  = BKBind !BackendMeta !Q !BackendPat ![Maybe BackendBinder] !BackendTerm !(Maybe RefActionWitness)
  | BKLet !BackendMeta !Q !BackendPat ![Maybe BackendBinder] !BackendTerm
  | BKLetQ !BackendMeta !BackendPat ![Maybe BackendBinder] !BackendTerm !(Maybe (BackendPat, [Maybe BackendBinder], BackendTerm))
  | BKExpr !BackendMeta !BackendTerm
  | BKVarItem !BackendMeta !(Maybe BackendBinder) !BackendTerm !BackendTerm !(Maybe RefActionWitness)
  | BKAssign !BackendMeta !Bool !BackendTerm !BackendTerm !(Maybe RefActionWitness)
  | BKReturn !BackendMeta !BackendTerm
  | BKWhile !BackendMeta !(Maybe Text) !BackendCond ![BackendItem] !(Maybe [BackendItem])
  | BKFor !BackendMeta !(Maybe Text) !BackendPat ![Maybe BackendBinder] !BackendTerm ![BackendItem] !(Maybe [BackendItem])
  | BKIf !BackendMeta ![(BackendTerm, [BackendItem])] !(Maybe [BackendItem])
  | BKDefer !BackendMeta !(Maybe Text) !BackendTerm
  | BKUsing !BackendMeta !BackendPat ![Maybe BackendBinder] !BackendTerm !BackendTerm
  | BKSubDo !BackendMeta !(Maybe Text) ![BackendItem]
  | BKBreak !BackendMeta !(Maybe Text)
  | BKContinue !BackendMeta !(Maybe Text)
  deriving stock (Eq, Show)

data BackendCond
  = BKCondPure !BackendTerm
  | BKCondAction !BackendTerm
  deriving stock (Eq, Show)

data LowerStatic = LowerStatic
  { lsOwner :: !GName
  , lsGlobals :: !(Map GName GlobalDef)
  , lsDatas :: !(Map GName DataInfo)
  , lsCtors :: !(Map GName CtorInfo)
  , lsTraits :: !(Map GName TraitInfo)
  , lsInstances :: ![InstanceEntry]
  , lsRuntimeErasedProofHeads :: !(Set GName)
  , lsBuiltinIntegerLiteralDicts :: !(Set GName)
  , lsCtx :: !EvalCtx
  }

data LowerState = LowerState
  { lstNextNode :: !Int
  , lstNextBinder :: !Int
  , lstLoweringViolations :: ![BackendIRViolation]
  , lstErasures :: ![BackendErasure]
  }

-- | One term-level scope slot. A local declaration universe telescope is
-- attached to the same de Bruijn binder as its generalized type; it is static
-- schema identity and never contributes a runtime slot.
data ScopeSlot = ScopeSlotData
  !(Maybe BackendBinderId)
  !(Maybe Value)
  !(Maybe DeclarationUniverseTelescope)
  !(Maybe RuntimeLocalAlias)

data RuntimeLocalAlias = RuntimeLocalAlias
  { rlaGroupBinder :: !BackendBinderId
  , rlaField :: !Text
  }

pattern ScopeSlot :: Maybe BackendBinderId -> Maybe Value -> Maybe DeclarationUniverseTelescope -> ScopeSlot
pattern ScopeSlot binder ty telescope <- ScopeSlotData binder ty telescope _
  where
    ScopeSlot binder ty telescope = ScopeSlotData binder ty telescope Nothing

{-# COMPLETE ScopeSlot #-}

type ScopeStack = [ScopeSlot]
type Lower = ReaderT LowerStatic (State LowerState)
type BinderEnv = Map BackendBinderId BackendBinder

finalizedGlobalType :: EvalCtx -> GlobalDef -> Term
finalizedGlobalType ctx definition =
  fromMaybe (quote ctx 0 (gdType definition)) (gdCoreType definition)

lowerKBackendIR :: CheckState -> KBackendIR
lowerKBackendIR = lowerKBackendIRForCapabilities Set.empty

-- | Lower for one declared backend profile. Optional representation classes
-- are selected only from this explicit capability set; target-neutral callers
-- get the conservative profile through 'lowerKBackendIR'.
lowerKBackendIRForCapabilities :: Set Text -> CheckState -> KBackendIR
lowerKBackendIRForCapabilities capabilities st =
  let bodies = linkedCoreBodies st
      builtinIntegerLiteralDicts =
        Set.fromList
          [ ieDict entry
          | entry <- csInstances st
          , ieTrait entry == gPrel traitFromInteger
          , let GName dictionaryModule _ = ieDict entry
          , dictionaryModule == preludeModule
          , case ieHead entry of
              [classifier] -> coreHeadGlobal classifier == Just prelInteger
              _ -> False
          ]
      lowered =
        Map.mapWithKey
          (lowerBody ctx globals (csDatas st) (csCtors st) (csTraits st) (csInstances st) builtinIntegerLiteralDicts)
          bodies
      exactNaturalCertificate =
        exactNaturalRepresentationForState
          st
          emptyRepresentationContext
          0
          (eval ctx [] (CGlob prelNat))
      fieldFacts = backendSourceFieldFacts st ctx
      sourceFields =
        Map.fromList
          [ (identity, storage)
          | (identity, storage, _) <- fieldFacts
          ]
      declarationRepresentations =
        mapMaybe
          (\(global, _) -> do
            definition <- Map.lookup global globals
            let ty = eval ctx [] (finalizedGlobalType ctx definition)
            guard (representationValueType ctx ty)
            pure
              ( BackendDeclarationSubject global
              , selectBackendRepresentation
                  st capabilities emptyRepresentationContext 0 ty sourceFields
              ))
          (Map.toAscList bodies)
      fieldRepresentations =
        mapMaybe
          (\(identity, storage, mFieldType) -> do
            guard (storage == BackendFieldStored)
            fieldType <- mFieldType
            closedType <- closeRepresentationValue ctx fieldType
            guard (representationValueType ctx closedType)
            pure
              ( BackendConstructorFieldSubject identity
              , selectBackendRepresentation
                  st capabilities emptyRepresentationContext 0 closedType sourceFields
              ))
          fieldFacts
   in KBackendIR
        { kbirModule = csModule st
        , kbirBodies = Map.map fst lowered
        , kbirCapabilities = capabilities
        , kbirExactNaturalCertificate = exactNaturalCertificate
        , kbirSourceFields = sourceFields
        , kbirRepresentations =
            Map.fromList (declarationRepresentations ++ fieldRepresentations)
        , kbirLoweringViolations = concatMap snd (Map.elems lowered)
        }
  where
    globals = csGlobals st
    ctx = EvalCtx (Globals globals) (csMetas st) False (csFacts st)

-- | Canonical, identity-deduplicated certificate material selected for this
-- backend artifact. KCoreText emission consumes this exact set; it must not
-- rescan source declarations and independently guess representation evidence.
kbackendRepresentationCertificates
  :: KBackendIR
  -> [VerifiedRepresentationCertificate]
kbackendRepresentationCertificates backendIr =
  Map.elems . Map.fromList $
    concatMap certificatesForDecision
      [ decision
      | (subject, decision) <- Map.toAscList (kbirRepresentations backendIr)
      , representationSubjectModule subject == kbirModule backendIr
      ]
  where
    representationSubjectModule = \case
      BackendDeclarationSubject (GName owner _) -> owner
      BackendConstructorFieldSubject identity ->
        case bsfiOwner identity of
          GName owner _ -> owner

    certificatesForDecision decision =
      [ ( ordinalRepresentationCertificateIdentity certificate
        , VerifiedOrdinalRepresentation certificate
        )
      | certificate <- maybeToList (brdOrdinalCertificate decision)
      ]
        ++ [ ( exactNaturalRepresentationCertificateIdentity certificate
             , VerifiedExactNaturalRepresentation certificate
             )
           | certificate <- maybeToList (brdExactNaturalCertificate decision)
           ]
        ++ [ ( refinementRepresentationCertificateIdentity certificate
             , VerifiedRefinementRepresentation certificate
             )
           | certificate <- maybeToList (brdRefinementCertificate decision)
           ]

-- | Classify a canonical logical-natural operation only when the backend IR
-- carries a replayable certificate for the canonical 'Nat' representation.
-- A custom operation with the same readable name, or a certificate for a
-- different unary type, does not pass this boundary.
backendExactNaturalOperation
  :: Maybe ExactNaturalRepresentationCertificate
  -> GName
  -> Maybe BackendExactNaturalOperation
backendExactNaturalOperation maybeCertificate operation = do
  certificate <- maybeCertificate
  guard (verifyExactNaturalRepresentationCertificate certificate == Right ())
  guard
    ( coreHeadGlobal (enrcRepresentedType certificate) == Just prelNat
        && enrcZeroConstructor certificate == prelNatZero
        && enrcSuccessorConstructor certificate == prelNatSucc
    )
  if
    | operation == prelNatAdd -> Just BackendNaturalAdd
    | operation == prelNatMultiply -> Just BackendNaturalMultiply
    | operation == prelNatCompare -> Just BackendNaturalCompare
    | otherwise -> Nothing

emptyRepresentationContext :: RepresentationContext
emptyRepresentationContext =
  RepresentationContext
    { rcBinderTypes = []
    , rcUniverseConstraints = []
    }

representationValueType :: EvalCtx -> Value -> Bool
representationValueType ctx value =
  case force ctx value of
    VPi {} -> False
    VSort {} -> False
    _ -> True

-- | A field containing local constructor parameters needs a contextual
-- certificate. Until that context is recorded in the field subject, retain the
-- conservative class rather than accidentally hashing an open term as closed.
closeRepresentationValue :: EvalCtx -> Value -> Maybe Value
closeRepresentationValue ctx value =
  let term = quote ctx 0 (force ctx value)
   in if termScopedAt 0 term
        then Just (eval ctx [] term)
        else Nothing

backendSourceFieldFacts
  :: CheckState
  -> EvalCtx
  -> [(BackendSourceFieldIdentity, BackendFieldStorage, Maybe Value)]
backendSourceFieldFacts state ctx =
  concatMap fieldsForConstructor (Map.toAscList (csCtors state))
  where
    fieldsForConstructor (constructor, info) =
      let sourceFields = ciSourceFields info
          placements =
            sourceCtorFieldRuntimePlacements
              ctx
              (length sourceFields)
              (eval ctx [] (ciType info))
       in [ ( identity sourceIndex sourceName
            , if runtime
                then BackendFieldStored
                else BackendFieldErased
                  (fromMaybe ErasedByQuantity provenance)
            , fieldType
            )
          | ( sourceIndex
            , ((_, sourceName), (runtime, _, fieldType, provenance))
            ) <- zip [0 :: Int ..] (zip sourceFields placements)
          ]
      where
        identity sourceIndex sourceName =
          BackendSourceFieldIdentity
            { bsfiOwner = ciData info
            , bsfiConstructor = constructor
            , bsfiSourceIndex = sourceIndex
            , bsfiName =
                fromMaybe
                  ("field" <> T.pack (show sourceIndex))
                  sourceName
            }

selectBackendRepresentation
  :: CheckState
  -> Set Text
  -> RepresentationContext
  -> Int
  -> Value
  -> Map BackendSourceFieldIdentity BackendFieldStorage
  -> BackendRepresentationDecision
selectBackendRepresentation
  state capabilities context depth represented sourceFields =
  BackendRepresentationDecision
    { brdTypeIdentity = selectedTypeIdentity
    , brdClass = selectedClass
    , brdRequiredExactNatural = isJust exactNatural
    , brdOrdinalCertificate = ordinal
    , brdExactNaturalCertificate = exactNatural
    , brdRefinementCertificate = refinement
    , brdProfileRestrictions =
        sort . nub $
          maybe [] orcProfileRestrictions ordinal
            ++ maybe [] enrcProfileRestrictions exactNatural
            ++ maybe [] rrcProfileRestrictions refinement
    , brdWrapperEliminated = False
    , brdErasedFields =
        sort . nub . mapMaybe resolveField $
          maybe [] orcErasedFields ordinal
            ++ maybe [] enrcErasedFields exactNatural
            ++ maybe [] rrcErasedEvidenceFields refinement
    }
  where
    evaluation =
      EvalCtx
        (Globals (csGlobals state))
        (csMetas state)
        False
        (csFacts state)
    representedTerm = quote evaluation depth (force evaluation represented)
    selectedTypeIdentity =
      representationTypeIdentity context representedTerm
    ordinal =
      ordinalRepresentationForState state context depth represented
    exactNatural =
      exactNaturalRepresentationForState state context depth represented
    refinement =
      refinementRepresentationForState state context depth represented
    selectedClass
      | "rt-compact-finite-ordinal" `Set.member` capabilities
      , Just certificate <- ordinal =
          Repr.FiniteOrdinal
            (orcCardinalityExpression certificate)
            (ordinalRepresentationCertificateIdentity certificate)
      | Just certificate <- exactNatural =
          Repr.ExactNatural
            (exactNaturalRepresentationCertificateIdentity certificate)
      | "rt-unboxed-refinement" `Set.member` capabilities
      , Just certificate <- refinement =
          brdClass
            ( selectBackendRepresentation
                state
                capabilities
                context
                depth
                (eval evaluation (rigidEnv depth) (rrcBaseType certificate))
                sourceFields
            )
      | otherwise = Repr.ConservativeBoxed
    resolveField path =
      listToMaybe
        [ identity
        | identity <- Map.keys sourceFields
        , bsfiConstructor identity == cfpConstructor path
        , bsfiSourceIndex identity == cfpSourceIndex path
        ]

coreHeadGlobal :: Term -> Maybe GName
coreHeadGlobal = \case
  CApp _ function _ -> coreHeadGlobal function
  CUniverseLift _ _ _ term -> coreHeadGlobal term
  CSchemaLift _ _ _ _ _ _ _ _ term -> coreHeadGlobal term
  CGlobal global _ -> Just global
  _ -> Nothing

-- | Fail-closed §30.2.2.9 checkpoint over finalized typed Core. The
-- target-neutral erasure planner is the authority for whether an occurrence
-- is compile-time-only; running just its lowering-violation pass here catches
-- witness-to-runtime promotion before ownership analysis or target backend
-- selection. Other KBackendIR structural checks remain backend-stage checks.
validateCoreCapabilities :: CheckState -> [BackendIRViolation]
validateCoreCapabilities st =
  validateFinalizedLevelScopes st
    ++ validateObservationModeFlows st
    ++ filter isCoreCapabilityViolation
      (kbirLoweringViolations (lowerKBackendIR st))
  where
    isCoreCapabilityViolation violation =
      bivCode violation
        `elem`
          [ "E_PARAMETRIC_TYPE_PROMOTION"
          , "E_PROOF_RELEVANT_TRANSPORT_NOT_LOWERABLE"
          , "E_BACKENDIR_OBSERVATION_ANALYSIS"
          , "E_KCORE_SCHEMA_CERTIFICATE_INVALID"
          , "E_UNIVERSE_SCHEMA_LIFT_INVALID"
          ]

-- | Recheck observation-mode flow at the finalized KCore boundary.  Modes are
-- structural facts on binders, fields, projections, patterns, and globals;
-- this pass deliberately does not recover them from quantities or occurrence
-- wrappers.  It rejects every ordinary kind-valued sink for which the input
-- term is structurally parametric, and it checks that lambda/projection facts
-- agree with their typed classifiers.
validateObservationModeFlows :: CheckState -> [BackendIRViolation]
validateObservationModeFlows st =
  concatMap checkInterface (Map.toList globals)
    ++ concatMap checkOwner
      [ (owner, body)
      | (owner@(GName moduleName _), body) <- Map.toList (csCoreBodies st)
      , moduleName == csModule st
      ]
  where
    globals = csGlobals st
    instanceDictionaries = Set.fromList (map ieDict (csInstances st))
    ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
    observationOracle =
      ObservationOracle
        { ooEvalCtx = ctx
        , ooThisType = Nothing
        , ooGlobalMode = \global@(GName moduleName _) ->
            (gdObservationMode <$> Map.lookup global globals)
              <|> (Ordinary <$ guard (moduleName == primModule))
        , ooGlobalBody = \global -> do
            guard (global `Set.notMember` instanceDictionaries)
            definition <- Map.lookup global globals
            if gdReducible definition then gdCoreBody definition else Nothing
        , ooGlobalPrimitive = \global ->
            maybe False (maybe False primitiveValue . gdValue)
              (Map.lookup global globals)
        , ooMetaMode = metaObservationMode st ctx
        , ooInferType = \depth localBindings term ->
            termTypeAt globals (csTraits st) ctx depth
              [ScopeSlot Nothing (obType binding) (obUniverses binding) | binding <- localBindings]
              term
        , ooProjectionMode = \receiverType field ->
            case force ctx receiverType of
              VGlobN trait _ ->
                ( Map.lookup trait (csTraits st) >>= \info ->
                    Map.lookup field (tiMemberModes info)
                      <|> (Ordinary <$ lookup field (tiSupers info))
                )
                  <|> (fst <$> nominalHiddenProjectionInfo st ctx 1 (CVar 0) receiverType field)
              _ ->
                fst <$> nominalHiddenProjectionInfo st ctx 1 (CVar 0) receiverType field
        , ooProjectionType = \depth receiver receiverType field ->
            case force ctx receiverType of
              VGlobI trait universes spine -> do
                ( do
                    info <- Map.lookup trait (csTraits st)
                    guard (field `elem` tiMembers info)
                    semanticSpine <-
                      traitSemanticSpine globals (csTraits st) ctx trait spine
                    case receiver of
                      CRecordV _ ->
                        traitMemberStorageType globals ctx depth
                          (tiParamCount info) trait universes field
                          (map snd semanticSpine) receiver
                      _ ->
                        traitMemberType globals ctx depth []
                          (tiParamCount info) trait universes field
                          (map snd semanticSpine) receiver
                  )
                  <|> (snd <$> nominalHiddenProjectionInfo st ctx depth receiver receiverType field)
              _ ->
                snd <$> nominalHiddenProjectionInfo st ctx depth receiver receiverType field
        , ooProjectionTrait = \receiverType field ->
            case force ctx receiverType of
              VGlobN trait _ -> do
                info <- Map.lookup trait (csTraits st)
                guard (Map.member field (tiMemberModes info))
                pure trait
              _ -> Nothing
        , ooConstructorType = \constructor universes ->
            case Map.lookup constructor (csCtors st) of
              Nothing -> Nothing
              Just info -> specializeConstructorType ctx universes info
        , ooProvisionalUniverseMetadata = False
        , ooExpandingGlobals = Set.empty
        }

    primitiveValue value = case force ctx value of
      VPrim {} -> True
      VIOAction {} -> True
      _ -> False

    checkInterface (owner, definition) =
      checkTerm owner 0 [] [] Nothing (finalizedGlobalType ctx definition)

    checkOwner (owner, body) = case Map.lookup owner globals of
      Just def ->
        let bodyType = observationCallableType ctx 0 (gdType def)
            analysisFailures =
              Set.filter dependencyBlocksFinalizedAnalysis
                (termDependencies [] [] (Just bodyType) body)
            analysisChecks =
              [ BackendIRViolation owner (BackendNodeId (-1))
                  "E_BACKENDIR_OBSERVATION_ANALYSIS"
                  "finalized typed Core could not be analyzed by the observation-dependency calculus"
                  [("failures", T.pack (show (Set.toAscList analysisFailures)))]
              | not (Set.null analysisFailures)
              ]
         in analysisChecks
              ++ checkLeadingResult owner (gdObservationMode def) bodyType body [] [] []
              ++ checkTerm owner 0 [] [] (Just bodyType) body
      _ -> []

    checkLeadingResult owner ownerMode ty term scopes modes advertised =
      case (force ctx ty, term) of
        (VPiM expectedMode ic _ _ _ dom (Closure closureEnv cod), CLamM actualMode actualIc _ _ body)
          | ic == actualIc ->
              let advertisesDependency =
                    parametricCodomainPropagates
                      ctx
                      (length modes)
                      expectedMode
                      (Closure closureEnv cod)
               in modeMismatch owner "lambda binder" expectedMode actualMode
                    ++ checkLeadingResult owner ownerMode
                      (eval ctx (VRigid (length modes) [] : closureEnv) cod)
                      body
                      (ScopeSlot Nothing (Just dom) Nothing : scopes)
                      (actualMode : modes)
                      (advertisesDependency : advertised)
        (_, value)
          | ownerMode == Ordinary
          , let unjustified = unjustifiedResultDependencies scopes modes advertised ty value
          , not (Set.null unjustified) ->
              [promotionWithDependencies owner "global result" unjustified]
        _ -> []

    checkTerm = checkTermWithConstructorCoverage False

    checkTermWithConstructorCoverage constructorDependenciesCovered owner depth scopes modes expected term =
      localChecks ++ case term of
        CLamM actualMode ic _ _ body ->
          case expected >>= piSite depth of
            Just (expectedMode, expectedIc, dom, cod)
              | ic == expectedIc ->
                  modeMismatch owner "lambda binder" expectedMode actualMode
                    ++ checkTerm owner (depth + 1) (ScopeSlot Nothing (Just dom) Nothing : scopes)
                      (actualMode : modes) (Just cod) body
            _ -> checkTerm owner (depth + 1) (ScopeSlot Nothing Nothing Nothing : scopes) (actualMode : modes) Nothing body
        CPiRuntimeM mode _ _ _ _ _ _ _ runtimeErasure dom cod ->
          runtimeErasureChecks owner depth scopes dom runtimeErasure
            ++ concatMap (checkTerm owner depth scopes modes Nothing) (toList runtimeErasure)
            ++ checkTerm owner depth scopes modes Nothing dom
            ++ checkTerm owner (depth + 1) (ScopeSlot Nothing (Just (evalTypeAt ctx depth dom)) Nothing : scopes)
              (mode : modes) Nothing cod
        CApp {} -> checkApplication owner depth scopes modes expected term
        CUniverseLift _ _ _ inner -> checkTerm owner depth scopes modes expected inner
        CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments inner ->
          concatMap (checkTerm owner depth scopes modes Nothing) (sourceArguments ++ targetArguments)
            ++ checkTerm owner depth scopes modes expected inner
        CArithmeticProof _ -> []
        CCtorI g universes annotation arguments ->
          maybe [] (checkTerm owner depth scopes modes Nothing) annotation
            ++ constructorChecks constructorDependenciesCovered owner depth scopes modes g universes annotation True
              (zip [0 :: Int ..] arguments)
        CMatch scrut ann _resultAnn alts ->
          let scrutineeType =
                (evalTypeAt ctx depth <$> ann)
                  <|> termTypeAt globals (csTraits st) ctx depth scopes scrut
              scrutineeMode = termMode scopes modes scrut
           in checkTerm owner depth scopes modes Nothing scrut
                ++ maybe [] (checkTerm owner depth scopes modes Nothing) ann
                ++ concatMap (checkAlt owner depth scopes modes (Just scrutineeMode) scrutineeType) alts
        CRecordTQ fields -> checkRecordTypeFields owner depth scopes modes fields
        CRecordV fields ->
          recordFieldChecks owner depth scopes modes expected fields
            ++ recordValueChecks owner depth scopes modes expected fields
        CProjM _ value _ -> checkTerm owner depth scopes modes Nothing value
        CProjAtM _ value _ _ -> checkTerm owner depth scopes modes Nothing value
        CVariantT members -> concatMap (checkTerm owner depth scopes modes Nothing) members
        CInject _ value -> checkTerm owner depth scopes modes Nothing value
        CLetRuntimeM mode _ _ runtimeErasure ty rhs body ->
          let tyV = evalTypeAt ctx depth ty
              binderChecks = ordinaryDependencySinkAt scopes modes depth owner "let binding" mode tyV
                (termDependencies scopes modes (Just tyV) rhs)
           in binderChecks
                ++ runtimeErasureChecks owner depth scopes ty runtimeErasure
                ++ concatMap (checkTerm owner depth scopes modes Nothing) (toList runtimeErasure)
                ++ checkTerm owner depth scopes modes Nothing ty
                ++ checkTerm owner depth scopes modes (Just tyV) rhs
                ++ checkTerm owner (depth + 1) (ScopeSlot Nothing (Just tyV) Nothing : scopes) (mode : modes) Nothing body
        CLetRecRuntimeM mode _ _ runtimeErasure ty rhs body ->
          let tyV = evalTypeAt ctx depth ty
              scopes' = ScopeSlot Nothing (Just tyV) Nothing : scopes
              modes' = mode : modes
              binderChecks = ordinaryDependencySinkAt scopes' modes' (depth + 1) owner "recursive let binding" mode tyV
                (termDependencies scopes' modes' (Just tyV) rhs)
           in binderChecks
                ++ runtimeErasureChecks owner depth scopes ty runtimeErasure
                ++ concatMap (checkTerm owner depth scopes modes Nothing) (toList runtimeErasure)
                ++ checkTerm owner depth scopes modes Nothing ty
                ++ checkTerm owner (depth + 1) scopes' modes' (Just tyV) rhs
                ++ checkTerm owner (depth + 1) scopes' modes' Nothing body
        CLetPolyRuntimeM mode _ _ telescope runtimeErasure ty rhs body ->
          let tyV = evalTypeAt ctx depth ty
              binderChecks = ordinaryDependencySinkAt scopes modes depth owner "universe-polymorphic let binding" mode tyV
                (termDependencies scopes modes (Just tyV) rhs)
              scopes' = ScopeSlot Nothing (Just tyV) (Just telescope) : scopes
           in binderChecks
                ++ runtimeErasureChecks owner depth scopes ty runtimeErasure
                ++ concatMap (checkTerm owner depth scopes modes Nothing) (toList runtimeErasure)
                ++ checkTerm owner depth scopes modes Nothing ty
                ++ checkTerm owner depth scopes modes (Just tyV) rhs
                ++ checkTerm owner (depth + 1) scopes' (mode : modes) Nothing body
        CLetRecPolyRuntimeM mode _ _ telescope runtimeErasure ty rhs body ->
          let tyV = evalTypeAt ctx depth ty
              scopes' = ScopeSlot Nothing (Just tyV) (Just telescope) : scopes
              modes' = mode : modes
              binderChecks = ordinaryDependencySinkAt scopes' modes' (depth + 1) owner "recursive universe-polymorphic let binding" mode tyV
                (termDependencies scopes' modes' (Just tyV) rhs)
           in binderChecks
                ++ runtimeErasureChecks owner depth scopes ty runtimeErasure
                ++ concatMap (checkTerm owner depth scopes modes Nothing) (toList runtimeErasure)
                ++ checkTerm owner depth scopes modes Nothing ty
                ++ checkTerm owner (depth + 1) scopes' modes' (Just tyV) rhs
                ++ checkTerm owner (depth + 1) scopes' modes' Nothing body
        CLetRecGroupM telescope definitions body ->
          let types = [evalTypeAt ctx depth (clrdType definition) | definition <- definitions]
              recursiveScopes =
                reverse [ScopeSlot Nothing (Just ty) (Just telescope) | ty <- types] ++ scopes
              recursiveModes = reverse (map clrdMode definitions) ++ modes
              groupDepth = depth + length definitions
              definitionChecks = concat
                [ ordinaryDependencySinkAt recursiveScopes recursiveModes groupDepth owner "local recursive SCC binding" (clrdMode definition) ty
                    (termDependencies recursiveScopes recursiveModes (Just ty) (clrdRhs definition))
                    ++ runtimeErasureChecks owner depth scopes (clrdType definition) (clrdRuntimeErasure definition)
                    ++ concatMap (checkTerm owner depth scopes modes Nothing) (toList (clrdRuntimeErasure definition))
                    ++ checkTerm owner depth scopes modes Nothing (clrdType definition)
                    ++ checkTerm owner groupDepth recursiveScopes recursiveModes (Just ty) (clrdRhs definition)
                | (definition, ty) <- zip definitions types
                ]
           in definitionChecks
                ++ checkTerm owner groupDepth recursiveScopes recursiveModes Nothing body
        CDo _ items ->
          let returnSite = expected >>= either (const Nothing) Just . kernelDoResultSite
              recoveryFailure =
                [ modeViolation owner "E_BACKENDIR_RETURN_CONTRACT"
                    ("finalized do block has an expected carrier whose result-slot observation contract cannot be recovered: "
                      <> maybe "<missing>" (T.pack . show . force ctx) expected)
                | isJust expected
                , maybe False (either (const True) (const False) . kernelDoResultSite) expected
                ]
           in recoveryFailure ++ checkItems owner depth scopes modes returnSite items
        CSealE _ value -> checkTerm owner depth scopes modes expected value
        CSigT _ value -> checkTerm owner depth scopes modes Nothing value
        CThunkE value suspensionType ->
          checkTerm owner depth scopes modes Nothing value
            <> maybe [] (checkTerm owner depth scopes modes Nothing) suspensionType
        CLazyE value suspensionType ->
          checkTerm owner depth scopes modes Nothing value
            <> maybe [] (checkTerm owner depth scopes modes Nothing) suspensionType
        CForceE value resultType ->
          checkTerm owner depth scopes modes Nothing value
            ++ maybe [] (checkTerm owner depth scopes modes Nothing) resultType
        CIf cond yes no ->
          checkTerm owner depth scopes modes Nothing cond
            ++ checkTerm owner depth scopes modes expected yes
            ++ checkTerm owner depth scopes modes expected no
        CQuote _ slots -> concatMap (checkTerm owner depth scopes modes Nothing) slots
        _ -> []
      where
        localChecks = case term of
          CProjM actualMode recv field -> projectionModeChecks owner depth scopes actualMode recv field
          CProjAtM actualMode recv field _ -> projectionModeChecks owner depth scopes actualMode recv field
          _ -> []

    checkRecordTypeFields owner depth scopes modes =
      go Map.empty Map.empty [] [] 0
      where
        go _ _ _ _ _ [] = []
        go fieldLocals fieldLevels fieldScopes fieldModes fieldCount (field : rest) =
          let fieldDepth = depth + fieldCount
              scopedType =
                scopeRecordFields depth fieldCount fieldLocals fieldLevels (rfType field)
              scopedRuntimeErasure =
                fmap
                  (scopeRecordFields depth fieldCount fieldLocals fieldLevels)
                  (rfRuntimeErasure field)
              scopesHere = fieldScopes ++ scopes
              modesHere = fieldModes ++ modes
              fieldType = evalTypeAt ctx fieldDepth scopedType
              nextLocals = Map.insert (rfName field) fieldDepth fieldLocals
              nextLevels =
                if coreTypeIsTypeLevel scopedType
                  then Map.insert (rfName field) fieldDepth fieldLevels
                  else fieldLevels
           in runtimeErasureChecks owner fieldDepth scopesHere scopedType scopedRuntimeErasure
                ++ concatMap
                  (checkTerm owner fieldDepth scopesHere modesHere Nothing)
                  (toList scopedRuntimeErasure)
                ++ checkTerm owner fieldDepth scopesHere modesHere Nothing scopedType
                ++ go nextLocals nextLevels
                  (ScopeSlot Nothing (Just fieldType) Nothing : fieldScopes)
                  (rfMode field : fieldModes)
                  (fieldCount + 1)
                  rest

    runtimeErasureChecks owner depth scopes classifier = \case
      RuntimeRelevant -> []
      RuntimeErased (RuntimeErasedEvidence goal evidence evidenceType) ->
        scopeChecks ++ metaChecks ++ goalChecks ++ carrierChecks ++ evidenceChecks
        where
          terms = [("goal", goal), ("evidence", evidence), ("evidence classifier", evidenceType)]
          scopeChecks =
            [ modeViolation owner "E_BACKENDIR_ERASURE_SCOPE"
                ("selected RuntimeErased " <> what <> " escapes its lexical scope")
            | (what, selected) <- terms
            , not (termScopedAt depth selected)
            ]
          metaChecks =
            [ modeViolation owner "E_BACKENDIR_ERASURE_META"
                ("selected RuntimeErased " <> what <> " contains an unresolved term or universe metavariable")
            | (what, selected) <- terms
            , not (null (metaIdsOf selected) && null (levelMetasOfTerm selected))
            ]
          structurallyFinal = null scopeChecks && null metaChecks
          goalCarrier = case spineOfTerm (stripEvidenceWrappers goal) of
            (CGlobal trait _, [(Expl, carrier)])
              | trait == prelRuntimeErased -> Just carrier
            _ -> Nothing
          goalChecks =
            [ modeViolation owner "E_BACKENDIR_ERASURE_GOAL"
                "selected erasure evidence does not carry an exact unary RuntimeErased goal"
            | structurallyFinal
            , not (isJust goalCarrier)
            ]
          carrierChecks = case goalCarrier of
            Just carrier
              | structurallyFinal
              , not
                  ( convertible ctx depth
                      (evalTypeAt ctx depth carrier)
                      (evalTypeAt ctx depth classifier)
                  ) ->
                  [ modeViolation owner "E_BACKENDIR_ERASURE_GOAL"
                      "selected RuntimeErased goal proves a different carrier than the erased binder or field"
                  ]
            _ -> []
          evidenceChecks = case goalCarrier of
            Just _
              | structurallyFinal
              , not
                  ( selectedEvidenceHasGoalType depth scopes goal evidence
                      && convertible
                        ctx
                        depth
                        (evalTypeAt ctx depth evidenceType)
                        (evalTypeAt ctx depth goal)
                  ) ->
                  [ modeViolation owner "E_BACKENDIR_ERASURE_EVIDENCE"
                      "selected RuntimeErased dictionary does not have the stored exact goal type"
                  ]
            _ -> []

    selectedEvidenceHasGoalType depth scopes goal evidence =
      case termTypeAt globals (csTraits st) ctx depth scopes evidence of
        Just evidenceType ->
          convertible ctx depth evidenceType (evalTypeAt ctx depth goal)
        Nothing -> False

    stripEvidenceWrappers = \case
      CUniverseLift _ _ _ inner -> stripEvidenceWrappers inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> stripEvidenceWrappers inner
      term -> term

    piSite depth value = case force ctx value of
      VPiM mode ic _ _ _ dom (Closure env cod) ->
        Just (mode, ic, dom, eval ctx (VRigid depth [] : env) cod)
      _ -> Nothing

    checkApplication owner depth scopes modes _expected app =
      case betaReduceLiteralProjectionApplication depth app of
        Just reduced -> checkTerm owner depth scopes modes _expected reduced
        Nothing -> case coreEtaCtorApp depth app of
          Just (constructor, universes, annotation, _arity, arguments) ->
            constructorChecks False owner depth scopes modes constructor universes annotation False arguments
          Nothing ->
            let (headTerm, args) = spineOfTerm app
             in case headTerm of
                  CLamM {} -> walkLambda headTerm (0 :: Int) args
                  _ ->
                    checkTerm owner depth scopes modes Nothing headTerm
                      ++ case termTypeAt globals (csTraits st) ctx depth scopes headTerm of
                        Nothing -> concatMap (checkTerm owner depth scopes modes Nothing . snd) args
                        Just headTy -> walk headTerm (0 :: Int) headTy args
      where
        walkLambda reduced _ [] =
          checkTerm owner depth scopes modes _expected reduced
        walkLambda (CLamM mode expectedIc _ _ body) argumentIndex ((ic, arg) : rest)
          | ic == expectedIc =
              ordinaryDependencySink owner
                ("direct-lambda application argument " <> T.pack (show argumentIndex))
                mode
                (termDependencies scopes modes Nothing arg)
                ++ checkTerm owner depth scopes modes Nothing arg
                ++ walkLambda
                  (substTopTermAt depth arg body)
                  (argumentIndex + 1)
                  rest
        walkLambda term _ remaining =
          checkTerm owner depth scopes modes _expected
            (foldl' (\function (icit, argument) -> CApp icit function argument) term remaining)

        walk _ _ _ [] = []
        walk headTerm argumentIndex ty ((ic, arg) : rest) = case force ctx ty of
          VPiM expectedMode expectedIc _ _ _ dom (Closure env cod)
            | ic == expectedIc ->
                let sinkChecks =
                      ordinaryDependencySinkAt scopes modes depth owner
                        ( "application argument " <> T.pack (show argumentIndex)
                            <> " to " <> renderTerm headTerm
                            <> " (" <> renderTerm arg <> ")"
                        )
                        expectedMode
                        dom
                        (termDependencies scopes modes (Just dom) arg)
                    argumentChecks = checkTerm owner depth scopes modes (Just dom) arg
                    resultType = eval ctx (eval ctx (rigidEnv depth) arg : env) cod
                 in sinkChecks
                      ++ argumentChecks
                      ++ walk headTerm (argumentIndex + 1) resultType rest
          _ -> concatMap (checkTerm owner depth scopes modes Nothing . snd) ((ic, arg) : rest)

    projectionModeChecks owner depth scopes actualMode recv field =
      case termTypeAt globals (csTraits st) ctx depth scopes recv >>= expectedProjectionMode field of
        Just expectedMode -> modeMismatch owner ("projection '" <> field <> "'") expectedMode actualMode
        Nothing -> []

    expectedProjectionMode field recvTy = case force ctx recvTy of
      VRecordTQ fields -> rfMode <$> findField field fields
      VSigT _ inner -> expectedProjectionMode field inner
      VGlobN trait _ -> Map.lookup trait (csTraits st) >>= \info ->
        Map.lookup field (tiMemberModes info)
          <|> (Ordinary <$ lookup field (tiSupers info))
      _ -> Nothing

    findField field = listToMaybe . filter ((== field) . rfName)

    recordFieldChecks owner depth scopes modes expected fields = case force ctx <$> expected of
      Just (VRecordTQ declared) -> concat
        [ ordinaryDependencySinkAt scopes modes depth owner ("record field '" <> name <> "'") (rfMode field) (rfType field)
            (termDependencies scopes modes (Just (rfType field)) value)
        | (name, value) <- fields
        , field <- maybeToList (findField name declared)
        ]
      Just (VGlobI traitG universes spine)
        | Just trait <- Map.lookup traitG (csTraits st) ->
            case traitSemanticSpine globals (csTraits st) ctx traitG spine of
              Nothing ->
                [ modeViolation owner "E_BACKENDIR_OBSERVATION_ANALYSIS"
                    ( "trait dictionary record has a malformed generated-evidence/source-parameter spine for "
                        <> T.pack (show traitG)
                    )
                ]
              Just semanticSpine ->
                let dictionaryTerm = CRecordV fields
                    arguments = map snd semanticSpine
                    permitted =
                      traitParametricDependencies scopes modes depth traitG universes semanticSpine
                 in concatMap
                      (traitFieldCheck traitG universes dictionaryTerm arguments permitted trait)
                      fields
      _ -> []
      where
        traitFieldCheck traitG universes dictionaryTerm arguments permitted trait (name, value)
          | name `notElem` tiMembers trait = []
          | Just memberMode <- Map.lookup name (tiMemberModes trait) =
              let memberExpected =
                    traitMemberStorageType globals ctx depth
                      (tiParamCount trait) traitG universes name arguments dictionaryTerm
                  dependencies = termDependencies scopes modes memberExpected value
                  relative =
                    maybe dependencies
                      (\classifier -> relativeDependencies scopes modes depth classifier dependencies)
                      memberExpected
                  unjustified = relative `Set.difference` permitted
               in [ promotionWithDependencies owner ("trait dictionary field '" <> name <> "'") unjustified
                  | memberMode == Ordinary
                  , not (Set.null unjustified)
                  ]
          | otherwise =
                  [ modeViolation owner "E_BACKENDIR_BINDER_METADATA"
                      ("trait member has no observation metadata for dictionary field '" <> name <> "'")
                  ]

    recordValueChecks owner depth scopes modes expected fields =
      case force ctx <$> expected of
        Just (VRecordTQ declared) -> concat
          [ checkTerm owner depth scopes modes (rfType <$> findField name declared) value
          | (name, value) <- fields
          ]
        Just (VGlobI traitG universes spine)
          | Just trait <- Map.lookup traitG (csTraits st) ->
              let dictionaryTerm = CRecordV fields
                  checkWithoutExpected =
                    concatMap (checkTerm owner depth scopes modes Nothing . snd) fields
               in case traitSemanticSpine globals (csTraits st) ctx traitG spine of
                    Nothing -> checkWithoutExpected
                    Just semanticSpine ->
                      let arguments = map snd semanticSpine
                       in concat
                            [ let memberExpected =
                                    traitMemberStorageType globals ctx depth
                                      (tiParamCount trait) traitG universes name arguments dictionaryTerm
                               in checkTerm owner depth scopes modes memberExpected value
                            | (name, value) <- fields
                            ]
        _ -> concatMap (checkTerm owner depth scopes modes Nothing . snd) fields

    -- §14.3.1A makes a trait dictionary relative to its checked head:
    -- member behavior may depend on parametric head arguments through
    -- ordinary dictionary passing, but no unrelated parametric origin may be
    -- smuggled into an ordinary member. Recover exactly those origins from
    -- the trait's semantic Pi telescope and subtract only them.
    traitParametricDependencies scopes modes depth traitG universes arguments =
      case Map.lookup traitG globals of
        Nothing -> Set.empty
        Just definition ->
          let rawType = quote ctx 0 (gdType definition)
              specialized =
                zonkTermWith
                  (\_ _ -> Nothing)
                  (substituteLevelParams universes)
                  0
                  rawType
           in walkTraitParameters (eval ctx [] specialized) arguments
      where
        walkTraitParameters _ [] = Set.empty
        walkTraitParameters functionType ((actualIcit, argument) : rest) =
          case force ctx functionType of
            VPiM parameterMode expectedIcit _ _ _ domain (Closure closureEnv codomain)
              | actualIcit == expectedIcit ->
                  let current =
                        if parameterMode == Parametric
                          then termDependencies scopes modes (Just domain) (quote ctx depth argument)
                          else Set.empty
                      resultType = eval ctx (argument : closureEnv) codomain
                   in current `Set.union` walkTraitParameters resultType rest
            _ -> Set.empty

    -- Consume the semantic constructor Pi telescope in lockstep with actual
    -- arguments.  Flattening domains up front leaves later dependent domains
    -- filled with rigid placeholders (for example @tail : List a@), which is
    -- neither valid typing authority nor stable under erased arguments.
    constructorChecks dependenciesCovered owner depth scopes modes g universes annotation requireComplete indexedArguments =
      case specializedConstructorType g universes
        <|> intrinsicEffectConstructorType ctx depth g annotation (map snd indexedArguments) of
        Nothing ->
          modeViolation owner "E_BACKENDIR_CONSTRUCTOR_INTERFACE"
            ("constructor interface is unavailable for '" <> gnameText g <> "'")
            : concatMap (checkTerm owner depth scopes modes Nothing . caTerm . snd) indexedArguments
        Just constructorType -> walkConstructor constructorType 0 indexedArguments
      where
        walkConstructor functionType position [] =
          [ modeViolation owner "E_BACKENDIR_CONSTRUCTOR_ARITY"
              ("constructor application for '" <> gnameText g <> "' omits semantic argument "
                <> T.pack (show position))
          | requireComplete
          , VPiM {} <- [force ctx functionType]
          ]
        walkConstructor functionType position remaining@((index, argument) : rest)
          | index /= position =
              modeViolation owner "E_BACKENDIR_CONSTRUCTOR_ARITY"
                ("constructor application for '" <> gnameText g
                  <> "' has a semantic argument gap before position " <> T.pack (show index))
                : concatMap (checkTerm owner depth scopes modes Nothing . caTerm . snd) remaining
          | otherwise = case force ctx functionType of
              VPiM mode expectedIcit _ _ _ domain (Closure closureEnv codomain)
                | caIcit argument == expectedIcit ->
                    let argumentTerm = caTerm argument
                        sinkChecks = ordinaryDependencySinkAt scopes modes depth owner
                          ("constructor argument " <> T.pack (show position))
                          mode
                          domain
                          (termDependencies scopes modes (Just domain) argumentTerm)
                        coveredSinkChecks
                          | dependenciesCovered && mode == Ordinary = []
                          | otherwise = sinkChecks
                        argumentChecks
                          | mode == Ordinary =
                              checkTermWithConstructorCoverage True owner depth scopes modes (Just domain) argumentTerm
                          | otherwise =
                              checkTerm owner depth scopes modes (Just domain) argumentTerm
                     in coveredSinkChecks
                          ++ argumentChecks
                          ++ if termScopedAt depth argumentTerm
                            then
                              let argumentValue = eval ctx (rigidEnv depth) argumentTerm
                                  resultType = eval ctx (argumentValue : closureEnv) codomain
                               in walkConstructor resultType (position + 1) rest
                            else
                              modeViolation owner "E_BACKENDIR_CONSTRUCTOR_SCOPE"
                                ("constructor argument " <> T.pack (show position)
                                  <> " is outside the finalized local telescope")
                                : concatMap (checkTerm owner depth scopes modes Nothing . caTerm . snd) rest
              _ ->
                modeViolation owner "E_BACKENDIR_CONSTRUCTOR_ARITY"
                  ("constructor application for '" <> gnameText g
                    <> "' has the wrong arity or icity at position " <> T.pack (show position))
                  : concatMap (checkTerm owner depth scopes modes Nothing . caTerm . snd) remaining

    specializedConstructorType g universes =
      case Map.lookup g (csCtors st) >>= specializeConstructorType ctx (Just universes) of
        Nothing -> Nothing
        Just constructorType -> Just constructorType

    ordinaryDependencySink owner site demanded dependencies
      | demanded == Ordinary
      , not (Set.null dependencies) = [promotionWithDependencies owner site dependencies]
      | otherwise = []

    ordinaryDependencySinkAt scopes modes currentDepth owner site demanded classifier dependencies =
      let classifierDependencies =
            observationDependencies observationOracle
              (observationBindings scopes modes) Nothing
              (quote ctx currentDepth classifier)
          unjustified =
            relativeDependencies scopes modes currentDepth classifier dependencies
       in [ BackendIRViolation owner (BackendNodeId (-1)) "E_PARAMETRIC_TYPE_PROMOTION"
              ("finalized typed Core passes a parametric witness to ordinary " <> site)
              [ ("dependencies", T.pack (show (Set.toAscList unjustified)))
              , ("classifier", renderTerm (quote ctx currentDepth classifier))
              , ("classifierDependencies", T.pack (show (Set.toAscList classifierDependencies)))
              ]
          | demanded == Ordinary
          , not (Set.null unjustified)
          ]

    relativeDependencies scopes modes currentDepth classifier dependencies =
      let relative =
            classifierRelativeDependencies observationOracle
              (observationBindings scopes modes) currentDepth classifier dependencies
       in evidenceRelativeCallableDependencies ctx currentDepth classifier relative

    checkAlt owner depth scopes modes expectedMode expectedType (CaseAlt pat guard body) =
      let patSites = reverse (patternSites depth expectedType pat)
          patModes = map fst patSites
          scopes' = [ScopeSlot Nothing ty Nothing | (_, ty) <- patSites] ++ scopes
          modes' = patModes ++ modes
          depth' = depth + length patModes
       in patternModeChecks owner depth expectedMode expectedType pat
            ++ maybe [] (checkTerm owner depth' scopes' modes' Nothing) guard
            ++ checkTerm owner depth' scopes' modes' Nothing body

    checkItems _ _ _ _ _ [] = []
    checkItems owner depth scopes modes returnSite (item : rest) = case item of
      KBind _ pat action witness -> bindItem True witness pat action
      KLet _ pat value -> bindItem False Nothing pat value
      KLetQ pat value mElse ->
        let valueType = termTypeAt globals (csTraits st) ctx depth scopes value
         in checkTerm owner depth scopes modes Nothing value
              ++ maybe
                   []
                   (\(elsePat, elseBody) ->
                      checkAlt owner depth scopes modes Nothing valueType
                        (CaseAlt elsePat Nothing elseBody))
                   mElse
              ++ continueWith valueType pat
      KExpr value -> checkTerm owner depth scopes modes Nothing value ++ checkItems owner depth scopes modes returnSite rest
      KVarItem _ initial action _ ->
        checkTerm owner depth scopes modes Nothing initial
          ++ checkTerm owner depth scopes modes Nothing action
          ++ checkItems owner (depth + 1)
            (ScopeSlot Nothing
              (termTypeAt globals (csTraits st) ctx depth scopes action >>= kernelActionResult)
              Nothing : scopes)
            (Ordinary : modes) returnSite rest
      KAssign ref _ rhs action _ -> concatMap (checkTerm owner depth scopes modes Nothing) [ref, rhs, action] ++ checkItems owner depth scopes modes returnSite rest
      KReturn value ->
        let resultType =
              fmap snd returnSite
                <|> termTypeAt globals (csTraits st) ctx depth scopes value
            sinkChecks =
              maybe []
                (\classifier ->
                  [promotion owner "do return"
                  | hasUnjustifiedDependencies scopes modes classifier value
                  ])
                resultType
         in sinkChecks
              ++ checkTerm owner depth scopes modes resultType value
              ++ checkItems owner depth scopes modes returnSite rest
      KBreak _ -> checkItems owner depth scopes modes returnSite rest
      KContinue _ -> checkItems owner depth scopes modes returnSite rest
      KWhile _ cond body mElse -> checkCond cond ++ checkItems owner depth scopes modes returnSite body ++ maybe [] (checkItems owner depth scopes modes returnSite) mElse ++ checkItems owner depth scopes modes returnSite rest
      KFor _ pat source body mElse ->
        checkTerm owner depth scopes modes Nothing source
          ++ checkItemsWithPat pat body
          ++ maybe [] (checkItems owner depth scopes modes returnSite) mElse
          ++ checkItems owner depth scopes modes returnSite rest
      KIf arms mElse -> concatMap (\(cond, body) -> checkTerm owner depth scopes modes Nothing cond ++ checkItems owner depth scopes modes returnSite body) arms ++ maybe [] (checkItems owner depth scopes modes returnSite) mElse ++ checkItems owner depth scopes modes returnSite rest
      KDefer _ action -> checkTerm owner depth scopes modes Nothing action ++ checkItems owner depth scopes modes returnSite rest
      KUsing pat acquire release -> checkTerm owner depth scopes modes Nothing acquire ++ checkTerm owner depth scopes modes Nothing release ++ continueWith Nothing pat
      KSubDo _ body -> checkItems owner depth scopes modes returnSite body ++ checkItems owner depth scopes modes returnSite rest
      where
        bindItem unwrapAction witness pat value =
          checkTerm owner depth scopes modes Nothing value
            ++ continueWith
              (witnessedReadResult witness value
                <|> (termTypeAt globals (csTraits st) ctx depth scopes value
                      >>= \ty -> if unwrapAction then kernelActionResult ty else Just ty))
              pat
        kernelActionResult value = case force ctx value of
          VGlobI global _ [(_, _errorType), (_, resultType)]
            | global == prelIO -> Just resultType
          VGlobI global _ [(_, resultType)]
            | global == prelSTM -> Just resultType
          _ -> Nothing
        witnessedReadResult witness action = case (witness, spineOfTerm action) of
          (Just BuiltinIORefRead {}, (CProjM Ordinary _ _, (Impl, elementType) : _))
            | termScopedAt depth elementType -> Just (eval ctx (rigidEnv depth) elementType)
          _ -> Nothing
        continueWith expectedType pat =
          let sites = reverse (patternSites depth expectedType pat)
              ps = map fst sites
              newScopes = [ScopeSlot Nothing ty Nothing | (_, ty) <- sites]
           in checkItems owner (depth + length ps) (newScopes ++ scopes) (ps ++ modes) returnSite rest
        checkItemsWithPat pat body =
          let sites = reverse (patternSites depth Nothing pat)
              ps = map fst sites
              newScopes = [ScopeSlot Nothing ty Nothing | (_, ty) <- sites]
           in checkItems owner (depth + length ps) (newScopes ++ scopes) (ps ++ modes) returnSite body
        checkCond = \case
          KCondPure value -> checkTerm owner depth scopes modes Nothing value
          KCondAction value -> checkTerm owner depth scopes modes Nothing value

    -- User monads and Eff/Elab blocks are desugared before KBackendIR. A
    -- surviving CDo is therefore either one of the two kernel carriers below
    -- or a pure-result block. Kernel carrier identity and arity are exact;
    -- every other finalized expected type is the pure result itself.
    kernelDoResultSite carrier = case force ctx carrier of
      VGlobI global _ [(_, _errorType), (_, resultType)]
        | global == prelIO -> Right (Ordinary, resultType)
      VGlobI global _ [(_, resultType)]
        | global == prelSTM -> Right (Ordinary, resultType)
      VGlobI global _ _
        | global == prelIO || global == prelSTM -> Left ()
      _ -> Right (Ordinary, carrier)

    patternModeChecks owner depth expectedMode expectedType = go expectedMode expectedType
      where
        go mode ty = \case
          CPWild -> []
          CPVarM actualMode _ -> maybe [] (\wanted -> modeMismatch owner "pattern binder" wanted actualMode) mode
          CPLit _ -> []
          CPCtorM _ _ _ constructor universes patterns ->
            case Map.lookup constructor (csCtors st) of
              Nothing ->
                [modeViolation owner "E_BACKENDIR_CONSTRUCTOR_INTERFACE"
                  ("constructor pattern interface is unavailable for '" <> gnameText constructor <> "'")]
              Just info ->
                case specializeConstructorType ctx (Just universes) info of
                  Nothing ->
                    [modeViolation owner "E_BACKENDIR_CONSTRUCTOR_ARITY"
                      ("constructor pattern for '" <> gnameText constructor
                        <> "' carries the wrong declaration-universe arity")]
                  Just constructorType ->
                    case ty >>= constructorPatternObservationSites
                          ctx False depth (length (ciFields info)) constructorType of
                      Nothing ->
                        BackendIRViolation owner (BackendNodeId (-1))
                          "E_BACKENDIR_CONSTRUCTOR_PATTERN_ALIGNMENT"
                          ("constructor pattern for '" <> gnameText constructor
                            <> "' cannot be aligned with its finalized scrutinee type")
                          [ ("constructorType", renderTerm (quote ctx depth constructorType))
                          , ("scrutineeType", maybe "<unavailable>" (renderTerm . quote ctx depth) ty)
                          ]
                          : concatMap (go Nothing Nothing) patterns
                      Just sites -> concat
                        [ go (Just fieldMode) (Just fieldType) pattern'
                        | (pattern', (fieldMode, fieldType)) <- zip patterns sites
                        ]
          CPTuple patterns -> case ty >>= forceRecordType ctx of
            Just fields -> concat
              [ go (Just (rfMode field)) (Just (rfType field)) pattern'
              | (pattern', field) <- zip patterns fields
              ]
            Nothing -> concatMap (go Nothing Nothing) patterns
          CPRecordM fields rest ->
            let declared = ty >>= forceRecordType ctx
                fieldChecks = concat
                  [ case declared >>= findField name of
                      Just field -> go (Just (rfMode field)) (Just (rfType field)) pattern'
                      Nothing -> go Nothing Nothing pattern'
                  | (name, pattern') <- fields
                  ]
                restChecks = case rest of
                  Just (actualMode, _) -> modeMismatch owner "record rest pattern" Ordinary actualMode
                  Nothing -> []
             in fieldChecks ++ restChecks
          CPInject _ pattern' -> go mode Nothing pattern'
          CPInjectRestM actualMode _ -> maybe [] (\wanted -> modeMismatch owner "variant rest pattern" wanted actualMode) mode
          CPOr patterns _ -> concatMap (go mode ty) patterns
          CPAsM actualMode _ pattern' ->
            maybe [] (\wanted -> modeMismatch owner "as-pattern binder" wanted actualMode) mode
              ++ go mode ty pattern'

    patternSites depth expectedType = \case
      CPWild -> []
      CPVarM mode _ -> [(mode, expectedType)]
      CPLit _ -> []
      CPCtorM existentialModes bridges hidden constructor universes patterns ->
        case Map.lookup constructor (csCtors st) of
          Nothing -> [(mode, Nothing) | mode <- existentialModes]
            ++ replicate (constructorBridgeBinderCount bridges) (Ordinary, Nothing)
            ++ constructorSourceSites depth hidden patterns Nothing
          Just info ->
            case specializeConstructorType ctx (Just universes) info of
              Nothing -> [(mode, Nothing) | mode <- existentialModes]
                ++ replicate (constructorBridgeBinderCount bridges) (Ordinary, Nothing)
                ++ constructorSourceSites depth hidden patterns Nothing
              Just constructorType ->
                let sites = do
                      scrutineeType <- expectedType
                      constructorPatternObservationSites
                        ctx False depth (length (ciFields info)) constructorType scrutineeType
                 in [(mode, Nothing) | mode <- existentialModes]
                      ++ replicate (constructorBridgeBinderCount bridges) (Ordinary, Nothing)
                      ++ constructorSourceSites depth hidden patterns sites
      CPTuple patterns -> case expectedType >>= forceRecordType ctx of
        Just fields -> concat
          [ patternSites depth (Just (rfType field)) pattern'
          | (pattern', field) <- zip patterns fields
          ]
        Nothing -> concatMap (patternSites depth Nothing) patterns
      CPRecordM fields rest ->
        let declared = expectedType >>= forceRecordType ctx
            fieldSites = concat
              [ patternSites depth (rfType <$> (declared >>= findField name)) pattern'
              | (name, pattern') <- fields
              ]
            restSites = case rest of
              Just (mode, name) | name /= "" -> [(mode, expectedType)]
              _ -> []
         in fieldSites ++ restSites
      CPInject _ pattern' -> patternSites depth Nothing pattern'
      CPInjectRestM mode _ -> [(mode, expectedType)]
      CPOr (pattern' : _) _ -> patternSites depth expectedType pattern'
      CPOr [] _ -> []
      CPAsM mode _ pattern' -> (mode, expectedType) : patternSites depth expectedType pattern'

    constructorSourceSites depth hidden patterns explicitSites =
      case
          interleaveConstructorSourceBinders
            hidden
            (zip patterns (maybe (repeat Nothing) (map (Just . snd)) explicitSites))
        of
          Just slots ->
            concatMap
              ( \case
                  Left binder -> [(chbMode binder, Nothing)]
                  Right (pattern', fieldType) ->
                    patternSites depth fieldType pattern'
              )
              slots
          Nothing ->
            [(Parametric, Nothing) | _ <- hidden]
              ++ concatMap (patternSites depth Nothing) patterns

    termDependencies scopes modes expected term =
      let depth = length modes
          bindings = observationBindings scopes modes
          inferred = termTypeAt globals (csTraits st) ctx depth
            scopes
            term
          -- Beta/zeta invariance comes from the dependency calculus'
          -- substitution equations. Executing arbitrary finalized Core here
          -- can unfold recursive globals and monadic actions, making this
          -- checkpoint diverge instead of failing closed.
          dependencies =
            observationDependencies observationOracle bindings
              (expected <|> inferred)
              term
       in dependencies

    observationBindings scopes modes =
      let localTypes = [scopeSlotType slot | slot <- scopes]
       in [ ObservationBinding
              { obMode = mode
              , obOrigin =
                  if mode == Parametric
                    then Just (ParametricExternal index "finalized-kcore-local")
                    else Nothing
              , obType = fromMaybe Nothing (indexMaybeLocal index localTypes)
              , obUniverses =
                  scopeSlotUniverses =<< indexMaybeLocal index scopes
              , obDefinition = Nothing
              }
          | (index, mode) <- zip [0 ..] modes
          ]

    termMode scopes modes term =
      dependenciesMode (termDependencies scopes modes Nothing term)

    hasUnjustifiedDependencies scopes modes classifier term =
      let dependencies = termDependencies scopes modes (Just classifier) term
          relative = classifierRelativeDependencies observationOracle
            (observationBindings scopes modes) (length modes) classifier dependencies
       in not (Set.null (evidenceRelativeCallableDependencies ctx (length modes) classifier relative))

    -- A declaration may abstract a leading parametric origin only when its Pi
    -- codomain advertises the exact SS30.2.0 propagation condition. Merely
    -- placing a parametric binder in the leading telescope does not justify
    -- returning its witness through an ordinary result.
    unjustifiedResultDependencies scopes modes advertised classifier term =
      let resultIsParametricKind =
            isParametricKindValue ctx (length modes) classifier
          ordinaryEvidenceTraits =
            Set.fromList
              [ trait
              | (mode, slot) <- zip modes scopes
              , mode == Ordinary
              , Just slotType <- [scopeSlotType slot]
              , VGlobI trait _ _ <- [force ctx slotType]
              , Map.member trait (csTraits st)
              ]
          isAdvertisedBinderOrigin = \case
            ParametricExternal index _ ->
              not resultIsParametricKind
                && fromMaybe False (listToMaybe (drop index advertised))
            ParametricTraitProjection _ trait _ ->
              not resultIsParametricKind
                && trait `Set.member` ordinaryEvidenceTraits
            _ -> False
       in Set.filter (not . isAdvertisedBinderOrigin)
            (termDependencies scopes modes (Just classifier) term)

    modeMismatch owner site expected actual
      | expected == actual = []
      | otherwise = [modeViolation owner "E_PARAMETRIC_TYPE_PROMOTION"
          (site <> " records " <> T.pack (show actual) <> " but its classifier requires " <> T.pack (show expected))]

    promotion owner site = modeViolation owner "E_PARAMETRIC_TYPE_PROMOTION"
      ("finalized typed Core passes a parametric witness to ordinary " <> site)

    promotionWithDependencies owner site dependencies =
      BackendIRViolation owner (BackendNodeId (-1)) "E_PARAMETRIC_TYPE_PROMOTION"
        ("finalized typed Core passes a parametric witness to ordinary " <> site)
        [("dependencies", T.pack (show (Set.toAscList dependencies)))]

    modeViolation owner code message = BackendIRViolation owner (BackendNodeId (-1)) code message []

-- | Finalized module artifacts are closed typed Core. A rigid level identity
-- is legal only beneath the term binder that introduced its TypeLevel value;
-- record-field identities and unresolved level metas must have been replaced
-- by an outer ceiling or solved before this boundary. Checking this before
-- erasure prevents malformed imported/generated artifacts from laundering an
-- escaped identity through the backend's compile-time-only representation.
validateFinalizedLevelScopes :: CheckState -> [BackendIRViolation]
validateFinalizedLevelScopes st =
  concatMap (uncurry checkGlobalTelescope) (Map.toList (csGlobals st))
    ++ concatMap (uncurry (checkOwner False)) (Map.toList (csCoreBodies st))
    ++ concatMap (uncurry (checkOwner True)) interfaceTerms
  where
    ec = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
    interfaceTerms = [(owner, quote ec 0 (gdType def)) | (owner, def) <- Map.toList (csGlobals st)]
    typeLevelOrdDictionaries =
      Set.fromList
        [ ieDict entry
        | entry <- csInstances st
        , ieTrait entry == gPrel "Ord"
        , [headTerm] <- [ieHead entry]
        , isTypeLevelHead headTerm
        ]

    isTypeLevelHead term = case stripIdentityWrappers term of
      CGlobal carrier [] -> carrier == prelTypeLevel
      _ -> False

    authorizedTypeLevelOrdDictionary term = case stripIdentityWrappers term of
      CGlobal dictionary _ -> dictionary `Set.member` typeLevelOrdDictionaries
      _ -> False

    stripIdentityWrappers = \case
      CUniverseLift _ _ _ inner -> stripIdentityWrappers inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> stripIdentityWrappers inner
      term -> term

    checkGlobalTelescope owner def =
      checkTelescope owner 0 emptyAssumptions (gdUniverses def)

    checkOwner interfaceArtifact owner term =
      let expected =
            if interfaceArtifact
              then Nothing
              else finalizedGlobalType ec <$> Map.lookup owner (csGlobals st)
       in checkTermExpected expected interfaceArtifact 0 owner (ownerUniverseArity owner)
            (ownerUniverseAssumptions owner) [] term

    checkTerm interfaceArtifact depth owner universeArity assumptions localSchemas term =
      checkTermExpected Nothing interfaceArtifact depth owner universeArity assumptions localSchemas term

    checkTermExpected expected interfaceArtifact depth owner universeArity assumptions localSchemas term =
      levelAt interfaceArtifact owner depth universeArity term
        ++ globalAt interfaceArtifact owner depth universeArity term
        ++ localAt interfaceArtifact owner depth universeArity localSchemas term
        ++ liftAt owner depth universeArity assumptions term
        ++ schemaLiftAt owner depth universeArity assumptions term
        ++ case term of
        CLamM _ actualIcit _ _ body -> case expected of
          Just (CPiEvidenceM mode formation expectedIcit quantity _ _ relation _ domain codomain)
            | actualIcit == expectedIcit ->
                let (assumptionErrors, authenticated) =
                      authenticateAssumption mode formation expectedIcit quantity domain relation
                 in assumptionErrors
                      ++ underBinderExpected authenticated (Just codomain) body
          _ -> underBinder Nothing body
        CPiRuntimeM mode formation icit quantity _ _ relation _ runtimeErasure dom cod ->
          let (assumptionErrors, authenticated) =
                authenticateAssumption mode formation icit quantity dom relation
           in concatMap recur (toList runtimeErasure)
                ++ recur dom
                ++ assumptionErrors
                ++ underBinder authenticated cod
        CApp _ fun arg -> recur fun ++ recur arg
        CUniverseLift _ _ _ inner -> recur inner
        CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments inner ->
          concatMap recur sourceArguments ++ concatMap recur targetArguments ++ recur inner
        CArithmeticProof certificate ->
          concatMap recur (foldMapArithmeticCertificate (: []) certificate)
        CCtorI _ _ ann arguments -> maybe [] recur ann ++ concatMap (recur . caTerm) arguments
        CMatch scrut ann resultAnn alts ->
          recur scrut
            ++ maybe [] recur ann
            ++ maybe [] recur resultAnn
            ++ concatMap (checkAlt interfaceArtifact depth owner universeArity assumptions localSchemas) alts
        CRecordTQ fields ->
          checkRecordFields interfaceArtifact depth owner universeArity assumptions localSchemas fields
        CRecordV fields -> concatMap (recur . snd) fields
        CProj value _ -> recur value
        CProjAt value _ _ -> recur value
        CVariantT members -> concatMap recur members
        CInject _ value -> recur value
        CLetRuntimeM _ _ _ runtimeErasure ty rhs body ->
          concatMap recur (toList runtimeErasure)
            ++ recur ty
            ++ checkTermExpected (Just ty) interfaceArtifact depth owner universeArity assumptions localSchemas rhs
            ++ underBinder Nothing body
        CLetRecRuntimeM _ _ _ runtimeErasure ty rhs body ->
          concatMap recur (toList runtimeErasure)
            ++ recur ty
            ++ underBinderExpected Nothing (Just (shiftTerm 1 0 ty)) rhs
            ++ underBinder Nothing body
        CLetPolyRuntimeM _ _ _ telescope runtimeErasure ty rhs body ->
          let innerArity = universeArity + dutParameterCount telescope
              shiftedAssumptions = shiftOuterAssumptions (dutParameterCount telescope) assumptions
              innerAssumptions = extendDeclarationAssumptions innerArity shiftedAssumptions ty
           in checkTelescope owner universeArity assumptions telescope
                ++ concatMap (checkTerm interfaceArtifact depth owner innerArity shiftedAssumptions localSchemas) (toList runtimeErasure)
                ++ checkTerm interfaceArtifact depth owner innerArity shiftedAssumptions localSchemas ty
                ++ checkTermExpected (Just ty) interfaceArtifact depth owner innerArity innerAssumptions localSchemas rhs
                ++ checkTerm interfaceArtifact (depth + 1) owner universeArity assumptions
                  (Just telescope : localSchemas) body
        CLetRecPolyRuntimeM _ _ _ telescope runtimeErasure ty rhs body ->
          let innerArity = universeArity + dutParameterCount telescope
              shiftedAssumptions = shiftOuterAssumptions (dutParameterCount telescope) assumptions
              innerAssumptions = extendDeclarationAssumptions innerArity shiftedAssumptions ty
              recursiveSchemas = Just telescope : localSchemas
           in checkTelescope owner universeArity assumptions telescope
                ++ concatMap (checkTerm interfaceArtifact depth owner innerArity shiftedAssumptions localSchemas) (toList runtimeErasure)
                ++ checkTerm interfaceArtifact depth owner innerArity shiftedAssumptions localSchemas ty
                ++ checkTermExpected (Just (shiftTerm 1 0 ty)) interfaceArtifact (depth + 1) owner innerArity innerAssumptions recursiveSchemas rhs
                ++ checkTerm interfaceArtifact (depth + 1) owner universeArity assumptions recursiveSchemas body
        CLetRecGroupM telescope definitions body ->
          let count = length definitions
              innerArity = universeArity + dutParameterCount telescope
              shiftedAssumptions = shiftOuterAssumptions (dutParameterCount telescope) assumptions
              recursiveSchemas = replicate count (Just telescope) ++ localSchemas
              checkDefinition definition =
                let definitionAssumptions =
                      extendDeclarationAssumptions innerArity shiftedAssumptions (clrdType definition)
                 in concatMap
                      (checkTerm interfaceArtifact depth owner innerArity shiftedAssumptions localSchemas)
                      (toList (clrdRuntimeErasure definition))
                  ++ checkTerm interfaceArtifact depth owner innerArity shiftedAssumptions localSchemas (clrdType definition)
                  ++ checkTermExpected (Just (shiftTerm count 0 (clrdType definition)))
                    interfaceArtifact (depth + count) owner innerArity definitionAssumptions
                    recursiveSchemas (clrdRhs definition)
           in checkTelescope owner universeArity assumptions telescope
                ++ concatMap checkDefinition definitions
                ++ checkTerm interfaceArtifact (depth + count) owner universeArity assumptions recursiveSchemas body
        CDo _ items -> checkItems interfaceArtifact depth owner universeArity assumptions localSchemas items
        CSealE _ value -> recur value
        CSigT _ value -> recur value
        CThunkE value suspensionType -> recur value <> maybe [] recur suspensionType
        CLazyE value suspensionType -> recur value <> maybe [] recur suspensionType
        CForceE value resultType -> recur value ++ maybe [] recur resultType
        CIf cond yes no -> recur cond ++ recur yes ++ recur no
        CQuote _ slots -> concatMap recur slots
        _ -> []
      where
        recur = checkTerm interfaceArtifact depth owner universeArity assumptions localSchemas
        underBinder relation =
          checkTerm interfaceArtifact (depth + 1) owner universeArity
            (addAssumption relation assumptions) (Nothing : localSchemas)
        underBinderExpected relation expectedBody =
          checkTermExpected expectedBody interfaceArtifact (depth + 1) owner universeArity
            (addAssumption relation assumptions) (Nothing : localSchemas)
        authenticateAssumption mode formation _icit quantity domain relation =
          let modeValid =
                mode == Ordinary
                  && formation == FormationOrdinary
                  && quantity == Q0
              scopedRelationErrors =
                concatMap
                  (checkLevel interfaceArtifact owner depth universeArity)
                  (maybe [] (\(lower, upper) -> [lower, upper]) relation)
           in case authenticatedLevelAssumptionWith authorizedTypeLevelOrdDictionary
                (artifactTermAsLevel depth) depth domain relation of
                Left message ->
                  ( scopedRelationErrors
                      ++ [scopeViolation "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" owner LZero (T.unpack message)]
                  , Nothing
                  )
                Right authenticated
                  | isJust authenticated && not modeValid ->
                      ( scopedRelationErrors
                          ++ [ scopeViolation
                                "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE"
                                owner
                                LZero
                                "level assumptions require an ordinary-formation, ordinary-observation, quantity-0 proof binder"
                             ]
                      , Nothing
                      )
                  | otherwise -> (scopedRelationErrors, authenticated)

    checkRecordFields interfaceArtifact depth owner universeArity assumptions localSchemas =
      go Map.empty Map.empty 0 assumptions
      where
        go _ _ _ _ [] = []
        go fieldLocals fieldLevels fieldCount fieldAssumptions (field : rest) =
          let fieldDepth = depth + fieldCount
              scopedType =
                scopeRecordFields depth fieldCount fieldLocals fieldLevels (rfType field)
              scopedRuntimeErasure =
                fmap
                  (scopeRecordFields depth fieldCount fieldLocals fieldLevels)
                  (rfRuntimeErasure field)
              scopedRelation =
                scopeRecordLevelAssumption fieldLevels (rfLevelAssumption field)
              (assumptionErrors, authenticated) =
                authenticateRecordAssumption fieldDepth field scopedType scopedRelation
              nextAssumptions = addAssumption authenticated fieldAssumptions
              nextLocals = Map.insert (rfName field) fieldDepth fieldLocals
              nextFields =
                if coreTypeIsTypeLevel scopedType
                  then Map.insert (rfName field) fieldDepth fieldLevels
                  else fieldLevels
           in assumptionErrors
                ++ concatMap
                  (checkTerm interfaceArtifact fieldDepth owner universeArity fieldAssumptions
                    (replicate fieldCount Nothing ++ localSchemas))
                  (toList scopedRuntimeErasure)
                ++ checkTerm interfaceArtifact fieldDepth owner universeArity fieldAssumptions
                  (replicate fieldCount Nothing ++ localSchemas) scopedType
                ++ go nextLocals nextFields (fieldCount + 1) nextAssumptions rest

        authenticateRecordAssumption fieldDepth field domain relation =
          let modeValid =
                rfMode field == Ordinary
                  && rfFormation field == FormationOrdinary
                  && rfQ field == Q0
              scopedRelationErrors =
                concatMap
                  (checkLevel interfaceArtifact owner fieldDepth universeArity)
                  (maybe [] (\(lower, upper) -> [lower, upper]) relation)
           in case authenticatedLevelAssumptionWith authorizedTypeLevelOrdDictionary
                (artifactTermAsLevel fieldDepth) fieldDepth domain relation of
                Left message ->
                  ( scopedRelationErrors
                      ++ [scopeViolation "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" owner LZero (T.unpack message)]
                  , Nothing
                  )
                Right authenticated
                  | isJust authenticated && not modeValid ->
                      ( scopedRelationErrors
                          ++ [ scopeViolation
                                "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE"
                                owner
                                LZero
                                "record level assumptions require an ordinary-formation, ordinary-observation, quantity-0 proof field"
                             ]
                      , Nothing
                      )
                  | otherwise -> (scopedRelationErrors, authenticated)

    checkAlt interfaceArtifact depth owner universeArity assumptions localSchemas (CaseAlt pat guard body) =
      let inner = depth + patBindersC pat
          schemas = replicate (patBindersC pat) Nothing ++ localSchemas
       in checkPattern interfaceArtifact depth owner universeArity pat
            ++ maybe [] (checkTerm interfaceArtifact inner owner universeArity assumptions schemas) guard
            ++ checkTerm interfaceArtifact inner owner universeArity assumptions schemas body

    checkPattern interfaceArtifact depth owner universeArity = \case
      CPWild -> []
      CPVarM {} -> []
      CPLit {} -> []
      CPCtorM _ _ _ constructor universes patterns ->
        concatMap (checkLevel interfaceArtifact owner depth universeArity) universes
          ++ concatMap (checkPattern interfaceArtifact depth owner universeArity) patterns
          ++ case globalUniverseArity constructor of
            Nothing ->
              [scopeViolation "E_UNIVERSE_SCHEMA_SCOPE" owner LZero
                ("constructor pattern interface is unavailable for " <> T.unpack (gKey constructor))]
            Just expected
              | expected == length universes -> []
              | otherwise ->
                  [scopeViolation "E_UNIVERSE_SCHEMA_ARITY_MISMATCH" owner LZero
                    ("constructor pattern " <> T.unpack (gKey constructor) <> " expects "
                      <> show expected <> " universe arguments, found " <> show (length universes))]
      CPTuple patterns -> concatMap (checkPattern interfaceArtifact depth owner universeArity) patterns
      CPRecordM fields _ -> concatMap (checkPattern interfaceArtifact depth owner universeArity . snd) fields
      CPInject _ pattern' -> checkPattern interfaceArtifact depth owner universeArity pattern'
      CPInjectRestM {} -> []
      CPOr patterns _ -> concatMap (checkPattern interfaceArtifact depth owner universeArity) patterns
      CPAsM _ _ pattern' -> checkPattern interfaceArtifact depth owner universeArity pattern'

    checkItems _ _ _ _ _ _ [] = []
    checkItems interfaceArtifact depth owner universeArity assumptions localSchemas (item : rest) = case item of
      KBind _ pat action _ -> checkPat pat ++ recur action ++ continueUnder (patBindersC pat) rest
      KLet _ pat value -> checkPat pat ++ recur value ++ continueUnder (patBindersC pat) rest
      KLetQ pat value mElse ->
        checkPat pat ++ recur value
          ++ maybe []
            (\(elsePat, elseBody) ->
              let count = patBindersC elsePat
               in checkPat elsePat
                    ++ checkTerm interfaceArtifact (depth + count) owner universeArity assumptions
                    (replicate count Nothing ++ localSchemas) elseBody)
            mElse
          ++ continueUnder (patBindersC pat) rest
      KExpr value -> recur value ++ continue rest
      KVarItem _ initial action _ -> recur initial ++ recur action ++ continueUnder 1 rest
      KAssign ref _ rhs action _ -> recur ref ++ recur rhs ++ recur action ++ continue rest
      KReturn value -> recur value ++ continue rest
      KBreak _ -> continue rest
      KContinue _ -> continue rest
      KWhile _ cond body mElse ->
        checkCond interfaceArtifact depth owner universeArity assumptions localSchemas cond
          ++ nested body ++ maybe [] nested mElse ++ continue rest
      KFor _ pat source body mElse -> checkPat pat ++ recur source ++ nestedUnder (patBindersC pat) body ++ maybe [] nested mElse ++ continue rest
      KIf arms mElse -> concatMap (\(cond, body) -> recur cond ++ nested body) arms ++ maybe [] nested mElse ++ continue rest
      KDefer _ action -> recur action ++ continue rest
      KUsing pat acquire release -> checkPat pat ++ recur acquire ++ recur release ++ continueUnder (patBindersC pat) rest
      KSubDo _ body -> nested body ++ continue rest
      where
        recur = checkTerm interfaceArtifact depth owner universeArity assumptions localSchemas
        checkPat = checkPattern interfaceArtifact depth owner universeArity
        continue = checkItems interfaceArtifact depth owner universeArity assumptions localSchemas
        continueUnder count = checkItems interfaceArtifact (depth + count) owner universeArity assumptions
          (replicate count Nothing ++ localSchemas)
        nested = checkItems interfaceArtifact depth owner universeArity assumptions localSchemas
        nestedUnder count = checkItems interfaceArtifact (depth + count) owner universeArity assumptions
          (replicate count Nothing ++ localSchemas)

    checkCond interfaceArtifact depth owner universeArity assumptions localSchemas = \case
      KCondPure term -> checkTerm interfaceArtifact depth owner universeArity assumptions localSchemas term
      KCondAction term -> checkTerm interfaceArtifact depth owner universeArity assumptions localSchemas term

    addAssumption Nothing assumptions = assumptions
    addAssumption (Just (lower, upper)) assumptions = insertAssumption lower upper assumptions

    -- Imported transparent aliases are represented by a typed semantic identity
    -- in the finalized module artifact. Reuse that authority when replaying an
    -- explicit level-proof binder: source spelling and reducibility are not part
    -- of the backend trust boundary.
    artifactTermAsLevel depth term =
      termAsLevel depth normalized <|> structuredOrNeutral normalized
      where
        stripped = stripIdentityWrappers term
        normalized = quote ec depth (force ec (eval ec (rigidEnv depth) stripped))

        structuredOrNeutral candidate = case spineOfTerm candidate of
          (CGlobal operator _, arguments)
            | operator == prelTypeLevelOmega || operator == prelTypeLevelOmegaAlias
            , null arguments -> Just LOmega
            | Just identity <- builtinIdentity operator <|> Map.lookup operator (csLevelOperatorAliases st) ->
                applyIdentity identity [argument | (Expl, argument) <- arguments]
          _ -> LNeutral . neutralLevelTermAtom <$> coreToNeutralLevelTerm depth candidate

        builtinIdentity operator
          | operator == prelTypeLevelZero = Just LevelOperatorZero
          | operator == prelTypeLevelOne = Just LevelOperatorOne
          | operator == prelTypeLevelFromInteger = Just LevelOperatorFromInteger
          | operator == prelTypeLevelSucc = Just LevelOperatorSucc
          | operator == prelTypeLevelAdd = Just LevelOperatorAdd
          | operator == prelTypeLevelMax = Just LevelOperatorMax
          | otherwise = Nothing

        applyIdentity identity arguments = case identity of
          LevelOperatorZero | null arguments -> Just LZero
          LevelOperatorOne | null arguments -> Just (LFinite 1)
          LevelOperatorSucc -> levelSucc <$> (singleArgument arguments >>= artifactTermAsLevel depth)
          LevelOperatorAdd -> uncurry levelAdd <$> lastTwo arguments
          LevelOperatorMax -> uncurry levelMax <$> lastTwo arguments
          LevelOperatorFromInteger -> do
            CLit (LitInt value) <- singleArgument arguments
            guard (value >= 0 && value <= fromIntegral (maxBound :: Int))
            pure (LFinite (fromIntegral value))
          LevelOperatorLt -> Nothing
          LevelOperatorLe -> Nothing

        singleArgument [argument] = Just argument
        singleArgument _ = Nothing

        lastTwo arguments = case reverse arguments of
          right : left : [] ->
            (,) <$> artifactTermAsLevel depth left <*> artifactTermAsLevel depth right
          _ -> Nothing

    levelAt interfaceArtifact owner depth universeArity = \case
      CSort level -> checkLevel interfaceArtifact owner depth universeArity level
      CLevel level -> checkLevel interfaceArtifact owner depth universeArity level
      _ -> []

    liftAt owner depth universeArity assumptions term@CUniverseLift {} =
      [ scopeViolation "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" owner LZero
            (T.unpack message <> " at " <> T.unpack (renderTerm term))
        | message <- validateUniverseLiftEvidenceUnder assumptions depth universeArity term
        ]
    liftAt _ _ _ _ _ = []

    -- A nominal lift is runtime identity only because its independently
    -- verified summary says so. Replay that authority at the final typed-Core
    -- boundary before KBackendIR erases the node; neither emitter is allowed
    -- to reconstruct this judgment from names, roles, or representation shape.
    schemaLiftAt owner depth universeArity assumptions term = case term of
      CSchemaLift family source target roles evidence certificate sourceArguments targetArguments inner ->
        case Map.lookup family (csGlobals st) >>= gdNominalSummary of
          Nothing ->
            [schemaViolation "E_KCORE_SCHEMA_CERTIFICATE_INVALID" owner
              ("schema lift for " <> gKey family <> " has no verified nominal interface summary")]
          Just summary
            | not (verifyNominalCumulativitySummary summary) ->
                [schemaViolation "E_KCORE_SCHEMA_CERTIFICATE_INVALID" owner
                  ("schema lift for " <> gKey family <> " cites an invalid nominal interface summary")]
            | ncsFamilyIdentity summary /= gKey family ->
                [schemaViolation "E_KCORE_SCHEMA_CERTIFICATE_INVALID" owner
                  ("schema lift for " <> gKey family <> " cites a summary for " <> ncsFamilyIdentity summary)]
            | otherwise -> certificateChecks summary ++ useChecks summary
        where
          familyDefinition = Map.lookup family (csGlobals st)
          familyTelescope = gdUniverses <$> familyDefinition
          familyConstraints =
            maybe []
              (\definition ->
                declarationUniverseConstraints
                  (dutParameterCount (gdUniverses definition))
                  (finalizedGlobalType ec definition))
              familyDefinition
          certificateChecks summary =
            [ schemaViolation "E_KCORE_SCHEMA_CERTIFICATE_INVALID" owner reason
            | (invalid, reason) <-
                [ (certificate /= ncsCertificateId summary, "schema lift certificate identity disagrees with the verified family summary")
                , (not (ncsRepresentationIdentity summary), "schema lift certificate does not prove runtime representation identity")
                , (maybe True ((/= length (ncsRoles summary)) . dutParameterCount) familyTelescope,
                    "schema lift role arity disagrees with the family declaration telescope")
                ]
            , invalid
            ]
          useChecks summary =
            shapeChecks summary
              ++ constraintChecks "source" source
              ++ constraintChecks "target" target
              ++ concat
                [ roleCheck role roleEvidence lower upper
                | (role, roleEvidence, lower, upper) <- zip4 roles evidence source target
                ]
          shapeChecks summary =
            [ schemaViolation "E_UNIVERSE_SCHEMA_LIFT_INVALID" owner reason
            | (invalid, reason) <-
                [ (roles /= ncsRoles summary, "schema lift role vector disagrees with the verified family summary")
                , (length source /= length roles, "schema lift source universe vector has the wrong arity")
                , (length target /= length roles, "schema lift target universe vector has the wrong arity")
                , (length evidence /= length roles, "schema lift role-evidence vector has the wrong arity")
                , (length sourceArguments /= ncsSaturationArity summary,
                    "schema lift source family application is not fully saturated")
                , (length targetArguments /= ncsSaturationArity summary,
                    "schema lift target family application is not fully saturated")
                ]
            , invalid
            ]
          constraintChecks endpoint levels = case familyTelescope of
            Nothing -> []
            Just _telescope ->
              [ schemaViolation "E_UNIVERSE_SCHEMA_LIFT_INVALID" owner
                  ("schema lift " <> endpoint <> " instance does not satisfy the family declaration constraints")
              | any (not . constraintHolds levels) familyConstraints
              ]
          constraintHolds levels constraint =
            proveLevelLeq assumptions
              (substituteLevelParams levels (ucLower constraint))
              (substituteLevelParams levels (ucUpper constraint)) == Proved
          roleCheck role roleEvidence lower upper = case (role, roleEvidence) of
            (Invariant, SchemaInvariantEvidence)
              | proveLevelEq assumptions lower upper == Proved -> []
            (Irrelevant, SchemaIrrelevantEvidence) -> []
            (Covariant, SchemaCovariantEvidence proof)
              | null (validateUniverseLiftEvidenceUnder assumptions depth universeArity
                  (CUniverseLift lower upper proof inner)) -> []
            _ ->
              [schemaViolation "E_UNIVERSE_SCHEMA_LIFT_INVALID" owner
                "schema lift role evidence does not prove its declared role obligation"]
      _ -> []

    globalAt interfaceArtifact owner depth universeArity = \case
      CGlobal target universes ->
        referenceChecks target universes
      CCtorI target universes _ _ ->
        referenceChecks target universes
      _ -> []
      where
        referenceChecks target universes =
          concatMap (checkLevel interfaceArtifact owner depth universeArity) universes
            ++ case globalUniverseArity target of
            -- Runtime primitives and the synthetic @__this@ receiver are
            -- intentionally not declarations in 'csGlobals'.  Their semantic
            -- availability is checked by the producer that introduces them;
            -- this boundary can enforce a universe arity only when a typed
            -- global or constructor declaration supplies that arity.
            Nothing -> []
            Just expected
              | expected == length universes -> []
              | otherwise ->
                  [scopeViolation "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" owner LZero
                    ("global " <> T.unpack (gKey target) <> " expects " <> show expected
                      <> " hidden universe arguments, found " <> show (length universes))]

    localAt interfaceArtifact owner depth universeArity localSchemas = \case
      CVar index ->
        case drop index localSchemas of
          Just telescope : _
            | dutParameterCount telescope > 0 ->
                [scopeViolation "E_UNIVERSE_SCHEMA_SCOPE" owner LZero
                  "universe-polymorphic local occurrence is missing its explicit static instantiation"]
          _ -> []
      CLocal index universes ->
        concatMap (checkLevel interfaceArtifact owner depth universeArity) universes
          ++ case drop index localSchemas of
            Just telescope : _
              | length universes == dutParameterCount telescope -> []
              | otherwise ->
                  [ scopeViolation "E_UNIVERSE_SCHEMA_ARITY_MISMATCH" owner LZero
                      ("local declaration expects " <> show (dutParameterCount telescope)
                        <> " universe arguments, found " <> show (length universes))
                  ]
            Nothing : _ ->
              [scopeViolation "E_UNIVERSE_SCHEMA_SCOPE" owner LZero
                "universe-specialized local occurrence has no local declaration schema"]
            [] ->
              [scopeViolation "E_UNIVERSE_SCHEMA_SCOPE" owner LZero
                "universe-specialized local occurrence is out of term scope"]
      _ -> []

    globalUniverseArity target =
      (dutParameterCount . gdUniverses <$> Map.lookup target (csGlobals st))
        <|> (dutParameterCount . ciUniverses <$> Map.lookup target (csCtors st))

    ownerUniverseArity owner =
      maybe 0 (dutParameterCount . gdUniverses) (Map.lookup owner (csGlobals st))

    ownerUniverseAssumptions owner =
      maybe emptyAssumptions
        (\definition ->
          foldr
            (\constraint -> insertAssumption (ucLower constraint) (ucUpper constraint))
            emptyAssumptions
            ( declarationUniverseConstraints
                (dutParameterCount (gdUniverses definition))
                (finalizedGlobalType ec definition)
            ))
        (Map.lookup owner (csGlobals st))

    checkLevel interfaceArtifact owner depth universeArity level
      | badVars@(_ : _) <- filter (>= depth) (levelVars level) =
          [scopeViolation (scopeCode interfaceArtifact) owner level ("unbound rigid level identities " <> show badVars)]
      | badParams@(_ : _) <- filter (\parameter -> parameter < 0 || parameter >= universeArity) (levelParams level) =
          [scopeViolation "E_UNIVERSE_SCHEMA_SCOPE" owner level ("unbound declaration-universe parameters " <> show badParams)]
      | badFields@(_ : _) <- levelFields level =
          [scopeViolation (scopeCode interfaceArtifact) owner level ("escaped record-field level identities " <> show badFields)]
      | badMetas@(_ : _) <- levelMetas level =
          [scopeViolation "E_UNSOLVED_METAVARIABLE" owner level ("unsolved level metavariables " <> show badMetas)]
      | otherwise = []

    checkTelescope owner outerArity outerAssumptions telescope =
      let count = dutParameterCount telescope
          shapeChecks =
            [scopeViolation "E_UNIVERSE_SCHEMA_SCOPE" owner LZero
              "declaration universe telescope has a negative parameter count"
            | count < 0]
          consistencyChecks =
            [scopeViolation "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" owner LZero
              "declaration universe telescope constraints are inconsistent"
            | not (assumptionsConsistent outerAssumptions)]
       in shapeChecks ++ consistencyChecks

    shiftOuterAssumptions count outerAssumptions =
      foldr
        (\(lower, upper) -> insertAssumption
          (abstractLocalLevelParams count lower)
          (abstractLocalLevelParams count upper))
        emptyAssumptions
        (assumptionsList outerAssumptions)

    extendDeclarationAssumptions arity assumptions ty =
      foldr
        (\constraint -> insertAssumption (ucLower constraint) (ucUpper constraint))
        assumptions
        (declarationUniverseConstraints arity ty)

    scopeCode True = "E_UNSOLVED_METAVARIABLE"
    scopeCode False = "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE"

    scopeViolation code owner level reason =
      BackendIRViolation
        { bivBody = owner
        , bivNode = BackendNodeId (-1)
        , bivCode = code
        , bivMessage =
            "finalized typed Core declaration " <> gKey owner <> " contains " <> T.pack reason
              <> " in universe " <> renderLevel level
        , bivPayloadFields = []
        }

    schemaViolation code owner reason =
      BackendIRViolation
        { bivBody = owner
        , bivNode = BackendNodeId (-1)
        , bivCode = code
        , bivMessage = "finalized typed Core declaration " <> gKey owner <> " contains " <> reason
        , bivPayloadFields = []
        }

validateKBackendIR :: KBackendIR -> [BackendIRViolation]
validateKBackendIR backendIr =
  kbirLoweringViolations backendIr
    ++ validateExactNaturalRuntimeCertificate backendIr
    ++ validateRepresentationDecisions backendIr
    ++ concatMap
      (uncurry validateBody)
      (Map.toList (kbirBodies backendIr))

validateExactNaturalRuntimeCertificate :: KBackendIR -> [BackendIRViolation]
validateExactNaturalRuntimeCertificate backendIr =
  case kbirExactNaturalCertificate backendIr of
    Nothing ->
      [ certificateViolation
          "E_BACKEND_REQUIRED_REPRESENTATION_MISSING"
          "the runnable backend IR has no verified exact-natural runtime certificate"
      ]
    Just certificate ->
      case verifyExactNaturalRepresentationCertificate certificate of
        Right () -> []
        Left detail ->
          [ certificateViolation
              "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID"
              ("exact-natural runtime certificate replay failed: " <> T.unpack detail)
          ]
  where
    certificateViolation code detail =
      case Map.elems (kbirBodies backendIr) of
        body : _ ->
          violation
            (bbOwner body)
            (backendMeta (bbRoot body))
            code
            detail
        [] ->
          BackendIRViolation
            { bivBody =
                GName
                  (kbirModule backendIr)
                  "<backend-ir>"
            , bivNode = BackendNodeId (-1)
            , bivCode = T.pack code
            , bivMessage = T.pack detail
            , bivPayloadFields = []
            }

validateRepresentationDecisions :: KBackendIR -> [BackendIRViolation]
validateRepresentationDecisions backendIr =
  concatMap validateDecision (Map.toAscList (kbirRepresentations backendIr))
  where
    capabilities = kbirCapabilities backendIr
    sourceFields = kbirSourceFields backendIr

    validateDecision (subject, decision) =
      subjectFinding subject
        ++ certificateFindings subject decision
        ++ classFindings subject decision
        ++ erasedFieldFindings subject decision

    subjectFinding = \case
      BackendDeclarationSubject _ -> []
      BackendConstructorFieldSubject identity
        | Map.member identity sourceFields -> []
        | otherwise ->
            [representationViolation identity
              "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID"
              "representation decision names a source field absent from KBackendIR"]

    certificateFindings subject decision =
      concat
        [ replay
            subject
            "ordinal"
            verifyOrdinalRepresentationCertificate
            (brdOrdinalCertificate decision)
        , replay
            subject
            "exact-natural"
            verifyExactNaturalRepresentationCertificate
            (brdExactNaturalCertificate decision)
        , replay
            subject
            "refinement"
            verifyRefinementRepresentationCertificate
            (brdRefinementCertificate decision)
        ]
        ++ [ subjectViolation subject
              "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID"
              "representation certificate type identity disagrees with its KBackendIR decision"
           | certificateTypeIdentityMismatch decision
           ]

    replay subject label verifyCertificate certificate =
      case certificate of
        Nothing -> []
        Just value ->
          case verifyCertificate value of
            Right () -> []
            Left detail ->
              [ subjectViolation subject
                  "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID"
                  (label <> " representation certificate replay failed: " <> detail)
              ]

    classFindings subject decision =
      requiredExactFinding ++ case brdClass decision of
        Repr.ConservativeBoxed -> []
        Repr.ExactNatural identity ->
          case brdExactNaturalCertificate decision of
            Just certificate
              | identity
                  == exactNaturalRepresentationCertificateIdentity certificate ->
                  []
            _ ->
              [ subjectViolation subject
                  "E_BACKEND_REQUIRED_REPRESENTATION_MISSING"
                  "ExactNatural was selected without its matching verified certificate"
              ]
        Repr.FiniteOrdinal cardinality identity ->
          capabilityFinding
            ++ case brdOrdinalCertificate decision of
              Just certificate
                | identity
                    == ordinalRepresentationCertificateIdentity certificate
                , orcCardinalityExpression certificate == cardinality ->
                    []
              _ ->
                [ subjectViolation subject
                    "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID"
                    "FiniteOrdinal was selected without its matching ordinal certificate"
                ]
      where
        requiredExactFinding
          | brdRequiredExactNatural decision
          , case brdClass decision of
              Repr.ExactNatural {} -> False
              _ -> True =
              [ subjectViolation subject
                  "E_BACKEND_REQUIRED_REPRESENTATION_MISSING"
                  "a certified exact-natural type has no ExactNatural backend representation"
              ]
          | otherwise = []
        capabilityFinding
          | "rt-compact-finite-ordinal" `Set.member` capabilities = []
          | otherwise =
              [ subjectViolation subject
                  "E_BACKEND_REQUIRED_REPRESENTATION_MISSING"
                  "FiniteOrdinal requires the rt-compact-finite-ordinal capability"
              ]

    erasedFieldFindings subject decision =
      [ subjectViolation subject
          "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID"
          ( "certificate claims erased source field "
              <> gKey (bsfiConstructor field)
              <> "."
              <> bsfiName field
              <> " but KBackendIR retains it"
          )
      | field <- brdErasedFields decision
      , case Map.lookup field sourceFields of
          Just BackendFieldErased {} -> False
          _ -> True
      ]
        ++ [ subjectViolation subject
              "E_BACKEND_REQUIRED_REPRESENTATION_MISSING"
              "refinement wrapper elimination requires rt-unboxed-refinement"
           | brdWrapperEliminated decision
           , "rt-unboxed-refinement" `Set.notMember` capabilities
           ]

    certificateTypeIdentityMismatch decision =
      any
        (/= brdTypeIdentity decision)
        ( maybeToList (orcTypeIdentity <$> brdOrdinalCertificate decision)
            ++ maybeToList
              (enrcTypeIdentity <$> brdExactNaturalCertificate decision)
            ++ maybeToList
              (rrcTypeIdentity <$> brdRefinementCertificate decision)
        )

    subjectViolation subject code message =
      BackendIRViolation
        { bivBody = subjectOwner subject
        , bivNode = BackendNodeId (-1)
        , bivCode = code
        , bivMessage = message
        , bivPayloadFields =
            [("subject", renderRepresentationSubject subject)]
        }

    representationViolation identity code message =
      subjectViolation
        (BackendConstructorFieldSubject identity)
        code
        message

    subjectOwner = \case
      BackendDeclarationSubject global -> global
      BackendConstructorFieldSubject identity -> bsfiOwner identity

    renderRepresentationSubject = \case
      BackendDeclarationSubject global -> gKey global
      BackendConstructorFieldSubject identity ->
        gKey (bsfiOwner identity) <> "." <> bsfiName identity

validateBody :: GName -> BackendBody -> [BackendIRViolation]
validateBody owner body =
  duplicateNodeFindings owner (metas ++ erasureMetas)
    ++ duplicateBinderFindings owner rootMeta (collectBodyBinders body)
    ++ duplicateUseFindings owner rootMeta (collectBodyUses body)
    ++ concatMap (validateErasure owner) (bbErasures body)
    ++ concatMap (validateParam owner rootMeta) (bbParams body)
    ++ validateTerm owner (bbRoot body)
    ++ validateBranchDropsTerm owner rootEnv (bbRoot body)
  where
    metas = collectMetas (bbRoot body)
    erasureMetas = [BackendMeta node [] | BackendErasure {beNode = node} <- bbErasures body]
    rootMeta = backendMeta (bbRoot body)
    rootEnv =
      Map.fromList
        [ (bbBinderId b, b)
        | BackendParam _ _ (Just b) <- bbParams body
        ]

validateErasure :: GName -> BackendErasure -> [BackendIRViolation]
validateErasure owner erasure =
  depthFinding ++ provenanceFindings
  where
    meta = BackendMeta (beNode erasure) []
    depth = beDepth erasure
    depthFinding
      | depth >= 0 = []
      | otherwise =
          [ violation owner meta "E_BACKENDIR_ERASURE_SCOPE"
              "erasure evidence carries a negative lexical depth"
          ]
    provenanceFindings = case beProvenance erasure of
      ErasedBySelectedEvidence goal evidence evidenceType ->
        scoped "goal" goal
          ++ scoped "evidence" evidence
          ++ scoped "evidence classifier" evidenceType
          ++ closed "goal" goal
          ++ closed "evidence" evidence
          ++ closed "evidence classifier" evidenceType
          ++ authenticatedGoal goal
          ++ authenticatedEvidence goal evidence evidenceType
      _ -> []
    scoped what term
      | depth >= 0 && termScopedAt depth term = []
      | otherwise =
          [ violation owner meta "E_BACKENDIR_ERASURE_SCOPE" $
              "selected RuntimeErased " <> what <> " escapes its recorded lexical scope"
          ]
    closed what term
      | null (metaIdsOf term) && null (levelMetasOfTerm term) = []
      | otherwise =
          [ violation owner meta "E_BACKENDIR_ERASURE_META" $
              "selected RuntimeErased " <> what <> " contains an unresolved metavariable"
          ]
    authenticatedGoal goal =
      case spineOfTerm goal of
        (CGlobal trait _, [(Expl, _)]) | trait == prelRuntimeErased -> []
        _ ->
          [ violation owner meta "E_BACKENDIR_ERASURE_GOAL"
              "selected erasure evidence does not prove an exact unary RuntimeErased goal"
          ]
    authenticatedEvidence goal evidence evidenceType =
      classifier
        ++ case evidence of
          CRecordV [] ->
            [ violation owner meta "E_BACKENDIR_ERASURE_EVIDENCE"
                "selected erasure evidence is anonymous structural data rather than a replayable typed identity"
            ]
          _ -> []
      where
        classifier
          | evidenceType == goal = []
          | otherwise =
              [ violation owner meta "E_BACKENDIR_ERASURE_EVIDENCE"
                  "selected erasure evidence classifier does not replay the stored exact RuntimeErased goal"
              ]

validateParam :: GName -> BackendMeta -> BackendParam -> [BackendIRViolation]
validateParam owner rootMeta (BackendParam _ name mb) =
  case mb of
    Just {} -> []
    Nothing ->
      [ violation owner rootMeta "W_BACKENDIR_MISSING_BINDER" $
          "runtime parameter has no backend ownership binder: " <> T.unpack name
      ]

validateBinder :: GName -> BackendMeta -> Text -> Maybe BackendBinder -> [BackendIRViolation]
validateBinder owner meta what = \case
  Just {} -> []
  Nothing ->
    [ violation owner meta "W_BACKENDIR_MISSING_BINDER" $
        T.unpack what <> " has no backend ownership binder"
    ]

validateUse :: GName -> BackendMeta -> Maybe BackendUse -> [BackendIRViolation]
validateUse owner meta = \case
  Just {} -> []
  Nothing ->
    [ violation owner meta "W_BACKENDIR_MISSING_USE" $
        "runtime variable has no backend ownership use"
    ]

validateCtor :: GName -> BackendMeta -> BackendCtorLayout -> [BackendTerm] -> [BackendIRViolation]
validateCtor owner meta layout args =
  fieldCountFinding ++ validateCtorLayout owner meta layout
  where
    fieldCountFinding
      | bclRuntimeFields layout == length args = []
      | otherwise =
          [ violation owner meta "W_BACKENDIR_CTOR_FIELD_MISMATCH" $
              "constructor layout runtime field count "
                <> show (bclRuntimeFields layout)
                <> " does not match lowered field count "
                <> show (length args)
          ]

validateCtorLayout :: GName -> BackendMeta -> BackendCtorLayout -> [BackendIRViolation]
validateCtorLayout owner meta layout =
  case bclInfo layout of
    Nothing -> []
    Just info
      | clArity info == bclRuntimeFields layout
          && length (clFieldReps info) == clArity info
          && clLayoutClass info == Repr.ctorLayout (clFieldReps info)
          && clBoxedFootprintBytes info == expectedFootprint info ->
          []
      | otherwise ->
          [ violation owner meta "W_BACKENDIR_CTOR_LAYOUT_INCONSISTENT" $
              "constructor layout metadata is internally inconsistent or does not match the runtime field count"
          ]
  where
    expectedFootprint info =
      case clLayoutClass info of
        Repr.LayoutImmediate -> Nothing
        Repr.LayoutMayPack -> Just (Repr.ctorBoxedFootprintBytes (clArity info))
        Repr.LayoutBoxed -> Just (Repr.ctorBoxedFootprintBytes (clArity info))

validateTerm :: GName -> BackendTerm -> [BackendIRViolation]
validateTerm owner = \case
  BUnit {} -> []
  BVar meta use _ -> validateUse owner meta use
  BGlob {} -> []
  BLit {} -> []
  BLam meta mb _ _ name body ->
    validateBinder owner meta (T.pack "lambda binder " <> name) mb ++ validateTerm owner body
  BApp _ hd args ->
    validateTerm owner hd ++ concatMap (\(_, _, arg) -> validateTerm owner arg) args
  BCtor meta layout args ->
    validateCtor owner meta layout args ++ concatMap (validateTerm owner) args
  BMatch _ scrut alts layouts ->
    let layoutMap = Map.fromList [(bclCtor layout, layout) | (_, layout) <- layouts]
     in validateTerm owner scrut ++ concatMap (validateAlt owner layoutMap) alts
  BRecord _ fs -> concatMap (validateTerm owner . snd) fs
  BProj _ e _ _ -> validateTerm owner e
  BInject _ _ e -> validateTerm owner e
  BLet meta mb _ name rhs body ->
    validateBinder owner meta (T.pack "let binder " <> name) mb
      ++ validateTerm owner rhs
      ++ validateTerm owner body
  BLetRec meta mb _ name rhs body ->
    validateBinder owner meta (T.pack "letrec binder " <> name) mb
      ++ validateTerm owner rhs
      ++ validateTerm owner body
  BDo _ _ items -> concatMap (validateItem owner) items
  BSeal _ _ e -> validateTerm owner e
  BThunk _ e -> validateTerm owner e
  BLazy _ e -> validateTerm owner e
  BForce _ e -> validateTerm owner e
  BIf _ c th el -> validateTerm owner c ++ validateTerm owner th ++ validateTerm owner el

validateAlt :: GName -> Map GName BackendCtorLayout -> BackendAlt -> [BackendIRViolation]
validateAlt owner layoutMap (BackendAlt meta pat binders guard body) =
  validatePattern owner meta layoutMap pat
    ++ concatMap (validateBinder owner meta (T.pack "pattern binder")) binders
    ++ maybe [] (validateTerm owner) guard
    ++ validateTerm owner body

validatePattern :: GName -> BackendMeta -> Map GName BackendCtorLayout -> BackendPat -> [BackendIRViolation]
validatePattern owner meta layoutMap = \case
  BPWild -> []
  BPVar {} -> []
  BPLit {} -> []
  BPCtor g runtimeArity fields ->
    ctorArityFinding g runtimeArity fields
      ++ positionalFindings "constructor" runtimeArity fields
      ++ concatMap (validatePattern owner meta layoutMap . snd) fields
  BPTuple runtimeArity fields ->
    positionalFindings "tuple" runtimeArity fields
      ++ concatMap (validatePattern owner meta layoutMap . snd) fields
  BPRecord fs _ -> concatMap (validatePattern owner meta layoutMap . snd) fs
  BPInject _ p -> validatePattern owner meta layoutMap p
  BPInjectRest {} -> []
  BPOr ps _ -> concatMap (validatePattern owner meta layoutMap) ps
  BPAs _ p -> validatePattern owner meta layoutMap p
  where
    ctorArityFinding g runtimeArity _ =
      case Map.lookup g layoutMap of
        Just layout ->
          validateCtorLayout owner meta layout
            ++ [ violation owner meta "W_BACKENDIR_CTOR_PATTERN_FIELD_MISMATCH" $
                  "constructor pattern records "
                    <> show runtimeArity
                    <> " runtime field(s), but layout records "
                    <> show (bclRuntimeFields layout)
                    <> " runtime field(s)"
               | runtimeArity /= bclRuntimeFields layout
               ]
        Nothing ->
          [ violation owner meta "W_BACKENDIR_CTOR_PATTERN_LAYOUT_MISSING" $
              "constructor pattern has no matching layout metadata entry for " <> T.unpack (gKey g)
          ]
    positionalFindings shape runtimeArity fields =
      [ violation owner meta "W_BACKENDIR_PATTERN_FIELD_INDEX_INVALID" $
          shape <> " pattern runtime field index " <> show index
            <> " is outside arity " <> show runtimeArity
      | (index, _) <- fields
      , index < 0 || index >= runtimeArity
      ]
        ++ [ violation owner meta "W_BACKENDIR_PATTERN_FIELD_INDEX_DUPLICATE" $
               shape <> " pattern repeats runtime field index " <> show index
           | index <- duplicates (map fst fields)
           ]
    duplicates indices =
      Map.keys
        (Map.filter (> (1 :: Int)) (Map.fromListWith (+) [(index, 1 :: Int) | index <- indices]))

validateBranchDropsItemMeta :: GName -> BackendMeta -> [BackendIRViolation]
validateBranchDropsItemMeta owner meta
  | null (bmBranchDrops meta) = []
  | otherwise =
      [ violation owner meta "W_BACKENDIR_BRANCH_DROP_UNEMITTED_ITEM" $
          "branch-drop metadata is attached to a do-item node, but native emission only drains branch drops from BackendTerm and BackendAlt nodes"
      ]

validateItem :: GName -> BackendItem -> [BackendIRViolation]
validateItem owner = \case
  BKBind meta _ _ binders action _ ->
    concatMap (validateBinder owner meta (T.pack "do-bind pattern binder")) binders
      ++ validateTerm owner action
  BKLet meta _ _ binders value ->
    concatMap (validateBinder owner meta (T.pack "do-let pattern binder")) binders
      ++ validateTerm owner value
  BKLetQ meta _ binders scrut mElse ->
    concatMap (validateBinder owner meta (T.pack "let? pattern binder")) binders
      ++ validateTerm owner scrut
      ++ maybe
        []
        ( \( _pat
           , ebinders
           , body
           ) ->
            concatMap (validateBinder owner meta (T.pack "let? else pattern binder")) ebinders
              ++ validateTerm owner body
        )
        mElse
  BKExpr _ action -> validateTerm owner action
  BKVarItem meta mb _initT action _ ->
    validateBinder owner meta (T.pack "var binder") mb
      ++ validateTerm owner action
  BKAssign _ _ _rhs action _ -> validateTerm owner action
  BKReturn _ value -> validateTerm owner value
  BKWhile _ _ cond body mElse ->
    validateCond owner cond
      ++ concatMap (validateItem owner) body
      ++ maybe [] (concatMap (validateItem owner)) mElse
  BKFor meta _ _ binders source body mElse ->
    concatMap (validateBinder owner meta (T.pack "for pattern binder")) binders
      ++ validateTerm owner source
      ++ concatMap (validateItem owner) body
      ++ maybe [] (concatMap (validateItem owner)) mElse
  BKIf _ arms mElse ->
    concatMap (\(cond, body) -> validateTerm owner cond ++ concatMap (validateItem owner) body) arms
      ++ maybe [] (concatMap (validateItem owner)) mElse
  BKDefer _ _ action -> validateTerm owner action
  BKUsing meta _ binders acquire release ->
    concatMap (validateBinder owner meta (T.pack "using pattern binder")) binders
      ++ validateTerm owner acquire
      ++ validateTerm owner release
  BKSubDo _ _ body -> concatMap (validateItem owner) body
  BKBreak {} -> []
  BKContinue {} -> []

validateCond :: GName -> BackendCond -> [BackendIRViolation]
validateCond owner = \case
  BKCondPure t -> validateTerm owner t
  BKCondAction t -> validateTerm owner t

validateBranchDropsMeta :: GName -> BinderEnv -> BackendMeta -> [BackendIRViolation]
validateBranchDropsMeta owner env meta =
  duplicateFindings ++ concatMap checkDrop drops
  where
    drops = bmBranchDrops meta
    counts =
      Map.fromListWith
        (+)
        [(bbBinderId b, 1 :: Int) | b <- drops]
    duplicateFindings =
      [ violation owner meta "W_BACKENDIR_BRANCH_DROP_DUPLICATE" $
          "branch-drop metadata names the same binder more than once at this branch node: " <> show bid
      | (bid, count) <- Map.toList counts
      , count > 1
      ]
    checkDrop b =
      let bid = bbBinderId b
       in case Map.lookup bid env of
            Nothing ->
              [ violation owner meta "W_BACKENDIR_BRANCH_DROP_OUT_OF_SCOPE" $
                  "branch-drop metadata names binder outside this runtime scope: " <> show bid
              ]
            Just canonical
              | canonical == b -> []
              | otherwise ->
                  [ violation owner meta "W_BACKENDIR_BRANCH_DROP_MISMATCH" $
                      "branch-drop metadata for "
                        <> show bid
                        <> " does not match the in-scope backend binder payload"
                  ]

validateBranchDropsTerm :: GName -> BinderEnv -> BackendTerm -> [BackendIRViolation]
validateBranchDropsTerm owner env term =
  validateBranchDropsMeta owner env (backendMeta term)
    ++ case term of
      BUnit {} -> []
      BVar {} -> []
      BGlob {} -> []
      BLit {} -> []
      BLam _ mb _ _ _ body ->
        validateBranchDropsTerm owner (addMaybeBinder mb env) body
      BApp _ hd args ->
        validateBranchDropsTerm owner env hd
          ++ concatMap (\(_, _, arg) -> validateBranchDropsTerm owner env arg) args
      BCtor _ _ args -> concatMap (validateBranchDropsTerm owner env) args
      BMatch _ scrut alts _ ->
        validateBranchDropsTerm owner env scrut
          ++ concatMap (validateBranchDropsAlt owner env) alts
      BRecord _ fs -> concatMap (validateBranchDropsTerm owner env . snd) fs
      BProj _ e _ _ -> validateBranchDropsTerm owner env e
      BInject _ _ e -> validateBranchDropsTerm owner env e
      BLet _ mb _ _ rhs body ->
        validateBranchDropsTerm owner env rhs
          ++ validateBranchDropsTerm owner (addMaybeBinder mb env) body
      BLetRec _ mb _ _ rhs body ->
        let env' = addMaybeBinder mb env
         in validateBranchDropsTerm owner env' rhs
              ++ validateBranchDropsTerm owner env' body
      BDo _ _ items -> fst (validateBranchDropsItems owner env items)
      BSeal _ _ e -> validateBranchDropsTerm owner env e
      BThunk _ e -> validateBranchDropsTerm owner env e
      BLazy _ e -> validateBranchDropsTerm owner env e
      BForce _ e -> validateBranchDropsTerm owner env e
      BIf _ c th el ->
        validateBranchDropsTerm owner env c
          ++ validateBranchDropsTerm owner env th
          ++ validateBranchDropsTerm owner env el

validateBranchDropsAlt :: GName -> BinderEnv -> BackendAlt -> [BackendIRViolation]
validateBranchDropsAlt owner env (BackendAlt meta _ binders guard body) =
  validateBranchDropsMeta owner env meta
    ++ maybe [] (validateBranchDropsTerm owner env') guard
    ++ validateBranchDropsTerm owner env' body
  where
    env' = addMaybeBinders binders env

validateBranchDropsItems :: GName -> BinderEnv -> [BackendItem] -> ([BackendIRViolation], BinderEnv)
validateBranchDropsItems owner = go
  where
    go env [] = ([], env)
    go env (item : rest) =
      let (here, env') = validateBranchDropsItem owner env item
          (there, env'') = go env' rest
       in (here ++ there, env'')

validateBranchDropsItem :: GName -> BinderEnv -> BackendItem -> ([BackendIRViolation], BinderEnv)
validateBranchDropsItem owner env item =
  case item of
    BKBind meta _ _ binders action _ ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env action
      , addMaybeBinders binders env
      )
    BKLet meta _ _ binders value ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env value
      , addMaybeBinders binders env
      )
    BKLetQ meta _ binders scrut mElse ->
      let env' = addMaybeBinders binders env
          elseFindings = case mElse of
            Nothing -> []
            Just (_, ebinders, body) ->
              validateBranchDropsTerm owner (addMaybeBinders ebinders env) body
       in ( validateBranchDropsItemMeta owner meta
              ++ validateBranchDropsTerm owner env scrut
              ++ elseFindings
          , env'
          )
    BKExpr meta action ->
      (validateBranchDropsItemMeta owner meta ++ validateBranchDropsTerm owner env action, env)
    BKVarItem meta mb initT action _ ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env initT
          ++ validateBranchDropsTerm owner env action
      , addMaybeBinder mb env
      )
    BKAssign meta _ rhs action _ ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env rhs
          ++ validateBranchDropsTerm owner env action
      , env
      )
    BKReturn meta value ->
      (validateBranchDropsItemMeta owner meta ++ validateBranchDropsTerm owner env value, env)
    BKWhile meta _ cond body mElse ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsCond owner env cond
          ++ fst (validateBranchDropsItems owner env body)
          ++ maybe [] (fst . validateBranchDropsItems owner env) mElse
      , env
      )
    BKFor meta _ _ binders source body mElse ->
      let bodyEnv = addMaybeBinders binders env
       in ( validateBranchDropsItemMeta owner meta
              ++ validateBranchDropsTerm owner env source
              ++ fst (validateBranchDropsItems owner bodyEnv body)
              ++ maybe [] (fst . validateBranchDropsItems owner env) mElse
          , env
          )
    BKIf meta arms mElse ->
      ( validateBranchDropsItemMeta owner meta
          ++ concatMap (\(cond, body) -> validateBranchDropsTerm owner env cond ++ fst (validateBranchDropsItems owner env body)) arms
          ++ maybe [] (fst . validateBranchDropsItems owner env) mElse
      , env
      )
    BKDefer meta _ action ->
      (validateBranchDropsItemMeta owner meta ++ validateBranchDropsTerm owner env action, env)
    BKUsing meta _ binders acquire release ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env acquire
          ++ validateBranchDropsTerm owner env release
      , addMaybeBinders binders env
      )
    BKSubDo meta _ body ->
      (validateBranchDropsItemMeta owner meta ++ fst (validateBranchDropsItems owner env body), env)
    BKBreak meta _ -> (validateBranchDropsItemMeta owner meta, env)
    BKContinue meta _ -> (validateBranchDropsItemMeta owner meta, env)

validateBranchDropsCond :: GName -> BinderEnv -> BackendCond -> [BackendIRViolation]
validateBranchDropsCond owner env = \case
  BKCondPure t -> validateBranchDropsTerm owner env t
  BKCondAction t -> validateBranchDropsTerm owner env t

addMaybeBinder :: Maybe BackendBinder -> BinderEnv -> BinderEnv
addMaybeBinder Nothing env = env
addMaybeBinder (Just b) env = Map.insert (bbBinderId b) b env

addMaybeBinders :: [Maybe BackendBinder] -> BinderEnv -> BinderEnv
addMaybeBinders bs env = foldr addMaybeBinder env bs

duplicateNodeFindings :: GName -> [BackendMeta] -> [BackendIRViolation]
duplicateNodeFindings owner metas =
  [ BackendIRViolation owner (BackendNodeId n) (T.pack "W_BACKENDIR_DUPLICATE_NODE_ID")
      (T.pack ("backend node id is not unique within body: " <> show n)) []
  | (n, count) <- Map.toList counts
  , count > (1 :: Int)
  ]
  where
    counts =
      Map.fromListWith
        (+)
        [(n, 1 :: Int) | BackendMeta (BackendNodeId n) _ <- metas]

duplicateBinderFindings :: GName -> BackendMeta -> [BackendBinder] -> [BackendIRViolation]
duplicateBinderFindings owner meta binders =
  [ violation owner meta "W_BACKENDIR_DUPLICATE_BINDER_ID" $
      "backend binder id is not unique within body: " <> show bid
  | (bid, count) <- Map.toList counts
  , count > (1 :: Int)
  ]
  where
    counts =
      Map.fromListWith
        (+)
        [(bid, 1 :: Int) | BackendBinder bid _ _ _ <- binders]

duplicateUseFindings :: GName -> BackendMeta -> [BackendUse] -> [BackendIRViolation]
duplicateUseFindings owner meta uses =
  [ violation owner meta "W_BACKENDIR_DUPLICATE_USE_ID" $
      "backend use id is not unique within body: " <> show uid
  | (uid, count) <- Map.toList counts
  , count > (1 :: Int)
  ]
  where
    counts =
      Map.fromListWith
        (+)
        [(uid, 1 :: Int) | BackendUse uid _ _ <- uses]

violation :: GName -> BackendMeta -> String -> String -> BackendIRViolation
violation owner meta code msg =
  BackendIRViolation owner (bmNodeId meta) (T.pack code) (T.pack msg) []

collectMetas :: BackendTerm -> [BackendMeta]
collectMetas t =
  backendMeta t : case t of
    BUnit {} -> []
    BVar {} -> []
    BGlob {} -> []
    BLit {} -> []
    BLam _ _ _ _ _ body -> collectMetas body
    BApp _ hd args -> collectMetas hd ++ concatMap (\(_, _, arg) -> collectMetas arg) args
    BCtor _ _ args -> concatMap collectMetas args
    BMatch _ scrut alts _ -> collectMetas scrut ++ concatMap collectAltMetas alts
    BRecord _ fs -> concatMap (collectMetas . snd) fs
    BProj _ e _ _ -> collectMetas e
    BInject _ _ e -> collectMetas e
    BLet _ _ _ _ rhs body -> collectMetas rhs ++ collectMetas body
    BLetRec _ _ _ _ rhs body -> collectMetas rhs ++ collectMetas body
    BDo _ _ items -> concatMap collectItemMetas items
    BSeal _ _ e -> collectMetas e
    BThunk _ e -> collectMetas e
    BLazy _ e -> collectMetas e
    BForce _ e -> collectMetas e
    BIf _ c th el -> collectMetas c ++ collectMetas th ++ collectMetas el

collectAltMetas :: BackendAlt -> [BackendMeta]
collectAltMetas (BackendAlt meta _ _ guard body) =
  meta : maybe [] collectMetas guard ++ collectMetas body

collectItemMetas :: BackendItem -> [BackendMeta]
collectItemMetas = \case
  BKBind meta _ _ _ action _ -> meta : collectMetas action
  BKLet meta _ _ _ value -> meta : collectMetas value
  BKLetQ meta _ _ scrut mElse ->
    meta : collectMetas scrut ++ maybe [] (\(_, _, body) -> collectMetas body) mElse
  BKExpr meta action -> meta : collectMetas action
  BKVarItem meta _ initT action _ -> meta : collectMetas initT ++ collectMetas action
  BKAssign meta _ rhs action _ -> meta : collectMetas rhs ++ collectMetas action
  BKReturn meta value -> meta : collectMetas value
  BKWhile meta _ cond body mElse ->
    meta : collectCondMetas cond ++ concatMap collectItemMetas body ++ maybe [] (concatMap collectItemMetas) mElse
  BKFor meta _ _ _ source body mElse ->
    meta : collectMetas source ++ concatMap collectItemMetas body ++ maybe [] (concatMap collectItemMetas) mElse
  BKIf meta arms mElse ->
    meta
      : concatMap (\(cond, body) -> collectMetas cond ++ concatMap collectItemMetas body) arms
        ++ maybe [] (concatMap collectItemMetas) mElse
  BKDefer meta _ action -> meta : collectMetas action
  BKUsing meta _ _ acquire release -> meta : collectMetas acquire ++ collectMetas release
  BKSubDo meta _ body -> meta : concatMap collectItemMetas body
  BKBreak meta _ -> [meta]
  BKContinue meta _ -> [meta]

collectCondMetas :: BackendCond -> [BackendMeta]
collectCondMetas = \case
  BKCondPure t -> collectMetas t
  BKCondAction t -> collectMetas t

collectBodyBinders :: BackendBody -> [BackendBinder]
collectBodyBinders body =
  mapMaybe bpBinder (bbParams body) ++ collectTermBinders (bbRoot body)

collectTermBinders :: BackendTerm -> [BackendBinder]
collectTermBinders = \case
  BUnit {} -> []
  BVar {} -> []
  BGlob {} -> []
  BLit {} -> []
  BLam _ mb _ _ _ body -> maybe [] pure mb ++ collectTermBinders body
  BApp _ hd args -> collectTermBinders hd ++ concatMap (\(_, _, arg) -> collectTermBinders arg) args
  BCtor _ _ args -> concatMap collectTermBinders args
  BMatch _ scrut alts _ -> collectTermBinders scrut ++ concatMap collectAltBinders alts
  BRecord _ fs -> concatMap (collectTermBinders . snd) fs
  BProj _ e _ _ -> collectTermBinders e
  BInject _ _ e -> collectTermBinders e
  BLet _ mb _ _ rhs body -> maybe [] pure mb ++ collectTermBinders rhs ++ collectTermBinders body
  BLetRec _ mb _ _ rhs body -> maybe [] pure mb ++ collectTermBinders rhs ++ collectTermBinders body
  BDo _ _ items -> concatMap collectItemBinders items
  BSeal _ _ e -> collectTermBinders e
  BThunk _ e -> collectTermBinders e
  BLazy _ e -> collectTermBinders e
  BForce _ e -> collectTermBinders e
  BIf _ c th el -> collectTermBinders c ++ collectTermBinders th ++ collectTermBinders el

collectAltBinders :: BackendAlt -> [BackendBinder]
collectAltBinders (BackendAlt _ _ binders guard body) =
  catMaybes binders ++ maybe [] collectTermBinders guard ++ collectTermBinders body

collectItemBinders :: BackendItem -> [BackendBinder]
collectItemBinders = \case
  BKBind _ _ _ binders action _ -> catMaybes binders ++ collectTermBinders action
  BKLet _ _ _ binders value -> catMaybes binders ++ collectTermBinders value
  BKLetQ _ _ binders scrut mElse ->
    catMaybes binders
      ++ collectTermBinders scrut
      ++ maybe [] (\(_, ebinders, body) -> catMaybes ebinders ++ collectTermBinders body) mElse
  BKExpr _ action -> collectTermBinders action
  BKVarItem _ mb initT action _ -> maybe [] pure mb ++ collectTermBinders initT ++ collectTermBinders action
  BKAssign _ _ rhs action _ -> collectTermBinders rhs ++ collectTermBinders action
  BKReturn _ value -> collectTermBinders value
  BKWhile _ _ cond body mElse ->
    collectCondBinders cond ++ concatMap collectItemBinders body ++ maybe [] (concatMap collectItemBinders) mElse
  BKFor _ _ _ binders source body mElse ->
    catMaybes binders ++ collectTermBinders source ++ concatMap collectItemBinders body ++ maybe [] (concatMap collectItemBinders) mElse
  BKIf _ arms mElse ->
    concatMap (\(cond, body) -> collectTermBinders cond ++ concatMap collectItemBinders body) arms
      ++ maybe [] (concatMap collectItemBinders) mElse
  BKDefer _ _ action -> collectTermBinders action
  BKUsing _ _ binders acquire release ->
    catMaybes binders ++ collectTermBinders acquire ++ collectTermBinders release
  BKSubDo _ _ body -> concatMap collectItemBinders body
  BKBreak {} -> []
  BKContinue {} -> []

collectCondBinders :: BackendCond -> [BackendBinder]
collectCondBinders = \case
  BKCondPure t -> collectTermBinders t
  BKCondAction t -> collectTermBinders t

collectBodyUses :: BackendBody -> [BackendUse]
collectBodyUses body = collectTermUses (bbRoot body)

collectTermUses :: BackendTerm -> [BackendUse]
collectTermUses = \case
  BUnit {} -> []
  BVar _ mb _ -> maybe [] pure mb
  BGlob {} -> []
  BLit {} -> []
  BLam _ _ _ _ _ body -> collectTermUses body
  BApp _ hd args -> collectTermUses hd ++ concatMap (\(_, _, arg) -> collectTermUses arg) args
  BCtor _ _ args -> concatMap collectTermUses args
  BMatch _ scrut alts _ -> collectTermUses scrut ++ concatMap collectAltUses alts
  BRecord _ fs -> concatMap (collectTermUses . snd) fs
  BProj _ e _ _ -> collectTermUses e
  BInject _ _ e -> collectTermUses e
  BLet _ _ _ _ rhs body -> collectTermUses rhs ++ collectTermUses body
  BLetRec _ _ _ _ rhs body -> collectTermUses rhs ++ collectTermUses body
  BDo _ _ items -> concatMap collectItemUses items
  BSeal _ _ e -> collectTermUses e
  BThunk _ e -> collectTermUses e
  BLazy _ e -> collectTermUses e
  BForce _ e -> collectTermUses e
  BIf _ c th el -> collectTermUses c ++ collectTermUses th ++ collectTermUses el

collectAltUses :: BackendAlt -> [BackendUse]
collectAltUses (BackendAlt _ _ _ guard body) =
  maybe [] collectTermUses guard ++ collectTermUses body

collectItemUses :: BackendItem -> [BackendUse]
collectItemUses = \case
  BKBind _ _ _ _ action _ -> collectTermUses action
  BKLet _ _ _ _ value -> collectTermUses value
  BKLetQ _ _ _ scrut mElse ->
    collectTermUses scrut ++ maybe [] (\(_, _, body) -> collectTermUses body) mElse
  BKExpr _ action -> collectTermUses action
  BKVarItem _ _ initT action _ -> collectTermUses initT ++ collectTermUses action
  BKAssign _ _ rhs action _ -> collectTermUses rhs ++ collectTermUses action
  BKReturn _ value -> collectTermUses value
  BKWhile _ _ cond body mElse ->
    collectCondUses cond ++ concatMap collectItemUses body ++ maybe [] (concatMap collectItemUses) mElse
  BKFor _ _ _ _ source body mElse ->
    collectTermUses source ++ concatMap collectItemUses body ++ maybe [] (concatMap collectItemUses) mElse
  BKIf _ arms mElse ->
    concatMap (\(cond, body) -> collectTermUses cond ++ concatMap collectItemUses body) arms
      ++ maybe [] (concatMap collectItemUses) mElse
  BKDefer _ _ action -> collectTermUses action
  BKUsing _ _ _ acquire release -> collectTermUses acquire ++ collectTermUses release
  BKSubDo _ _ body -> concatMap collectItemUses body
  BKBreak {} -> []
  BKContinue {} -> []

collectCondUses :: BackendCond -> [BackendUse]
collectCondUses = \case
  BKCondPure t -> collectTermUses t
  BKCondAction t -> collectTermUses t

-- ── Backend-IR ownership annotation ──────────────────────────────────

data BackendUseMode = BackendConsumes | BackendReads
  deriving stock (Eq, Show)

data BackendOwnState = BackendOwnState
  { bosNextUse :: !Int
  , bosConsumingLastUses :: !(Set BackendBinderId)
  , bosBorrowDeps :: !(Map BackendBinderId (Set BackendBinderId))
  }

type OwnAnnot = State BackendOwnState

annotateBackendBodyOwnership :: BackendBody -> BackendBody
annotateBackendBodyOwnership body =
  let initialScopes = reverse (mapMaybe bpBinder (bbParams body))
      (root0, st') =
        runState
          (fst <$> walkBackendTerm BackendConsumes initialScopes (bbRoot body) Set.empty)
          (BackendOwnState 0 Set.empty Map.empty)
      hot = bosConsumingLastUses st'
   in refreshBodyBinders hot body {bbRoot = root0}

freshUse :: OwnAnnot BackendUseId
freshUse = do
  n <- gets bosNextUse
  modify' $ \st -> st {bosNextUse = n + 1}
  pure (BackendUseId n)

recordConsumingLast :: BackendBinderId -> OwnAnnot ()
recordConsumingLast bid =
  modify' $ \st -> st {bosConsumingLastUses = Set.insert bid (bosConsumingLastUses st)}

recordBorrowDeps :: BackendBinderId -> Set BackendBinderId -> OwnAnnot ()
recordBorrowDeps bid deps =
  modify' $ \st ->
    st
      { bosBorrowDeps =
          if Set.null deps
            then Map.delete bid (bosBorrowDeps st)
            else Map.insert bid deps (bosBorrowDeps st)
      }

expandLiveDeps :: Set BackendBinderId -> OwnAnnot (Set BackendBinderId)
expandLiveDeps seeds = do
  deps <- gets bosBorrowDeps
  pure (closeIds deps seeds)

closeIds :: Map BackendBinderId (Set BackendBinderId) -> Set BackendBinderId -> Set BackendBinderId
closeIds deps seeds = go seeds (Set.toList seeds)
  where
    go seen [] = seen
    go seen (bid : rest) =
      let next = Map.findWithDefault Set.empty bid deps `Set.difference` seen
       in go (seen `Set.union` next) (Set.toList next ++ rest)

walkBackendTerm :: BackendUseMode -> [BackendBinder] -> BackendTerm -> Set BackendBinderId -> OwnAnnot (BackendTerm, Set BackendBinderId)
walkBackendTerm mode scopes term liveOut = case term of
  BUnit {} -> pure (term, liveOut)
  BGlob {} -> pure (term, liveOut)
  BLit {} -> pure (term, liveOut)
  BVar meta _ i ->
    case binderAtRuntimeIndex i scopes of
      Nothing -> pure (BVar meta Nothing i, liveOut)
      Just binder -> do
        uid <- freshUse
        let bid = bbBinderId binder
            kind
              | boBorrowed (bbBinderOwn binder) = Borrowed
              | bid `Set.member` liveOut = NonLast
              | otherwise = LastUse
            consumes = mode == BackendConsumes && kind /= Borrowed
        when (consumes && kind == LastUse) (recordConsumingLast bid)
        pure (BVar meta (Just (BackendUse uid kind consumes)) i, Set.insert bid liveOut)
  BLam meta mb ic q nm body -> do
    let scopes' = maybe scopes (: scopes) mb
    (body', liveBody) <- walkBackendTerm BackendConsumes scopes' body liveOut
    pure (BLam meta mb ic q nm body', maybe liveBody (`Set.delete` liveBody) (bbBinderId <$> mb))
  BApp meta hd args -> do
    (args', liveArgs) <-
      foldr
        ( \(ic, conv, arg) action -> do
            (restArgs, restLive) <- action
            (arg', argLive) <- walkBackendTerm (backendArgUseMode ic conv) scopes arg restLive
            pure ((ic, conv, arg') : restArgs, argLive)
        )
        (pure ([], liveOut))
        args
    (hd', liveHead) <- walkBackendTerm BackendConsumes scopes hd liveArgs
    pure (BApp meta hd' args', liveHead)
  BCtor meta layout args -> do
    (args', liveArgs) <- walkBackendTerms BackendConsumes scopes args liveOut
    pure (BCtor meta layout args', liveArgs)
  BMatch meta scrut alts layouts -> do
    (alts0, armInfos) <- walkBackendAlts scopes alts liveOut
    entryLives <- mapM (expandLiveDeps . baiEntryLive) armInfos
    bodyLives <- mapM (expandLiveDeps . baiBodyLive) armInfos
    let liveAll = Set.unions entryLives
        (alts', _) =
          mapAccumLStrict
            ( \(fallthrough, idx) (alt, info) ->
                let liveAtDrop = if baiHasGuard info then bodyLives !! idx else entryLives !! idx
                    excluded = fallthrough `Set.union` baiGuardConsumes info
                    dropIds = (liveAll `Set.difference` liveAtDrop) `Set.difference` excluded
                    drops = bindersForIds scopes dropIds
                    alt' = addDropsToAlt drops alt
                 in ((fallthrough `Set.union` baiGuardConsumes info, idx + 1), alt')
            )
            (Set.empty, 0 :: Int)
            (zip alts0 armInfos)
    (scrut', liveScrut) <- walkBackendTerm BackendConsumes scopes scrut liveAll
    pure (BMatch meta scrut' alts' layouts, liveScrut)
  BRecord meta fs -> do
    (vals, liveVals) <- walkBackendTerms BackendConsumes scopes (map snd fs) liveOut
    pure (BRecord meta (zip (map fst fs) vals), liveVals)
  BProj meta e f mi -> do
    (e', liveE) <- walkBackendTerm BackendReads scopes e liveOut
    pure (BProj meta e' f mi, liveE)
  BInject meta tag e -> do
    (e', liveE) <- walkBackendTerm BackendConsumes scopes e liveOut
    pure (BInject meta tag e', liveE)
  BLet meta mb q nm rhs body -> do
    forM_ mb $ \binder ->
      recordBorrowDeps (bbBinderId binder) (borrowedResultDeps scopes rhs)
    let scopes' = maybe scopes (: scopes) mb
    (body', liveBody) <- walkBackendTerm mode scopes' body liveOut
    let liveBeforeRhs = maybe liveBody (`Set.delete` liveBody) (bbBinderId <$> mb)
    (rhs', liveRhs) <- walkBackendTerm BackendConsumes scopes rhs liveBeforeRhs
    pure (BLet meta mb q nm rhs' body', liveRhs)
  BLetRec meta mb q nm rhs body -> do
    forM_ mb $ \binder ->
      recordBorrowDeps (bbBinderId binder) (borrowedResultDeps scopes rhs)
    let scopes' = maybe scopes (: scopes) mb
    (body', liveBody) <- walkBackendTerm mode scopes' body liveOut
    (rhs', liveRhs) <- walkBackendTerm BackendConsumes scopes' rhs liveBody
    pure (BLetRec meta mb q nm rhs' body', maybe liveRhs (`Set.delete` liveRhs) (bbBinderId <$> mb))
  BDo meta lbl items -> do
    (items', liveItems) <- walkBackendItems scopes items liveOut
    pure (BDo meta lbl items', liveItems)
  BSeal meta labs e -> do
    (e', liveE) <- walkBackendTerm mode scopes e liveOut
    pure (BSeal meta labs e', liveE)
  BThunk meta e -> do
    (e', liveE) <- walkBackendTerm BackendConsumes scopes e liveOut
    pure (BThunk meta e', liveE)
  BLazy meta e -> do
    (e', liveE) <- walkBackendTerm BackendConsumes scopes e liveOut
    pure (BLazy meta e', liveE)
  BForce meta e -> do
    (e', liveE) <- walkBackendTerm BackendConsumes scopes e liveOut
    pure (BForce meta e', liveE)
  BIf meta c th el -> do
    (th0, liveTh) <- walkBackendTerm mode scopes th liveOut
    (el0, liveEl) <- walkBackendTerm mode scopes el liveOut
    liveTh' <- expandLiveDeps liveTh
    liveEl' <- expandLiveDeps liveEl
    let liveBranches = liveTh' `Set.union` liveEl'
        thDrops = bindersForIds scopes (liveBranches `Set.difference` liveTh')
        elDrops = bindersForIds scopes (liveBranches `Set.difference` liveEl')
        th' = addDropsToTerm thDrops th0
        el' = addDropsToTerm elDrops el0
    (c', liveC) <- walkBackendTerm BackendConsumes scopes c liveBranches
    pure (BIf meta c' th' el', liveC)

walkBackendTerms :: BackendUseMode -> [BackendBinder] -> [BackendTerm] -> Set BackendBinderId -> OwnAnnot ([BackendTerm], Set BackendBinderId)
walkBackendTerms mode scopes terms liveOut =
  foldr
    ( \term action -> do
        (restTerms, restLive) <- action
        (term', termLive) <- walkBackendTerm mode scopes term restLive
        pure (term' : restTerms, termLive)
    )
    (pure ([], liveOut))
    terms

data BackendAltInfo = BackendAltInfo
  { baiEntryLive :: !(Set BackendBinderId)
  , baiBodyLive :: !(Set BackendBinderId)
  , baiGuardConsumes :: !(Set BackendBinderId)
  , baiHasGuard :: !Bool
  }

walkBackendAlts :: [BackendBinder] -> [BackendAlt] -> Set BackendBinderId -> OwnAnnot ([BackendAlt], [BackendAltInfo])
walkBackendAlts scopes alts liveOut = go alts
  where
    go [] = pure ([], [])
    go (alt : rest) = do
      (rest', restInfo) <- go rest
      let guardFailLive = Set.unions (map baiEntryLive restInfo)
      (alt', info) <- walkBackendAlt scopes alt liveOut guardFailLive
      pure (alt' : rest', info : restInfo)

walkBackendAlt :: [BackendBinder] -> BackendAlt -> Set BackendBinderId -> Set BackendBinderId -> OwnAnnot (BackendAlt, BackendAltInfo)
walkBackendAlt scopes (BackendAlt meta pat binders guard body) liveOut guardFailLive = do
  let newBinders = catMaybes binders
      scopes' = newBinders ++ scopes
      localIds = Set.fromList (map bbBinderId newBinders)
  (body', liveBody0) <- walkBackendTerm BackendConsumes scopes' body liveOut
  beforeGuard <- gets bosConsumingLastUses
  (guard', liveEntry0) <-
    case guard of
      Nothing -> pure (Nothing, liveBody0)
      Just g -> do
        (g', liveG) <- walkBackendTerm BackendConsumes scopes' g (liveBody0 `Set.union` guardFailLive)
        pure (Just g', liveG)
  afterGuard <- gets bosConsumingLastUses
  let liveBody = liveBody0 `Set.difference` localIds
      liveEntry = liveEntry0 `Set.difference` localIds
      guardConsumes =
        case guard of
          Nothing -> Set.empty
          Just {} -> afterGuard `Set.difference` beforeGuard
      info =
        BackendAltInfo
          { baiEntryLive = liveEntry
          , baiBodyLive = liveBody
          , baiGuardConsumes = guardConsumes
          , baiHasGuard = maybe False (const True) guard
          }
  pure (BackendAlt meta pat binders guard' body', info)

walkBackendCond :: [BackendBinder] -> BackendCond -> Set BackendBinderId -> OwnAnnot (BackendCond, Set BackendBinderId)
walkBackendCond scopes cond liveOut =
  case cond of
    BKCondPure t -> do
      (t', liveT) <- walkBackendTerm BackendConsumes scopes t liveOut
      pure (BKCondPure t', liveT)
    BKCondAction t -> do
      (t', liveT) <- walkBackendTerm BackendConsumes scopes t liveOut
      pure (BKCondAction t', liveT)

walkBackendItems :: [BackendBinder] -> [BackendItem] -> Set BackendBinderId -> OwnAnnot ([BackendItem], Set BackendBinderId)
walkBackendItems scopes items liveOut = go scopes items liveOut
  where
    go _ [] lo = pure ([], lo)
    go scs (item : rest) lo =
      case item of
        BKBind meta q pat binders action wit -> do
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
          (rest', liveRest) <- go scs' rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action (liveRest `Set.difference` localIds)
          pure (BKBind meta q pat binders action' wit : rest', liveAction)
        BKLet meta q pat binders value -> do
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
          forM_ newBinders $ \binder ->
            recordBorrowDeps (bbBinderId binder) (borrowedResultDeps scs value)
          (rest', liveRest) <- go scs' rest lo
          (value', liveValue) <- walkBackendTerm BackendConsumes scs value (liveRest `Set.difference` localIds)
          pure (BKLet meta q pat binders value' : rest', liveValue)
        BKLetQ meta pat binders scrut mElse -> do
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
          (rest', liveRest) <- go scs' rest lo
          let liveSuccess = liveRest `Set.difference` localIds
          (mElse', liveElse) <-
            case mElse of
              Nothing -> pure (Nothing, Set.empty)
              Just (ep, ebinders, et) -> do
                let ebs = catMaybes ebinders
                    escs = ebs ++ scs
                    eids = Set.fromList (map bbBinderId ebs)
                (et', liveEt) <- walkBackendTerm BackendConsumes escs et lo
                pure (Just (ep, ebinders, et'), liveEt `Set.difference` eids)
          (scrut', liveScrut) <- walkBackendTerm BackendConsumes scs scrut (liveSuccess `Set.union` liveElse)
          pure (BKLetQ meta pat binders scrut' mElse' : rest', liveScrut)
        BKExpr meta action -> do
          (rest', liveRest) <- go scs rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action liveRest
          pure (BKExpr meta action' : rest', liveAction)
        BKVarItem meta mb initT action wit -> do
          let scs' = maybe scs (: scs) mb
              localIds = maybe Set.empty (Set.singleton . bbBinderId) mb
          (rest', liveRest) <- go scs' rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action (liveRest `Set.difference` localIds)
          (initT', _) <- walkBackendTerm BackendReads scs initT Set.empty
          pure (BKVarItem meta mb initT' action' wit : rest', liveAction)
        BKAssign meta monadic rhs action wit -> do
          (rest', liveRest) <- go scs rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action liveRest
          (rhs', liveRhs) <- walkBackendTerm BackendConsumes scs rhs liveAction
          pure (BKAssign meta monadic rhs' action' wit : rest', liveRhs)
        BKReturn meta value -> do
          (value', liveValue) <- walkBackendTerm BackendConsumes scs value lo
          pure ([BKReturn meta value'], liveValue)
        BKWhile meta pureCond cond body mElse -> do
          (rest', liveRest) <- go scs rest lo
          let loopUses = freeBackendCond scs cond `Set.union` freeBackendItems scs body
              loopLiveOut = liveRest `Set.union` loopUses
          (body', liveBody) <- walkBackendItems scs body loopLiveOut
          (mElse', liveElse) <-
            case mElse of
              Nothing -> pure (Nothing, liveRest)
              Just els -> do
                (els', liveEls) <- walkBackendItems scs els liveRest
                pure (Just els', liveEls)
          (cond', liveCond) <- walkBackendCond scs cond (Set.unions [loopLiveOut, liveBody, liveElse])
          pure (BKWhile meta pureCond cond' body' mElse' : rest', liveCond)
        BKFor meta ml pat binders source body mElse -> do
          (rest', liveRest) <- go scs rest lo
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
              loopUses = freeBackendItems scs' body `Set.difference` localIds
              loopLiveOut = liveRest `Set.union` loopUses
          (body', liveBody0) <- walkBackendItems scs' body loopLiveOut
          let liveBody = liveBody0 `Set.difference` localIds
          (mElse', liveElse) <-
            case mElse of
              Nothing -> pure (Nothing, liveRest)
              Just els -> do
                (els', liveEls) <- walkBackendItems scs els liveRest
                pure (Just els', liveEls)
          (source', liveSource) <- walkBackendTerm BackendConsumes scs source (Set.unions [liveRest, liveBody, liveElse])
          pure (BKFor meta ml pat binders source' body' mElse' : rest', liveSource)
        BKIf meta arms mElse -> do
          (rest', liveRest) <- go scs rest lo
          (arms', mElse', liveIf) <- walkBackendIfItems scs arms mElse liveRest
          pure (BKIf meta arms' mElse' : rest', liveIf)
        BKDefer meta lbl action -> do
          (rest', liveRest) <- go scs rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action liveRest
          pure (BKDefer meta lbl action' : rest', liveAction)
        BKUsing meta pat binders acquire release -> do
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
          (rest', liveRest) <- go scs' rest lo
          (release', liveRelease) <- walkBackendTerm BackendConsumes scs release (liveRest `Set.difference` localIds)
          (acquire', liveAcquire) <- walkBackendTerm BackendConsumes scs acquire liveRelease
          pure (BKUsing meta pat binders acquire' release' : rest', liveAcquire)
        BKSubDo meta lbl body -> do
          (rest', liveRest) <- go scs rest lo
          (body', liveBody) <- walkBackendItems scs body liveRest
          pure (BKSubDo meta lbl body' : rest', liveBody)
        BKBreak {} -> pure (item : rest, lo)
        BKContinue {} -> pure (item : rest, lo)

walkBackendIfItems
  :: [BackendBinder]
  -> [(BackendTerm, [BackendItem])]
  -> Maybe [BackendItem]
  -> Set BackendBinderId
  -> OwnAnnot ([(BackendTerm, [BackendItem])], Maybe [BackendItem], Set BackendBinderId)
walkBackendIfItems scopes arms mElse liveRest = do
  (mElse', liveElse) <-
    case mElse of
      Nothing -> pure (Nothing, liveRest)
      Just els -> do
        (els', liveEls) <- walkBackendItems scopes els liveRest
        pure (Just els', liveEls)
  (arms', liveArms) <- go arms liveElse
  pure (arms', mElse', liveArms)
  where
    go [] liveMore = pure ([], liveMore)
    go ((cond, body) : rest) liveMore = do
      (rest', liveRestArms) <- go rest liveMore
      (body', liveBody) <- walkBackendItems scopes body liveRest
      (cond', liveCond) <- walkBackendTerm BackendConsumes scopes cond (liveBody `Set.union` liveRestArms)
      pure ((cond', body') : rest', liveCond)

freeBackendCond :: [BackendBinder] -> BackendCond -> Set BackendBinderId
freeBackendCond scopes cond =
  snd $
    evalState
      (walkBackendCond scopes cond Set.empty)
      (BackendOwnState 0 Set.empty Map.empty)

freeBackendItems :: [BackendBinder] -> [BackendItem] -> Set BackendBinderId
freeBackendItems scopes items =
  snd $
    evalState
      (walkBackendItems scopes items Set.empty)
      (BackendOwnState 0 Set.empty Map.empty)

freeBackendTermPlain :: [BackendBinder] -> BackendTerm -> Set BackendBinderId
freeBackendTermPlain scopes term =
  snd $
    evalState
      (walkBackendTerm BackendConsumes scopes term Set.empty)
      (BackendOwnState 0 Set.empty Map.empty)

borrowedResultDeps :: [BackendBinder] -> BackendTerm -> Set BackendBinderId
borrowedResultDeps scopes = \case
  BProj _ e _ _ -> freeBackendTermPlain scopes e
  BSeal _ _ e -> borrowedResultDeps scopes e
  BIf _ _ th el -> borrowedResultDeps scopes th `Set.union` borrowedResultDeps scopes el
  BLet _ mb _ _ rhs body ->
    let rhsDeps = borrowedResultDeps scopes rhs
        scopes' = maybe scopes (: scopes) mb
        bodyDeps = borrowedResultDeps scopes' body
     in rhsDeps `Set.union` (bodyDeps `Set.difference` maybe Set.empty (Set.singleton . bbBinderId) mb)
  BLetRec _ mb _ _ rhs body ->
    let scopes' = maybe scopes (: scopes) mb
        localIds = maybe Set.empty (Set.singleton . bbBinderId) mb
     in (borrowedResultDeps scopes' rhs `Set.union` borrowedResultDeps scopes' body) `Set.difference` localIds
  BMatch _ scrut alts _ ->
    freeBackendTermPlain scopes scrut
      `Set.union` Set.unions [maybe Set.empty (borrowedResultDeps scopes) guard `Set.union` borrowedResultDeps scopes body | BackendAlt _ _ _ guard body <- alts]
  t@BApp {} -> freeBackendTermPlain scopes t
  _ -> Set.empty

backendArgUseMode :: Icit -> Maybe ArgConv -> BackendUseMode
backendArgUseMode ic conv
  | ic /= Expl = BackendReads
  | otherwise =
      case conv of
        Just Repr.ArgBorrowed -> BackendReads
        _ -> BackendConsumes

binderAtRuntimeIndex :: Int -> [BackendBinder] -> Maybe BackendBinder
binderAtRuntimeIndex i scopes
  | i < 0 = Nothing
  | otherwise = indexMaybeLocal i scopes

indexMaybeLocal :: Int -> [a] -> Maybe a
indexMaybeLocal i xs
  | i < 0 = Nothing
  | otherwise = go i xs
  where
    go 0 (x : _) = Just x
    go n (_ : rest) = go (n - 1) rest
    go _ [] = Nothing

bindersForIds :: [BackendBinder] -> Set BackendBinderId -> [BackendBinder]
bindersForIds scopes ids =
  [ binder
  | binder <- scopes
  , bbBinderId binder `Set.member` ids
  ]

addDropsToAlt :: [BackendBinder] -> BackendAlt -> BackendAlt
addDropsToAlt drops alt@(BackendAlt meta pat binders guard body)
  | null drops = alt
  | otherwise = BackendAlt (addDropsToMeta drops meta) pat binders guard body

addDropsToTerm :: [BackendBinder] -> BackendTerm -> BackendTerm
addDropsToTerm drops term
  | null drops = term
  | otherwise = mapTermMeta (addDropsToMeta drops) term

addDropsToMeta :: [BackendBinder] -> BackendMeta -> BackendMeta
addDropsToMeta drops (BackendMeta nid existing) =
  BackendMeta nid (existing ++ drops)

mapAccumLStrict :: (acc -> x -> (acc, y)) -> acc -> [x] -> ([y], acc)
mapAccumLStrict f = go []
  where
    go ys !acc [] = (reverse ys, acc)
    go ys !acc (x : xs) =
      let (!acc', !y) = f acc x
       in go (y : ys) acc' xs

mapTermMeta :: (BackendMeta -> BackendMeta) -> BackendTerm -> BackendTerm
mapTermMeta f = \case
  BUnit meta -> BUnit (f meta)
  BVar meta use i -> BVar (f meta) use i
  BGlob meta g -> BGlob (f meta) g
  BLit meta l -> BLit (f meta) l
  BLam meta mb ic q nm body -> BLam (f meta) mb ic q nm body
  BApp meta hd args -> BApp (f meta) hd args
  BCtor meta layout args -> BCtor (f meta) layout args
  BMatch meta scrut alts layouts -> BMatch (f meta) scrut alts layouts
  BRecord meta fs -> BRecord (f meta) fs
  BProj meta e fld mi -> BProj (f meta) e fld mi
  BInject meta tag e -> BInject (f meta) tag e
  BLet meta mb q nm rhs body -> BLet (f meta) mb q nm rhs body
  BLetRec meta mb q nm rhs body -> BLetRec (f meta) mb q nm rhs body
  BDo meta lbl items -> BDo (f meta) lbl items
  BSeal meta labs e -> BSeal (f meta) labs e
  BThunk meta e -> BThunk (f meta) e
  BLazy meta e -> BLazy (f meta) e
  BForce meta e -> BForce (f meta) e
  BIf meta c th el -> BIf (f meta) c th el

refreshBodyBinders :: Set BackendBinderId -> BackendBody -> BackendBody
refreshBodyBinders hot body =
  body
    { bbParams = map (refreshParamBinders hot) (bbParams body)
    , bbRoot = refreshTermBinders hot (bbRoot body)
    }

refreshParamBinders :: Set BackendBinderId -> BackendParam -> BackendParam
refreshParamBinders hot p =
  p {bpBinder = refreshMaybeBinder hot (bpBinder p)}

refreshMaybeBinder :: Set BackendBinderId -> Maybe BackendBinder -> Maybe BackendBinder
refreshMaybeBinder hot = fmap (refreshBinder hot)

refreshBinder :: Set BackendBinderId -> BackendBinder -> BackendBinder
refreshBinder hot binder =
  binder {bbBinderHasConsumingLastUse = bbBinderId binder `Set.member` hot}

refreshMetaBinders :: Set BackendBinderId -> BackendMeta -> BackendMeta
refreshMetaBinders hot (BackendMeta nid drops) =
  BackendMeta nid (map (refreshBinder hot) drops)

refreshTermBinders :: Set BackendBinderId -> BackendTerm -> BackendTerm
refreshTermBinders hot = \case
  BUnit meta -> BUnit (refreshMetaBinders hot meta)
  BVar meta use i -> BVar (refreshMetaBinders hot meta) use i
  BGlob meta g -> BGlob (refreshMetaBinders hot meta) g
  BLit meta l -> BLit (refreshMetaBinders hot meta) l
  BLam meta mb ic q nm body ->
    BLam (refreshMetaBinders hot meta) (refreshMaybeBinder hot mb) ic q nm (refreshTermBinders hot body)
  BApp meta hd args ->
    BApp (refreshMetaBinders hot meta) (refreshTermBinders hot hd) [(ic, conv, refreshTermBinders hot arg) | (ic, conv, arg) <- args]
  BCtor meta layout args ->
    BCtor (refreshMetaBinders hot meta) layout (map (refreshTermBinders hot) args)
  BMatch meta scrut alts layouts ->
    BMatch (refreshMetaBinders hot meta) (refreshTermBinders hot scrut) (map (refreshAltBinders hot) alts) layouts
  BRecord meta fs -> BRecord (refreshMetaBinders hot meta) [(n, refreshTermBinders hot v) | (n, v) <- fs]
  BProj meta e fld mi -> BProj (refreshMetaBinders hot meta) (refreshTermBinders hot e) fld mi
  BInject meta tag e -> BInject (refreshMetaBinders hot meta) tag (refreshTermBinders hot e)
  BLet meta mb q nm rhs body ->
    BLet (refreshMetaBinders hot meta) (refreshMaybeBinder hot mb) q nm (refreshTermBinders hot rhs) (refreshTermBinders hot body)
  BLetRec meta mb q nm rhs body ->
    BLetRec (refreshMetaBinders hot meta) (refreshMaybeBinder hot mb) q nm (refreshTermBinders hot rhs) (refreshTermBinders hot body)
  BDo meta lbl items -> BDo (refreshMetaBinders hot meta) lbl (map (refreshItemBinders hot) items)
  BSeal meta labs e -> BSeal (refreshMetaBinders hot meta) labs (refreshTermBinders hot e)
  BThunk meta e -> BThunk (refreshMetaBinders hot meta) (refreshTermBinders hot e)
  BLazy meta e -> BLazy (refreshMetaBinders hot meta) (refreshTermBinders hot e)
  BForce meta e -> BForce (refreshMetaBinders hot meta) (refreshTermBinders hot e)
  BIf meta c th el ->
    BIf (refreshMetaBinders hot meta) (refreshTermBinders hot c) (refreshTermBinders hot th) (refreshTermBinders hot el)

refreshAltBinders :: Set BackendBinderId -> BackendAlt -> BackendAlt
refreshAltBinders hot (BackendAlt meta pat binders guard body) =
  BackendAlt
    (refreshMetaBinders hot meta)
    pat
    (map (refreshMaybeBinder hot) binders)
    (refreshTermBinders hot <$> guard)
    (refreshTermBinders hot body)

refreshItemBinders :: Set BackendBinderId -> BackendItem -> BackendItem
refreshItemBinders hot = \case
  BKBind meta q pat binders action wit ->
    BKBind (refreshMetaBinders hot meta) q pat (map (refreshMaybeBinder hot) binders) (refreshTermBinders hot action) wit
  BKLet meta q pat binders value ->
    BKLet (refreshMetaBinders hot meta) q pat (map (refreshMaybeBinder hot) binders) (refreshTermBinders hot value)
  BKLetQ meta pat binders scrut mElse ->
    BKLetQ
      (refreshMetaBinders hot meta)
      pat
      (map (refreshMaybeBinder hot) binders)
      (refreshTermBinders hot scrut)
      ( (\(ep, ebinders, body) -> (ep, map (refreshMaybeBinder hot) ebinders, refreshTermBinders hot body)) <$> mElse
      )
  BKExpr meta action -> BKExpr (refreshMetaBinders hot meta) (refreshTermBinders hot action)
  BKVarItem meta mb initT action wit ->
    BKVarItem (refreshMetaBinders hot meta) (refreshMaybeBinder hot mb) (refreshTermBinders hot initT) (refreshTermBinders hot action) wit
  BKAssign meta monadic rhs action wit ->
    BKAssign (refreshMetaBinders hot meta) monadic (refreshTermBinders hot rhs) (refreshTermBinders hot action) wit
  BKReturn meta value -> BKReturn (refreshMetaBinders hot meta) (refreshTermBinders hot value)
  BKWhile meta pureCond cond body mElse ->
    BKWhile
      (refreshMetaBinders hot meta)
      pureCond
      (refreshCondBinders hot cond)
      (map (refreshItemBinders hot) body)
      (fmap (map (refreshItemBinders hot)) mElse)
  BKFor meta ml pat binders source body mElse ->
    BKFor
      (refreshMetaBinders hot meta)
      ml
      pat
      (map (refreshMaybeBinder hot) binders)
      (refreshTermBinders hot source)
      (map (refreshItemBinders hot) body)
      (fmap (map (refreshItemBinders hot)) mElse)
  BKIf meta arms mElse ->
    BKIf
      (refreshMetaBinders hot meta)
      [(refreshTermBinders hot cond, map (refreshItemBinders hot) body) | (cond, body) <- arms]
      (fmap (map (refreshItemBinders hot)) mElse)
  BKDefer meta lbl action -> BKDefer (refreshMetaBinders hot meta) lbl (refreshTermBinders hot action)
  BKUsing meta pat binders acquire release ->
    BKUsing
      (refreshMetaBinders hot meta)
      pat
      (map (refreshMaybeBinder hot) binders)
      (refreshTermBinders hot acquire)
      (refreshTermBinders hot release)
  BKSubDo meta lbl body -> BKSubDo (refreshMetaBinders hot meta) lbl (map (refreshItemBinders hot) body)
  BKBreak meta lbl -> BKBreak (refreshMetaBinders hot meta) lbl
  BKContinue meta lbl -> BKContinue (refreshMetaBinders hot meta) lbl

refreshCondBinders :: Set BackendBinderId -> BackendCond -> BackendCond
refreshCondBinders hot = \case
  BKCondPure t -> BKCondPure (refreshTermBinders hot t)
  BKCondAction t -> BKCondAction (refreshTermBinders hot t)

backendMeta :: BackendTerm -> BackendMeta
backendMeta = \case
  BUnit meta -> meta
  BVar meta _ _ -> meta
  BGlob meta _ -> meta
  BLit meta _ -> meta
  BLam meta _ _ _ _ _ -> meta
  BApp meta _ _ -> meta
  BCtor meta _ _ -> meta
  BMatch meta _ _ _ -> meta
  BRecord meta _ -> meta
  BProj meta _ _ _ -> meta
  BInject meta _ _ -> meta
  BLet meta _ _ _ _ _ -> meta
  BLetRec meta _ _ _ _ _ -> meta
  BDo meta _ _ -> meta
  BSeal meta _ _ -> meta
  BThunk meta _ -> meta
  BLazy meta _ -> meta
  BForce meta _ -> meta
  BIf meta _ _ _ -> meta

lowerBody :: EvalCtx -> Map GName GlobalDef -> Map GName DataInfo -> Map GName CtorInfo -> Map GName TraitInfo -> [InstanceEntry] -> Set GName -> GName -> Term -> (BackendBody, [BackendIRViolation])
lowerBody ctx globals datas ctors traits instances builtinIntegerLiteralDicts g body =
  let (body0, st') = runState (runReaderT go static) (LowerState 0 0 [] [])
      bodyWithErasures = body0 {bbErasures = bbErasures body0 ++ reverse (lstErasures st')}
      body' = annotateBackendBodyOwnership bodyWithErasures
   in (body', reverse (lstLoweringViolations st'))
  where
    static =
      LowerStatic
        { lsOwner = g
        , lsGlobals = globals
        , lsDatas = datas
        , lsCtors = ctors
        , lsTraits = traits
        , lsInstances = instances
        , lsRuntimeErasedProofHeads =
            Set.fromList
              ( prelNatAddRightIdentity
                  : [ traitMemberGlobal trait member
                    | (trait, info) <- Map.toList traits
                    , member <- tiMembers info
                    , Map.lookup member (tiMemberQs info) == Just Q0
                    ]
              )
        , lsBuiltinIntegerLiteralDicts = builtinIntegerLiteralDicts
        , lsCtx = ctx
        }
    paramSites = maybe [] (paramLowerSites ctx . gdType) (Map.lookup g globals)
    go = do
      (params, erasures, scopes, root0) <- lowerLeadingParams paramSites [] [] [] body
      if bodyRuntimeErased g root0
        then do
          meta <- metaAt
          pure BackendBody {bbOwner = g, bbParams = [], bbErasures = erasures, bbRoot = BUnit meta}
        else do
          root <- lowerTermExpected (bodyResultExpected (length scopes)) root0 (length scopes) scopes
          pure BackendBody {bbOwner = g, bbParams = params, bbErasures = erasures, bbRoot = root}

    bodyRuntimeErased owner root =
      Repr.resultIsProofBodyGlobal globals ctx owner
        || maybe False (globalResultIsCompileTimeOnly ctx . gdType) (Map.lookup owner globals)
        || sourceArgErased globals ctx root

    bodyResultExpected paramCount =
      Map.lookup g globals >>= resultTypeAfterParams ctx paramCount . gdType

globalResultIsCompileTimeOnly :: EvalCtx -> Value -> Bool
globalResultIsCompileTimeOnly ctx = go 0
  where
    go lvl ty =
      case force ctx ty of
        VPi _ _ _ _ _ (Closure env cod) ->
          go (lvl + 1) (eval ctx (VRigid lvl [] : env) cod)
        result -> Repr.valueDomainIsCompileTimeOnly ctx lvl result

resultTypeAfterParams :: EvalCtx -> Int -> Value -> Maybe Value
resultTypeAfterParams ctx count = go 0 count
  where
    go _ 0 ty = Just ty
    go lvl n ty =
      case force ctx ty of
        VPi _ _ _ _ _ (Closure env cod) ->
          go (lvl + 1) (n - 1) (eval ctx (VRigid lvl [] : env) cod)
        _ -> Nothing

paramLowerSites :: EvalCtx -> Value -> [ParamLowerSite]
paramLowerSites ctx = go 0
  where
    go lvl ty =
      case force ctx ty of
        VPiRuntimeM mode _ ic q borrowed _ _ _ runtimeErasure dom (Closure env cod) ->
          let x = VRigid lvl []
              domV = force ctx dom
              codV = eval ctx (x : env) cod
              site =
                ParamLowerSite
                  { plsIcit = ic
                  , plsMode = mode
                  , plsQ = q
                  , plsBorrowed = borrowed
                  , plsErasure = erasureProvenanceForPiDomain ctx lvl mode q runtimeErasure domV
                  , plsDomain = domV
                  }
           in site : go (lvl + 1) codV
        _ -> []


erasureProvenanceForDomain :: EvalCtx -> Int -> ObservationMode -> Q -> Value -> Maybe ErasureProvenance
erasureProvenanceForDomain ctx lvl mode q dom
  | q == Q0 = Just ErasedByQuantity
  | Repr.valueDomainIsKind ctx lvl dom = case mode of
      Ordinary -> Just ErasedOrdinaryTypeCode
      Parametric -> case force ctx dom of
        VSort rho -> Just (ErasedParametricTypeWitness rho)
        _ -> Just ErasedParametricTypeFormer
  | Repr.valueDomainIsCompileTimeOnly ctx lvl dom =
      Just ErasedIntrinsicCompileTimeValue
  | Repr.resultIsProofValue ctx lvl dom = Just ErasedProofOrTraitEvidence
  | otherwise = Nothing

erasureProvenanceForPiDomain
  :: EvalCtx
  -> Int
  -> ObservationMode
  -> Q
  -> RuntimeErasure Value
  -> Value
  -> Maybe ErasureProvenance
erasureProvenanceForPiDomain ctx lvl mode q runtimeErasure dom
  | q == Q0 = Just ErasedByQuantity
  | RuntimeErased (RuntimeErasedEvidence goal evidence evidenceType) <- runtimeErasure =
      Just
        ( ErasedBySelectedEvidence
            (quote ctx lvl goal)
            (quote ctx lvl evidence)
            (quote ctx lvl evidenceType)
        )
  | otherwise = erasureProvenanceForDomain ctx lvl mode q dom

erasureProvenanceForLocalDomain
  :: EvalCtx
  -> Int
  -> ObservationMode
  -> Q
  -> RuntimeErasure Term
  -> Value
  -> Maybe ErasureProvenance
erasureProvenanceForLocalDomain ctx depth mode quantity runtimeErasure domain
  | quantity == Q0 = Just ErasedByQuantity
  | RuntimeErased (RuntimeErasedEvidence goal evidence evidenceType) <- runtimeErasure =
      Just (ErasedBySelectedEvidence goal evidence evidenceType)
  | otherwise = erasureProvenanceForDomain ctx depth mode quantity domain

qDroppable :: Q -> Bool
qDroppable = \case
  Q0 -> True
  QLe1 -> True
  QW -> True
  Q1 -> False
  QGe1 -> False

lowerLeadingParams :: [ParamLowerSite] -> [BackendParam] -> [BackendErasure] -> ScopeStack -> Term -> Lower ([BackendParam], [BackendErasure], ScopeStack, Term)
lowerLeadingParams sites params erasures scopes = \case
  CLamM mode ic q nm body -> do
    let (declMode, declQ, borrowed, provenance, mTy, sites') = case takeMatchingParam ic sites of
          Just (site, rest) -> (plsMode site, plsQ site, plsBorrowed site, plsErasure site, Just (plsDomain site), rest)
          Nothing -> (mode, q, False, if q == Q0 then Just ErasedByQuantity else Nothing, Nothing, sites)
        erased = isJust provenance
    when (declMode /= mode) $ do
      mismatchMeta <- metaAt
      recordLoweringViolation mismatchMeta "E_PARAMETRIC_TYPE_PROMOTION"
        ("lambda observation mode disagrees with its declared parameter: " <> T.pack (show mode)
          <> " vs " <> T.pack (show declMode))
    whenJust provenance $ \reason -> do
      erasureMeta <- metaAt
      recordErasureAt (length scopes) erasureMeta ErasedParameterSite ic nm reason
    mb <- if erased then pure Nothing else binderAtWith declQ borrowed (T.pack ("parameter " <> T.unpack nm))
    let scopes' = ScopeSlot (mbId mb) mTy Nothing : scopes
        params' = params ++ [BackendParam ic nm mb | not erased]
        erasures' = erasures
    lowerLeadingParams sites' params' erasures' scopes' body
  t -> pure (params, erasures, scopes, t)
  where
    mbId = fmap bbBinderId
    takeMatchingParam _ [] = Nothing
    takeMatchingParam ic (site : rest)
      | ic == plsIcit site = Just (site, rest)
      | otherwise =
          second (site :) <$> takeMatchingParam ic rest

    whenJust Nothing _ = pure ()
    whenJust (Just value) action = action value

second :: (b -> c) -> (a, b) -> (a, c)
second f (a, b) = (a, f b)

lowerTerm :: Term -> Int -> ScopeStack -> Lower BackendTerm
lowerTerm = lowerTermExpected Nothing

lowerTermExpected :: Maybe Value -> Term -> Int -> ScopeStack -> Lower BackendTerm
lowerTermExpected expected term depth scopes = do
  ctx <- asks lsCtx
  if expectedIsErasedProofResult ctx depth expected && not (isEvidenceWrapper term)
    then BUnit <$> metaAt
    else lowerRuntimeTermExpected expected term depth scopes
  where
    -- Universe/schema wrappers carry certificates that must still be replayed.
    -- Their recursive call reaches this erasure boundary after validation.
    isEvidenceWrapper = \case
      CUniverseLift {} -> True
      CSchemaLift {} -> True
      _ -> False

expectedIsErasedProofResult :: EvalCtx -> Int -> Maybe Value -> Bool
expectedIsErasedProofResult ctx depth = \case
  Nothing -> False
  Just expected ->
    case force ctx expected of
      VPiRuntimeM {} -> False
      _ -> Repr.resultIsProofBodyValue ctx depth expected

lowerRuntimeTermExpected :: Maybe Value -> Term -> Int -> ScopeStack -> Lower BackendTerm
lowerRuntimeTermExpected expected term depth scopes = case term of
  CUniverseLift _ _ _ inner -> do
    owner <- asks lsOwner
    globals <- asks lsGlobals
    ctx <- asks lsCtx
    let ownerUniverses = maybe emptyDeclarationUniverseTelescope gdUniverses (Map.lookup owner globals)
        universeArity = dutParameterCount ownerUniverses
        ownerConstraints =
          maybe []
            (declarationUniverseConstraints universeArity . finalizedGlobalType ctx)
            (Map.lookup owner globals)
        assumptions =
          foldr
            (\constraint -> insertAssumption (ucLower constraint) (ucUpper constraint))
            emptyAssumptions
            ownerConstraints
    forM_ (validateUniverseLiftEvidenceUnder assumptions depth universeArity term) $ \message -> do
      meta <- metaAt
      loweringViolation meta "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" message
    lowerTermExpected expected inner depth scopes
  CSchemaLift family source target _ _ _ sourceArguments targetArguments inner -> do
    owner <- asks lsOwner
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    meta <- metaAt
    let ownerUniverses = maybe emptyDeclarationUniverseTelescope gdUniverses (Map.lookup owner globals)
        universeArity = dutParameterCount ownerUniverses
        ownerConstraints =
          maybe []
            (declarationUniverseConstraints universeArity . finalizedGlobalType ctx)
            (Map.lookup owner globals)
        assumptions =
          foldr
            (\constraint -> insertAssumption (ucLower constraint) (ucUpper constraint))
            emptyAssumptions
            ownerConstraints
        actualSource = termTypeAt globals traits ctx depth scopes inner
        sourceErrors =
          schemaLiftInstanceErrors ctx depth assumptions "source" family source sourceArguments actualSource
        targetErrors =
          case expected of
            Nothing ->
              ["schema lift target has no typed expectation at the erasure boundary"]
            Just targetType ->
              schemaLiftInstanceErrors
                ctx depth assumptions "target" family target targetArguments (Just targetType)
    forM_ (sourceErrors ++ targetErrors) $ \message ->
      recordLoweringViolation meta "E_UNIVERSE_SCHEMA_LIFT_INVALID" message
    lowerTermExpected expected inner depth scopes
  CVar i -> do
    meta <- metaAt
    let runtimeIdx = length [() | ScopeSlot (Just _) _ _ <- take i scopes]
    case drop i scopes of
      ScopeSlotData _ _ telescope (Just alias) : _ -> do
        when (maybe False ((> 0) . dutParameterCount) telescope) $
          recordLoweringViolation meta "E_UNIVERSE_SCHEMA_SCOPE"
            "a universe-polymorphic local recursive member was referenced without an explicit universe instantiation"
        lowerRuntimeLocalAlias meta scopes alias
      ScopeSlot (Just _) _ _ : _ -> pure (BVar meta Nothing runtimeIdx)
      ScopeSlot Nothing classifier _ : _ -> do
        ctx <- asks lsCtx
        let classifierDetail = case classifier of
              Nothing -> ""
              Just value ->
                "; classifier " <> renderTerm (quote ctx depth value)
        erasedRuntimeAt meta
          ( "erased variable occurrence reached a runtime BackendIR value position"
              <> " (de Bruijn index " <> T.pack (show i)
              <> "; scope erasure mask "
              <> T.pack
                   [ case slot of
                       ScopeSlot (Just _) _ _ -> 'R'
                       ScopeSlot Nothing _ _ -> 'E'
                   | slot <- scopes
                   ]
              <> classifierDetail <> ")"
          )
      _ -> erasedRuntimeAt meta "out-of-scope variable occurrence reached a runtime BackendIR value position"
  CLocal i universes -> do
    meta <- metaAt
    let runtimeIdx = length [() | ScopeSlot (Just _) _ _ <- take i scopes]
    case drop i scopes of
      ScopeSlotData _ _ (Just telescope) (Just alias) : _ -> do
        when (length universes /= dutParameterCount telescope) $
          recordLoweringViolation meta "E_UNIVERSE_SCHEMA_ARITY_MISMATCH"
            ( "local declaration expects " <> T.pack (show (dutParameterCount telescope))
                <> " universe arguments, found " <> T.pack (show (length universes))
            )
        lowerRuntimeLocalAlias meta scopes alias
      ScopeSlot (Just _) _ (Just telescope) : _ -> do
        when (length universes /= dutParameterCount telescope) $
          recordLoweringViolation meta "E_UNIVERSE_SCHEMA_ARITY_MISMATCH"
            ( "local declaration expects " <> T.pack (show (dutParameterCount telescope))
                <> " universe arguments, found " <> T.pack (show (length universes))
            )
        pure (BVar meta Nothing runtimeIdx)
      ScopeSlot (Just _) _ Nothing : _ -> do
        recordLoweringViolation meta "E_UNIVERSE_SCHEMA_SCOPE"
          "universe-specialized occurrence refers to a local without a universe schema"
        pure (BVar meta Nothing runtimeIdx)
      ScopeSlot Nothing _ _ : _ ->
        erasedRuntimeAt meta "erased universe-polymorphic local reached a runtime BackendIR value position"
      _ -> erasedRuntimeAt meta "out-of-scope universe-polymorphic local reached a runtime BackendIR value position"
  CGlobal g _ -> do
    meta <- metaAt
    globals <- asks lsGlobals
    ctx <- asks lsCtx
    if globalRuntimeErased globals ctx g
      then erasedRuntimeAt meta ("erased global reached a runtime BackendIR value position: " <> gKey g)
      else pure (BGlob meta g)
  CLit l -> BLit <$> metaAt <*> pure l
  CLamM mode ic q nm body -> do
    meta <- metaAt
    ctx <- asks lsCtx
    let mSite = lambdaExpectedSite ctx depth ic expected
        (declMode, declQ, borrowed, erased, provenance, mDom, mCod) = case mSite of
          Just site -> site
          Nothing -> (mode, q, False, q == Q0, if q == Q0 then Just ErasedByQuantity else Nothing, Nothing, Nothing)
    when (declMode /= mode) $
      recordLoweringViolation meta "E_PARAMETRIC_TYPE_PROMOTION"
        ("lambda observation mode disagrees with its expected classifier: " <> T.pack (show mode)
          <> " vs " <> T.pack (show declMode))
    if erased
      then do
        erasureMeta <- metaAt
        recordErasureAt depth erasureMeta ErasedLambdaSite ic nm (fromMaybe ErasedByQuantity provenance)
        lowerTermExpected mCod body (depth + 1) (ScopeSlot Nothing mDom Nothing : scopes)
      else do
        mb <- binderAtWith declQ borrowed (T.pack ("lambda " <> T.unpack nm))
        body' <- lowerTermExpected mCod body (depth + 1) (ScopeSlot (fmap bbBinderId mb) mDom Nothing : scopes)
        pure (BLam meta mb ic declQ nm body')
  CApp {} -> lowerApp expected term depth scopes
  CArithmeticProof _ -> BUnit <$> metaAt
  CSort {} -> metaAt >>= \meta -> erasedRuntimeAt meta "sort/type term reached a runtime BackendIR value position"
  CLevel {} -> metaAt >>= \meta -> erasedRuntimeAt meta "declaration universe identity reached a runtime BackendIR value position"
  CPiRuntimeM {} ->
    metaAt >>= \meta ->
      erasedRuntimeAt meta
        ( "function type reached a runtime BackendIR value position: "
            <> renderTerm term
        )
  CRecordTQ {} -> metaAt >>= \meta -> erasedRuntimeAt meta "record type reached a runtime BackendIR value position"
  CVariantT {} -> metaAt >>= \meta -> erasedRuntimeAt meta "variant type reached a runtime BackendIR value position"
  CSigT {} -> metaAt >>= \meta -> erasedRuntimeAt meta "signature type reached a runtime BackendIR value position"
  CMeta {} -> metaAt >>= \meta -> erasedRuntimeAt meta "unsolved compile-time meta reached a runtime BackendIR value position"
  CQuote {} -> metaAt >>= \meta -> erasedRuntimeAt meta "quoted syntax/proof term reached a runtime BackendIR value position"
  CCtorI g _universes ann arguments -> do
    meta <- metaAt
    lowerCtorTerm meta g ann
      [caTerm argument | argument <- arguments, caPayload argument]
      depth scopes
  CMatch s _ann _resultAnn alts -> do
    meta <- metaAt
    datas <- asks lsDatas
    ctors <- asks lsCtors
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    let scrutTy = termTypeAt globals traits ctx depth scopes s
    let scrutineeErased =
          maybe False (Repr.runtimeErasedParam ctx depth QW) scrutTy
            || erasedScopeVariable s scopes
    case erasedSingletonAlternative ctx datas ctors scrutineeErased scrutTy alts of
      Just alternative -> do
        let reason =
              fromMaybe ErasedProofOrTraitEvidence
                (scrutTy >>= erasureProvenanceForDomain ctx depth Ordinary QW)
        recordErasureAt depth meta ErasedMatchScrutineeSite Expl "match scrutinee" reason
        lowerErasedSingletonAlt scrutTy alternative depth scopes
      Nothing -> do
        s' <- lowerTerm s depth scopes
        alts' <- forM alts $ \a -> lowerAlt scrutTy a depth scopes
        pure (BMatch meta s' alts' (concatMap (patLayouts ctx ctors . caPat) alts))
  CRecordV fs -> do
    meta <- metaAt
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    let mRuntimeFields =
          case expected of
            Just ty -> runtimeRecordFieldNamesOfType globals traits ctx depth ty
            Nothing -> runtimeRecordFieldNames globals traits ctx depth scopes term
        expectedFieldType name =
          expected >>= recordFieldExpectedType globals traits ctx depth term name
    fs' <-
      fmap catMaybes $
        forM fs $ \(name, v) ->
          if recordFieldErased mRuntimeFields globals traits ctx depth scopes name v
            then do
              erasureMeta <- metaAt
              recordErasureAt depth erasureMeta ErasedRecordFieldSite Expl name
                ( fromMaybe ErasedOrdinaryTypeCode
                    ( (expected >>= recordFieldErasureProvenanceOfType ctx depth name)
                        <|> erasureProvenanceForTerm globals ctx v
                    )
                )
              pure Nothing
            else do
              v' <- lowerTermExpected (expectedFieldType name) v depth scopes
              pure (Just (name, v'))
    pure (BRecord meta fs')
  CProjM _ e f -> BProj <$> metaAt <*> lowerTerm e depth scopes <*> pure f <*> pure Nothing
  CProjAtM _ e f _i -> do
    meta <- metaAt
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    e' <- lowerTerm e depth scopes
    pure (BProj meta e' f (runtimeRecordFieldIndex globals traits ctx depth scopes e f))
  CInject tag e -> BInject <$> metaAt <*> pure tag <*> lowerTerm e depth scopes
  CLetRuntimeM mode q nm runtimeErasure ty rhs body -> do
    ctx <- asks lsCtx
    let tyV = evalTypeAt ctx depth ty
        runtimeErasureV = fmap (evalTypeAt ctx depth) runtimeErasure
        erasedByType = Repr.runtimeErasedPiParam ctx depth runtimeErasureV q tyV
    if erasedByType
      then do
        erasureMeta <- metaAt
        recordErasureAt depth erasureMeta ErasedLetSite Expl nm
          (fromMaybe ErasedByQuantity (erasureProvenanceForLocalDomain ctx depth mode q runtimeErasure tyV))
        lowerTerm body (depth + 1) (ScopeSlot Nothing (Just tyV) Nothing : scopes)
      else do
        meta <- metaAt
        mb <- binderAtWith q False (T.pack ("let " <> T.unpack nm))
        rhs' <- lowerTermExpected (Just tyV) rhs depth scopes
        body' <- lowerTerm body (depth + 1) (ScopeSlot (fmap bbBinderId mb) (Just tyV) Nothing : scopes)
        pure (BLet meta mb q nm rhs' body')
  CLetRecRuntimeM mode q nm runtimeErasure ty rhs body -> do
    ctx <- asks lsCtx
    let tyV = evalTypeAt ctx depth ty
        runtimeErasureV = fmap (evalTypeAt ctx depth) runtimeErasure
        erasedByType = Repr.runtimeErasedPiParam ctx depth runtimeErasureV q tyV
    if erasedByType
      then do
        erasureMeta <- metaAt
        recordErasureAt depth erasureMeta ErasedLetSite Expl nm
          (fromMaybe ErasedByQuantity (erasureProvenanceForLocalDomain ctx depth mode q runtimeErasure tyV))
        lowerTerm body (depth + 1) (ScopeSlot Nothing (Just tyV) Nothing : scopes)
      else do
        meta <- metaAt
        mb <- binderAtWith q False (T.pack ("letrec " <> T.unpack nm))
        let scopes' = ScopeSlot (fmap bbBinderId mb) (Just tyV) Nothing : scopes
        rhs' <- lowerTermExpected (Just tyV) rhs (depth + 1) scopes'
        body' <- lowerTerm body (depth + 1) scopes'
        pure (BLetRec meta mb q nm rhs' body')
  CLetPolyRuntimeM mode q nm telescope runtimeErasure ty rhs body -> do
    ctx <- asks lsCtx
    let tyV = evalTypeAt ctx depth ty
        runtimeErasureV = fmap (evalTypeAt ctx depth) runtimeErasure
        erasedByType = Repr.runtimeErasedPiParam ctx depth runtimeErasureV q tyV
    if erasedByType
      then do
        erasureMeta <- metaAt
        recordErasureAt depth erasureMeta ErasedLetSite Expl nm
          (fromMaybe ErasedByQuantity (erasureProvenanceForLocalDomain ctx depth mode q runtimeErasure tyV))
        lowerTerm body (depth + 1) (ScopeSlot Nothing (Just tyV) (Just telescope) : scopes)
      else do
        meta <- metaAt
        mb <- binderAtWith q False (T.pack ("let " <> T.unpack nm))
        rhs' <- lowerTermExpected (Just tyV) rhs depth scopes
        body' <- lowerTerm body (depth + 1)
          (ScopeSlot (fmap bbBinderId mb) (Just tyV) (Just telescope) : scopes)
        pure (BLet meta mb q nm rhs' body')
  CLetRecPolyRuntimeM mode q nm telescope runtimeErasure ty rhs body -> do
    ctx <- asks lsCtx
    let tyV = evalTypeAt ctx depth ty
        runtimeErasureV = fmap (evalTypeAt ctx depth) runtimeErasure
        erasedByType = Repr.runtimeErasedPiParam ctx depth runtimeErasureV q tyV
    if erasedByType
      then do
        erasureMeta <- metaAt
        recordErasureAt depth erasureMeta ErasedLetSite Expl nm
          (fromMaybe ErasedByQuantity (erasureProvenanceForLocalDomain ctx depth mode q runtimeErasure tyV))
        let scopes' = ScopeSlot Nothing (Just tyV) (Just telescope) : scopes
        lowerTerm body (depth + 1) scopes'
      else do
        meta <- metaAt
        mb <- binderAtWith q False (T.pack ("letrec " <> T.unpack nm))
        let scopes' = ScopeSlot (fmap bbBinderId mb) (Just tyV) (Just telescope) : scopes
        rhs' <- lowerTermExpected (Just tyV) rhs (depth + 1) scopes'
        body' <- lowerTerm body (depth + 1) scopes'
        pure (BLetRec meta mb q nm rhs' body')
  CLetRecGroupM telescope definitions body ->
    lowerLocalRecursiveGroup telescope definitions body depth scopes
  CDo lbl items -> BDo <$> metaAt <*> pure lbl <*> lowerItems items depth scopes
  CSealE labs e -> BSeal <$> metaAt <*> pure labs <*> lowerTerm e depth scopes
  CThunkE e _ -> BThunk <$> metaAt <*> lowerTerm e depth scopes
  CLazyE e _ -> BLazy <$> metaAt <*> lowerTerm e depth scopes
  CForceE e _ -> BForce <$> metaAt <*> lowerTerm e depth scopes
  CIf c t e ->
    BIf <$> metaAt
      <*> lowerTerm c depth scopes
      <*> lowerTerm t depth scopes
      <*> lowerTerm e depth scopes

lowerRuntimeLocalAlias :: BackendMeta -> ScopeStack -> RuntimeLocalAlias -> Lower BackendTerm
lowerRuntimeLocalAlias meta scopes RuntimeLocalAlias {rlaGroupBinder, rlaField} =
  case runtimeIndexForBinder rlaGroupBinder scopes of
    Just runtimeIndex -> do
      variableMeta <- metaAt
      pure (BProj meta (BVar variableMeta Nothing runtimeIndex) rlaField Nothing)
    Nothing ->
      erasedRuntimeAt meta "local recursive member refers to a missing runtime SCC environment binder"

runtimeIndexForBinder :: BackendBinderId -> ScopeStack -> Maybe Int
runtimeIndexForBinder target = go 0
  where
    go _ [] = Nothing
    go runtimeIndex (ScopeSlot (Just binder) _ _ : rest)
      | binder == target = Just runtimeIndex
      | otherwise = go (runtimeIndex + 1) rest
    go runtimeIndex (_ : rest) = go runtimeIndex rest

lowerLocalRecursiveGroup
  :: DeclarationUniverseTelescope
  -> [CoreLocalRecDef]
  -> Term
  -> Int
  -> ScopeStack
  -> Lower BackendTerm
lowerLocalRecursiveGroup telescope definitions body depth scopes = do
  ctx <- asks lsCtx
  let typedDefinitions =
        [ let ty = evalTypeAt ctx depth (clrdType definition)
              runtimeErasureV = fmap (evalTypeAt ctx depth) (clrdRuntimeErasure definition)
           in ( definition
              , ty
              , Repr.runtimeErasedPiParam ctx depth runtimeErasureV (clrdQuantity definition) ty
              )
        | definition <- definitions
        ]
      runtimeDefinitions =
        [ (definition, ty)
        | (definition, ty, erased) <- typedDefinitions
        , not erased
        ]
      runtimeNames = Set.fromList [clrdName definition | (definition, _) <- runtimeDefinitions]
      groupDepth = depth + length definitions
  forM_ typedDefinitions $ \(definition, ty, erased) ->
    when erased $ do
      erasureMeta <- metaAt
      recordErasureAt depth erasureMeta ErasedLetSite Expl (clrdName definition)
        ( fromMaybe ErasedByQuantity
            ( erasureProvenanceForLocalDomain ctx depth (clrdMode definition) (clrdQuantity definition)
                (clrdRuntimeErasure definition) ty
            )
        )
  case runtimeDefinitions of
    [] -> do
      let groupScopes =
            reverse
              [ ScopeSlotData Nothing (Just ty) (Just telescope) Nothing
              | (_, ty, _) <- typedDefinitions
              ]
              ++ scopes
      lowerTerm body groupDepth groupScopes
    _ -> do
      meta <- metaAt
      groupBinder <- binderAtWith QW False "local recursive SCC environment"
      case groupBinder of
        Nothing -> do
          recordLoweringViolation meta "E_BACKENDIR_BINDER_METADATA"
            "a runtime local recursive SCC did not receive a backend binder identity"
          lowerTerm body groupDepth
            (reverse [ScopeSlot Nothing (Just ty) (Just telescope) | (_, ty, _) <- typedDefinitions] ++ scopes)
        Just binder -> do
          let binderId = bbBinderId binder
              sourceSlots =
                [ ScopeSlotData
                    (if index == 0 then Just binderId else Nothing)
                    (Just ty)
                    (Just telescope)
                    ( if clrdName definition `Set.member` runtimeNames
                        then Just (RuntimeLocalAlias binderId (clrdName definition))
                        else Nothing
                    )
                | (index, (definition, ty, _)) <- zip [0 :: Int ..] (reverse typedDefinitions)
                ]
              groupScopes = sourceSlots ++ scopes
          fields <- forM runtimeDefinitions $ \(definition, ty) -> do
            rhs <- lowerTermExpected (Just ty) (clrdRhs definition) groupDepth groupScopes
            pure (clrdName definition, rhs)
          recordMeta <- metaAt
          body' <- lowerTerm body groupDepth groupScopes
          pure (BLetRec meta (Just binder) QW "__local_recursive_scc" (BRecord recordMeta fields) body')

lowerApp :: Maybe Value -> Term -> Int -> ScopeStack -> Lower BackendTerm
lowerApp expected term depth scopes = do
  meta <- metaAt
  globals <- asks lsGlobals
  traits <- asks lsTraits
  instances <- asks lsInstances
  runtimeErasedProofHeads <- asks lsRuntimeErasedProofHeads
  builtinIntegerLiteralDicts <- asks lsBuiltinIntegerLiteralDicts
  ctx <- asks lsCtx
  case selectedBuiltinIntegerLiteral builtinIntegerLiteralDicts term of
    Just literal -> pure (BLit meta (LitInt literal))
    Nothing -> case coreEtaCtorApp depth term of
      Just (g, _universes, ann, _k, picks) -> do
        lowerCtorTerm meta g ann
          [caTerm argument | (_, argument) <- picks, caPayload argument]
          depth
          scopes
      Nothing -> do
        let (hd, annotatedArgs) = spineOfTermWithErasure term
            args = [(icit, argument) | (icit, _, argument) <- annotatedArgs]
            selectedRuntimeErasures =
              [runtimeErasure | (_, runtimeErasure, _) <- annotatedArgs]
            k = length args
            actualIcs = map fst args
            expectedSites = appExpectedArgSites globals traits ctx depth scopes term
            localPlan = case hd of
              CGlob {} -> Nothing
              _ ->
                termTypeAt globals traits ctx depth scopes hd >>= \ty ->
                  Repr.argPlanSelectForArgsAt ctx depth ty actualIcs
            checkedErasurePlan = case hd of
              CGlob global ->
                Repr.erasedSpinePositionsForArgsMaybe globals ctx global actualIcs
              _ -> map fst <$> localPlan
            inferredFlags =
              applicationErasureFlags
                globals traits ctx depth scopes hd args localPlan
            flags =
              case checkedErasurePlan of
                Just checkedFlags -> checkedFlags
                Nothing ->
                  zipWith
                    (\selected inferred -> runtimeErasureSelected selected || inferred)
                    (selectedRuntimeErasures ++ repeat RuntimeRelevant)
                    (inferredFlags ++ repeat False)
            convs = case hd of
              CGlob g -> fromMaybe (replicate k Nothing) (Repr.argConvSelectGlobalForArgs ctx g actualIcs)
              _ -> maybe (replicate k Nothing) (map snd) localPlan
            aligned =
              [ (index, ic, erased, conv, expectedArg, a)
              | (index, (((ic, a), (erased, conv)), expectedArg)) <-
                  zip [0 :: Int ..] $
                  zip (zip args (zip (flags ++ repeat False) (convs ++ repeat Nothing))) (expectedSites ++ repeat Nothing)
              ]
            kept =
              [ (ic, conv, expectedArg, a)
              | (_, ic, erased, conv, expectedArg, a) <- aligned
              , not erased || isJust (runtimeReification a)
              ]
            runtimeReification argument =
              case hd of
                CGlobal intrinsic _
                  | intrinsic == prelHandleEff ->
                      checkedEffectLabelRuntimeToken globals ctx argument
                _ -> Nothing
            lowerGeneric = do
              forM_ aligned $ \(index, ic, erased, _, expectedSite, arg) ->
                when erased $ do
                  erasureMeta <- metaAt
                  let selectedProvenance =
                        case drop index selectedRuntimeErasures of
                          RuntimeErased justification : _ ->
                            Just (selectedErasureProvenance justification)
                          _ -> Nothing
                      provenance =
                        selectedProvenance
                          <|> (expectedSite >>= \(mode, expectedArg) -> erasureProvenanceForDomain ctx depth mode Q0 expectedArg)
                          <|> erasureProvenanceForTerm globals ctx arg
                  recordErasureAt depth erasureMeta ErasedApplicationArgumentSite ic
                    ("argument" <> T.pack (show index)) (fromMaybe ErasedByQuantity provenance)
              hd' <- lowerTerm hd depth scopes
              args' <-
                forM kept $ \(ic, conv, expectedSite, a) -> do
                  a' <- case runtimeReification a of
                    Just token -> BLit <$> metaAt <*> pure (LitStr token)
                    Nothing -> lowerTermExpected (snd <$> expectedSite) a depth scopes
                  pure (ic, conv, a')
              pure (BApp meta hd' args')
        case runtimeTransportApplication term of
          Nothing -> lowerGeneric
          Just transport ->
            let selectedProofErasure =
                  case drop (rtaProofIndex transport) selectedRuntimeErasures of
                    RuntimeErased justification : _ -> Just justification
                    _ -> Nothing
                proofErased =
                  proofTermIsRuntimeErased
                    globals
                    traits
                    instances
                    ctx
                    depth
                    scopes
                    runtimeErasedProofHeads
                    (rtaProof transport)
                    || isJust selectedProofErasure
                    || case [erased | (index, _, erased, _, _, _) <- aligned, index == rtaProofIndex transport] of
                      erased : _ -> erased
                      [] -> True
             in if proofErased
                  then do
                    forM_ selectedProofErasure $ \justification -> do
                      erasureMeta <- metaAt
                      recordErasureAt
                        depth
                        erasureMeta
                        ErasedApplicationArgumentSite
                        Expl
                        ("argument" <> T.pack (show (rtaProofIndex transport)))
                        (selectedErasureProvenance justification)
                    lowerTermExpected expected (rtaReduced transport) depth scopes
                  else if proofIsDefinitionallyRefl ctx depth (rtaProof transport)
                    then lowerTermExpected expected (rtaReduced transport) depth scopes
                    else do
                      recordLoweringViolationWith meta
                        "E_PROOF_RELEVANT_TRANSPORT_NOT_LOWERABLE"
                        ( "runtime-relevant " <> rtaEliminator transport
                            <> " uses an abstract equality proof with no computational path lowering rule"
                        )
                        [ ("eliminator", rtaEliminator transport)
                        , ("equalityProofArgument", renderTerm (rtaProof transport))
                        , ("proofArgumentRuntimeRelevant", "true")
                        , ("resultRuntimeRelevant", "true")
                        , ("reason", "proof is not definitionally refl and no computational path implementation is active")
                        , ("transportOrigin", "explicit eliminator application in finalized KCore")
                        , ("activeLanguageProfile", "kappa-v1")
                        , ("computationalPathFeatureGate", "none")
                        ]
                      -- The diagnostic prevents KBackendIR publication. Lowering
                      -- the representation-identical payload keeps recovery
                      -- total without pretending that abstract transport is
                      -- executable.
                      lowerTermExpected expected (rtaReduced transport) depth scopes
  where
    runtimeErasureSelected = \case
      RuntimeRelevant -> False
      RuntimeErased _ -> True

    selectedErasureProvenance (RuntimeErasedEvidence goal evidence classifier) =
      ErasedBySelectedEvidence goal evidence classifier

selectedBuiltinIntegerLiteral :: Set GName -> Term -> Maybe Integer
selectedBuiltinIntegerLiteral dictionaries term =
  case spineOfTerm term of
    (CProjM Ordinary dictionary "fromInteger", [(Expl, CLit (LitInt literal))])
      | Just selectedDictionary <- coreHeadGlobal dictionary
      , selectedDictionary `Set.member` dictionaries ->
          Just literal
    _ -> Nothing

data RuntimeTransportApplication = RuntimeTransportApplication
  { rtaEliminator :: !Text
  , rtaProofIndex :: !Int
  , rtaProof :: !Term
  , rtaReduced :: !Term
  }

-- | Recognize only the resolved standard eliminator identities. The argument
-- positions are part of their checked §11.4.1 source declarations; surface
-- spelling and arbitrary functions named @subst@/@pathInd@ are irrelevant.
runtimeTransportApplication :: Term -> Maybe RuntimeTransportApplication
runtimeTransportApplication term =
  let (headTerm, arguments) = spineOfTerm term
      applyRest consumed base =
        foldl (\function (icit, argument) -> CApp icit function argument)
          base (drop consumed arguments)
      terms = map snd arguments
   in case headTerm of
        CGlobal eliminator _
          | eliminator == prelSubst
          , length arguments >= 6 ->
              Just RuntimeTransportApplication
                { rtaEliminator = "subst"
                , rtaProofIndex = 4
                , rtaProof = terms !! 4
                , rtaReduced = applyRest 6 (terms !! 5)
                }
          | eliminator == prelPathInd
          , length arguments >= 6 ->
              Just RuntimeTransportApplication
                { rtaEliminator = "pathInd"
                , rtaProofIndex = 5
                , rtaProof = terms !! 5
                , rtaReduced = applyRest 6 (terms !! 3)
                }
        _ -> Nothing

proofIsDefinitionallyRefl :: EvalCtx -> Int -> Term -> Bool
proofIsDefinitionallyRefl ctx depth proof =
  case force ctx (eval ctx (rigidEnv depth) proof) of
    VCtor constructor _ -> constructor == prelRefl
    _ -> False

-- | A checked trait-member layout records quantity zero only after the
-- member's complete result has been proved RuntimeErased. Member accessors
-- have stable semantic global identities, so an application headed by one of
-- those accessors is an erased proof producer even when the generic
-- eliminator telescope cannot recover the selected IsSet evidence from the
-- equality type alone.
proofTermIsRuntimeErased
  :: Map GName GlobalDef
  -> Map GName TraitInfo
  -> [InstanceEntry]
  -> EvalCtx
  -> Int
  -> ScopeStack
  -> Set GName
  -> Term
  -> Bool
proofTermIsRuntimeErased globals traits instances ctx depth scopes runtimeErasedHeads proof =
  go proof
  where
    go candidate =
      erasedScopeVariable candidate scopes
        || proofHeadIsRuntimeErased runtimeErasedHeads candidate
        || projectedTraitMemberIsRuntimeErased candidate
        || proofTypeIsRuntimeErased candidate
        || proofCombinatorHasOnlyErasedEvidence candidate
        -- Erasure demand propagates through the exact checked equality
        -- eliminators. If their payload is already runtime-erased, using the
        -- transported result in an erased proof slot makes the nested
        -- transport erased as well; its abstract equality witness is not a
        -- runtime dependency (§11.4.1, §31.2).
        || maybe False (go . rtaReduced) (runtimeTransportApplication candidate)

    -- The standard equality combinators do not manufacture a runtime path:
    -- they only rearrange already-checked equality evidence. Their result is
    -- therefore runtime-erased exactly when every proof input is independently
    -- runtime-erased. This is deliberately recursive rather than a head-only
    -- classification: @sym p@ for an abstract runtime proof remains
    -- proof-relevant and is rejected by the transport lowerability gate.
    proofCombinatorHasOnlyErasedEvidence candidate =
      let (headTerm, arguments) = spineOfTerm candidate
          explicit = [argument | (Expl, argument) <- arguments]
          evidenceInputs =
            case coreHeadGlobal headTerm of
              Just global
                | global == gPrel "sym" ->
                    takeLast 1 explicit
                | global == gPrel "trans" ->
                    takeLast 2 explicit
              _ -> []
       in not (null evidenceInputs) && all go evidenceInputs

    takeLast count values =
      drop (max 0 (length values - count)) values

    projectedTraitMemberIsRuntimeErased candidate =
      case projectionHead candidate of
        Just (receiver, field) ->
          case force ctx <$> termTypeAt globals traits ctx depth scopes receiver of
            Just (VGlobN trait _) ->
              maybe False
                ((== Just Q0) . Map.lookup field . tiMemberQs)
                (Map.lookup trait traits)
            _ -> False
        Nothing -> False

    -- Runtime erasure is a judgment on the proof's checked type, not on the
    -- spelling of its producer. For equality, §11.1.6/§11.4.1 derives that
    -- judgment from semantic IsSet evidence for the homogeneous carrier.
    -- Current-scope evidence is followed through declared supertraits; an
    -- exact closed instance is also sufficient. Anything requiring fresh
    -- instance variables or unresolved premises remains runtime-relevant and
    -- therefore fails closed at the transport lowerability gate.
    proofTypeIsRuntimeErased candidate =
      case force ctx <$> termTypeAt globals traits ctx depth scopes candidate of
        Just proofType ->
          maybe
            False
            (\(carrier, _, _) -> carrierHasIsSetEvidence carrier)
            (canonicalEqualityPayload ctx proofType)
        Nothing -> False

    carrierHasIsSetEvidence carrier =
      any
        (maybe False (evidenceEntailsIsSet Set.empty carrier) . scopeSlotType)
        scopes
        || any (closedIsSetInstance carrier) instances

    evidenceEntailsIsSet seen carrier evidenceType =
      case force ctx evidenceType of
        VGlobI trait _ spine ->
          maybe False
            (traitApplicationEntailsIsSet seen carrier trait . map snd)
            (traitSemanticSpine globals traits ctx trait spine)
        VGlobN trait spine ->
          maybe False
            (traitApplicationEntailsIsSet seen carrier trait . map snd)
            (traitSemanticSpine globals traits ctx trait spine)
        _ -> False

    traitApplicationEntailsIsSet seen carrier trait arguments
      | trait `Set.member` seen = False
      | otherwise =
          case Map.lookup trait traits of
            Nothing -> False
            Just info ->
              let semanticArguments = arguments
                  direct =
                    trait == prelIsSet
                      && case semanticArguments of
                        [candidate] ->
                          convertible ctx depth (force ctx candidate) (force ctx carrier)
                        _ -> False
                  inherited =
                    any
                      ( maybe False
                          (evidenceEntailsIsSet (Set.insert trait seen) carrier)
                          . traitSuperType ctx semanticArguments
                          . snd
                      )
                      (tiSupers info)
               in length semanticArguments == tiParamCount info
                    && (direct || inherited)

    closedIsSetInstance carrier entry
      | ieTrait entry /= prelIsSet
          || ieTeleLen entry /= 0
          || not (null (iePremises entry)) =
          False
      | otherwise =
          case ieHead entry of
            [headTerm] ->
              convertible
                ctx
                depth
                (force ctx (eval ctx [] headTerm))
                (force ctx carrier)
            _ -> False

    projectionHead candidate =
      case fst (spineOfTerm (stripWrappers candidate)) of
        CProjM _ receiver field -> Just (receiver, field)
        CProjAtM _ receiver field _ -> Just (receiver, field)
        _ -> Nothing

    stripWrappers = \case
      CUniverseLift _ _ _ inner -> stripWrappers inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> stripWrappers inner
      inner -> inner

-- The projection case above is intentionally tied to both the resolved
-- receiver trait identity and its finalized member layout. A field spelling
-- by itself is not erasure authority.
proofHeadIsRuntimeErased :: Set GName -> Term -> Bool
proofHeadIsRuntimeErased runtimeErasedHeads = \case
  -- Arithmetic certificates are independently checked proof-only KCore
  -- nodes and lower directly to BUnit. Treating one as a runtime equality
  -- object would contradict both that representation and §15.8.7.
  CArithmeticProof _ -> True
  proof ->
    maybe False (`Set.member` runtimeErasedHeads) (coreHeadGlobal proof)

-- | Runtime effect nodes carry a token derived from a checked static effect
-- label identity. The source value itself remains compile-time-only: only an
-- exact global of type 'EffLabel' whose finalized Core body is the compiler-
-- issued literal token can cross this intrinsic ABI boundary.
checkedEffectLabelRuntimeToken :: Map GName GlobalDef -> EvalCtx -> Term -> Maybe Text
checkedEffectLabelRuntimeToken globals ctx = \case
  CGlobal label _ -> do
    definition <- Map.lookup label globals
    case force ctx (gdType definition) of
      VGlobN classifier _ | classifier == prelEffLabel -> pure ()
      _ -> Nothing
    case gdCoreBody definition of
      Just (CLit (LitStr token)) -> Just token
      _ -> Nothing
  _ -> Nothing

lowerCtorTerm :: BackendMeta -> GName -> Maybe Term -> [Term] -> Int -> ScopeStack -> Lower BackendTerm
lowerCtorTerm meta g ann args depth scopes
  | g == prelEffOp =
      lowerEffectOperation meta ann args depth scopes
lowerCtorTerm meta g _ [] _ _
  | g == prelNatZero =
      pure (BLit meta (LitInt 0))
lowerCtorTerm _ g _ [predecessor] depth scopes
  | g == prelNatSucc =
      -- The source/KCore constructor remains authoritative. Runtime IR uses
      -- the exact natural representation and therefore computes Succ with
      -- the resolved integer primitive rather than allocating a unary cell.
      lowerTerm
        ( CApp Expl
            (CApp Expl (CGlob (gPrel "addInt")) predecessor)
            (CLit (LitInt 1))
        )
        depth
        scopes
lowerCtorTerm meta g ann args depth scopes = do
  ctx <- asks lsCtx
  ctors <- asks lsCtors
  let mCi = Map.lookup g ctors
      sourceFacts =
        case mCi of
          Nothing -> []
          Just ci -> explicitCtorFieldRuntimeFacts ctx (length (ciFields ci)) (eval ctx [] (ciType ci))
      coreFacts =
        case mCi of
          Nothing ->
            case ann of
              Just constructorType
                | termScopedAt depth constructorType ->
                    coreCtorPayloadRuntimeFactsAt depth ctx (evalTypeAt ctx depth constructorType)
              _ -> []
          Just ci -> coreCtorPayloadRuntimeFacts ctx (eval ctx [] (ciType ci))
      sourceShape = maybe False (\ci -> length args == length (ciFields ci)) mCi
      coreShape = not (null coreFacts) && length args == length coreFacts
      selectedFacts
        | coreShape = coreFacts
        | sourceShape = sourceFacts
        | otherwise = replicate (length args) (True, Nothing, Nothing)
      aligned = zip3 [0 :: Int ..] args selectedFacts
      kept = [(fieldTy, arg) | (_, arg, (True, fieldTy, _)) <- aligned]
      annInfo = Repr.ctorLayoutOfAt ctx depth ann
      ctorInfo = Repr.ctorLayoutOf ctx (ciType <$> mCi)
      info = selectCtorLayoutInfo (length kept) annInfo ctorInfo
  globals <- asks lsGlobals
  forM_ aligned $ \(index, arg, (runtime, fieldTy, recordedProvenance)) ->
    unless runtime $ do
      erasureMeta <- metaAt
      let provenance =
            erasureProvenanceForTerm globals ctx arg
              <|> recordedProvenance
      recordErasureAt depth erasureMeta ErasedConstructorFieldSite Expl
        ("field" <> T.pack (show index)) (fromMaybe ErasedByQuantity provenance)
  args' <- forM kept $ \(expectedField, arg) ->
    lowerTermExpected expectedField arg depth scopes
  pure (BCtor meta (BackendCtorLayout g info (length args')) args')

-- | '__EffOp' is a compiler-owned runtime node. Its label field is a reified
-- token derived from static identity, while every other field follows the
-- occurrence-local checked constructor telescope. This keeps general
-- 'EffLabel' values erased without changing the runtime's four-field node ABI.
lowerEffectOperation :: BackendMeta -> Maybe Term -> [Term] -> Int -> ScopeStack -> Lower BackendTerm
lowerEffectOperation meta annotation arguments depth scopes = do
  globals <- asks lsGlobals
  ctx <- asks lsCtx
  let facts =
        case annotation of
          Just constructorType
            | termScopedAt depth constructorType ->
                coreCtorPayloadRuntimeFactsAt depth ctx (evalTypeAt ctx depth constructorType)
          _ -> []
      aligned =
        zip3
          [0 :: Int ..]
          arguments
          (facts ++ repeat (True, Nothing, Nothing))
      labelTokens =
        [ (index, token)
        | (index, argument, _) <- aligned
        , token <- maybeToList (checkedEffectLabelRuntimeToken globals ctx argument)
        ]
  if length arguments /= 4 || length labelTokens /= 1
    then
      loweringViolation
        meta
        "E_BACKENDIR_EFFECT_LABEL_REIFICATION"
        "effect operation runtime node requires exactly one checked static label identity and four checked fields"
    else do
      lowered <- forM aligned $ \(index, argument, (_, expectedField, _)) ->
        case lookup index labelTokens of
          Just token -> do
            erasureMeta <- metaAt
            recordErasureAt
              depth
              erasureMeta
              ErasedConstructorFieldSite
              Expl
              ("field" <> T.pack (show index))
              ErasedIntrinsicCompileTimeValue
            BLit <$> metaAt <*> pure (LitStr token)
          Nothing -> lowerTermExpected expectedField argument depth scopes
      let fieldRepresentations = replicate 4 Repr.RepBoxed
          layoutInfo =
            CtorLayoutInfo
              { clArity = 4
              , clLayoutClass = Repr.LayoutBoxed
              , clBoxedFootprintBytes = Just (Repr.ctorBoxedFootprintBytes 4)
              , clFieldReps = fieldRepresentations
              }
      pure
        ( BCtor
            meta
            (BackendCtorLayout prelEffOp (Just layoutInfo) 4)
            lowered
        )

selectCtorLayoutInfo :: Int -> Maybe CtorLayoutInfo -> Maybe CtorLayoutInfo -> Maybe CtorLayoutInfo
selectCtorLayoutInfo runtimeFields annInfo ctorInfo =
  case annInfo of
    Just info | clArity info == runtimeFields -> Just info
    _ ->
      case ctorInfo of
        Just info | clArity info == runtimeFields -> Just info
        _ ->
          case annInfo of
            Just info -> Just info
            Nothing -> ctorInfo

sourceArgErased :: Map GName GlobalDef -> EvalCtx -> Term -> Bool
sourceArgErased globals ctx = \case
  CSort {} -> True
  CPi {} -> True
  CRecordT {} -> True
  CVariantT {} -> True
  CSigT {} -> True
  CMeta {} -> True
  CQuote {} -> True
  CUniverseLift _ _ _ inner -> sourceArgErased globals ctx inner
  CSchemaLift _ _ _ _ _ _ _ _ inner -> sourceArgErased globals ctx inner
  CSealE _ e -> sourceArgErased globals ctx e
  CApp _ f _ -> sourceArgErased globals ctx f
  CGlob g ->
    Repr.resultIsProofGlobal globals ctx g
      || maybe False (globalResultIsCompileTimeOnly ctx . gdType) (Map.lookup g globals)
  _ -> False

-- | Runtime erasure for an application argument has two independent checked
-- authorities.  The callee telescope proves which parameter positions are
-- erased; the argument term itself can prove that it is a type, kind, erased
-- local, or proof value.  Trait-member projections and other dependent heads
-- can temporarily lack a reconstructible telescope during final lowering, so
-- defaulting solely from that missing plan would reintroduce static terms at
-- runtime.  The term judgment is one-way and conservative: it can erase a
-- statically classified argument, but it never turns an ordinary argument
-- into an erased one based on spelling.
applicationErasureFlags
  :: Map GName GlobalDef
  -> Map GName TraitInfo
  -> EvalCtx
  -> Int
  -> ScopeStack
  -> Term
  -> [(Icit, Term)]
  -> Maybe [(Bool, Maybe ArgConv)]
  -> [Bool]
applicationErasureFlags globals traits ctx depth scopes headTerm arguments localPlan =
  case headTerm of
    CGlob global
      | Just flags <- Repr.erasedSpinePositionsForArgsMaybe globals ctx global actualIcs ->
          flags
    _
      | Just plan <- localPlan -> map fst plan ++ repeat False
      | otherwise -> termFlags
  where
    actualIcs = map fst arguments
    termFlags =
      map
        (sourceTermErased globals traits ctx depth scopes . snd)
        arguments

sourceTermErased :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Bool
sourceTermErased globals traits ctx depth scopes = \case
  CVar i -> case drop i scopes of
    ScopeSlot Nothing _ _ : _ -> True
    _ -> False
  CLocal i _ -> case drop i scopes of
    ScopeSlot Nothing _ _ : _ -> True
    _ -> False
  CUniverseLift _ _ _ inner ->
    sourceTermErased globals traits ctx depth scopes inner
  CSchemaLift _ _ _ _ _ _ _ _ inner ->
    sourceTermErased globals traits ctx depth scopes inner
  CSealE _ e -> sourceTermErased globals traits ctx depth scopes e
  CLam _ q _ body ->
    let mb = if q == Q0 then Nothing else Just (BackendBinderId (-1))
     in sourceTermErased globals traits ctx (depth + 1) (ScopeSlot mb Nothing Nothing : scopes) body
  CLetRuntimeM _ quantity _ runtimeErasure ty rhs body ->
    let tyV = evalTypeAt ctx depth ty
        runtimeErasureV = fmap (evalTypeAt ctx depth) runtimeErasure
        binder = if Repr.runtimeErasedPiParam ctx depth runtimeErasureV quantity tyV then Nothing else Just (BackendBinderId (-1))
     in sourceTermErased globals traits ctx depth scopes rhs
          && sourceTermErased globals traits ctx (depth + 1) (ScopeSlot binder (Just tyV) Nothing : scopes) body
  CLetRecRuntimeM _ quantity _ runtimeErasure ty rhs body ->
    let tyV = evalTypeAt ctx depth ty
        runtimeErasureV = fmap (evalTypeAt ctx depth) runtimeErasure
        binder = if Repr.runtimeErasedPiParam ctx depth runtimeErasureV quantity tyV then Nothing else Just (BackendBinderId (-1))
        scopes' = ScopeSlot binder (Just tyV) Nothing : scopes
     in sourceTermErased globals traits ctx (depth + 1) scopes' rhs
          && sourceTermErased globals traits ctx (depth + 1) scopes' body
  CLetPolyRuntimeM _ quantity _ telescope runtimeErasure ty rhs body ->
    let tyV = evalTypeAt ctx depth ty
        runtimeErasureV = fmap (evalTypeAt ctx depth) runtimeErasure
        binder = if Repr.runtimeErasedPiParam ctx depth runtimeErasureV quantity tyV then Nothing else Just (BackendBinderId (-1))
     in sourceTermErased globals traits ctx depth scopes rhs
          && sourceTermErased globals traits ctx (depth + 1)
            (ScopeSlot binder (Just tyV) (Just telescope) : scopes) body
  CLetRecPolyRuntimeM _ quantity _ telescope runtimeErasure ty rhs body ->
    let tyV = evalTypeAt ctx depth ty
        runtimeErasureV = fmap (evalTypeAt ctx depth) runtimeErasure
        binder = if Repr.runtimeErasedPiParam ctx depth runtimeErasureV quantity tyV then Nothing else Just (BackendBinderId (-1))
        scopes' = ScopeSlot binder (Just tyV) (Just telescope) : scopes
     in sourceTermErased globals traits ctx (depth + 1) scopes' rhs
          && sourceTermErased globals traits ctx (depth + 1) scopes' body
  CLetRecGroupM telescope definitions body ->
    let count = length definitions
        slots =
          reverse
            [ let ty = evalTypeAt ctx depth (clrdType definition)
                  runtimeErasureV = fmap (evalTypeAt ctx depth) (clrdRuntimeErasure definition)
                  binder = if Repr.runtimeErasedPiParam ctx depth runtimeErasureV (clrdQuantity definition) ty then Nothing else Just (BackendBinderId (-1))
               in ScopeSlot binder (Just ty) (Just telescope)
            | definition <- definitions
            ]
              ++ scopes
        groupDepth = depth + count
     in all (\definition -> sourceTermErased globals traits ctx groupDepth slots (clrdRhs definition)) definitions
          && sourceTermErased globals traits ctx groupDepth slots body
  t@CApp {} ->
    sourceArgErased globals ctx t
      || sourceProofApplicationErased globals traits ctx depth scopes t
  t -> sourceArgErased globals ctx t

sourceProofApplicationErased :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Bool
sourceProofApplicationErased globals traits ctx depth scopes term =
  case termTypeAt globals traits ctx depth scopes term of
    Just ty | Repr.resultIsProofBodyValue ctx depth ty || sourceProofHeadErased hd ->
      let (headTerm, args) = spineOfTerm term
          actualIcs = map fst args
          localPlan = case headTerm of
            CGlob {} -> Nothing
            _ ->
              termTypeAt globals traits ctx depth scopes headTerm >>= \tyH ->
                Repr.argPlanSelectForArgsAt ctx depth tyH actualIcs
          flags =
            applicationErasureFlags
              globals traits ctx depth scopes headTerm args localPlan
          runtimeArgs =
            [ a
            | ((_, a), erased) <- zip args (flags ++ repeat False)
            , not erased
            ]
       in not (null runtimeArgs)
            && all (sourceTermErased globals traits ctx depth scopes) runtimeArgs
    _ -> False
  where
    (hd, _argsForHead) = spineOfTerm term
    sourceProofHeadErased = \case
      CGlob g -> Repr.resultIsProofBodyGlobal globals ctx g
      CSealE _ e -> sourceProofHeadErased e
      _ -> False

erasureProvenanceForTerm :: Map GName GlobalDef -> EvalCtx -> Term -> Maybe ErasureProvenance
erasureProvenanceForTerm globals ctx = \case
  CGlobal g _
    | Just def <- Map.lookup g globals
    , gdObservationMode def == Parametric -> case force ctx (gdType def) of
        VSort level -> Just (ErasedParametricTypeWitness level)
        _ -> Just ErasedParametricTypeFormer
  CProjM Parametric _ _ -> Just ErasedParametricTypeFormer
  CProjAtM Parametric _ _ _ -> Just ErasedParametricTypeFormer
  CSort _ -> Just ErasedOrdinaryTypeCode
  term
    | (CGlob headG, _) <- spineOfTerm term
    , Repr.resultIsProofBodyGlobal globals ctx headG -> Just ErasedProofOrTraitEvidence
  _ -> Nothing

globalRuntimeErased :: Map GName GlobalDef -> EvalCtx -> GName -> Bool
globalRuntimeErased globals ctx g =
  Repr.resultIsProofGlobal globals ctx g
    || maybe False (globalResultIsCompileTimeOnly ctx . gdType) (Map.lookup g globals)

lambdaExpectedSite :: EvalCtx -> Int -> Icit -> Maybe Value -> Maybe (ObservationMode, Q, Bool, Bool, Maybe ErasureProvenance, Maybe Value, Maybe Value)
lambdaExpectedSite ctx depth actualIc expected = do
  ty <- expected
  case force ctx ty of
    VPiRuntimeM mode _ ic q borrowed _ _ _ runtimeErasure dom (Closure env cod)
      | ic == actualIc ->
          let domV = force ctx dom
              codV = eval ctx (VRigid depth [] : env) cod
           in Just
                ( mode
                , q
                , borrowed
                , Repr.runtimeErasedPiParam ctx depth runtimeErasure q domV
                , erasureProvenanceForPiDomain ctx depth mode q runtimeErasure domV
                , Just domV
                , Just codV
                )
    _ -> Nothing

recordFieldErased :: Maybe (Set Text) -> Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Text -> Term -> Bool
recordFieldErased mRuntimeFields globals traits ctx depth scopes name value =
  case mRuntimeFields of
    Just runtimeFields ->
      name `Set.notMember` runtimeFields
        || sourceTermErased globals traits ctx depth scopes value
    Nothing -> sourceTermErased globals traits ctx depth scopes value

termTypeAt :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Maybe Value
termTypeAt globals traits ctx depth scopes = go
  where
    go term
      | Just (_, _, Just constructorType, _, pickedArguments) <- coreEtaCtorApp depth term =
          applyArgs
            (evalTypeAt ctx depth constructorType)
            [(caIcit argument, caTerm argument) | (_, argument) <- pickedArguments]
      | otherwise = goRegular term

    goRegular = \case
      CGlobal g universes ->
        (Map.lookup g globals >>= specializeGlobalDefinitionType ctx universes)
          <|> Repr.argConvGlobalType ctx g
      CVar i -> scopeSlotType =<< indexMaybeLocal i scopes
      CLocal i universes -> do
        slot <- indexMaybeLocal i scopes
        ty <- scopeSlotType slot
        telescope <- scopeSlotUniverses slot
        if length universes == dutParameterCount telescope
          then Just (specializeLocalType telescope universes ty)
          else Nothing
      CProj e field -> projectionFieldType globals traits ctx depth scopes e field =<< go e
      CProjAt e field _ -> projectionFieldType globals traits ctx depth scopes e field =<< go e
      CSealE _ e -> go e
      CIf _ t f -> sameType (go t) (go f)
      CMatch _ _ resultAnn _ -> evalTypeAt ctx depth <$> resultAnn
      CCtorI _ _ (Just constructorType) arguments ->
        applyArgs
          (evalTypeAt ctx depth constructorType)
          [(caIcit argument, caTerm argument) | argument <- arguments]
      t@CApp {} ->
        let (h, args) = spineOfTerm t
         in go h >>= \ty -> applyArgs ty args
      _ -> Nothing

    applyArgs ty [] = Just ty
    applyArgs ty ((ic, arg) : rest) =
      case force ctx ty of
        VPi pic _ _ _ _ (Closure env cod)
          | ic == pic ->
              let argV = eval ctx (rigidEnv depth) arg
               in applyArgs (eval ctx (argV : env) cod) rest
        _ -> Nothing

    sameType (Just a) (Just b)
      | convertible ctx depth (force ctx a) (force ctx b) =
          Just a
    sameType _ _ = Nothing

    specializeLocalType telescope universes generalizedType =
      let raw = quote (ctx {ecFacts = Map.empty}) depth generalizedType
          specialized =
            zonkTermWith (\_ _ -> Nothing)
              (instantiateLocalLevelParams (dutParameterCount telescope) universes)
              0 raw
       in eval ctx (rigidEnv depth) specialized

appExpectedArgSites :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> [Maybe (ObservationMode, Value)]
appExpectedArgSites globals traits ctx depth scopes appTerm =
  case spineOfTerm appTerm of
    (hd, args) ->
      case termTypeAt globals traits ctx depth scopes hd of
        Nothing -> replicate (length args) Nothing
        Just ty0 -> walk ty0 args
  where
    walk _ [] = []
    walk ty ((ic, arg) : rest) =
      case force ctx ty of
        VPiM mode pic _ _ _ dom (Closure env cod)
          | ic == pic ->
              let argV = eval ctx (rigidEnv depth) arg
               in Just (mode, dom) : walk (eval ctx (argV : env) cod) rest
        _ -> replicate (1 + length rest) Nothing

projectionFieldType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Text -> Value -> Maybe Value
projectionFieldType globals traits ctx depth scopes recvTerm field recvTy =
  case force ctx recvTy of
    VRecordT fs -> lookup field fs
    VSigT _ inner -> projectionFieldType globals traits ctx depth scopes recvTerm field inner
    VGlobI traitG universes spine
      | Just ti <- Map.lookup traitG traits -> do
          semanticSpine <- traitSemanticSpine globals traits ctx traitG spine
          traitProjectionType globals traits ctx depth scopes traitG universes
            (map snd semanticSpine) recvTerm field ti
    _ -> Nothing

traitProjectionType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> GName -> [Level] -> [Value] -> Term -> Text -> TraitInfo -> Maybe Value
traitProjectionType globals _traits ctx depth scopes traitG universes args recvTerm field ti
  | field `elem` tiMembers ti =
      traitMemberType globals ctx depth scopes (tiParamCount ti) traitG universes field args recvTerm
  | Just supClosed <- lookup field (tiSupers ti) =
      traitSuperType ctx args supClosed
  | otherwise =
      Nothing
traitMemberType :: Map GName GlobalDef -> EvalCtx -> Int -> ScopeStack -> Int -> GName -> [Level] -> Text -> [Value] -> Term -> Maybe Value
traitMemberType globals ctx depth _scopes parameterCount traitG universes member args dictTm = do
  gd <- Map.lookup (traitMemberGlobal traitG member) globals
  memberType <- specializeGlobalDefinitionTypePrefix ctx universes gd
  let memberTypeTerm = quote ctx depth memberType
      argumentTerms = map (quote ctx depth) args
  projectedTypeTerm <-
    specializeTraitMemberProjectionType
      depth
      parameterCount
      argumentTerms
      dictTm
      memberTypeTerm
  pure (eval ctx (rigidEnv depth) projectedTypeTerm)

traitMemberStorageType
  :: Map GName GlobalDef
  -> EvalCtx
  -> Int
  -> Int
  -> GName
  -> [Level]
  -> Text
  -> [Value]
  -> Term
  -> Maybe Value
traitMemberStorageType globals ctx depth parameterCount traitG universes member args dictTm = do
  gd <- Map.lookup (traitMemberGlobal traitG member) globals
  memberType <- specializeGlobalDefinitionTypePrefix ctx universes gd
  storageType <-
    specializeTraitMemberStorageType
      depth
      parameterCount
      (map (quote ctx depth) args)
      dictTm
      (quote ctx depth memberType)
  pure (eval ctx (rigidEnv depth) storageType)

specializeGlobalDefinitionType :: EvalCtx -> [Level] -> GlobalDef -> Maybe Value
specializeGlobalDefinitionType ctx universes definition
  | length universes /= dutParameterCount (gdUniverses definition) = Nothing
  | null universes = Just (gdType definition)
  | otherwise =
      let raw = quote (ctx {ecFacts = Map.empty}) 0 (gdType definition)
          specialized = zonkTermWith (\_ _ -> Nothing) (substituteLevelParams universes) 0 raw
       in Just (eval ctx [] specialized)

specializeConstructorType :: EvalCtx -> Maybe [Level] -> CtorInfo -> Maybe Value
specializeConstructorType ctx selectedUniverses info =
  case selectedUniverses of
    Nothing -> Just (eval ctx [] (ciType info))
    Just universes ->
      let telescope = ciUniverses info
          rawType = ciType info
          provisionalMetas = nub (levelMetasOfTerm rawType)
          provisionalParameterArity = case levelParamsOfTerm rawType of
            [] -> 0
            parameters -> 1 + maximum parameters
          specialize substitution =
            Just (eval ctx [] (zonkTermWith (\_ _ -> Nothing) substitution 0 rawType))
       in if dutParameterCount telescope > 0
            then
              if length universes == dutParameterCount telescope
                then specialize (substituteLevelParams universes)
                else Nothing
            else
              if not (null provisionalMetas) && length universes == length provisionalMetas
                then specialize
                  (substituteLevelMetas (Map.fromList (zip provisionalMetas universes)))
                else if null provisionalMetas && length universes == provisionalParameterArity
                  then specialize (substituteLevelParams universes)
                  else Nothing

traitSuperType :: EvalCtx -> [Value] -> Term -> Maybe Value
traitSuperType ctx args superClosed =
  applyExpl (eval ctx [] superClosed) args
  where
    applyExpl v [] = Just (force ctx v)
    applyExpl v (a : as) =
      case force ctx v of
        VLam Expl _ _ (Closure env body) ->
          applyExpl (eval ctx (a : env) body) as
        _ -> Nothing

runtimeRecordFieldIndex :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Text -> Maybe Int
runtimeRecordFieldIndex globals traits ctx depth scopes recordTerm field =
  termTypeAt globals traits ctx depth scopes recordTerm >>= runtimeRecordFieldIndexOfType globals traits ctx depth field

runtimeRecordFieldIndexOfType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> Text -> Value -> Maybe Int
runtimeRecordFieldIndexOfType globals traits ctx depth field ty =
  runtimeRecordFieldOrderOfType globals traits ctx depth ty >>= elemIndex field

runtimeRecordFieldNames :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Maybe (Set Text)
runtimeRecordFieldNames globals traits ctx depth scopes recordTerm =
  termTypeAt globals traits ctx depth scopes recordTerm >>= runtimeRecordFieldNamesOfType globals traits ctx depth

runtimeRecordFieldNamesOfType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> Value -> Maybe (Set Text)
runtimeRecordFieldNamesOfType globals traits ctx depth ty =
  Set.fromList <$> runtimeRecordFieldOrderOfType globals traits ctx depth ty

recordFieldExpectedType
  :: Map GName GlobalDef
  -> Map GName TraitInfo
  -> EvalCtx
  -> Int
  -> Term
  -> Text
  -> Value
  -> Maybe Value
recordFieldExpectedType globals traits ctx depth dictionaryTerm fieldName expected =
  case force ctx expected of
    VRecordTQ fields -> rfType <$> find ((== fieldName) . rfName) fields
    VGlobI traitG universes spine -> do
      trait <- Map.lookup traitG traits
      guard (fieldName `elem` tiMembers trait || isJust (lookup fieldName (tiSupers trait)))
      semanticSpine <- traitSemanticSpine globals traits ctx traitG spine
      traitMemberStorageType globals ctx depth
        (tiParamCount trait) traitG universes fieldName
        (map snd semanticSpine) dictionaryTerm
    _ -> Nothing

-- | Recover a trait's source parameters from finalized Core. The backend is
-- a trust boundary: generated declaration proofs must be physically present
-- with the exact prefix authorized by the checked declaration telescope.
-- Source implicit arguments are never classified by spelling or shape.
traitSemanticSpine
  :: Map GName GlobalDef
  -> Map GName TraitInfo
  -> EvalCtx
  -> GName
  -> [(Icit, argument)]
  -> Maybe [(Icit, argument)]
traitSemanticSpine globals traits ctx trait arguments = do
  definition <- Map.lookup trait globals
  info <- Map.lookup trait traits
  finalizedSemanticSpineAfterGeneratedConstraints
    (dutParameterCount (gdUniverses definition))
    (tiParamCount info)
    (quote ctx 0 (gdType definition))
    arguments

recordFieldErasureProvenanceOfType :: EvalCtx -> Int -> Text -> Value -> Maybe ErasureProvenance
recordFieldErasureProvenanceOfType ctx depth fieldName ty = do
  fields <- forceRecordType ctx ty
  field <- find ((== fieldName) . rfName) fields
  guard (Repr.runtimeErasedRecordField ctx depth field)
  erasureProvenanceForPiDomain
    ctx depth (rfMode field) (rfQ field) (rfRuntimeErasure field) (rfType field)

runtimeRecordFieldOrderOfType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> Value -> Maybe [Text]
runtimeRecordFieldOrderOfType globals traits ctx depth ty =
  case force ctx ty of
    VRecordTQ fs ->
      Just
        [ rfName field
        | field <- fs
        , not (Repr.runtimeErasedRecordField ctx depth field)
        ]
    VGlobN traitG _
      | Just ti <- Map.lookup traitG traits ->
          Just (traitRuntimeFieldOrder globals ctx traitG ti)
    _ -> Nothing

traitRuntimeFieldOrder :: Map GName GlobalDef -> EvalCtx -> GName -> TraitInfo -> [Text]
traitRuntimeFieldOrder globals ctx traitG ti =
  sort $
    map fst (tiSupers ti)
      ++ [ member
         | member <- tiMembers ti
         , member `Set.notMember` tiAssociatedStaticMembers ti
         , Map.lookup member (tiMemberQs ti) /= Just Q0
         , not (globalRuntimeErased globals ctx (traitMemberGlobal traitG member))
         ]

traitMemberGlobal :: GName -> Text -> GName
traitMemberGlobal (GName m t) member = GName m (t <> "." <> member)

scopeSlotType :: ScopeSlot -> Maybe Value
scopeSlotType (ScopeSlot _ ty _) = ty

scopeSlotUniverses :: ScopeSlot -> Maybe DeclarationUniverseTelescope
scopeSlotUniverses (ScopeSlot _ _ telescope) = telescope

evalTypeAt :: EvalCtx -> Int -> Term -> Value
evalTypeAt ctx depth = eval ctx (rigidEnv depth)

rigidEnv :: Int -> [Value]
rigidEnv depth = [VRigid (depth - 1 - i) [] | i <- [0 .. depth - 1]]

-- | A schema lift is erased only after the payload's inferred type and the
-- contextual target type agree with the fully saturated family instances
-- recorded on the lift node. Arity alone is not alignment: ordinary family
-- arguments are compared definitionally and universe parameters under the
-- declaration's authenticated assumptions.
schemaLiftInstanceErrors
  :: EvalCtx
  -> Int
  -> Assumptions
  -> Text
  -> GName
  -> [Level]
  -> [Term]
  -> Maybe Value
  -> [Text]
schemaLiftInstanceErrors ctx depth assumptions endpoint family recordedLevels recordedArguments = \case
  Nothing ->
    ["schema lift " <> endpoint <> " family instance cannot be inferred at the erasure boundary"]
  Just instanceType ->
    let normalized = stripIdentity (quote ctx depth (force ctx instanceType))
        (headTerm, actualSpine) = spineOfTerm normalized
        actualArguments = map snd actualSpine
     in case stripIdentity headTerm of
          CGlobal actualFamily actualLevels ->
            [ "schema lift " <> endpoint <> " type has family "
                <> gKey actualFamily <> ", expected " <> gKey family
            | actualFamily /= family
            ]
              ++ [ "schema lift " <> endpoint <> " universe instance has the wrong arity"
                 | length actualLevels /= length recordedLevels
                 ]
              ++ [ "schema lift " <> endpoint <> " universe argument "
                    <> T.pack (show index) <> " disagrees with the recorded instance"
                 | (index, (actual, recorded)) <- zip [0 :: Int ..] (zip actualLevels recordedLevels)
                 , proveLevelEq assumptions actual recorded /= Proved
                 ]
              ++ [ "schema lift " <> endpoint <> " ordinary family application has the wrong arity"
                 | length actualArguments /= length recordedArguments
                 ]
              ++ [ "schema lift " <> endpoint <> " ordinary argument "
                    <> T.pack (show index) <> " disagrees with the recorded family application"
                 | (index, (actual, recorded)) <- zip [0 :: Int ..] (zip actualArguments recordedArguments)
                 , not
                     ( convertible
                         ctx
                         depth
                         (force ctx (eval ctx (rigidEnv depth) actual))
                         (force ctx (eval ctx (rigidEnv depth) recorded))
                     )
                 ]
          _ ->
            ["schema lift " <> endpoint <> " type is not an application of its recorded nominal family"]
  where
    stripIdentity = \case
      CUniverseLift _ _ _ inner -> stripIdentity inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> stripIdentity inner
      term -> term

coreEtaCtorApp :: Int -> Term -> Maybe (GName, [Level], Maybe Term, Int, [(Int, ConstructorArg)])
coreEtaCtorApp depth term =
  case spineOfTerm term of
    (hd, sargs)
      | (binders, body) <- coreFuncBinders hd
      , let k = length binders
      , let supplied = length sargs
      , k >= 1
      , supplied <= k
      , all ((== Q0) . snd) (drop supplied binders) ->
          case betaReduceAppliedHeadAt depth hd sargs of
            Just (CCtorI g universes ann constructorArgs)
              | supplied == k ->
                  Just
                    ( g
                    , universes
                    , ann
                    , k
                    , zip [0 :: Int ..] constructorArgs
                    )
            _
              | CCtorI g universes ann constructorArgs <- body ->
                  (\picks -> (g, universes, ann, k, concat picks))
                    <$> traverse (pick (map snd sargs) k) (zip [0 :: Int ..] constructorArgs)
            _ -> Nothing
    _ -> Nothing
  where
    pick args k (argumentIndex, argument) = case caTerm argument of
      CVar j
        | j >= 0
        , j < k
        , let binderIndex = k - 1 - j
        , binderIndex < length args ->
            Just [(argumentIndex, argument {caTerm = args !! binderIndex})]
        | not (caPayload argument) -> Just []
      _ -> Nothing

-- | Reduce an application whose head is a selected field of a concrete
-- record literal. This is the backend validator's counterpart of the
-- observation calculus's projection/beta equation: the selected field is the
-- only evaluated value, and the finite syntactic reduction cannot cross an
-- opacity or recursion boundary.
betaReduceLiteralProjectionApplication :: Int -> Term -> Maybe Term
betaReduceLiteralProjectionApplication depth application = do
  let (headTerm, arguments) = spineOfTerm application
  selected <- case headTerm of
    CProjM _ (CRecordV fields) field -> lookup field fields
    CProjAtM _ (CRecordV fields) field index -> do
      (storedField, value) <- indexMaybeLocal index fields
      guard (storedField == field)
      pure value
    _ -> Nothing
  betaReduceAppliedHeadAt depth selected arguments

betaReduceAppliedHeadAt :: Int -> Term -> [(Icit, Term)] -> Maybe Term
betaReduceAppliedHeadAt _ function [] = Just function
betaReduceAppliedHeadAt depth (CLamM _ expectedIcit _ _ body) ((actualIcit, argument) : rest)
  | expectedIcit == actualIcit =
      betaReduceAppliedHeadAt depth (substTopTermAt depth argument body) rest
betaReduceAppliedHeadAt _ _ _ = Nothing

coreFuncBinders :: Term -> ([(Icit, Q)], Term)
coreFuncBinders = go []
  where
    go !binders (CLam ic q _ b) = go ((ic, q) : binders) b
    go !binders t = (reverse binders, t)

-- | A checked value erased by proposition evidence has no runtime object to
-- inspect.  A match over it is nevertheless executable when the datatype and
-- constructor interfaces prove that there is exactly one possible constructor
-- and that constructor has no runtime payload.  This is a semantic reduction,
-- not a representation guess: every other match follows ordinary lowering.
erasedSingletonAlternative
  :: EvalCtx
  -> Map GName DataInfo
  -> Map GName CtorInfo
  -> Bool
  -> Maybe Value
  -> [CaseAlt]
  -> Maybe CaseAlt
erasedSingletonAlternative ctx datas ctors scrutineeErased scrutineeType alternatives = do
  ty <- scrutineeType
  guard scrutineeErased
  family <- case force ctx ty of
    VGlobN global _ -> Just global
    _ -> Nothing
  DataInfo [soleConstructor] _ _ <- Map.lookup family datas
  constructorInfo <- Map.lookup soleConstructor ctors
  guard (ciData constructorInfo == family)
  guard
    ( all
        (not . firstOfThree)
        (coreCtorPayloadRuntimeFacts ctx (eval ctx [] (ciType constructorInfo)))
    )
  alternative@(CaseAlt pattern' Nothing _) <- listToMaybe alternatives
  guard (length alternatives == 1)
  case pattern' of
    CPCtorM _ _ _ constructor _ _ -> do
      guard (constructor == soleConstructor)
      pure alternative
    -- Source @()@ is retained in checked Core as the structural zero-tuple
    -- pattern. Its acceptance against this nominal scrutinee has already been
    -- certified by pattern checking; the datatype proof above establishes
    -- that the checked shape is irrefutable and binds no runtime slots.
    CPTuple [] -> pure alternative
    _ -> Nothing
  where
    firstOfThree (value, _, _) = value

-- | Selected RuntimeErased evidence is attached to the checked Pi binder and
-- consumed when its 'ScopeSlot' is created.  The absent backend binder is the
-- occurrence-level authority for a direct local reference; reclassifying only
-- its domain would discard that selected evidence.
erasedScopeVariable :: Term -> ScopeStack -> Bool
erasedScopeVariable (CVar index) scopes =
  case indexMaybeLocal index scopes of
    Just (ScopeSlotData Nothing _ _ Nothing) -> True
    _ -> False
erasedScopeVariable _ _ = False

lowerErasedSingletonAlt :: Maybe Value -> CaseAlt -> Int -> ScopeStack -> Lower BackendTerm
lowerErasedSingletonAlt expected (CaseAlt pattern' Nothing body) depth scopes = do
  meta <- metaAt
  (_, binders, patternScopes, totalSlots) <-
    lowerPattern depth expected QW False "erased singleton match pattern" pattern'
  if null binders
    then lowerTerm body (depth + totalSlots) (patternScopes ++ scopes)
    else
      loweringViolation
        meta
        "E_BACKENDIR_ERASED_SINGLETON_PATTERN"
        "erased singleton reduction produced a runtime pattern binder"
lowerErasedSingletonAlt _ _ _ _ = do
  meta <- metaAt
  loweringViolation
    meta
    "E_BACKENDIR_ERASED_SINGLETON_PATTERN"
    "erased singleton reduction requires one unguarded constructor alternative"

lowerAlt :: Maybe Value -> CaseAlt -> Int -> ScopeStack -> Lower BackendAlt
lowerAlt expected (CaseAlt pat guard body) depth scopes = do
  meta <- metaAt
  (pat', binders, patScopes, totalSlots) <- lowerPattern depth expected QW False (T.pack "match pattern") pat
  let scopes' = patScopes ++ scopes
      depth' = depth + totalSlots
  guard' <- mapM (\g -> lowerTerm g depth' scopes') guard
  body' <- lowerTerm body depth' scopes'
  pure (BackendAlt meta pat' binders guard' body')

lowerItems :: [KItem] -> Int -> ScopeStack -> Lower [BackendItem]
lowerItems items depth scopes = go depth scopes items
  where
    go _ _ [] = pure []
    go d scs (item : rest) = do
      (out, d', scs') <- lowerItem item d scs
      (out :) <$> go d' scs' rest

lowerItem :: KItem -> Int -> ScopeStack -> Lower (BackendItem, Int, ScopeStack)
lowerItem item depth scopes = case item of
  KBind q pat action wit -> do
    meta <- metaAt
    action' <- lowerTerm action depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth Nothing q False (T.pack "do-bind pattern") pat
    pure (BKBind meta q pat' binders action' wit, depth + totalSlots, patScopes ++ scopes)
  KLet q pat value -> do
    meta <- metaAt
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    let expected = termTypeAt globals traits ctx depth scopes value
    value' <- lowerTerm value depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth expected q False (T.pack "do-let pattern") pat
    pure (BKLet meta q pat' binders value', depth + totalSlots, patScopes ++ scopes)
  KLetQ pat scrut mElse -> do
    meta <- metaAt
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    let expected = termTypeAt globals traits ctx depth scopes scrut
    scrut' <- lowerTerm scrut depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth expected QW False (T.pack "let? pattern") pat
    else' <- forM mElse $ \(ep, et) -> do
      (ep', ebinders, eScopes, eSlots) <-
        lowerPattern depth expected QW False (T.pack "let? else pattern") ep
      et' <- lowerTerm et (depth + eSlots) (eScopes ++ scopes)
      pure (ep', ebinders, et')
    pure (BKLetQ meta pat' binders scrut' else', depth + totalSlots, patScopes ++ scopes)
  KExpr action -> do
    meta <- metaAt
    action' <- lowerTerm action depth scopes
    pure (BKExpr meta action', depth, scopes)
  KVarItem _ initT act wit -> do
    meta <- metaAt
    mb <- binderAtWith QW False (T.pack "var")
    initT' <- lowerTerm initT depth scopes
    act' <- lowerTerm act depth scopes
    pure (BKVarItem meta mb initT' act' wit, depth + 1, binderSlotUnknown mb : scopes)
  KAssign _ monadic rhs act wit -> do
    meta <- metaAt
    rhs' <- lowerTerm rhs depth scopes
    act' <- lowerTerm act depth scopes
    pure (BKAssign meta monadic rhs' act' wit, depth, scopes)
  KReturn value -> do
    meta <- metaAt
    value' <- lowerTerm value depth scopes
    pure (BKReturn meta value', depth, scopes)
  KWhile pureCond cond body mElse -> do
    meta <- metaAt
    cond' <- lowerCond cond depth scopes
    body' <- lowerItems body depth scopes
    else' <- mapM (\es -> lowerItems es depth scopes) mElse
    pure (BKWhile meta pureCond cond' body' else', depth, scopes)
  KFor q pat source body mElse -> do
    meta <- metaAt
    source' <- lowerTerm source depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth Nothing QW False (T.pack "for pattern") pat
    let scopes' = patScopes ++ scopes
    body' <- lowerItems body (depth + totalSlots) scopes'
    else' <- mapM (\es -> lowerItems es depth scopes) mElse
    pure (BKFor meta q pat' binders source' body' else', depth, scopes)
  KIf arms mElse -> do
    meta <- metaAt
    arms' <-
      forM arms $ \(cond, body) -> do
        cond' <- lowerTerm cond depth scopes
        body' <- lowerItems body depth scopes
        pure (cond', body')
    else' <- mapM (\es -> lowerItems es depth scopes) mElse
    pure (BKIf meta arms' else', depth, scopes)
  KDefer lbl action -> do
    meta <- metaAt
    action' <- lowerTerm action depth scopes
    pure (BKDefer meta lbl action', depth, scopes)
  KUsing pat acquire release -> do
    meta <- metaAt
    acquire' <- lowerTerm acquire depth scopes
    release' <- lowerTerm release depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth Nothing QW True (T.pack "using pattern") pat
    pure (BKUsing meta pat' binders acquire' release', depth + totalSlots, patScopes ++ scopes)
  KSubDo lbl body -> do
    meta <- metaAt
    body' <- lowerItems body depth scopes
    pure (BKSubDo meta lbl body', depth, scopes)
  KBreak lbl -> do
    meta <- metaAt
    pure (BKBreak meta lbl, depth, scopes)
  KContinue lbl -> do
    meta <- metaAt
    pure (BKContinue meta lbl, depth, scopes)

lowerPattern :: Int -> Maybe Value -> Q -> Bool -> Text -> CorePat -> Lower (BackendPat, [Maybe BackendBinder], ScopeStack, Int)
lowerPattern depth expected q borrowed origin pat = do
  (pat', slots) <- lowerPatShape depth expected pat
  binders <- forM slots $ \slot ->
    if slot
      then binderAtWith q borrowed origin
      else pure Nothing
  -- Core pattern binders are produced in matchPat/source order, and evaluation
  -- extends the environment with reverse binds so the rightmost/runtime-latest
  -- binder becomes de Bruijn 0 while erased existential slots sit below the
  -- runtime fields. KBackendIR carries only runtime binders outward, but its
  -- internal scope map must preserve the full reversed slot stream.
  let runtimeBinders = reverse [mb | (True, mb) <- zip slots binders]
      scopeSlots = reverse (map binderSlotFromMaybe binders)
  pure (pat', runtimeBinders, scopeSlots, length slots)

lowerPatShape :: Int -> Maybe Value -> CorePat -> Lower (BackendPat, [Bool])
lowerPatShape depth expected = \case
  CPWild -> pure (BPWild, [])
  CPVarM _ n -> pure (BPVar n, [True])
  CPLit l -> pure (BPLit l, [])
  CPCtorM existentialModes bridges hidden g _ ps -> do
    source <-
      case interleaveConstructorSourceBinders hidden ps of
        Just aligned -> pure aligned
        Nothing -> do
          violationMeta <- metaAt
          recordLoweringViolation
            violationMeta
            "E_BACKENDIR_CONSTRUCTOR_PATTERN_ALIGNMENT"
            "constructor pattern hidden-field positions do not form a valid source telescope"
          pure (map Left hidden ++ map Right ps)
    (runtimeArity, fieldFacts) <-
      ctorSourceRuntimePatternFacts g (length source)
    lowered <-
      forM (zip3 [0 :: Int ..] source fieldFacts) $
        \(sourceIndex, sourceField, (runtime, physicalIndex, fieldType, provenance)) -> do
          let icit = either (const Impl) (const Expl) sourceField
          unless runtime $ do
            erasureMeta <- metaAt
            recordErasureAt depth erasureMeta ErasedPatternSlotSite icit
              ("constructor-field" <> T.pack (show sourceIndex))
              (fromMaybe ErasedByQuantity provenance)
          case sourceField of
            Left _ ->
              pure
                ( case (runtime, physicalIndex) of
                    (True, Just index) -> [(index, BPVar "__ctor_implicit")]
                    _ -> []
                , [runtime]
                )
            Right pattern' -> do
              (pattern'', patternSlots) <- lowerPatShape depth fieldType pattern'
              pure
                ( case (runtime, physicalIndex) of
                    (True, Just index) -> [(index, pattern'')]
                    _ -> []
                , if runtime
                    then patternSlots
                    else map (const False) patternSlots
                )
    let pats' = concatMap fst lowered
        sourceSlots = concatMap snd lowered
        -- A complete fact stream is required for physical extraction. The
        -- helper returns exactly one fact per authenticated source slot; any
        -- future metadata drift remains a hard lowering violation rather than
        -- silently assigning a different field to a branch binder.
        factsComplete = length fieldFacts == length source
    unless factsComplete $ do
      violationMeta <- metaAt
      recordLoweringViolation
        violationMeta
        "E_BACKENDIR_CONSTRUCTOR_PATTERN_ALIGNMENT"
        "constructor source-field runtime placements do not match the checked pattern telescope"
    let slots =
          replicate
            (length existentialModes + constructorBridgeBinderCount bridges)
            False
            ++ sourceSlots
    pure (BPCtor g runtimeArity pats', slots)
  CPTuple ps -> do
    ctx <- asks lsCtx
    let (runtimeArity, fieldFacts) = positionalRecordPatternFacts ctx depth expected (length ps)
    forM_ (zip [0 :: Int ..] fieldFacts) $ \(index, (runtime, _, _, provenance)) ->
      unless runtime $ do
        erasureMeta <- metaAt
        recordErasureAt depth erasureMeta ErasedPatternSlotSite Expl
          ("tuple-field" <> T.pack (show index)) (fromMaybe ErasedByQuantity provenance)
    lowered <- forM (zip ps (map (\(_, _, ty, _) -> ty) fieldFacts ++ repeat Nothing)) $ \(p, fieldTy) ->
      lowerPatShape depth fieldTy p
    let placements = map (\(runtime, physicalIndex, _, _) -> (runtime, physicalIndex)) fieldFacts
          ++ [(True, Just index) | index <- [runtimeArity ..]]
        fields = zip3 placements (map fst lowered) (map snd lowered)
        pats' = [(physicalIndex, p') | ((True, Just physicalIndex), p', _) <- fields]
        slots =
          concat
            [ if keep then patSlots else map (const False) patSlots
            | ((keep, _), _, patSlots) <- fields
            ]
    pure (BPTuple runtimeArity pats', slots)
  CPRecordM fs restDescriptor ->
    do
      ctx <- asks lsCtx
      let rest = fmap snd restDescriptor
          fieldFacts = namedRecordPatternFacts ctx depth expected
      forM_ fieldFacts $ \(name, runtime, _, provenance) ->
        unless runtime $ do
          erasureMeta <- metaAt
          recordErasureAt depth erasureMeta ErasedPatternSlotSite Expl name
            (fromMaybe ErasedByQuantity provenance)
      lowered <- forM fs $ \(name, p) -> do
        let fieldTy = fromMaybe Nothing (lookup name [(n, ty) | (n, _, ty, _) <- fieldFacts])
        loweredPat <- lowerPatShape depth fieldTy p
        pure (name, maybe True id (lookup name [(n, keep) | (n, keep, _, _) <- fieldFacts]), loweredPat)
      let
        restSlot = case rest of
          Just nm | not (T.null nm) -> [True]
          _ -> []
        fields =
          [ (keep, (name, p'), patSlots)
          | (name, keep, (p', patSlots)) <- lowered
          ]
        pats' = [(name, p') | (True, (name, p'), _) <- fields]
        slots =
          concat
            [ if keep then patSlots else map (const False) patSlots
            | (keep, _, patSlots) <- fields
            ]
      pure (BPRecord pats' rest, slots ++ restSlot)
  CPInject tag p -> do
    (p', slots) <- lowerPatShape depth Nothing p
    pure (BPInject tag p', slots)
  CPInjectRestM _ tags -> pure (BPInjectRest tags, [True])
  CPAsM _ name p -> do
    (p', slots) <- lowerPatShape depth expected p
    pure (BPAs name p', True : slots)
  CPOr ps perms -> do
    lowered <- mapM (lowerPatShape depth expected) ps
    let runtimePerms = adjustRuntimePerms (map snd lowered) perms
    pure (BPOr (map fst lowered) runtimePerms, maybe [] snd (listToMaybe lowered))

ctorSourceRuntimePatternFacts :: GName -> Int -> Lower (Int, [(Bool, Maybe Int, Maybe Value, Maybe ErasureProvenance)])
ctorSourceRuntimePatternFacts g sourceCount = do
  ctors <- asks lsCtors
  ctx <- asks lsCtx
  pure $
    case Map.lookup g ctors of
      Nothing ->
        (sourceCount, [(True, Just index, Nothing, Nothing) | index <- [0 .. sourceCount - 1]])
      Just ci ->
        let constructorType = eval ctx [] (ciType ci)
            runtimeArity =
              length [() | (runtime, _, _) <- coreCtorPayloadRuntimeFacts ctx constructorType, runtime]
            facts =
              take sourceCount $
                sourceCtorFieldRuntimePlacements ctx (length (ciSourceFields ci)) constructorType
                  ++ [(True, Just index, Nothing, Nothing) | index <- [runtimeArity ..]]
         in (runtimeArity, facts)

constructorObservationSites :: EvalCtx -> Value -> [(ObservationMode, Value)]
constructorObservationSites ctx = collect 0
  where
    collect lvl value = case force ctx value of
      VPiM mode _ _ _ _ dom (Closure env cod) ->
        (mode, dom) : collect (lvl + 1) (eval ctx (VRigid lvl [] : env) cod)
      _ -> []

explicitCtorFieldRuntimeFacts :: EvalCtx -> Int -> Value -> [(Bool, Maybe Value, Maybe ErasureProvenance)]
explicitCtorFieldRuntimeFacts ctx fieldCount ty =
  [ (runtime, fieldTy, provenance)
  | (runtime, _, fieldTy, provenance) <-
      explicitCtorFieldRuntimePlacements ctx fieldCount ty
  ]

explicitCtorFieldRuntimePlacements
  :: EvalCtx
  -> Int
  -> Value
  -> [(Bool, Maybe Int, Maybe Value, Maybe ErasureProvenance)]
explicitCtorFieldRuntimePlacements ctx fieldCount ty =
  let explicitMask =
        [ placement
        | (icit, placement) <- allCtorBinderRuntimePlacements ctx ty
        , icit == Expl
        ]
   in drop (max 0 (length explicitMask - fieldCount)) explicitMask

sourceCtorFieldRuntimePlacements
  :: EvalCtx
  -> Int
  -> Value
  -> [(Bool, Maybe Int, Maybe Value, Maybe ErasureProvenance)]
sourceCtorFieldRuntimePlacements ctx fieldCount ty =
  reindex 0
    (drop
      (max 0 (length allFields - fieldCount))
      allFields)
  where
    allFields = map snd (allCtorBinderRuntimePlacements ctx ty)
    reindex _ [] = []
    reindex runtimeIndex ((runtime, _, fieldType, provenance) : rest) =
      ( runtime
      , if runtime then Just runtimeIndex else Nothing
      , fieldType
      , provenance
      )
        : reindex
            (if runtime then runtimeIndex + 1 else runtimeIndex)
            rest

allCtorBinderRuntimePlacements
  :: EvalCtx
  -> Value
  -> [(Icit, (Bool, Maybe Int, Maybe Value, Maybe ErasureProvenance))]
allCtorBinderRuntimePlacements ctx = collect 0 0
  where
    collect lvl runtimeIndex v =
      case force ctx v of
        VPiRuntimeM mode _ ic q _ _ _ _ runtimeErasure dom (Closure env cod) ->
          let x = VRigid lvl []
              runtime = Repr.runtimeConstructorPiField ctx lvl runtimeErasure ic q dom
              physicalIndex = if runtime then Just runtimeIndex else Nothing
              nextRuntimeIndex = if runtime then runtimeIndex + 1 else runtimeIndex
              rest = collect (lvl + 1) nextRuntimeIndex (eval ctx (x : env) cod)
           in ( ic
              , ( runtime
                , physicalIndex
                , Just dom
                , if runtime
                    then Nothing
                    else erasureProvenanceForPiDomain ctx lvl mode q runtimeErasure dom
                )
              )
                : rest
        _ -> []

coreCtorPayloadRuntimeFacts :: EvalCtx -> Value -> [(Bool, Maybe Value, Maybe ErasureProvenance)]
coreCtorPayloadRuntimeFacts = coreCtorPayloadRuntimeFactsAt 0

coreCtorPayloadRuntimeFactsAt :: Int -> EvalCtx -> Value -> [(Bool, Maybe Value, Maybe ErasureProvenance)]
coreCtorPayloadRuntimeFactsAt baseLevel ctx = collect 0
  where
    collect lvl v =
      case force ctx v of
        VPiRuntimeM mode _ ic q _ _ _ _ runtimeErasure dom (Closure env cod) ->
          let absoluteLevel = baseLevel + lvl
              x = VRigid absoluteLevel []
              runtime = Repr.runtimeConstructorPiField ctx absoluteLevel runtimeErasure ic q dom
              keepInCore = ic == Expl || runtime
              rest = collect (lvl + 1) (eval ctx (x : env) cod)
           in if keepInCore
                then (runtime, Just dom, if runtime then Nothing else erasureProvenanceForPiDomain ctx absoluteLevel mode q runtimeErasure dom) : rest
                else rest
        _ -> []

positionalRecordPatternFacts
  :: EvalCtx
  -> Int
  -> Maybe Value
  -> Int
  -> (Int, [(Bool, Maybe Int, Maybe Value, Maybe ErasureProvenance)])
positionalRecordPatternFacts ctx depth expected patCount =
  case expected of
      Just ty ->
        case forceRecordType ctx ty of
          Just fs ->
            let (_, runtimeArity, facts) =
                  foldl'
                    (\(sourceIndex, runtimeIndex, accumulated) field ->
                      let runtime = not (Repr.runtimeErasedRecordField ctx depth field)
                          physicalIndex = if runtime then Just runtimeIndex else Nothing
                          nextRuntimeIndex = if runtime then runtimeIndex + 1 else runtimeIndex
                          fact =
                            ( runtime
                            , physicalIndex
                            , Just (rfType field)
                            , if runtime then Nothing else erasureProvenanceForPiDomain ctx depth (rfMode field) (rfQ field) (rfRuntimeErasure field) (rfType field)
                            )
                       in (sourceIndex + 1, nextRuntimeIndex, accumulated ++ [fact]))
                    (0 :: Int, 0 :: Int, [])
                    fs
             in (runtimeArity, take patCount facts)
          Nothing -> fallback
      Nothing -> fallback
  where
    fallback =
      (patCount, [(True, Just index, Nothing, Nothing) | index <- [0 .. patCount - 1]])

namedRecordPatternFacts :: EvalCtx -> Int -> Maybe Value -> [(Text, Bool, Maybe Value, Maybe ErasureProvenance)]
namedRecordPatternFacts ctx depth expected =
  case expected >>= forceRecordType ctx of
    Just fs ->
      [ let runtime = not (Repr.runtimeErasedRecordField ctx depth field)
         in (rfName field, runtime, Just (rfType field), if runtime then Nothing else erasureProvenanceForPiDomain ctx depth (rfMode field) (rfQ field) (rfRuntimeErasure field) (rfType field))
      | field <- fs
      ]
    Nothing -> []

forceRecordType :: EvalCtx -> Value -> Maybe [RecordField Value]
forceRecordType ctx ty =
  case force ctx ty of
    VRecordTQ fs -> Just fs
    VSigT _ inner -> forceRecordType ctx inner
    _ -> Nothing

adjustRuntimePerms :: [[Bool]] -> [[Int]] -> [[Int]]
adjustRuntimePerms [] _ = []
adjustRuntimePerms (canonSlots : altSlots) perms =
  zipWith adjust (canonSlots : altSlots) perms
  where
    runtimeCanon = [i | (i, True) <- zip [0 ..] canonSlots]
    adjust slots perm =
      mapMaybe
        ( \canonIx -> do
            altIx <- indexMaybeLocal canonIx perm
            if altIx >= 0 && altIx < length slots && slots !! altIx
              then Just (length (filter id (take altIx slots)))
              else Nothing
        )
        runtimeCanon

lowerCond :: KCond -> Int -> ScopeStack -> Lower BackendCond
lowerCond cond depth scopes = case cond of
  KCondPure t -> BKCondPure <$> lowerTerm t depth scopes
  KCondAction t -> BKCondAction <$> lowerTerm t depth scopes

metaAt :: Lower BackendMeta
metaAt = do
  nid <- freshNode
  pure (BackendMeta nid [])

recordErasureAt :: Int -> BackendMeta -> ErasureSite -> Icit -> Text -> ErasureProvenance -> Lower ()
recordErasureAt depth meta site ic name provenance =
  modify' $ \st ->
    st
      { lstErasures =
          BackendErasure (bmNodeId meta) depth site ic name provenance : lstErasures st
      }

erasedRuntimeAt :: BackendMeta -> Text -> Lower BackendTerm
erasedRuntimeAt meta = loweringViolation meta "E_BACKENDIR_ERASED_RUNTIME_TERM"

loweringViolation :: BackendMeta -> Text -> Text -> Lower BackendTerm
loweringViolation meta code msg = do
  recordLoweringViolation meta code msg
  pure (BUnit meta)

recordLoweringViolation :: BackendMeta -> Text -> Text -> Lower ()
recordLoweringViolation meta code msg =
  recordLoweringViolationWith meta code msg []

recordLoweringViolationWith :: BackendMeta -> Text -> Text -> [(Text, Text)] -> Lower ()
recordLoweringViolationWith meta code msg payloadFields = do
  owner <- asks lsOwner
  modify' $ \st ->
    st
      { lstLoweringViolations =
          BackendIRViolation owner (bmNodeId meta) code msg payloadFields
            : lstLoweringViolations st
      }

freshNode :: Lower BackendNodeId
freshNode = do
  n <- gets lstNextNode
  modify' $ \st -> st {lstNextNode = n + 1}
  pure (BackendNodeId n)

freshBinder :: Lower BackendBinderId
freshBinder = do
  n <- gets lstNextBinder
  modify' $ \st -> st {lstNextBinder = n + 1}
  pure (BackendBinderId n)

binderAtWith :: Q -> Bool -> Text -> Lower (Maybe BackendBinder)
binderAtWith q borrowed origin = do
  bid <- freshBinder
  pure
    ( Just
        ( BackendBinder
            bid
            origin
            (BinderOwn q Nothing borrowed (qDroppable q))
            False
        )
    )

binderSlotUnknown :: Maybe BackendBinder -> ScopeSlot
binderSlotUnknown mb = ScopeSlot (fmap bbBinderId mb) Nothing Nothing

binderSlotFromMaybe :: Maybe BackendBinder -> ScopeSlot
binderSlotFromMaybe mb = ScopeSlot (fmap bbBinderId mb) Nothing Nothing

patLayouts :: EvalCtx -> Map GName CtorInfo -> CorePat -> [(GName, BackendCtorLayout)]
patLayouts ctx ctors = \case
  CPCtor g _ ps ->
    let info = Repr.ctorLayoutOf ctx (ciType <$> Map.lookup g ctors)
        layout = BackendCtorLayout g info (maybe 0 clArity info)
     in (g, layout) : concatMap (patLayouts ctx ctors) ps
  CPTuple ps -> concatMap (patLayouts ctx ctors) ps
  CPRecord fs _ -> concatMap (patLayouts ctx ctors . snd) fs
  CPInject _ p -> patLayouts ctx ctors p
  CPOr ps _ -> concatMap (patLayouts ctx ctors) ps
  CPAs _ p -> patLayouts ctx ctors p
  CPWild -> []
  CPVar _ -> []
  CPLit _ -> []
  CPInjectRest _ -> []
