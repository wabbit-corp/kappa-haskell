{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Core calculus (a pragmatic KCore subset, Spec §30.2) and its
-- normalization-by-evaluation machinery (§31.1).
--
-- Two central types live here, and the difference between them is the key
-- to the whole back half of the compiler:
--
--   * 'Term' is /syntax/ — what elaboration produces. Variables are de
--     Bruijn __indices__ ('CVar', counting outward from the use site).
--   * 'Value' is the /semantic/ domain used during evaluation. Variables
--     are de Bruijn __levels__ ('VRigid', counting inward from the top),
--     and functions are real Haskell 'Closure's.
--
-- 'Kappa.Eval' shuttles between them (@eval :: Term -> Value@,
-- @quote :: Value -> Term@) to normalize and compare terms. See
-- docs/CONCEPTS.md for the index-vs-level and NbE background.
--
-- Representation choices, mapped to the spec:
--
--   * Pi binders carry quantities; quantity is part of function-type
--     identity in conversion (§31.1).
--   * Record types and values are canonicalized to lexicographic field
--     order (the §31.4 canonical order for non-dependent records); field
--     initializers are still evaluated in source order by elaborating
--     through a 'CLet' chain.
--   * Variant members are identified by the canonical rendering of the
--     member type (§31.3 stable member identities); widening is a no-op.
--   * @do@ blocks, loops and abrupt control are kept structured ('CDo')
--     and executed by the interpreter per the §18.8 completion kernel.
--   * Definitions record 'conversionReducible' separately from being
--     total-certified (§15.1); only reducible definitions δ-unfold.
module Kappa.Core
  ( GName (..)
  , gnameText
  , gKey
  , primModule
  , Icit (..)
  , Q (..)
  , ObservationMode (..)
  , FormationMode (..)
  , BinderOrigin (..)
  , RuntimeErasure (..)
  , ErasureJustification (..)
  , RecordField (..)
  , ConstructorArg (..)
  , ConstructorValueArg (..)
  , CoreLocalRecDef (..)
  , Level (..)
  , NeutralLevelAtom (..)
  , NeutralLevelTerm (..)
  , NeutralLevelLiteral (..)
  , neutralLevelTermAtom
  , neutralLevelTermDigest
  , mapNeutralLevelTermLevels
  , mapNeutralLevelAtomLevels
  , neutralLevelTermLocals
  , UniverseConstraint (..)
  , DeclarationUniverseTelescope (..)
  , UniverseEvidence (..)
  , UniverseEvidenceStep (..)
  , SchemaRoleEvidence (..)
  , UniverseVariance (..)
  , SchemaActionCertificateId (..)
  , ArithmeticDomain (..)
  , ArithmeticNormalizationTheory (..)
  , ArithmeticNormalizationProvider (..)
  , ArithmeticVariableKind (..)
  , ArithmeticVariable (..)
  , ArithmeticProviderEvidence (..)
  , ArithmeticAssumptionSource (..)
  , ArithmeticAssumption (..)
  , ArithmeticCertificate (..)
  , arithmeticCertificateVersion
  , mapArithmeticCertificate
  , traverseArithmeticCertificate
  , foldMapArithmeticCertificate
  , emptyDeclarationUniverseTelescope
  , finiteLevel
  , levelSucc
  , levelAdd
  , levelMax
  , solverUniverseEvidence
  , mapUniverseEvidenceLevels
  , universeLift
  , validateUniverseLiftEvidence
  , validateUniverseLiftEvidenceUnder
  , Term (.., CApp, CAppRuntime, CCtor)
  , pattern CPiEvidenceM
  , pattern CPiM
  , pattern CPiBoundM
  , pattern CPiFormedM
  , pattern CPiBoundFormedM
  , pattern CGlob
  , pattern CGlobI
  , pattern CLam
  , pattern CPi
  , pattern CProj
  , pattern CProjAt
  , pattern CLetM
  , pattern CLetRecM
  , pattern CLetPolyM
  , pattern CLetRecPolyM
  , pattern CLet
  , pattern CLetRec
  , pattern CRecordT
  , pattern CPVar
  , pattern CPCtor
  , pattern CPRecord
  , pattern CPInjectRest
  , pattern CPAs
  , CaseAlt (..)
  , ConstructorBridge (..)
  , ConstructorHiddenBinder (..)
  , constructorBridgeBinderCount
  , interleaveConstructorSourceBinders
  , propositionalConstructorBridges
  , CorePat (..)
  , KItem (..)
  , KCond (..)
  , RefCellId (..)
  , RefLoweringWitness (..)
  , RefActionWitness (..)
  , Literal (..)
  , Telescope
  , TelescopeEntry (..)
  , Value (.., VCtor)
  , pattern VPiEvidenceM
  , pattern VPiM
  , pattern VPiBoundM
  , pattern VPiFormedM
  , pattern VPiBoundFormedM
  , pattern VGlobN
  , pattern VGlobI
  , pattern VLam
  , pattern VPi
  , pattern VRecordT
  , Closure (..)
  , Env
  , Spine
  , MetaId
  , QuoteCapture (..)
  , QuotedSyntax (..)
  ) where

import Data.Data (Data)
import Control.Concurrent (ThreadId)
import Control.Concurrent.MVar (MVar)
import Control.Concurrent.STM (TVar)
import Data.Array.IO (IOArray)
import Data.ByteString (ByteString)
import Data.List (nub, sort)
import Data.IORef (IORef)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word8)
import Kappa.Level
  ( DeclarationUniverseTelescope (..)
  , Assumptions
  , Level (..)
  , NeutralLevelAtom (..)
  , NeutralLevelTerm (..)
  , NeutralLevelLiteral (..)
  , SolveResult (..)
  , UniverseConstraint (..)
  , assumptionsConsistent
  , assumptionsList
  , emptyDeclarationUniverseTelescope
  , emptyAssumptions
  , finiteLevel
  , levelAdd
  , levelMax
  , levelSucc
  , levelFields
  , levelMetas
  , levelParams
  , levelVars
  , normalizeLevel
  , neutralLevelTermAtom
  , neutralLevelTermDigest
  , neutralLevelTermLocals
  , mapNeutralLevelTermLevels
  , mapNeutralLevelAtomLevels
  , proveLevelLeq
  , insertAssumption
  )
import Kappa.Observation (FormationMode (..), ObservationMode (..))
import Kappa.NominalVariance (SchemaActionCertificateId (..), UniverseVariance (..))
import Kappa.Source (ModuleName (..), Span)
import Kappa.Syntax (Expr)

-- | Module owning interpreter primitives.
primModule :: ModuleName
primModule = ModuleName ["__prim"]

-- | Global name: defining module + spelling.
data GName = GName !ModuleName !Text
  deriving stock (Eq, Ord, Show, Data)

gnameText :: GName -> Text
gnameText (GName _ t) = t

-- | The fully-qualified dotted key of a global: its module path segments and
-- spelling joined by @.@ (e.g. @std.prelude.Unit@, or just @__rat@ for a
-- module-less runtime name). The stable string identity used by the backends
-- (and "Kappa.Builtins") to key constructor-tag and primitive tables.
gKey :: GName -> Text
gKey (GName (ModuleName segs) nm) = T.intercalate "." (segs ++ [nm])

data Icit = Expl | Impl
  deriving stock (Eq, Ord, Show, Data)

-- | Provenance of a dependent binder in the typed interface. Generated
-- declaration-universe constraints are inserted ahead of the source term
-- telescope and may be discharged before a source-written explicit implicit
-- argument. A source-written proof binder remains directly applicable.
data BinderOrigin
  = BinderSourceWritten
  | BinderGenerated
  deriving stock (Eq, Ord, Show, Data)

-- | Checked runtime-representation authority attached to a dependent binder.
-- Quantity-zero and intrinsically compile-time classifiers remain derivable
-- from the ordinary Pi fields; this annotation records the non-syntactic case
-- where selected semantic evidence proves the classifier runtime-erased.
data RuntimeErasure evidence
  = RuntimeRelevant
  | RuntimeErased !(ErasureJustification evidence)
  deriving stock (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

data ErasureJustification evidence
  = RuntimeErasedEvidence
      !evidence -- ^ The checked @RuntimeErased T@ goal.
      !evidence -- ^ Evidence selected for that exact goal.
      !evidence -- ^ The evidence's independently checked classifier.
  deriving stock (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

-- | Core quantities (§12.2). The five portable interval quantities.
data Q = Q0 | Q1 | QW | QLe1 | QGe1
  deriving stock (Eq, Ord, Show, Data)

-- | A dependent record field retains its quantity in KCore.  This is required
-- both for parametric-witness capability and for erasure justification; a
-- plain @(name, type)@ pair cannot distinguish an ordinary static type-code
-- field from a quantity-zero witness field.
data RecordField a = RecordField
  { rfName :: !Text
  , rfMode :: !ObservationMode
  , rfFormation :: !FormationMode
  , rfQ :: !Q
  , rfLevelAssumption :: !(Maybe (Level, Level))
  -- ^ Authenticated lexical level bound introduced by this field when it is
  -- an erased comparison proof. This is proof-interface metadata, not a
  -- source-shape inference performed by later phases.
  , rfRuntimeErasure :: !(RuntimeErasure a)
  -- ^ Checked non-syntactic runtime-erasure authority for this field. The
  -- quantity and classifier remain the canonical authority for quantity-zero
  -- and kind-domain erasure; this field preserves selected evidence that
  -- cannot be reconstructed by later phases.
  , rfType :: !a
  }
  deriving stock (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

-- | One replayable universe-ordering derivation used by KCore.  The scoped
-- assumptions are part of the certificate rather than ambient checker state:
-- substitution and serialization therefore cannot retain a stale proof while
-- changing only its endpoint levels (§11.1.2.8, §30.2.1A).
data UniverseEvidenceStep = UniverseEvidenceStep
  { uesLower :: !Level
  , uesUpper :: !Level
  , uesAssumptions :: ![(Level, Level)]
  }
  deriving stock (Eq, Ord, Show, Data)

-- | One independently replayable obligation of a nominal schema lift.
data SchemaRoleEvidence
  = SchemaInvariantEvidence
  | SchemaCovariantEvidence !UniverseEvidence
  | SchemaIrrelevantEvidence
  deriving stock (Eq, Ord, Show, Data)

-- | Canonical evidence for one cumulative lift.  More than one step records a
-- composed lift; retaining the chain preserves every proof dependency.
newtype UniverseEvidence = UniverseEvidence
  { ueSteps :: [UniverseEvidenceStep]
  }
  deriving stock (Eq, Ord, Show, Data)

-- | Freeze a successful solver judgment into KCore evidence.
solverUniverseEvidence :: Assumptions -> Level -> Level -> UniverseEvidence
solverUniverseEvidence assumptions lower upper =
  UniverseEvidence [canonicalUniverseEvidenceStep lower upper (assumptionsList assumptions)]

canonicalUniverseEvidenceStep :: Level -> Level -> [(Level, Level)] -> UniverseEvidenceStep
canonicalUniverseEvidenceStep lower upper assumptions =
  UniverseEvidenceStep normalizedLower normalizedUpper proofDependencies
  where
    normalizedLower = normalizeLevel lower
    normalizedUpper = normalizeLevel upper
    normalizedAssumptions =
      sort (nub [(normalizeLevel a, normalizeLevel b) | (a, b) <- assumptions])
    normalizedContext = assumptionsFrom normalizedAssumptions
    proofDependencies
      | assumptionsConsistent normalizedContext
      , proveLevelLeq normalizedContext normalizedLower normalizedUpper == Proved =
          minimizeDependencies normalizedAssumptions
      | otherwise = normalizedAssumptions
    minimizeDependencies dependencies =
      case
          [ candidate
          | candidate <- removeOne dependencies
          , let context = assumptionsFrom candidate
          , assumptionsConsistent context
          , proveLevelLeq context normalizedLower normalizedUpper == Proved
          ] of
        candidate : _ -> minimizeDependencies candidate
        [] -> dependencies
    removeOne [] = []
    removeOne (first : rest) = rest : map (first :) (removeOne rest)
    assumptionsFrom = foldr (uncurry insertAssumption) emptyAssumptions

mapUniverseEvidenceLevels :: (Level -> Level) -> UniverseEvidence -> UniverseEvidence
mapUniverseEvidenceLevels f (UniverseEvidence steps) =
  UniverseEvidence
    [ canonicalUniverseEvidenceStep
        (f uesLower)
        (f uesUpper)
        [(f a, f b) | (a, b) <- uesAssumptions]
    | UniverseEvidenceStep {..} <- steps
    ]

-- | Construct a canonical cumulative lift. Identity lifts disappear and
-- adjacent nested lifts compose while preserving their evidence steps.
universeLift :: UniverseEvidence -> Term -> Term
universeLift evidence term = case evidenceEndpoints evidence of
  Just (from, to)
    | from == to -> term
    | CUniverseLift innerFrom innerTo innerEvidence inner <- term
    , innerTo == from ->
        CUniverseLift innerFrom to (composeEvidence innerEvidence evidence) inner
    | otherwise -> CUniverseLift from to evidence term
  Nothing -> CUniverseLift LZero LZero evidence term
  where
    composeEvidence (UniverseEvidence left) (UniverseEvidence right) =
      UniverseEvidence (left ++ right)

evidenceEndpoints :: UniverseEvidence -> Maybe (Level, Level)
evidenceEndpoints (UniverseEvidence steps) = case steps of
  [] -> Nothing
  first : rest -> Just (uesLower first, uesUpper (last (first : rest)))

-- | Replay the evidence attached to a single lift node. The caller supplies
-- the in-scope term-binder depth and hidden declaration-universe arity. An
-- empty result is valid; messages are intentionally stable enough for the
-- typed-checkpoint diagnostic bridge.
validateUniverseLiftEvidence :: Int -> Int -> Term -> [Text]
validateUniverseLiftEvidence = validateUniverseLiftEvidenceUnder emptyAssumptions

-- | Replay lift evidence against assumptions supplied by the typed owner and
-- lexical proof context. Evidence records which assumptions its derivation
-- used, but those records are dependencies, not authorities: an assumption
-- absent from this trusted context invalidates the certificate.
validateUniverseLiftEvidenceUnder :: Assumptions -> Int -> Int -> Term -> [Text]
validateUniverseLiftEvidenceUnder trusted depth universeArity = \case
  CUniverseLift from0 to0 evidence@(UniverseEvidence steps) _ ->
    endpointErrors ++ chainErrors ++ concatMap validateStep steps
    where
      from = normalizeLevel from0
      to = normalizeLevel to0
      endpointErrors = case evidenceEndpoints evidence of
        Nothing -> ["cumulative lift is missing universe evidence"]
        Just (eFrom, eTo) ->
          ["cumulative lift evidence endpoints do not match the lift" | (normalizeLevel eFrom, normalizeLevel eTo) /= (from, to)]
      chainErrors =
        [ "cumulative lift evidence steps are not composable"
        | (left, right) <- zip steps (drop 1 steps)
        , normalizeLevel (uesUpper left) /= normalizeLevel (uesLower right)
        ]
      validateStep UniverseEvidenceStep {..} =
        let normalizedTrusted =
              sort (nub [(normalizeLevel a, normalizeLevel b) | (a, b) <- assumptionsList trusted])
            normalizedDependencies =
              sort (nub [(normalizeLevel a, normalizeLevel b) | (a, b) <- uesAssumptions])
            replayAssumptions =
              foldr
                (uncurry insertAssumption)
                emptyAssumptions
                normalizedDependencies
            levels = uesLower : uesUpper : concatMap (\(a, b) -> [a, b]) uesAssumptions
            scopeErrors = concatMap validateLevel levels
            authorityErrors =
              [ "universe evidence depends on an assumption not supplied by its typed scope; evidence uses "
                  <> T.pack (show normalizedDependencies)
                  <> ", scope supplies " <> T.pack (show normalizedTrusted)
              | any (`notElem` normalizedTrusted) normalizedDependencies
              ]
            proofErrors =
              ["universe evidence assumptions are inconsistent" | not (assumptionsConsistent replayAssumptions)]
                ++ [ "universe evidence does not prove "
                       <> T.pack (show (normalizeLevel uesLower))
                       <> " <= " <> T.pack (show (normalizeLevel uesUpper))
                       <> " from its recorded dependencies " <> T.pack (show normalizedDependencies)
                   | assumptionsConsistent replayAssumptions
                   , proveLevelLeq replayAssumptions uesLower uesUpper /= Proved
                   ]
         in scopeErrors ++ authorityErrors ++ proofErrors
      validateLevel level =
        ["universe evidence contains an out-of-scope local level" | any (>= depth) (levelVars level)]
          ++ ["universe evidence contains an out-of-scope declaration universe" | any (\p -> p < 0 || p >= universeArity) (levelParams level)]
          ++ ["universe evidence contains an escaped record-field level" | not (null (levelFields level))]
          ++ ["universe evidence contains an unsolved level metavariable" | not (null (levelMetas level))]
  _ -> []

type MetaId = Int

-- | Stable identity for a checker-created mutable cell within one elaborated
-- Core body. Backends use it only as proof-carrying metadata; it is not a
-- source-visible reference and does not affect runtime values.
newtype RefCellId = RefCellId Int
  deriving stock (Eq, Ord, Show, Data)

-- | A lowering witness proving that a source `var` cell was created through the
-- checker-selected prelude `MonadRef (IO e)` dictionary, whose members are the
-- builtin native IO-ref primitives. Absence of this witness means backend
-- optimizations must use the generic selected-action path.
data RefLoweringWitness
  = BuiltinIORefWitness
      { rlwCellId :: !RefCellId
      }
  deriving stock (Eq, Ord, Show, Data)

-- | Occurrence-level evidence for a mutable-reference action selected by the
-- checker. The action term remains authoritative for semantics; the witness is
-- only a conservative optimization proof for backends.
data RefActionWitness
  = BuiltinIORefNew !RefLoweringWitness
  | BuiltinIORefRead !RefLoweringWitness
  | BuiltinIORefWrite !RefLoweringWitness
  deriving stock (Eq, Ord, Show, Data)

data Literal
  = LitInt !Integer -- Nat/Int/Integer share representation
  | LitDouble !Double
  | LitStr !Text
  | LitScalar !Char
  | LitByte !Word8 -- §6.5 conventional 'b' handler payload
  | LitBytes !ByteString -- §29.5 byte sequences (exact byte content)
  | LitGrapheme !Text -- §6.5 conventional 'g' handler payload (exact scalar sequence)
  deriving stock (Eq, Ord, Show, Data)

-- | Core terms, de Bruijn indexed. Grouped into families below for reading.
-- | One typed constructor argument. 'caPayload' records membership in the
-- evaluator/source-pattern payload view; every argument remains in KCore, but
-- implicit erased type/proof arguments are absent from 'VCtor' and are later
-- erased by KBackendIR. 'caIcit' is part of the checked application spine.
data ConstructorArg = ConstructorArg
  { caIcit :: !Icit
  , caPayload :: !Bool
  , caName :: !(Maybe Text)
  , caTerm :: !Term
  }
  deriving stock (Eq, Show, Data)

-- | Semantic counterpart of 'ConstructorArg'.  Keeping the complete typed
-- spine in the value domain makes normalization-by-evaluation lossless for
-- hidden constructor universes and erased arguments; the 'VCtor' compatibility
-- view below exposes only the historical evaluator payload.
data ConstructorValueArg = ConstructorValueArg
  { cvaIcit :: !Icit
  , cvaPayload :: !Bool
  , cvaName :: !(Maybe Text)
  , cvaValue :: !Value
  }

-- | One member of a local mutually recursive declaration SCC. All members of
-- a 'CLetRecGroupM' share its declaration-universe telescope, while every
-- 'CLocal' occurrence still supplies a fresh specialization of that shared
-- schema. Member types are outside the term-level recursive scope; every RHS
-- and the group body are under all members (last member is de Bruijn index 0).
data CoreLocalRecDef = CoreLocalRecDef
  { clrdMode :: !ObservationMode
  , clrdQuantity :: !Q
  , clrdName :: !Text
  , clrdRuntimeErasure :: !(RuntimeErasure Term)
  , clrdType :: !Term
  , clrdRhs :: !Term
  }
  deriving stock (Eq, Show, Data)

-- | Arithmetic proposition domains whose proof rules are independently
-- replayed at typed checkpoints (§15.8.2/§30.2.0A). First-class
-- 'TypeLevel' propositions use the universe solver's certified normalization
-- bridge, but remain explicit proof terms and never extend conversion.
data ArithmeticDomain
  = ArithmeticNatural
  | ArithmeticInteger
  | ArithmeticTypeLevel
  | ArithmeticProviderLaw
  deriving stock (Eq, Ord, Show, Data)

-- | A portable algebraic theory understood by the proof-normalization
-- service.  These are semantic roles, not source trait names.
data ArithmeticNormalizationTheory
  = ArithmeticMonoid
  | ArithmeticCommutativeMonoid
  deriving stock (Eq, Ord, Show, Data)

-- | The identity-bearing, versioned part of one §15.8.2 provider artifact.
-- The selected dictionary remains occurrence-specific and is stored alongside
-- this descriptor in 'ArithmeticProviderEvidence'.
data ArithmeticNormalizationProvider = ArithmeticNormalizationProvider
  { anpIdentity :: !Text
  , anpTheory :: !ArithmeticNormalizationTheory
  , anpLawIdentity :: !GName
  , anpNormalFormVersion :: !Integer
  , anpProviderVersion :: !Integer
  , anpCheckerVersion :: !Integer
  }
  deriving stock (Eq, Ord, Show, Data)

data ArithmeticVariableKind
  = ArithmeticVariableNatural
  | ArithmeticVariableInteger
  deriving stock (Eq, Ord, Show, Data)

data ArithmeticVariable a = ArithmeticVariable
  { avKind :: !ArithmeticVariableKind
  , avTerm :: !a
  }
  deriving stock (Eq, Show, Data)

-- | One selected provider admitted to an arithmetic proof. The trait identity
-- and the exact selected evidence term are both retained; a verifier never
-- reconstructs either from a member spelling.
data ArithmeticProviderEvidence a = ArithmeticProviderEvidence
  { apeNormalizationProvider :: !(Maybe ArithmeticNormalizationProvider)
  , apeTrait :: !GName
  , apeEvidence :: !a
  }
  deriving stock (Eq, Show, Data)

data ArithmeticAssumptionSource a
  = ArithmeticAssumptionProof
      { aasProposition :: !a
      , aasEvidence :: !a
      }
  | ArithmeticAssumptionConversion
      { aasProposition :: !a
      }
  | ArithmeticAssumptionBranch
      { aasBranchTruth :: !Bool
      , aasBranchCondition :: !a
      }
  deriving stock (Eq, Show, Data)

data ArithmeticAssumption a = ArithmeticAssumption
  { aaTruth :: !Bool
  , aaProposition :: !a
  , aaReplayProposition :: !a
  , aaSource :: !(ArithmeticAssumptionSource a)
  }
  deriving stock (Eq, Show, Data)

-- | A proof-producing arithmetic decision. The portable artifact adds the
-- canonical replay normal form; Core retains identity-bearing source material
-- so shifting, substitution, and NbE can transform it without stale variable
-- numbers.
data ArithmeticCertificate a = ArithmeticCertificate
  { acVersion :: !Integer
  , acDomain :: !ArithmeticDomain
  , acProviders :: ![ArithmeticProviderEvidence a]
  , acVariables :: ![ArithmeticVariable a]
  , acAssumptions :: ![ArithmeticAssumption a]
  , acGoal :: !a
  -- ^ The original checked proposition inhabited by this proof.
  , acReplayGoal :: !a
  -- ^ A definitionally equal view in the portable arithmetic fragment.
  -- It is explicit so independent artifact verification never has to trust
  -- elaborator-only normalization state.
  }
  deriving stock (Eq, Show, Data)

-- | Version of the independently replayed arithmetic-certificate payload.
-- Version 3 uses ordered multiplicative words in polynomial normal forms.
arithmeticCertificateVersion :: Integer
arithmeticCertificateVersion = 3

mapArithmeticCertificate :: (a -> b) -> ArithmeticCertificate a -> ArithmeticCertificate b
mapArithmeticCertificate transform certificate =
  ArithmeticCertificate
    { acVersion = acVersion certificate
    , acDomain = acDomain certificate
    , acProviders =
        [ ArithmeticProviderEvidence provider trait (transform evidence)
        | ArithmeticProviderEvidence provider trait evidence <- acProviders certificate
        ]
    , acVariables =
        [ ArithmeticVariable kind (transform variable)
        | ArithmeticVariable kind variable <- acVariables certificate
        ]
    , acAssumptions =
        [ ArithmeticAssumption
            truth
            (transform proposition)
            (transform replayProposition)
            (mapArithmeticAssumptionSource transform source)
        | ArithmeticAssumption truth proposition replayProposition source <- acAssumptions certificate
        ]
    , acGoal = transform (acGoal certificate)
    , acReplayGoal = transform (acReplayGoal certificate)
    }

traverseArithmeticCertificate
  :: Applicative f
  => (a -> f b)
  -> ArithmeticCertificate a
  -> f (ArithmeticCertificate b)
traverseArithmeticCertificate transform certificate =
  ArithmeticCertificate
    (acVersion certificate)
    (acDomain certificate)
    <$> traverse
      (\(ArithmeticProviderEvidence provider trait evidence) ->
        ArithmeticProviderEvidence provider trait <$> transform evidence)
      (acProviders certificate)
    <*> traverse
      (\(ArithmeticVariable kind variable) ->
        ArithmeticVariable kind <$> transform variable)
      (acVariables certificate)
    <*> traverse
      (\(ArithmeticAssumption truth proposition replayProposition source) ->
        ArithmeticAssumption truth
          <$> transform proposition
          <*> transform replayProposition
          <*> traverseArithmeticAssumptionSource transform source)
      (acAssumptions certificate)
    <*> transform (acGoal certificate)
    <*> transform (acReplayGoal certificate)

foldMapArithmeticCertificate
  :: Monoid m
  => (a -> m)
  -> ArithmeticCertificate a
  -> m
foldMapArithmeticCertificate transform certificate =
  foldMap (transform . apeEvidence) (acProviders certificate)
    <> foldMap (transform . avTerm) (acVariables certificate)
    <> foldMap
      (\assumption ->
        transform (aaProposition assumption)
          <> transform (aaReplayProposition assumption)
          <> foldMapArithmeticAssumptionSource transform (aaSource assumption))
      (acAssumptions certificate)
    <> transform (acGoal certificate)
    <> transform (acReplayGoal certificate)

mapArithmeticAssumptionSource
  :: (a -> b)
  -> ArithmeticAssumptionSource a
  -> ArithmeticAssumptionSource b
mapArithmeticAssumptionSource transform = \case
  ArithmeticAssumptionProof proposition evidence ->
    ArithmeticAssumptionProof (transform proposition) (transform evidence)
  ArithmeticAssumptionConversion proposition ->
    ArithmeticAssumptionConversion (transform proposition)
  ArithmeticAssumptionBranch truth condition ->
    ArithmeticAssumptionBranch truth (transform condition)

traverseArithmeticAssumptionSource
  :: Applicative f
  => (a -> f b)
  -> ArithmeticAssumptionSource a
  -> f (ArithmeticAssumptionSource b)
traverseArithmeticAssumptionSource transform = \case
  ArithmeticAssumptionProof proposition evidence ->
    ArithmeticAssumptionProof
      <$> transform proposition
      <*> transform evidence
  ArithmeticAssumptionConversion proposition ->
    ArithmeticAssumptionConversion <$> transform proposition
  ArithmeticAssumptionBranch truth condition ->
    ArithmeticAssumptionBranch truth <$> transform condition

foldMapArithmeticAssumptionSource
  :: Monoid m
  => (a -> m)
  -> ArithmeticAssumptionSource a
  -> m
foldMapArithmeticAssumptionSource transform = \case
  ArithmeticAssumptionProof proposition evidence ->
    transform proposition <> transform evidence
  ArithmeticAssumptionConversion proposition ->
    transform proposition
  ArithmeticAssumptionBranch _ condition ->
    transform condition

data Term
  = -- Lambda-calculus core ------------------------------------------------
    CVar !Int -- ^ a bound variable, as a de Bruijn /index/ (0 = nearest binder)
  | CLocal !Int ![Level]
    -- ^ A local declaration occurrence specialized at a fresh declaration-
    -- universe spine.  Unlike 'CVar', this is not a term application: the
    -- levels are static identity and erase before runtime lowering.
  | CGlobal !GName ![Level]
  | CLamM !ObservationMode !Icit !Q !Text !Term
  -- | Dependent function type. The 'Bool' is the binder's borrow marker
  -- (§12.3: @(& x : A) -> …@) — part of the binder information carried in
  -- core so usage analysis reads it from the type, not the surface AST. It
  -- is metadata for the quantity/borrow checker: conversion ignores it
  -- (borrow on a parameter is not part of definitional type identity here).
  | CPiRuntimeM !ObservationMode !FormationMode !Icit !Q !Bool !Text !(Maybe (Level, Level)) !BinderOrigin !(RuntimeErasure Term) !Term !Term
    -- ^ A dependent function type plus the authenticated level assumption
    -- introduced by this binder, when any. The proposition remains the
    -- ordinary domain term; this metadata is the designated universe-proof
    -- interface and is never reconstructed from a rendered source shape.
    -- 'BinderOrigin' distinguishes user evidence from declaration-solver
    -- evidence; explicit implicit application depends on that provenance.
  | CAppM !Icit !(RuntimeErasure Term) !Term !Term
    -- ^ Application with the checker-selected, occurrence-local runtime
    -- representation of its argument.  The annotation is required when a
    -- generic binder becomes erasable only through evidence available at
    -- this call site (notably an equality proof under local @IsSet@
    -- evidence).  Backends consume this fact; they never repeat evidence
    -- selection after elaboration.
  | CSort !Level -- ^ @Type u@
  | CLevel !Level
    -- ^ A static declaration-universe identity used while checking a level
    -- expression. It is neither a term binder nor a runtime TypeLevel value.
  | CUniverseLift !Level !Level !UniverseEvidence !Term
    -- ^ Explicit cumulative subsumption (§30.2.1A). Evaluation and runtime
    -- representation are transparent; typed checkpoints validate evidence
    -- before KBackendIR erases the node.
  | CSchemaLift !GName ![Level] ![Level] ![UniverseVariance]
      ![SchemaRoleEvidence] !SchemaActionCertificateId ![Term] ![Term] !Term
    -- ^ Certified cumulative subsumption between two fully saturated
    -- instances of one nominal family (§30.2.1B). The aligned terms are the
    -- complete source and aligned target family argument spines, including
    -- generated erased proof arguments. This node is representation identity
    -- and erases before KBackendIR only after independent verification.
  | CArithmeticProof !(ArithmeticCertificate Term)
    -- ^ Runtime-erased proof evidence. KCoreText independently reifies the
    -- authenticated operations and replays the canonical certificate before
    -- any backend may erase it.
  | CLit !Literal
  -- Data and pattern matching --------------------------------------------
  -- | Saturated constructor application. The optional 'Term' is the
  -- KBackendIR Stage 0 /head-type annotation/: the constructor's
  -- instantiated, monomorphic head type as a quoted Core type term
  -- (e.g. @Option Int@ rather than the polymorphic @Option a@), or
  -- 'Nothing' where the concrete head was not in scope at the build
  -- site. It is observe-only metadata: NO backend reads it, and
  -- conversion\/'Eq' must ignore it (see 'Eq' instance note below), so
  -- it can never change tag ids, codegen, or evaluation.
  | CCtorI !GName ![Level] !(Maybe Term) ![ConstructorArg]
    -- ^ Saturated typed constructor occurrence: declaration-universe
    -- instantiation, observe-only checked head type, and the full constructor
    -- Pi spine. Runtime/evaluator consumers select only 'caPayload' arguments.
  -- | Pattern match. The optional terms are the scrutinee's monomorphic type
  -- and the match's checked result type. Both are observe-only typed-checkpoint
  -- metadata: backends and conversion ignore them, while KCoreText uses them
  -- to replay constructor elimination and dependent motives without guessing
  -- from an enclosing expected type.
  | CMatch !Term !(Maybe Term) !(Maybe Term) ![CaseAlt]
  -- Records --------------------------------------------------------------
  | CRecordTQ ![RecordField Term] -- ^ canonical dependency-respecting field order
  | CRecordV ![(Text, Term)]
  | CProjM !ObservationMode !Term !Text
  | -- | @CProjAt e f i@: a projection of field @f@ from a record of a
    -- statically-known CLOSED layout, where @i@ is @f@'s index in the
    -- lexicographically-sorted field list (= the @K_REC@ slot order).
    -- Semantically identical to @CProj e f@ — the interpreter ignores @i@ and
    -- looks up by name; the native backend (P0.4) reads the field at a fixed
    -- offset (@krec_at@) instead of a name scan.  Emitted only by the closed
    -- @VRecordT@ projection branch in elaboration; every other projection
    -- stays a plain @CProj@.
    CProjAtM !ObservationMode !Term !Text !Int
  -- Variants -------------------------------------------------------------
  | CVariantT ![Term] -- ^ canonical member order
  | CInject !Text !Term -- ^ member-identity tag + payload
  -- Binding and metavariables --------------------------------------------
  | CLetRuntimeM !ObservationMode !Q !Text !(RuntimeErasure Term) !Term !Term !Term -- ^ mode, q, name, erasure, type, rhs, body
  | CLetRecRuntimeM !ObservationMode !Q !Text !(RuntimeErasure Term) !Term !Term !Term -- ^ recursive local let: rhs and body live under the binder
  | CLetPolyRuntimeM !ObservationMode !Q !Text !DeclarationUniverseTelescope !(RuntimeErasure Term) !Term !Term !Term
    -- ^ Universe-polymorphic non-recursive local declaration.  The type and
    -- rhs are closed over the telescope's 'LParam's; only the body is under
    -- the term binder.
  | CLetRecPolyRuntimeM !ObservationMode !Q !Text !DeclarationUniverseTelescope !(RuntimeErasure Term) !Term !Term !Term
    -- ^ Universe-polymorphic recursive local declaration.  Both rhs and body
    -- are under the term binder, as for 'CLetRecM'.
  | CLetRecGroupM !DeclarationUniverseTelescope ![CoreLocalRecDef] !Term
    -- ^ A local mutually recursive declaration SCC. The group has one shared
    -- static universe telescope; each member remains a distinct recursive
    -- identity and every RHS/body is under all member term binders.
  | CMeta !MetaId -- ^ an unsolved unification variable (a "hole" the checker will fill)
  -- Effectful do-kernel --------------------------------------------------
  | CDo !(Maybe Text) ![KItem] -- ^ §18.8 do kernel (optional scope label, §18.7); executed natively
  -- Sealed packages / existentials ---------------------------------------
  | CSealE ![Text] !Term -- ^ §13.2.10 sealed package: opaque labels + record
  | CSigT ![Text] !Term -- ^ §13.2.10 signature type: opaque labels + record type
  -- Suspensions (laziness) -----------------------------------------------
  | CThunkE !Term !(Maybe Term) -- ^ Delay + observe-only checked suspension type
  | CLazyE !Term !(Maybe Term) -- ^ Memo + observe-only checked suspension type
  | CForceE !Term !(Maybe Term) -- ^ suspension value + observe-only checked result type
  -- Conditional and metaprogramming --------------------------------------
  | CIf !Term !Term !Term
  | CQuote !QuotedSyntax ![Term] -- ^ §21.1 syntax quote: payload + in-quote splice slots
  deriving stock (Show, Data)

-- | Structural equality on 'Term'.
--
-- Hand-written rather than derived for ONE reason: the KBackendIR Stage 0
-- checked-type annotations on 'CCtor', 'CMatch', 'CThunkE', 'CLazyE', and
-- 'CForceE' are observe-only metadata
-- and MUST NOT participate in term identity. Two terms that differ only in
-- their annotation are the same term for every existing client (conversion
-- caches, quote-payload comparison, dedup), so we compare the structural
-- fields and deliberately drop the annotation. Every other constructor is
-- compared field-by-field exactly as the derived instance would.
instance Eq Term where
  CVar a == CVar a' = a == a'
  CLocal a us == CLocal a' us' = a == a' && us == us'
  CGlobal a us == CGlobal a' us' = a == a' && us == us'
  CLamM m a b c d == CLamM m' a' b' c' d' = m == m' && a == a' && b == b' && c == c' && d == d'
  CPiRuntimeM m fm a b c d p o r e f == CPiRuntimeM m' fm' a' b' c' d' p' o' r' e' f' =
    m == m' && fm == fm' && a == a' && b == b' && c == c' && d == d' && p == p' && o == o' && r == r' && e == e' && f == f'
  CAppM a _ b c == CAppM a' _ b' c' = a == a' && b == b' && c == c'
  CSort a == CSort a' = a == a'
  CLevel a == CLevel a' = a == a'
  CUniverseLift a b c d == CUniverseLift a' b' c' d' =
    a == a' && b == b' && c == c' && d == d'
  CSchemaLift a b c d e f g h i == CSchemaLift a' b' c' d' e' f' g' h' i' =
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f'
      && g == g' && h == h' && i == i'
  CArithmeticProof a == CArithmeticProof a' = a == a'
  CLit a == CLit a' = a == a'
  -- The occurrence-local head annotation is fresh-elaboration metadata and is
  -- intentionally ignored. Hidden universes, explicitness, payload marks,
  -- and erased arguments are typed constructor identity and must survive every
  -- structural equality/checkpoint comparison.
  CCtorI g us _ as == CCtorI g' us' _ as' =
    g == g' && us == us' && as == as'
  CMatch s _ _ alts == CMatch s' _ _ alts' = s == s' && alts == alts'
  CRecordTQ a == CRecordTQ a' = a == a'
  CRecordV a == CRecordV a' = a == a'
  CProjM a b c == CProjM a' b' c' = a == a' && b == b' && c == c'
  CProjAtM a b c d == CProjAtM a' b' c' d' = a == a' && b == b' && c == c' && d == d'
  CVariantT a == CVariantT a' = a == a'
  CInject a b == CInject a' b' = a == a' && b == b'
  CLetRuntimeM a b c r d e f == CLetRuntimeM a' b' c' r' d' e' f' =
    a == a' && b == b' && c == c' && r == r' && d == d' && e == e' && f == f'
  CLetRecRuntimeM a b c r d e f == CLetRecRuntimeM a' b' c' r' d' e' f' =
    a == a' && b == b' && c == c' && r == r' && d == d' && e == e' && f == f'
  CLetPolyRuntimeM a b c u r d e f == CLetPolyRuntimeM a' b' c' u' r' d' e' f' =
    a == a' && b == b' && c == c' && u == u' && r == r' && d == d' && e == e' && f == f'
  CLetRecPolyRuntimeM a b c u r d e f == CLetRecPolyRuntimeM a' b' c' u' r' d' e' f' =
    a == a' && b == b' && c == c' && u == u' && r == r' && d == d' && e == e' && f == f'
  CLetRecGroupM telescope definitions body == CLetRecGroupM telescope' definitions' body' =
    telescope == telescope' && definitions == definitions' && body == body'
  CMeta a == CMeta a' = a == a'
  CDo a b == CDo a' b' = a == a' && b == b'
  CSealE a b == CSealE a' b' = a == a' && b == b'
  CSigT a b == CSigT a' b' = a == a' && b == b'
  CThunkE a _ == CThunkE a' _ = a == a'
  CLazyE a _ == CLazyE a' _ = a == a'
  CForceE a _ == CForceE a' _ = a == a'
  CIf a b c == CIf a' b' c' = a == a' && b == b' && c == c'
  CQuote a b == CQuote a' b' = a == a' && b == b'
  _ == _ = False

-- | A free object-language binder captured by a syntax quote (§21.4
-- hidden syntax-scope metadata): the fresh hygienic spelling used in
-- the quoted payload, the original source spelling, and the de Bruijn
-- LEVEL of the binder in the quote site's elaboration context.
data QuoteCapture = QuoteCapture
  { qcHyg :: !Text
  , qcOrig :: !Text
  , qcLevel :: !Int
  }
  deriving stock (Eq, Show, Data)

-- | The meta-phase payload of an elaborated syntax quote (§21.1):
-- surface syntax (with 'Kappa.Syntax.EQuoteHole' grafting slots for
-- in-quote splices) plus hygiene metadata and the quote's origin.
data QuotedSyntax = QuotedSyntax
  { qsExpr :: !Expr
  , qsCaptures :: ![QuoteCapture]
  , qsSpan :: !Span
  }
  deriving stock (Show, Data)

-- | Quotes compare by rendered payload and captures ('Expr' has no
-- structural equality); used only by 'Term' equality, where comparing
-- two quotes is rare and a conservative answer is sound.
instance Eq QuotedSyntax where
  a == b =
    show (qsExpr a) == show (qsExpr b)
      && qsCaptures a == qsCaptures b

-- | Match alternative over core patterns.
data CaseAlt = CaseAlt
  { caPat :: !CorePat
  , caGuard :: !(Maybe Term) -- ^ guard, under pattern binders
  , caBody :: !Term -- ^ under pattern binders (left-to-right)
  }
  deriving stock (Eq, Show, Data)

-- | One proof-producing compatibility step for a constructor branch whose
-- result indices are propositionally, but not definitionally, compatible with
-- the demanded scrutinee instance (§30.2.2.11 / §30.2.7).
--
-- Entries are dependency ordered.  Each entry is checked in the context of
-- the constructor existentials and the preceding entries, then introduces one
-- erased ordinary binder before the source-field binders.  Runtime matching
-- therefore needs only a placeholder slot, while KCore retains and
-- independently checks the proof that licenses the branch.
data ConstructorBridge
  = ConstructorForcedEquality
      { cbLeft :: !Term
      , cbRight :: !Term
      }
  | ConstructorPropositionalBridge
      { cbType :: !Term
      , cbProof :: !Term
      }
  deriving stock (Eq, Show, Data)

constructorBridgeBinderCount :: [ConstructorBridge] -> Int
constructorBridgeBinderCount =
  length . propositionalConstructorBridges

propositionalConstructorBridges
  :: [ConstructorBridge]
  -> [ConstructorBridge]
propositionalConstructorBridges =
  filter $ \case
    ConstructorPropositionalBridge {} -> True
    ConstructorForcedEquality {} -> False

-- | One source-written implicit constructor field omitted from surface
-- patterns.  The field still introduces an erased branch-local binder when a
-- constructor is eliminated.  'chbAfterExplicitFields' records its exact
-- declaration position as the number of explicit source fields preceding it;
-- several hidden fields at one position retain list order.
data ConstructorHiddenBinder = ConstructorHiddenBinder
  { chbAfterExplicitFields :: !Int
  , chbMode :: !ObservationMode
  }
  deriving stock (Eq, Show, Data)

-- | Reconstruct the source constructor telescope from explicit pattern fields
-- and the authenticated hidden-field positions carried by 'CPCtorM'.  Invalid
-- positions fail closed instead of silently choosing a different branch
-- environment order.
interleaveConstructorSourceBinders
  :: [ConstructorHiddenBinder]
  -> [a]
  -> Maybe [Either ConstructorHiddenBinder a]
interleaveConstructorSourceBinders hidden explicit
  | any invalid hidden = Nothing
  | map chbAfterExplicitFields hidden /= sort (map chbAfterExplicitFields hidden) = Nothing
  | otherwise = Just (go 0 hidden explicit)
  where
    explicitCount = length explicit
    invalid binder =
      chbAfterExplicitFields binder < 0
        || chbAfterExplicitFields binder > explicitCount
    go _ [] [] = []
    go index remaining [] =
      [Left binder | binder <- remaining, chbAfterExplicitFields binder == index]
    go index remaining (field : fields) =
      let (before, later) =
            span ((== index) . chbAfterExplicitFields) remaining
       in map Left before ++ Right field : go (index + 1) later fields

data CorePat
  = CPWild
  | CPVarM !ObservationMode !Text
  | CPLit !Literal
  | -- | A constructor pattern @C p₁ … pₖ@. The mode list describes the
    -- EXISTENTIAL
    -- GADT-index skolems the unpack binds (§17.1): @MkP : forall s. Tag s -> P@
    -- binds an existential @s@ not pinned by the result type, which the checker
    -- promotes to a rigid skolem occupying a real de Bruijn slot in the arm's
    -- elaboration context (see 'Kappa.Check.ctorFieldTypesCtx'). Those skolems sit
    -- BELOW the field binders in the de Bruijn order, so Core matching accounts
    -- for the same N erased slots UNDER the field values
    -- — otherwise every index in the arm body referring to an outer-bound variable
    -- is inflated by N with no matching Core environment slot. The placeholders are never
    -- read (a skolem is an erased type); the slots only keep the OTHER indices
    -- correct. An empty list denotes an ordinary (non-existential)
    -- constructor pattern. Per-binder modes are required because one GADT
    -- constructor may quantify over both ordinary and parametric existentials.
    -- The declaration-universe spine is the exact instantiation selected while
    -- elaborating this occurrence.  It is identity-bearing checkpoint data:
    -- later passes validate/specialize it and never reconstruct it from the
    -- scrutinee result type.
    CPCtorM
      ![ObservationMode]
      ![ConstructorBridge]
      ![ConstructorHiddenBinder]
      !GName
      ![Level]
      ![CorePat]
  | CPTuple ![CorePat]
  | CPRecordM ![(Text, CorePat)] !(Maybe (ObservationMode, Text))
  -- ^ fields, optional rest binder (binds the remaining fields; @Just ""@
  -- discards them)
  | CPInject !Text !CorePat -- ^ variant member pattern
  | CPInjectRestM !ObservationMode ![Text] -- ^ residual-row pattern: excluded tags
  | -- | An or-pattern @p₁ | … | pₖ@ (§17.2.3). All alternatives bind the same
    -- set of names; the BODY uses the first alternative's binder order
    -- (canonical). The parallel @[[Int]]@ holds, per alternative, the
    -- permutation from that alternative's own structural binder order to the
    -- canonical order: when alternative @i@ matches and yields bindings @bs@
    -- (structural order), the canonical bindings are @[bs !! (perm!!j)]@. This
    -- keeps the body's de Bruijn layout correct no matter which alternative
    -- matched, even when alternatives list the shared binders in different
    -- positions (e.g. @A p q | B q p@).
    CPOr ![CorePat] ![[Int]]
  | CPAsM !ObservationMode !Text !CorePat -- ^ as-pattern: binds the whole value, then inner
  deriving stock (Eq, Show, Data)

-- | do-kernel items (typed during elaboration, executed by Interp).
data KItem
  = KBind !Q !CorePat !Term !(Maybe RefActionWitness) -- ^ let pat <- e
  | KLet !Q !CorePat !Term -- ^ let pat = e
  | KLetQ !CorePat !Term !(Maybe (CorePat, Term)) -- ^ let? with optional else
  | KExpr !Term
  | KVarItem !Text !Term !Term !(Maybe RefActionWitness) -- ^ name, initializer value, MonadRef.newRef action
  | KAssign !Term !Bool !Term !Term !(Maybe RefActionWitness) -- ^ ref-term, monadic?, rhs, MonadRef.writeRef action
  | KReturn !Term
  | KBreak !(Maybe Text)
  | KContinue !(Maybe Text)
  | KWhile !(Maybe Text) !KCond ![KItem] !(Maybe [KItem])
  | KFor !(Maybe Text) !CorePat !Term ![KItem] !(Maybe [KItem])
  | KIf ![(Term, [KItem])] !(Maybe [KItem])
  | KDefer !(Maybe Text) !Term -- ^ defer (Nothing) / defer@label (§18.7)
  | KUsing !CorePat !Term !Term -- ^ pattern, acquire, release-dict-member
  | -- | A nested @do@ block written in statement position (§18.8.3.1): it runs
    -- as a child scope — its own optional label, bindings, and LIFO exit
    -- actions — but it is TRANSPARENT to abrupt completion, so a @break@ /
    -- @continue@ / @return\@L@ inside it that targets an enclosing loop or
    -- function (resolved against the inherited lexical context) propagates
    -- outward. Distinct from a first-class @do@ VALUE (e.g. @let x = do …@),
    -- which is an opaque computation reached through 'KExpr'/'KBind'.
    KSubDo !(Maybe Text) ![KItem]
  deriving stock (Eq, Show, Data)

-- | A while condition is either the ordinary pure Bool condition, or the
-- §18.6 monadic condition action that must be run again for every test.
data KCond
  = KCondPure !Term
  | KCondAction !Term
  deriving stock (Eq, Show, Data)

data TelescopeEntry = TelescopeEntry
  { teIcit :: !Icit
  , teMode :: !ObservationMode
  , teFormation :: !FormationMode
  , teQ :: !Q
  , teBorrow :: !Bool
  , teName :: !Text
  , teDomain :: !Term
  , teLevelAssumption :: !(Maybe (Level, Level))
  }
  deriving stock (Eq, Show, Data)

type Telescope = [TelescopeEntry]

-- ── Values (NbE domain) ──────────────────────────────────────────────

type Env = [Value]

-- | Application spine of a neutral value.
type Spine = [(Icit, Value)]

data Closure = Closure !Env !Term
  deriving stock (Show)

-- | The result of evaluating a 'Term' ('Kappa.Eval'). The first three are
-- the /neutral heads/: a head that can't reduce yet (a variable, an unsolved
-- meta, or an unfolded-elsewhere global) applied to a 'Spine' of arguments.
-- They are how evaluation represents "stuck" computation; the stuck
-- /eliminators/ 'VMatchN', 'VProjN', and 'VIfN' (a match\/projection\/if on
-- a neutral) are neutral too. The distinction between 'VRigid' (a real
-- variable — stuck for good until substituted) and 'VFlex' (a meta — could
-- still reduce once the meta is solved) is what unification keys off.
data Value
  = VRigid !Int !Spine -- ^ neutral: a bound variable as a de Bruijn /level/ (0 = outermost) + its args
  | VFlex !MetaId !Spine -- ^ neutral: an unsolved metavariable + its args
  | VGlobal !GName ![Level] !Spine -- ^ neutral global plus hidden universe instantiation
  | VLamM !ObservationMode !Icit !Q !Text !Closure
  | VPiRuntimeM !ObservationMode !FormationMode !Icit !Q !Bool !Text !(Maybe (Level, Level)) !BinderOrigin !(RuntimeErasure Value) !Value !Closure
    -- ^ Semantic Pi carrying the same checked level-assumption authority as
    -- 'CPiEvidenceM'. 'Bool' is the binder borrow marker (§12.3).
  | VSort !Level
  | VLevel !Level
  | VUniverseLift !Level !Level !UniverseEvidence !Value
    -- ^ Proof-carrying semantic universe lift. It is transparent to
    -- conversion and forcing, but quotation retains it so dependent
    -- substitution and inferred-type readback do not erase the explicit
    -- cumulative-use node required at KCore checkpoints (§30.2.1A).
  | VArithmeticProof !(ArithmeticCertificate Value)
  | VLit !Literal
  | VCtorI !GName ![Level] ![ConstructorValueArg]
  | VRecordTQ ![RecordField Value]
  | VRecordV ![(Text, Value)]
  | VVariantT ![Value]
  | VInject !Text !Value
  | VMatchN !Value !(Maybe Value) !(Maybe Value) ![CaseAlt] !Env
    -- ^ stuck match retaining its checked scrutinee and result types
  | VProjN !ObservationMode !Value !Text -- ^ stuck projection with its checked field mode
  | VAppN !Icit !Value !Value -- ^ stuck application preserving its typed application shape
  | VSealV ![Text] !Value -- ^ §13.2.10 sealed package (opaque member projections stick)
  | VSigT ![Text] !Value -- ^ §13.2.10 signature type (opaque labels + record type)
  | VDoV !(Maybe Text) ![KItem] !Env -- ^ suspended do block (optional scope label, §18.7)
  | VThunkV !Closure
  | VLazyV !Closure
  | VIfN !Value !Closure !Closure -- ^ stuck if
  | VPrim !Text ![Value] -- ^ builtin primitive, partially applied
  | VRef !(IORef Value) -- ^ runtime mutable cell (MonadRef, §18.6.1)
  | VArr !Int !(IOArray Int Value) -- ^ MUTABLE-ARRAY-DESIGN: boxed mutable O(1) array (K_ARRAY oracle); fixed length (cached, so arrayLen is pure) + in-place get/set
  | VMVar !(MVar Value) -- ^ §18.11 one-shot-promise cell (blocking read parks the fiber)
  | VFiber !ThreadId !(MVar Value) -- ^ §18.1.4 fiber handle: interrupt target (ThreadId) + terminal-Exit cell
  | VScope !(IORef [Value]) -- ^ §18.1.8 explicit supervision scope: registry of attached fibers
  | VFiberRef !Int -- ^ §18.1.7 fiber-local cell identity (per-fiber values live in the runtime registry)
  | VTVar !(TVar Value) -- ^ §18.1.13 STM transactional variable
  | VIOAction !Text ![Value] -- ^ suspended IO primitive application
  | VQuote !QuotedSyntax ![Value] -- ^ §21.1 syntax value: payload + slot values (grafted lazily)

instance Show Value where
  show _ = "<value>"

-- | Compatibility view for consumers that do not need field quantities.
-- New elaboration sites that own source field declarations must construct
-- 'CRecordTQ'/'VRecordTQ' directly so capability information is not erased.
pattern CRecordT :: [(Text, Term)] -> Term
pattern CRecordT fs <- CRecordTQ (recordFieldPairs -> fs)
  where
    CRecordT fs = CRecordTQ [RecordField n Ordinary FormationOrdinary QW Nothing RuntimeRelevant t | (n, t) <- fs]

pattern VRecordT :: [(Text, Value)] -> Value
pattern VRecordT fs <- VRecordTQ (recordFieldPairs -> fs)
  where
    VRecordT fs = VRecordTQ [RecordField n Ordinary FormationOrdinary QW Nothing RuntimeRelevant t | (n, t) <- fs]

-- | Compatibility view for global references. Pattern matches preserve the
-- semantic global identity while clients that need declaration-universe
-- instances use 'CGlobI'/'VGlobI'. New polymorphic references must construct
-- the explicit forms.
pattern CGlob :: GName -> Term
pattern CGlob g <- CGlobal g _
  where
    CGlob g = CGlobal g []

pattern CGlobI :: GName -> [Level] -> Term
pattern CGlobI g universes = CGlobal g universes

-- | Compatibility constructor/view for an ordinary runtime-relevant
-- application.  Semantic consumers that need the selected calling
-- convention must use 'CAppRuntime'.
pattern CApp :: Icit -> Term -> Term -> Term
pattern CApp ic function argument <- CAppM ic _ function argument
  where
    CApp ic function argument = CAppM ic RuntimeRelevant function argument

-- | Complete application view retaining occurrence-local erasure evidence.
pattern CAppRuntime :: Icit -> RuntimeErasure Term -> Term -> Term -> Term
pattern CAppRuntime ic runtimeErasure function argument =
  CAppM ic runtimeErasure function argument

pattern VGlobN :: GName -> Spine -> Value
pattern VGlobN g spine <- VGlobal g _ spine
  where
    VGlobN g spine = VGlobal g [] spine

pattern VGlobI :: GName -> [Level] -> Spine -> Value
pattern VGlobI g universes spine = VGlobal g universes spine

-- | Payload compatibility view for constructor values.  Primitive and test
-- producers may construct monomorphic payload-only values; typed evaluation
-- uses 'VCtorI' so quoting can reproduce the complete constructor occurrence.
pattern VCtor :: GName -> [Value] -> Value
pattern VCtor constructor payload <-
  VCtorI constructor _ (constructorPayloadValues -> payload)
  where
    VCtor constructor payload =
      VCtorI constructor []
        [ConstructorValueArg Expl True Nothing argument | argument <- payload]

constructorPayloadValues :: [ConstructorValueArg] -> [Value]
constructorPayloadValues arguments =
  [cvaValue argument | argument <- arguments, cvaPayload argument]

-- | Payload compatibility view used by evaluator/runtime analyses and by
-- synthetic monomorphic constructors. Typed constructor production uses
-- 'CCtorI' directly so erased arguments and universe instantiations survive to
-- KCoreText.
pattern CCtor :: GName -> Maybe Term -> [Term] -> Term
pattern CCtor constructor annotation payload <-
  CCtorI constructor _ annotation (constructorPayloadTerms -> payload)
  where
    CCtor constructor annotation payload =
      CCtorI constructor [] annotation
        [ConstructorArg Expl True Nothing argument | argument <- payload]

constructorPayloadTerms :: [ConstructorArg] -> [Term]
constructorPayloadTerms arguments = [caTerm argument | argument <- arguments, caPayload argument]

-- Read-only views for analyses where observation mode is provably irrelevant.
-- KCore producers must construct 'CLamM' and one of the formed Pi constructors
-- explicitly.
pattern CLam :: Icit -> Q -> Text -> Term -> Term
pattern CLam ic q n body <- CLamM _ ic q n body

-- | Read-only compatibility view for Pi binders that introduce no level
-- assumption. Formation is independent evidence and therefore cannot be
-- reconstructed from observation mode by a compatibility constructor.
pattern CPiM :: ObservationMode -> Icit -> Q -> Bool -> Text -> Term -> Term -> Term
pattern CPiEvidenceM :: ObservationMode -> FormationMode -> Icit -> Q -> Bool -> Text -> Maybe (Level, Level) -> BinderOrigin -> Term -> Term -> Term
pattern CPiEvidenceM mode formation ic q borrowed name assumption origin domain codomain <-
  CPiRuntimeM mode formation ic q borrowed name assumption origin _ domain codomain
  where
    CPiEvidenceM mode formation ic q borrowed name assumption origin domain codomain =
      CPiRuntimeM mode formation ic q borrowed name assumption origin RuntimeRelevant domain codomain

pattern CPiM mode ic q borrowed name domain codomain <-
  CPiRuntimeM mode _ ic q borrowed name _ _ _ domain codomain

pattern CPiBoundM :: ObservationMode -> Icit -> Q -> Bool -> Text -> Maybe (Level, Level) -> Term -> Term -> Term
pattern CPiBoundM mode ic q borrowed name assumption domain codomain <-
  CPiRuntimeM mode _ ic q borrowed name assumption _ _ domain codomain

pattern CPiFormedM :: ObservationMode -> FormationMode -> Icit -> Q -> Bool -> Text -> Term -> Term -> Term
pattern CPiFormedM mode formation ic q borrowed name domain codomain <-
  CPiRuntimeM mode formation ic q borrowed name _ _ _ domain codomain
  where
    CPiFormedM mode formation ic q borrowed name domain codomain =
      CPiEvidenceM mode formation ic q borrowed name Nothing BinderSourceWritten domain codomain

pattern CPiBoundFormedM :: ObservationMode -> FormationMode -> Icit -> Q -> Bool -> Text -> Maybe (Level, Level) -> Term -> Term -> Term
pattern CPiBoundFormedM mode formation ic q borrowed name assumption domain codomain =
  CPiEvidenceM mode formation ic q borrowed name assumption BinderSourceWritten domain codomain

pattern CPi :: Icit -> Q -> Bool -> Text -> Term -> Term -> Term
pattern CPi ic q borrowed n dom cod <- CPiM _ ic q borrowed n dom cod

pattern CProj :: Term -> Text -> Term
pattern CProj value field <- CProjM _ value field

pattern CProjAt :: Term -> Text -> Int -> Term
pattern CProjAt value field index <- CProjAtM _ value field index

-- | Compatibility observers for clients that do not inspect local erasure
-- authority. They are intentionally unidirectional: Core producers must
-- construct the evidence-bearing nodes explicitly.
pattern CLetM :: ObservationMode -> Q -> Text -> Term -> Term -> Term -> Term
pattern CLetM mode quantity name ty rhs body <-
  CLetRuntimeM mode quantity name _ ty rhs body

pattern CLetRecM :: ObservationMode -> Q -> Text -> Term -> Term -> Term -> Term
pattern CLetRecM mode quantity name ty rhs body <-
  CLetRecRuntimeM mode quantity name _ ty rhs body

pattern CLetPolyM :: ObservationMode -> Q -> Text -> DeclarationUniverseTelescope -> Term -> Term -> Term -> Term
pattern CLetPolyM mode quantity name telescope ty rhs body <-
  CLetPolyRuntimeM mode quantity name telescope _ ty rhs body

pattern CLetRecPolyM :: ObservationMode -> Q -> Text -> DeclarationUniverseTelescope -> Term -> Term -> Term -> Term
pattern CLetRecPolyM mode quantity name telescope ty rhs body <-
  CLetRecPolyRuntimeM mode quantity name telescope _ ty rhs body

pattern CLet :: Q -> Text -> Term -> Term -> Term -> Term
pattern CLet q name ty rhs body <- CLetM _ q name ty rhs body

pattern CLetRec :: Q -> Text -> Term -> Term -> Term -> Term
pattern CLetRec q name ty rhs body <- CLetRecM _ q name ty rhs body

pattern CPVar :: Text -> CorePat
pattern CPVar name <- CPVarM _ name

pattern CPCtor :: GName -> Int -> [CorePat] -> CorePat
pattern CPCtor constructor erasedBinderCount fields <-
  (viewConstructorPattern -> Just (constructor, erasedBinderCount, fields))

viewConstructorPattern :: CorePat -> Maybe (GName, Int, [CorePat])
viewConstructorPattern = \case
  CPCtorM existentials bridges hidden constructor _ fields ->
    Just
      ( constructor
      , length existentials
          + constructorBridgeBinderCount bridges
          + length hidden
      , fields
      )
  _ -> Nothing

pattern CPRecord :: [(Text, CorePat)] -> Maybe Text -> CorePat
pattern CPRecord fields rest <- CPRecordM fields (patternRestName -> rest)

pattern CPInjectRest :: [Text] -> CorePat
pattern CPInjectRest excluded <- CPInjectRestM _ excluded

pattern CPAs :: Text -> CorePat -> CorePat
pattern CPAs name inner <- CPAsM _ name inner

pattern VLam :: Icit -> Q -> Text -> Closure -> Value
pattern VLam ic q n body <- VLamM _ ic q n body

pattern VPiM :: ObservationMode -> Icit -> Q -> Bool -> Text -> Value -> Closure -> Value
pattern VPiEvidenceM :: ObservationMode -> FormationMode -> Icit -> Q -> Bool -> Text -> Maybe (Level, Level) -> BinderOrigin -> Value -> Closure -> Value
pattern VPiEvidenceM mode formation ic q borrowed name assumption origin domain codomain <-
  VPiRuntimeM mode formation ic q borrowed name assumption origin _ domain codomain
  where
    VPiEvidenceM mode formation ic q borrowed name assumption origin domain codomain =
      VPiRuntimeM mode formation ic q borrowed name assumption origin RuntimeRelevant domain codomain

pattern VPiM mode ic q borrowed name domain codomain <-
  VPiRuntimeM mode _ ic q borrowed name _ _ _ domain codomain

pattern VPiBoundM :: ObservationMode -> Icit -> Q -> Bool -> Text -> Maybe (Level, Level) -> Value -> Closure -> Value
pattern VPiBoundM mode ic q borrowed name assumption domain codomain <-
  VPiRuntimeM mode _ ic q borrowed name assumption _ _ domain codomain

pattern VPiFormedM :: ObservationMode -> FormationMode -> Icit -> Q -> Bool -> Text -> Value -> Closure -> Value
pattern VPiFormedM mode formation ic q borrowed name domain codomain <-
  VPiRuntimeM mode formation ic q borrowed name _ _ _ domain codomain
  where
    VPiFormedM mode formation ic q borrowed name domain codomain =
      VPiEvidenceM mode formation ic q borrowed name Nothing BinderSourceWritten domain codomain

pattern VPiBoundFormedM :: ObservationMode -> FormationMode -> Icit -> Q -> Bool -> Text -> Maybe (Level, Level) -> Value -> Closure -> Value
pattern VPiBoundFormedM mode formation ic q borrowed name assumption domain codomain =
  VPiEvidenceM mode formation ic q borrowed name assumption BinderSourceWritten domain codomain

pattern VPi :: Icit -> Q -> Bool -> Text -> Value -> Closure -> Value
pattern VPi ic q borrowed n dom cod <- VPiM _ ic q borrowed n dom cod

patternRestName :: Maybe (ObservationMode, Text) -> Maybe Text
patternRestName = fmap snd

{-# COMPLETE CPWild, CPVar, CPLit, CPCtor, CPTuple, CPRecord, CPInject,
  CPInjectRest, CPOr, CPAs #-}

{-# COMPLETE CVar, CLocal, CGlob, CLam, CPiBoundM, CApp, CSort, CLevel, CUniverseLift, CSchemaLift, CLit,
  CCtor, CMatch, CRecordT, CRecordV, CProj, CProjAt, CVariantT, CInject,
  CLet, CLetRec, CLetPolyM, CLetRecPolyM, CLetRecGroupM, CMeta, CDo, CSealE, CSigT, CThunkE, CLazyE, CForceE,
  CIf, CQuote #-}

-- Total traversals that preserve all typed metadata should match the real
-- constructors rather than a compatibility view. This COMPLETE set prevents
-- GHC from selecting one of the lossy read-only pattern-synonym sets above.
{-# COMPLETE CVar, CLocal, CGlobal, CLamM, CPiRuntimeM, CApp, CSort, CLevel,
  CUniverseLift, CSchemaLift, CArithmeticProof, CLit, CCtorI, CMatch, CRecordTQ, CRecordV, CProjM, CProjAtM,
  CVariantT, CInject, CLetRuntimeM, CLetRecRuntimeM, CLetPolyRuntimeM, CLetRecPolyRuntimeM, CLetRecGroupM, CMeta, CDo, CSealE, CSigT, CThunkE,
  CLazyE, CForceE, CIf, CQuote #-}

{-# COMPLETE CVar, CLocal, CGlob, CLam, CPiM, CApp, CSort, CLevel, CUniverseLift, CSchemaLift, CArithmeticProof, CLit,
  CCtor, CMatch, CRecordT, CRecordV, CProj, CProjAt, CVariantT, CInject,
  CLet, CLetRec, CLetPolyM, CLetRecPolyM, CLetRecGroupM, CMeta, CDo, CSealE, CSigT, CThunkE, CLazyE, CForceE,
  CIf, CQuote #-}

{-# COMPLETE CVar, CLocal, CGlob, CLam, CPi, CApp, CSort, CLevel, CUniverseLift, CSchemaLift, CArithmeticProof, CLit,
  CCtor, CMatch, CRecordT, CRecordV, CProj, CProjAt, CVariantT, CInject,
  CLet, CLetRec, CLetPolyM, CLetRecPolyM, CLetRecGroupM, CMeta, CDo, CSealE, CSigT, CThunkE, CLazyE, CForceE,
  CIf, CQuote #-}

{-# COMPLETE VRigid, VFlex, VGlobN, VLam, VPiBoundM, VSort, VLevel, VArithmeticProof, VLit, VCtor,
  VRecordT, VRecordV, VVariantT, VInject, VMatchN, VProjN, VAppN, VSealV,
  VSigT, VDoV, VThunkV, VLazyV, VIfN, VPrim, VRef, VArr, VMVar,
  VFiber, VScope, VFiberRef, VTVar, VIOAction, VQuote #-}

{-# COMPLETE VRigid, VFlex, VGlobal, VLamM, VPiRuntimeM, VSort, VLevel, VArithmeticProof, VLit,
  VCtorI, VRecordTQ, VRecordV, VVariantT, VInject, VMatchN, VProjN, VAppN, VSealV,
  VSigT, VDoV, VThunkV, VLazyV, VIfN, VPrim, VRef, VArr, VMVar, VFiber,
  VScope, VFiberRef, VTVar, VIOAction, VQuote #-}

{-# COMPLETE VRigid, VFlex, VGlobN, VLam, VPiM, VSort, VLevel, VArithmeticProof, VLit, VCtor,
  VRecordT, VRecordV, VVariantT, VInject, VMatchN, VProjN, VAppN, VSealV,
  VSigT, VDoV, VThunkV, VLazyV, VIfN, VPrim, VRef, VArr, VMVar,
  VFiber, VScope, VFiberRef, VTVar, VIOAction, VQuote #-}

{-# COMPLETE VRigid, VFlex, VGlobN, VLam, VPi, VSort, VLevel, VArithmeticProof, VLit, VCtor,
  VRecordT, VRecordV, VVariantT, VInject, VMatchN, VProjN, VAppN, VSealV,
  VSigT, VDoV, VThunkV, VLazyV, VIfN, VPrim, VRef, VArr, VMVar,
  VFiber, VScope, VFiberRef, VTVar, VIOAction, VQuote #-}

recordFieldPairs :: [RecordField a] -> [(Text, a)]
recordFieldPairs = map (\RecordField {..} -> (rfName, rfType))
