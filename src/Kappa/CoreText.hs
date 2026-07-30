{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Canonical KCoreText schema 1 (Spec §30.2.0A).
--
-- This module is a trust boundary. Parsing reconstructs only explicit facts;
-- it performs no name lookup, mode/default inference, implicit insertion, or
-- universe solving. 'verifyKCoreText' then checks identities, scopes,
-- modalities, universe constraints, and lift evidence before a unit is
-- accepted.
module Kappa.CoreText
  ( KCoreFile
  , KCoreInterface
  , KCoreTextError (..)
  , KCoreDataInfo (..)
  , KCoreConstructorInfo (..)
  , parseKCoreText
  , verifyKCoreText
  , verifyKCoreTextWithGlobals
  , parseAndVerifyKCoreText
  , parseAndVerifyKCoreTextWithGlobals
  , parseAndVerifyKCoreTextWithEnvironment
  , parseAndVerifyKCoreInterface
  , parseAndVerifyKCoreInterfaceWithInterfaces
  , verifyKCoreTextWithInterfaces
  , printCanonicalKCoreText
  , semanticHashKCoreText
  , kcoreArithmeticCertificateCount
  , kcoreRepresentationCertificateCount
  , kcoreHasValidSchemaCertificate
  , kcoreLevelCertificateDependencies
  , kcoreNominalRoles
  , renderKCoreModule
  ) where

import Control.Applicative ((<|>))
import Control.Monad ((<=<), foldM, forM, forM_, guard, unless, when, zipWithM, zipWithM_)
import Control.Monad.State.Strict (State, StateT, evalState, evalStateT, execState, get, gets, modify', put, runStateT)
import Control.Monad.Trans.Class (lift)
import qualified Data.ByteString as BS
import Data.Char (chr, isAlpha, isAlphaNum, isDigit, isHexDigit, ord)
import Data.Data (Data, dataTypeName, dataTypeOf, fromConstrM, gmapQ, readConstr, showConstr, toConstr)
import Data.Function (on)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (find, nub, nubBy, sort, sortOn, zip4)
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe, mapMaybe, maybeToList)
import Data.Ord (Down (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Typeable (cast)
import Data.Word (Word8)
import Kappa.Arithmetic
  ( ACmp (..)
  , AExpr (..)
  , AFact (..)
  , AFormula (..)
  , ArithmeticNormalForm (..)
  , ArithmeticProofRule (..)
  , ArithmeticReplay (..)
  , ArithmeticFormulaReplay (..)
  , ArithmeticAssumptionCaseReplay (..)
  , ArithmeticSemantics (..)
  , PrimitiveComparisonDomain (..)
  , decodePrimitiveComparisonOperand
  , deriveArithmeticFormulaReplayWithAssumptions
  , negateFact
  , reindexArithmeticFormula
  )
import Kappa.Builtins
  ( associatedStaticCarrierGlobals
  , gPrel
  , prelAnd
  , prelBool
  , prelByte
  , prelCompareTypeLevel
  , prelDouble
  , prelEff
  , prelEffLabel
  , prelEffOp
  , prelEffPure
  , prelEffRowCons
  , prelEffRowNil
  , prelEqType
  , prelFalse
  , prelFin
  , prelGrapheme
  , prelInt
  , prelInteger
  , prelIsTraitWitness
  , prelList
  , prelLT
  , prelMonotone
  , prelNat
  , prelNatAdd
  , prelNatCompare
  , prelNatMultiply
  , prelNatSucc
  , prelNatZero
  , prelOrd
  , prelOrdering
  , prelOr
  , prelEQ
  , prelGT
  , prelString
  , prelSubst
  , prelSyntax
  , prelTraitSubsingletonWitness
  , prelThis
  , prelThunk
  , prelTrue
  , prelNot
  , prelNeed
  , prelTypeLevel
  , prelTypeLevelAdd
  , prelTypeLevelFromInteger
  , prelTypeLevelMax
  , prelTypeLevelOmega
  , prelTypeLevelOne
  , prelTypeLevelSucc
  , prelTypeLevelZero
  , prelUnicodeScalar
  , prelUnit
  )
import Kappa.Core
import Kappa.CoreOps
  ( declarationUniverseConstraints
  , foldTerm
  , globalsOfTerm
  , levelParamsOfTerm
  , shiftTerm
  , substGlobal
  , substTopTermAt
  , zonkTermWith
  )
import Kappa.Eval (EvalCtx, GlobalDef (..), eval, evalApp, force, quote)
import Kappa.Level
  ( Assumptions
  , SolveResult (..)
  , assumptionsConsistent
  , emptyAssumptions
  , insertAssumption
  , instantiateLocalLevelParams
  , levelFields
  , proveLevelEq
  , levelVars
  , normalizeLevel
  , compareClosedLevel
  , proveLevelLeq
  , renderLevel
  , substituteLevelParams
  )
import Kappa.Termination (canonicalTrustedIntPrimitive)
import Kappa.LevelEvidence
  ( coreTypeIsTypeLevel
  , scopeRecordFields
  , scopeRecordLevelAssumption
  )
import Kappa.Source (ModuleName (..), Pos (..), Span (..))
import Kappa.NominalVariance
  ( NominalClauseKind (..)
  , NominalCumulativitySummary (..)
  , NominalEvidenceDependency (..)
  , NominalMonotoneWitness (..)
  , NominalSignatureClosure (..)
  , RoleRequirement (..)
  , TypeLevelSemanticVersions (..)
  , currentTypeLevelSemanticVersions
  , inferUniverseRoles
  , verifyNominalCumulativitySummary
  )
import Kappa.SemanticHash (canonicalIdentityHex, sha256Hex)
import Kappa.Syntax (Expr (EQuoteHole), Name (nameText))
import Kappa.SyntaxOps (boundNamesIn, freeVarOccurrences, queryExprs)
import Kappa.TypeTag (semanticTypeTag)
import Numeric (showHex)
import Text.Read (readMaybe)

globalCoreType :: EvalCtx -> GlobalDef -> Term
globalCoreType ec definition =
  fromMaybe (quote ec 0 (gdType definition)) (gdCoreType definition)

familyCoreParameterCount :: EvalCtx -> Map GName GlobalDef -> GName -> Maybe Int
familyCoreParameterCount ec globals family = do
  definition <- Map.lookup family globals
  pure (length (fst (splitCorePiTelescope (globalCoreType ec definition))))

data KCoreTextError = KCoreTextError
  { kcteCode :: !Text
  , kcteMessage :: !Text
  }
  deriving stock (Eq, Show)

-- | Authoritative declaration facts supplied by the typed checkpoint when a
-- generated unit is serialized or verified against imported declarations.
-- KCoreText never reconstructs these facts from readable names.
data KCoreDataInfo = KCoreDataInfo
  { kcdiConstructors :: ![GName]
  , kcdiParameterCount :: !Int
  }
  deriving stock (Eq, Show)

data KCoreConstructorInfo = KCoreConstructorInfo
  { kcciData :: !GName
  , kcciUniverses :: !DeclarationUniverseTelescope
  , kcciType :: !Term
  , kcciSourceFields :: ![(Icit, Maybe Text)]
  -- ^ The complete source field telescope, including named implicit proof
  -- fields. Core constructor patterns contain only explicit source fields;
  -- KCore case alternatives retain this full telescope so their binder and
  -- projection indices agree with the semantic constructor declaration.
  }
  deriving stock (Eq, Show)

data StableRef = StableRef
  { srName :: !Text
  , srId :: !Text
  }
  deriving stock (Show)

-- Readable names are presentation metadata. The stable id is the complete
-- semantic identity used by maps, ordering, typechecking, and hashing.
instance Eq StableRef where
  left == right = srId left == srId right

instance Ord StableRef where
  compare left right = compare (srId left) (srId right)

data LocalRef = LocalRef
  { lrName :: !Text
  , lrId :: !Int
  }
  deriving stock (Show)

-- Local and universe names are presentation metadata just like the readable
-- component of 'StableRef'. Canonicalization may rename a binder without
-- changing references to its identity; substitution, scope, ordering, and
-- semantic equality must therefore use the numeric identity alone.
instance Eq LocalRef where
  left == right = lrId left == lrId right

instance Ord LocalRef where
  compare left right = compare (lrId left) (lrId right)

data UniverseRef = UniverseRef
  { urName :: !Text
  , urId :: !Int
  }
  deriving stock (Show)

instance Eq UniverseRef where
  left == right = urId left == urId right

instance Ord UniverseRef where
  compare left right = compare (urId left) (urId right)

data KLevel
  = KLFinite !Integer
  | KLGlobal !StableRef
  | KLUniverse !UniverseRef
  | KLSucc !KLevel
  | KLMax !KLevel !KLevel
  | KLAdd !KLevel !KLevel
  | KLTerm !KTerm
  deriving stock (Eq, Ord, Show)

data KQuantity = KQ0 | KQ1 | KQOmega | KQAffine | KQRelevant | KQTerm !KTerm
  deriving stock (Eq, Ord, Show)

data KExplicitness = KExplicit | KImplicit
  deriving stock (Eq, Ord, Show)

data KAccess = KValue | KBorrow !(Maybe KRef)
  deriving stock (Eq, Ord, Show)

data KRef = KRLocal !LocalRef | KRGlobal !StableRef
  deriving stock (Eq, Ord, Show)

data KBinder = KBinder
  { kbMode :: !ObservationMode
  , kbFormation :: !FormationMode
  , kbQuantity :: !KQuantity
  , kbExplicitness :: !KExplicitness
  , kbAccess :: !KAccess
  , kbOrigin :: !BinderOrigin
  , kbRef :: !LocalRef
  , kbType :: !KTerm
  }
  deriving stock (Eq, Ord, Show)

data KEvidence
  = KELocal !LocalRef
  | KEGlobal !StableRef ![KLevel]
  | KECertificate !StableRef ![KLevel]
  deriving stock (Eq, Ord, Show)

data KArgument = KArgument !KExplicitness !KTerm
  deriving stock (Eq, Ord, Show)

data KValueNode
  = KVTerm !KTerm
  | KVLevel !KLevel
  | KVQuantity !KQuantity
  | KVObservationMode !ObservationMode
  | KVExplicitness !KExplicitness
  | KVAccess !KAccess
  | KVGlobal !StableRef ![KLevel]
  | KVLocal !LocalRef ![KLevel]
  | KVBinder !KBinder
  | KVPattern !KPattern
  | KVText !Text
  | KVInteger !Integer
  | KVList ![KValueNode]
  deriving stock (Eq, Ord, Show)

-- | The version-1 structural syntax interchange used by 'CQuote'. Constructor
-- labels in this codec are frozen KCoreText schema tokens: changing a Haskell
-- syntax constructor requires an explicit schema migration/version bump.
-- Source file paths are deliberately excluded from embedded spans so moving a
-- source tree cannot change semantic hashes.
syntaxDataValue :: Data a => a -> KValueNode
syntaxDataValue value =
  case cast value :: Maybe Span of
    Just (Span _ (Pos startLine startColumn) (Pos endLine endColumn)) ->
      atom "span"
        [ KVInteger (toInteger startLine)
        , KVInteger (toInteger startColumn)
        , KVInteger (toInteger endLine)
        , KVInteger (toInteger endColumn)
        ]
    Nothing -> case cast value :: Maybe Text of
      Just textValue -> atom "text" [KVText textValue]
      Nothing -> case cast value :: Maybe Int of
        Just intValue -> atom "int" [KVInteger (toInteger intValue)]
        Nothing -> case cast value :: Maybe Integer of
          Just integerValue -> atom "integer" [KVInteger integerValue]
          Nothing -> case cast value :: Maybe Word8 of
            Just byteValue -> atom "word8" [KVInteger (toInteger byteValue)]
            Nothing -> case cast value :: Maybe Double of
              Just doubleValue -> atom "double" [KVText (T.pack (show doubleValue))]
              Nothing -> case cast value :: Maybe Char of
                Just charValue -> atom "char" [KVInteger (toInteger (ord charValue))]
                Nothing ->
                  atom
                    "constructor"
                    [ KVText (T.pack (dataTypeName (dataTypeOf value)))
                    , KVText (T.pack (showConstr (toConstr value)))
                    , KVList (gmapQ syntaxDataValue value)
                    ]
  where
    atom tag payload = KVList (KVText "kappa-syntax-v1" : KVText tag : payload)

decodeSyntaxData :: forall a. Data a => KValueNode -> Either KCoreTextError a
decodeSyntaxData encoded =
  case encoded of
    KVList [KVText "kappa-syntax-v1", KVText "span", KVInteger sl, KVInteger sc, KVInteger el, KVInteger ec]
      | all validPosition [sl, sc, el, ec] ->
          castDecoded
            ( Span "<kcore-syntax>"
                (Pos (fromInteger sl) (fromInteger sc))
                (Pos (fromInteger el) (fromInteger ec))
            )
      | otherwise -> malformed "syntax span position is outside the target range"
    KVList [KVText "kappa-syntax-v1", KVText "text", KVText value] -> castDecoded value
    KVList [KVText "kappa-syntax-v1", KVText "int", KVInteger value]
      | let decoded = fromInteger value :: Int
      , toInteger decoded == value -> castDecoded decoded
      | otherwise -> malformed "syntax Int leaf is outside the target range"
    KVList [KVText "kappa-syntax-v1", KVText "integer", KVInteger value] -> castDecoded value
    KVList [KVText "kappa-syntax-v1", KVText "word8", KVInteger value]
      | value >= 0 && value <= 255 -> castDecoded (fromInteger value :: Word8)
      | otherwise -> malformed "syntax Word8 leaf is outside 0..255"
    KVList [KVText "kappa-syntax-v1", KVText "double", KVText value] ->
      maybe (malformed "syntax Double leaf is malformed") castDecoded
        (readMaybe (T.unpack value) :: Maybe Double)
    KVList [KVText "kappa-syntax-v1", KVText "char", KVInteger value]
      | value >= 0 && value <= 0x10ffff -> castDecoded (chr (fromInteger value))
      | otherwise -> malformed "syntax Char leaf is outside the Unicode range"
    KVList [KVText "kappa-syntax-v1", KVText "constructor", KVText typeName, KVText constructorName, KVList children] -> do
      let expectedType = dataTypeOf (undefined :: a)
      unless (typeName == T.pack (dataTypeName expectedType)) $
        malformed
          ( "syntax constructor belongs to " <> typeName
              <> ", expected " <> T.pack (dataTypeName expectedType)
          )
      constructor <- maybe
        (malformed ("unknown syntax constructor '" <> constructorName <> "'"))
        pure
        (readConstr expectedType (T.unpack constructorName))
      (decoded, remaining) <- runStateT (fromConstrM nextField constructor) children
      unless (null remaining) $
        malformed ("syntax constructor '" <> constructorName <> "' has excess fields")
      pure decoded
    _ -> malformed "malformed structural syntax value"
  where
    malformed = Left . invalid
    validPosition value =
      let decoded = fromInteger value :: Int
       in value >= 0 && toInteger decoded == value
    castDecoded :: forall b. (Data b) => b -> Either KCoreTextError a
    castDecoded value =
      maybe
        (malformed "syntax primitive wrapper does not match its expected field type")
        pure
        (cast value)
    nextField :: forall b. Data b => StateT [KValueNode] (Either KCoreTextError) b
    nextField = do
      remaining <- get
      case remaining of
        [] -> lift (malformed "syntax constructor is missing a field")
        field : rest -> put rest >> lift (decodeSyntaxData field)

data KBlockItem
  = KBLet !KBinder !KTerm
  deriving stock (Eq, Ord, Show)

data KLocalDef = KLocalDef
  { kldRef :: !LocalRef
  , kldMode :: !ObservationMode
  , kldUniverses :: ![UniverseRef]
  , kldType :: !KTerm
  , kldBody :: !KTerm
  }
  deriving stock (Eq, Ord, Show)

-- | Explicit recursive pattern syntax for the typed checkpoint. Pattern
-- binders carry their checked type and observation mode; constructors carry
-- semantic identity and universe instantiation. This is intentionally not a
-- rendered source-pattern string.
data KPattern = KPattern
  { kpSlot :: !KBinder
  , kpExposed :: !Bool
  , kpNode :: !KPatternNode
  }
  deriving stock (Eq, Ord, Show)

data KPatternNode
  = KPNWild
  | KPNLiteral !Literal
  | KPNConstructor !StableRef ![KLevel] ![KBinder] ![KConstructorBridge] ![KPattern]
  | KPNTuple ![KPattern]
  | KPNRecord ![(StableRef, Bool, KPattern)] !(Maybe KPattern)
  | KPNInject !Text !KPattern
  | KPNInjectRest ![Text]
  | KPNOr ![KPattern] ![[Int]]
  | KPNAs !KPattern
  deriving stock (Eq, Ord, Show)

data KConstructorBridge = KConstructorBridge
  { kcbBinder :: !KBinder
  , kcbProof :: !KTerm
  }
  deriving stock (Eq, Ord, Show)

data KCaseBinding
  = KCasePayload !KBinder
  | KCaseBridge !KConstructorBridge
  deriving stock (Eq, Ord, Show)

data KCaseAlt
  = KCaseConstructor !StableRef ![KLevel] ![KCaseBinding] !KTerm
  | KCaseDefault !KTerm
  | KCasePattern !KPattern !(Maybe KTerm) !KTerm
  deriving stock (Eq, Ord, Show)

caseBindingBinder :: KCaseBinding -> KBinder
caseBindingBinder = \case
  KCasePayload binder -> binder
  KCaseBridge bridge -> kcbBinder bridge

casePayloadBinders :: [KCaseBinding] -> [KBinder]
casePayloadBinders =
  mapMaybe $ \case
    KCasePayload binder -> Just binder
    KCaseBridge {} -> Nothing

mapKCaseBinding
  :: (KBinder -> KBinder)
  -> (KTerm -> KTerm)
  -> KCaseBinding
  -> KCaseBinding
mapKCaseBinding mapBinder mapTerm = \case
  KCasePayload binder -> KCasePayload (mapBinder binder)
  KCaseBridge bridge ->
    KCaseBridge
      (KConstructorBridge
        (mapBinder (kcbBinder bridge))
        (mapTerm (kcbProof bridge)))

mapKPattern
  :: (KBinder -> KBinder)
  -> (KLevel -> KLevel)
  -> (KTerm -> KTerm)
  -> KPattern
  -> KPattern
mapKPattern mapBinder mapLevel mapTerm (KPattern slot exposed node) =
  KPattern (mapBinder slot) exposed $ case node of
    KPNWild -> KPNWild
    KPNLiteral literal -> KPNLiteral literal
    KPNConstructor constructor levels existentials bridges fields ->
      KPNConstructor
        constructor
        (map mapLevel levels)
        (map mapBinder existentials)
        [ KConstructorBridge
            (mapBinder (kcbBinder bridge))
            (mapTerm (kcbProof bridge))
        | bridge <- bridges
        ]
        (map recurse fields)
    KPNTuple fields -> KPNTuple (map recurse fields)
    KPNRecord fields rest ->
      KPNRecord [(field, selected, recurse pattern') | (field, selected, pattern') <- fields] (fmap recurse rest)
    KPNInject tag payload -> KPNInject tag (recurse payload)
    KPNInjectRest excluded -> KPNInjectRest excluded
    KPNOr alternatives permutations -> KPNOr (map recurse alternatives) permutations
    KPNAs payload -> KPNAs (recurse payload)
  where
    recurse = mapKPattern mapBinder mapLevel mapTerm

data KTerm
  = KTLocal !LocalRef ![KLevel]
  | KTGlobal !StableRef ![KLevel]
  | KTType !KLevel
  | KTPi !KBinder !KTerm
  | KTSigma !KBinder !KTerm
  | KTLambda !KBinder !KTerm
  | KTApply !KTerm ![KArgument]
  | KTBlock ![KBlockItem] !KTerm
  | KTLetRec ![KLocalDef] !KTerm
  | KTCase !KTerm !KTerm ![KCaseAlt]
  | KTConstruct !StableRef ![KLevel] ![KArgument]
  | KTProject !StableRef !KTerm
  | KTLift !KLevel !KLevel !KEvidence !KTerm
  | KTSchemaLift !StableRef ![KLevel] ![KLevel] !StableRef
      ![KSchemaRoleEvidence] ![KArgument] !KTerm
  | KTAscribe !KTerm !KTerm
  | KTLiteral !Literal
  | KTRecordType ![(StableRef, KBinder)]
  | KTRecordValue ![(Text, KTerm)]
  | KTIf !KTerm !KTerm !KTerm
  | KTGeneric !Text ![(Text, KValueNode)]
  deriving stock (Eq, Ord, Show)

data KConstraint = KConstraint !Bool !KLevel !KLevel
  -- ^ True is strict (<), False is non-strict (<=).
  deriving stock (Eq, Ord, Show)

data KLevelProof
  = KLPAssumption !Int
  | KLPClosed
  | KLPArithmetic ![Int]
  | KLPMaxLeast !KLevelProof !KLevelProof
  | KLPZero !KLevel
  | KLPRefl !KLevel
  | KLPTrans !KLevelProof !KLevelProof
  | KLPSuccMono !KLevelProof
  | KLPMaxLeft !KLevel !KLevel
  | KLPMaxRight !KLevel !KLevel
  | KLPAddMonoLeft !KLevel !KLevelProof
  | KLPAddMonoRight !KLevel !KLevelProof
  deriving stock (Eq, Ord, Show)

-- Named constructor fields are semantic metadata, not binder presentation.
-- Each entry maps an authoritative field identity to its zero-based payload
-- position. Positional/anonymous fields simply have no entry.
data KCtorDecl = KCtorDecl !StableRef ![UniverseRef] ![(StableRef, Int)] !KTerm
  deriving stock (Eq, Ord, Show)

data KSchemaRoleEvidence
  = KSchemaInvariant
  | KSchemaCovariant !KEvidence
  | KSchemaIrrelevant
  deriving stock (Eq, Ord, Show)

data KSchemaCertificate = KSchemaCertificate
  { kscRef :: !StableRef
  , kscFamily :: !StableRef
  , kscCheckerVersion :: !Integer
  , kscSemanticVersions :: !TypeLevelSemanticVersions
  , kscSignatureHash :: !Text
  , kscSaturationArity :: !Int
  , kscRoles :: ![UniverseVariance]
  , kscClauseKinds :: ![NominalClauseKind]
  , kscMonotoneWitnesses :: ![KMonotoneWitness]
  }
  deriving stock (Eq, Ord, Show)

data KMonotoneWitness = KMonotoneWitness
  { kmwParameter :: !Int
  , kmwOperator :: !KTerm
  , kmwGoal :: !KTerm
  , kmwEvidence :: !KTerm
  , kmwDependencies :: ![KRef]
  }
  deriving stock (Eq, Ord, Show)

-- | One independently checked associated static-member equation. The
-- dictionary and field are semantic identities; the telescope binds every
-- argument needed to saturate the dictionary global before projecting the
-- field.
data KAssociatedNormalization = KAssociatedNormalization
  { kanDictionary :: !StableRef
  , kanField :: !StableRef
  , kanUniverses :: ![UniverseRef]
  , kanBinders :: ![KBinder]
  , kanValue :: !KTerm
  }
  deriving stock (Eq, Ord, Show)

type KAssociatedNormalizationKey = (StableRef, StableRef)

data KRepresentationCertificateKind
  = KRepresentationOrdinal
  | KRepresentationExactNatural
  | KRepresentationRefinement
  deriving stock (Eq, Ord, Show)

data KRepresentationCertificate = KRepresentationCertificate
  { krcRef :: !StableRef
  , krcUniverses :: ![UniverseRef]
  , krcBinders :: ![KBinder]
  , krcCheckerVersion :: !Integer
  , krcCertificateVersion :: !Integer
  , krcKind :: !KRepresentationCertificateKind
  , krcTarget :: !KTerm
  , krcConstraints :: ![KConstraint]
  , krcPayload :: ![(Text, KValueNode)]
  }
  deriving stock (Eq, Ord, Show)

data KDecl
  = KDDef !StableRef !ObservationMode ![UniverseRef] !KTerm !KTerm
  | KDAxiom !StableRef !ObservationMode ![UniverseRef] !KTerm
  | KDInterface !StableRef ![UniverseRef] !KTerm
  | KDAssociatedNormalization !KAssociatedNormalization
  | KDData !StableRef ![(UniverseRef, UniverseVariance)] ![KBinder] !KTerm !StableRef ![KCtorDecl]
  | KDSchemaCertificate !KSchemaCertificate
  | KDTermProbe !KTerm
  | KDLevelCertificate !StableRef ![UniverseRef] ![KConstraint] !KConstraint !KLevelProof
  | KDRepresentationCertificate !KRepresentationCertificate
  | KDExtension !Text !Integer
  | KDGeneric !Text ![(Text, KValueNode)]
  deriving stock (Eq, Ord, Show)

data KModule = KModule
  { kmRef :: !StableRef
  , kmMetadata :: ![(Text, Text)]
  , kmDecls :: ![KDecl]
  }
  deriving stock (Eq, Ord, Show)

data KCoreFile = KCoreFile !Integer ![KModule]
  deriving stock (Eq, Ord, Show)

data VerifyContext = VerifyContext
  { vcGlobalArities :: !(Map StableRef Int)
  , vcGlobalTypes :: !(Map StableRef ([UniverseRef], KTerm))
  , vcGlobalModes :: !(Map StableRef ObservationMode)
  , vcGlobalBodies :: !(Map StableRef ([UniverseRef], KTerm))
  , vcRecordInterfaces :: !(Map StableRef ([UniverseRef], KTerm))
  , vcAssociatedNormalizations :: !(Map KAssociatedNormalizationKey KAssociatedNormalization)
  , vcConstructorTypes :: !(Map StableRef ([UniverseRef], [KBinder], KTerm))
  , vcConstructorFields :: !(Map StableRef (Map StableRef Int))
  , vcLevelCertificates :: !(Map StableRef ([UniverseRef], [KConstraint], KConstraint, KLevelProof))
  , vcSchemaCertificates :: !(Map StableRef KSchemaCertificate)
  , vcNominalFamilies :: !(Map StableRef KNominalFamily)
  , vcExtensions :: !(Set Text)
  , vcArithmeticBranchFacts :: ![(Bool, KTerm)]
  }

withArithmeticBranchFact :: Bool -> KTerm -> VerifyContext -> VerifyContext
withArithmeticBranchFact truth condition context =
  context
    { vcArithmeticBranchFacts =
        (truth, condition) : vcArithmeticBranchFacts context
    }

data KNominalFamily = KNominalFamily
  { knfUniverses :: ![(UniverseRef, UniverseVariance)]
  , knfBinders :: ![KBinder]
  , knfResult :: !KTerm
  , knfCertificate :: !StableRef
  , knfConstructors :: ![KCtorDecl]
  }

-- | Opaque, verified, source-free import environment reconstructed from a
-- KCoreText artifact. Consumers cannot manufacture its semantic maps without
-- passing the parser and verifier.
data KCoreInterface = KCoreInterface
  { kciTypes :: !(Map StableRef ([UniverseRef], KTerm))
  , kciModes :: !(Map StableRef ObservationMode)
  , kciBodies :: !(Map StableRef ([UniverseRef], KTerm))
  , kciRecordInterfaces :: !(Map StableRef ([UniverseRef], KTerm))
  , kciAssociatedNormalizations :: !(Map KAssociatedNormalizationKey KAssociatedNormalization)
  , kciConstructors :: !(Map StableRef ([UniverseRef], [KBinder], KTerm))
  , kciLevelCertificates :: !(Map StableRef ([UniverseRef], [KConstraint], KConstraint, KLevelProof))
  , kciRepresentationCertificates :: !(Map StableRef KRepresentationCertificate)
  , kciSchemaCertificates :: !(Map StableRef KSchemaCertificate)
  , kciNominalFamilies :: !(Map StableRef KNominalFamily)
  }

data LocalEntry
  = LocalBinder !KBinder
  | LocalDefinition !ObservationMode ![UniverseRef] !KTerm !KTerm

type LocalEnv = Map Int LocalEntry

-- Observation origins are semantic identities, not readable names. Projection
-- occurrences additionally carry their canonical-tree path because the same
-- field facet may be observed at more than one independent site.
data KObservationOrigin
  = KObservationLocal !Int
  | KObservationGlobal !Text
  | KObservationProjection ![Int] !Text
  deriving stock (Eq, Ord, Show)

type KDependencySet = Set KObservationOrigin

data KDependencyBinding = KDependencyBinding
  { kdbDependencies :: !KDependencySet
  , kdbDefinition :: !(Maybe ([UniverseRef], KTerm))
  , kdbEntry :: !LocalEntry
  }

type KDependencyEnv = Map Int KDependencyBinding

-- Lexer ---------------------------------------------------------------------

data Token
  = TWord !Text
  | TInt !Integer
  | TString !Text
  | TSym !Text
  deriving stock (Eq, Show)

lexKCore :: Text -> Either KCoreTextError [Token]
lexKCore = go . T.unpack
  where
    go [] = Right []
    go ('-' : '-' : xs) = go (dropComment xs)
    go ('-' : c : xs)
      | isDigit c =
          let (rawTail, rest) = span wordChar xs
              token = c : rawTail
           in if all isDigit token
                then (TInt (negate (read token)) :) <$> go rest
                else Left (invalid ("malformed negative integer -" <> T.pack token))
    go (c : xs)
      | c == ' ' || c == '\t' || c == '\r' || c == '\n' = go xs
      | c == '"' = do
          (value, rest) <- string [] xs
          (TString (T.pack (reverse value)) :) <$> go rest
      | isDigit c =
          let (rawTail, rawRest) = span wordChar xs
              (tailWord, rest) = returnTrailingDots rawTail rawRest
              token = c : tailWord
           in if all isDigit token
                then (TInt (read token) :) <$> go rest
                else (TWord (T.pack token) :) <$> go rest
      | isAlpha c || c == '_' =
          let (rawTail, rawRest) = span wordChar xs
              (tailWord, rest) = returnTrailingDots rawTail rawRest
           in (TWord (T.pack (c : tailWord)) :) <$> go rest
      | otherwise = case c : take 1 xs of
          "->" -> (TSym "->" :) <$> go (drop 1 xs)
          "<=" -> (TSym "<=" :) <$> go (drop 1 xs)
          _ | c `elem` ("{}[]();:,.@#%^=<>+" :: String) ->
                (TSym (T.singleton c) :) <$> go xs
            | otherwise -> Left (invalid ("unexpected character " <> T.singleton c))

    wordChar c = isAlphaNum c || c `elem` ("_.-" :: String)
    returnTrailingDots raw rest =
      let (dots, reversedWord) = span (== '.') (reverse raw)
       in (reverse reversedWord, dots ++ rest)
    dropComment = drop 1 . dropWhile (/= '\n')
    string _ [] = Left (invalid "unterminated string literal")
    string acc ('"' : rest) = Right (acc, rest)
    string acc ('\\' : c : rest) = case c of
      'n' -> string ('\n' : acc) rest
      'r' -> string ('\r' : acc) rest
      't' -> string ('\t' : acc) rest
      '"' -> string ('"' : acc) rest
      '\\' -> string ('\\' : acc) rest
      _ -> Left (invalid "unsupported string escape")
    string acc (c : rest) = string (c : acc) rest

invalid :: Text -> KCoreTextError
invalid = KCoreTextError "E_KCORE_TEXT_INVALID"

arithmeticCertificateInvalid :: Text -> KCoreTextError
arithmeticCertificateInvalid =
  KCoreTextError "E_KCORE_ARITHMETIC_CERTIFICATE_INVALID"

representationCertificateInvalid :: Text -> KCoreTextError
representationCertificateInvalid =
  KCoreTextError "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID"

data KArithmeticProvider = KArithmeticProvider
  { kapIdentity :: !(Maybe StableRef)
  , kapTheory :: !(Maybe ArithmeticNormalizationTheory)
  , kapTrait :: !StableRef
  , kapLaw :: !(Maybe StableRef)
  , kapNormalFormVersion :: !(Maybe Integer)
  , kapProviderVersion :: !(Maybe Integer)
  , kapCheckerVersion :: !(Maybe Integer)
  , kapEvidence :: !KTerm
  }
  deriving stock (Eq, Ord, Show)

-- | The portable provider value used both to order serialized entries and to
-- verify them. Canonicalization must happen after Core terms are converted:
-- erased Core distinctions can otherwise collapse to one KCore evidence term.
portableArithmeticProvider
  :: StableRef
  -> KTerm
  -> Maybe ArithmeticNormalizationProvider
  -> KArithmeticProvider
portableArithmeticProvider trait evidence = \case
  Nothing ->
    KArithmeticProvider
      { kapIdentity = Nothing
      , kapTheory = Nothing
      , kapTrait = trait
      , kapLaw = Nothing
      , kapNormalFormVersion = Nothing
      , kapProviderVersion = Nothing
      , kapCheckerVersion = Nothing
      , kapEvidence = evidence
      }
  Just provider ->
    KArithmeticProvider
      { kapIdentity = Just (stableRefForText (anpIdentity provider))
      , kapTheory = Just (anpTheory provider)
      , kapTrait = trait
      , kapLaw = Just (stableRefForGlobal (anpLawIdentity provider))
      , kapNormalFormVersion = Just (anpNormalFormVersion provider)
      , kapProviderVersion = Just (anpProviderVersion provider)
      , kapCheckerVersion = Just (anpCheckerVersion provider)
      , kapEvidence = evidence
      }

standardNormalizationProviders :: KTerm -> [KArithmeticProvider]
standardNormalizationProviders evidence =
  [ provider
      "std.prelude.provider.additive-monoid.left-identity"
      ArithmeticMonoid
      "AdditiveMonoid"
      "addLeftIdentity"
  , provider
      "std.prelude.provider.additive-monoid.right-identity"
      ArithmeticMonoid
      "AdditiveMonoid"
      "addRightIdentity"
  , provider
      "std.prelude.provider.commutative-additive-monoid"
      ArithmeticCommutativeMonoid
      "CommutativeAdditiveMonoid"
      "addCommutative"
  ]
  where
    provider identity theory trait law =
      KArithmeticProvider
        { kapIdentity = Just (stableRefForText identity)
        , kapTheory = Just theory
        , kapTrait = stableRefForGlobal (gPrel trait)
        , kapLaw = Just (stableRefForGlobal (gPrel (trait <> "." <> law)))
        , kapNormalFormVersion = Just 1
        , kapProviderVersion = Just 1
        , kapCheckerVersion = Just 1
        , kapEvidence = evidence
        }

encodeArithmeticReplay :: ArithmeticReplay -> KValueNode
encodeArithmeticReplay replay =
  KVList
    [ encodeArithmeticFact (arGoal replay)
    , KVText (encodeArithmeticRule (arRule replay))
    , encodeArithmeticNormalForm (arNormalForm replay)
    ]

encodeArithmeticFormulaReplay :: ArithmeticFormulaReplay -> KValueNode
encodeArithmeticFormulaReplay = \case
  ReplayTruth truth ->
    node "truth" [truthNode truth]
  ReplayAtom truth replay ->
    node "atom" [truthNode truth, encodeArithmeticReplay replay]
  ReplayAndTrue lhs rhs ->
    binary "and-true" lhs rhs
  ReplayAndFalseLeft replay ->
    unary "and-false-left" replay
  ReplayAndFalseRight replay ->
    unary "and-false-right" replay
  ReplayOrTrueLeft replay ->
    unary "or-true-left" replay
  ReplayOrTrueRight replay ->
    unary "or-true-right" replay
  ReplayOrFalse lhs rhs ->
    binary "or-false" lhs rhs
  ReplayNot replay ->
    unary "not" replay
  ReplayAssumptionCases cases ->
    node "assumption-cases" [KVList (map encodeCase cases)]
  where
    node tag fields = KVList (KVText tag : fields)
    truthNode truth = KVInteger (if truth then 1 else 0)
    unary tag replay =
      node tag [encodeArithmeticFormulaReplay replay]
    binary tag lhs rhs =
      node
        tag
        [ encodeArithmeticFormulaReplay lhs
        , encodeArithmeticFormulaReplay rhs
        ]
    encodeCase = \case
      ReplayAssumptionContradiction index replay ->
        node
          "contradiction"
          [KVInteger (toInteger index), encodeArithmeticReplay replay]
      ReplayAssumptionImpossible index ->
        node "impossible" [KVInteger (toInteger index)]
      ReplayAssumptionGoal replay ->
        node "goal" [encodeArithmeticFormulaReplay replay]

encodeArithmeticFact :: AFact -> KValueNode
encodeArithmeticFact (AFact comparison lhs rhs) =
  KVList
    [ KVText $ case comparison of
        ACmpLt -> "lt"
        ACmpLe -> "le"
        ACmpEq -> "eq"
        ACmpNe -> "ne"
    , encodeArithmeticExpression lhs
    , encodeArithmeticExpression rhs
    ]

encodeArithmeticExpression :: AExpr -> KValueNode
encodeArithmeticExpression = \case
  AConst value -> node "constant" [KVInteger value]
  AVar variable -> node "variable" [KVInteger (toInteger variable)]
  AScale scale expression -> node "scale" [KVInteger scale, encodeArithmeticExpression expression]
  AAdd lhs rhs -> binary "add" lhs rhs
  ASub lhs rhs -> binary "subtract" lhs rhs
  AMul lhs rhs -> binary "multiply" lhs rhs
  ADiv lhs rhs -> binary "divide" lhs rhs
  AMod lhs rhs -> binary "modulo" lhs rhs
  ANeg expression -> node "negate" [encodeArithmeticExpression expression]
  AMax lhs rhs -> binary "maximum" lhs rhs
  AMin lhs rhs -> binary "minimum" lhs rhs
  AIf condition thenExpression elseExpression ->
    node
      "if"
      [ encodeArithmeticFormula condition
      , encodeArithmeticExpression thenExpression
      , encodeArithmeticExpression elseExpression
      ]
  where
    node tag fields = KVList (KVText tag : fields)
    binary tag lhs rhs =
      node tag [encodeArithmeticExpression lhs, encodeArithmeticExpression rhs]

encodeArithmeticFormula :: AFormula -> KValueNode
encodeArithmeticFormula = \case
  ATruth truth ->
    node "truth" [KVInteger (if truth then 1 else 0)]
  AAtom fact ->
    node "atom" [encodeArithmeticFact fact]
  AAnd lhs rhs -> binary "and" lhs rhs
  AOr lhs rhs -> binary "or" lhs rhs
  ANot formula ->
    node "not" [encodeArithmeticFormula formula]
  where
    node tag fields = KVList (KVText tag : fields)
    binary tag lhs rhs =
      node tag [encodeArithmeticFormula lhs, encodeArithmeticFormula rhs]

encodeArithmeticRule :: ArithmeticProofRule -> Text
encodeArithmeticRule = \case
  ProvePolynomialEquality -> "polynomial-equality"
  ProveLinearEquality -> "linear-equality"
  ProveStrictLowerBound -> "strict-lower-bound"
  ProveNonStrictLowerBound -> "nonstrict-lower-bound"
  ProveDisequality -> "disequality"
  ProveCaseSplit -> "case-split"

encodeArithmeticNormalForm :: ArithmeticNormalForm -> KValueNode
encodeArithmeticNormalForm = \case
  NormalPolynomial monomials ->
    KVList
      [ KVText "polynomial"
      , KVList
          [ KVList
              [ KVList
                  [KVList [KVInteger (toInteger variable), KVInteger (toInteger exponent)] | (variable, exponent) <- variables]
              , KVInteger coefficient
              ]
          | (variables, coefficient) <- monomials
          ]
      ]
  NormalLinear constant coefficients ->
    KVList
      [ KVText "linear"
      , KVInteger constant
      , KVList
          [KVList [KVInteger (toInteger variable), KVInteger coefficient] | (variable, coefficient) <- coefficients]
      ]
  NormalLowerBound lower ->
    KVList [KVText "lower-bound", KVInteger lower]
  NormalDisequality ->
    KVList [KVText "disequality"]
  NormalCaseSplit condition thenReplay elseReplay ->
    KVList
      [ KVText "case-split"
      , encodeArithmeticFormula condition
      , encodeArithmeticReplay thenReplay
      , encodeArithmeticReplay elseReplay
      ]

decodeArithmeticReplay :: KValueNode -> Either KCoreTextError ArithmeticReplay
decodeArithmeticReplay = \case
  KVList [fact, KVText rule, normalForm] ->
    ArithmeticReplay
      <$> decodeArithmeticFact fact
      <*> decodeArithmeticRule rule
      <*> decodeArithmeticNormalForm normalForm
  _ -> malformed "arithmetic replay must contain goal, rule, and normal form"
  where
    malformed = Left . arithmeticCertificateInvalid

decodeArithmeticFormulaReplay
  :: KValueNode
  -> Either KCoreTextError ArithmeticFormulaReplay
decodeArithmeticFormulaReplay = \case
  KVList [KVText "truth", truth] ->
    ReplayTruth <$> decodeTruth truth
  KVList [KVText "atom", truth, replay] ->
    ReplayAtom
      <$> decodeTruth truth
      <*> decodeArithmeticReplay replay
  KVList [KVText "and-true", lhs, rhs] ->
    ReplayAndTrue <$> recurse lhs <*> recurse rhs
  KVList [KVText "and-false-left", replay] ->
    ReplayAndFalseLeft <$> recurse replay
  KVList [KVText "and-false-right", replay] ->
    ReplayAndFalseRight <$> recurse replay
  KVList [KVText "or-true-left", replay] ->
    ReplayOrTrueLeft <$> recurse replay
  KVList [KVText "or-true-right", replay] ->
    ReplayOrTrueRight <$> recurse replay
  KVList [KVText "or-false", lhs, rhs] ->
    ReplayOrFalse <$> recurse lhs <*> recurse rhs
  KVList [KVText "not", replay] ->
    ReplayNot <$> recurse replay
  KVList [KVText "assumption-cases", KVList cases] ->
    ReplayAssumptionCases <$> mapM decodeCase cases
  _ -> malformed "arithmetic formula replay has an invalid structure"
  where
    recurse = decodeArithmeticFormulaReplay
    decodeTruth = \case
      KVInteger 0 -> pure False
      KVInteger 1 -> pure True
      _ -> malformed "arithmetic formula truth value must be 0 or 1"
    decodeCase = \case
      KVList [KVText "contradiction", KVInteger index, replay] ->
        ReplayAssumptionContradiction
          <$> checkedInt "arithmetic contradiction fact index" index
          <*> decodeArithmeticReplay replay
      KVList [KVText "impossible", KVInteger index] ->
        ReplayAssumptionImpossible
          <$> checkedInt "arithmetic impossible-assumption index" index
      KVList [KVText "goal", replay] ->
        ReplayAssumptionGoal <$> recurse replay
      _ -> malformed "arithmetic assumption-case replay has an invalid structure"
    malformed = Left . arithmeticCertificateInvalid

decodeArithmeticFact :: KValueNode -> Either KCoreTextError AFact
decodeArithmeticFact = \case
  KVList [KVText comparison, lhs, rhs] ->
    AFact
      <$> case comparison of
        "lt" -> pure ACmpLt
        "le" -> pure ACmpLe
        "eq" -> pure ACmpEq
        "ne" -> pure ACmpNe
        _ -> malformed "arithmetic fact has an unknown comparison"
      <*> decodeArithmeticExpression lhs
      <*> decodeArithmeticExpression rhs
  _ -> malformed "arithmetic fact must contain a comparison and two expressions"
  where
    malformed = Left . arithmeticCertificateInvalid

decodeArithmeticExpression :: KValueNode -> Either KCoreTextError AExpr
decodeArithmeticExpression encoded =
  case encoded of
    KVList [KVText "constant", KVInteger value] -> pure (AConst value)
    KVList [KVText "variable", KVInteger variable] ->
      AVar <$> checkedInt "arithmetic variable identity" variable
    KVList [KVText "scale", KVInteger scale, expression] ->
      AScale scale <$> recurse expression
    KVList [KVText "add", lhs, rhs] -> binary AAdd lhs rhs
    KVList [KVText "subtract", lhs, rhs] -> binary ASub lhs rhs
    KVList [KVText "multiply", lhs, rhs] -> binary AMul lhs rhs
    KVList [KVText "divide", lhs, rhs] -> binary ADiv lhs rhs
    KVList [KVText "modulo", lhs, rhs] -> binary AMod lhs rhs
    KVList [KVText "negate", expression] -> ANeg <$> recurse expression
    KVList [KVText "maximum", lhs, rhs] -> binary AMax lhs rhs
    KVList [KVText "minimum", lhs, rhs] -> binary AMin lhs rhs
    KVList [KVText "if", condition, thenExpression, elseExpression] ->
      AIf
        <$> decodeArithmeticFormula condition
        <*> recurse thenExpression
        <*> recurse elseExpression
    _ -> malformed "arithmetic expression has an invalid structural encoding"
  where
    recurse = decodeArithmeticExpression
    binary constructor lhs rhs = constructor <$> recurse lhs <*> recurse rhs
    malformed = Left . arithmeticCertificateInvalid

decodeArithmeticFormula :: KValueNode -> Either KCoreTextError AFormula
decodeArithmeticFormula = \case
  KVList [KVText "truth", KVInteger 0] -> pure (ATruth False)
  KVList [KVText "truth", KVInteger 1] -> pure (ATruth True)
  KVList [KVText "atom", fact] ->
    AAtom <$> decodeArithmeticFact fact
  KVList [KVText "and", lhs, rhs] -> binary AAnd lhs rhs
  KVList [KVText "or", lhs, rhs] -> binary AOr lhs rhs
  KVList [KVText "not", formula] ->
    ANot <$> decodeArithmeticFormula formula
  _ ->
    Left
      ( arithmeticCertificateInvalid
          "arithmetic formula has an invalid structural encoding"
      )
  where
    binary constructor lhs rhs =
      constructor
        <$> decodeArithmeticFormula lhs
        <*> decodeArithmeticFormula rhs

decodeArithmeticRule :: Text -> Either KCoreTextError ArithmeticProofRule
decodeArithmeticRule = \case
  "polynomial-equality" -> pure ProvePolynomialEquality
  "linear-equality" -> pure ProveLinearEquality
  "strict-lower-bound" -> pure ProveStrictLowerBound
  "nonstrict-lower-bound" -> pure ProveNonStrictLowerBound
  "disequality" -> pure ProveDisequality
  "case-split" -> pure ProveCaseSplit
  _ -> Left (arithmeticCertificateInvalid "arithmetic replay has an unknown proof rule")

decodeArithmeticNormalForm :: KValueNode -> Either KCoreTextError ArithmeticNormalForm
decodeArithmeticNormalForm = \case
  KVList [KVText "polynomial", KVList monomials] ->
    NormalPolynomial <$> mapM decodeMonomial monomials
  KVList [KVText "linear", KVInteger constant, KVList coefficients] ->
    NormalLinear constant <$> mapM decodeCoefficient coefficients
  KVList [KVText "lower-bound", KVInteger lower] ->
    pure (NormalLowerBound lower)
  KVList [KVText "disequality"] ->
    pure NormalDisequality
  KVList [KVText "case-split", condition, thenReplay, elseReplay] ->
    NormalCaseSplit
      <$> decodeArithmeticFormula condition
      <*> decodeArithmeticReplay thenReplay
      <*> decodeArithmeticReplay elseReplay
  _ -> malformed "arithmetic normal form has an invalid structural encoding"
  where
    decodeMonomial = \case
      KVList [KVList variables, KVInteger coefficient] ->
        (, coefficient) <$> mapM decodePower variables
      _ -> malformed "polynomial monomial has an invalid structural encoding"
    decodePower = \case
      KVList [KVInteger variable, KVInteger exponent] ->
        (,)
          <$> checkedInt "polynomial variable identity" variable
          <*> checkedInt "polynomial exponent" exponent
      _ -> malformed "polynomial power has an invalid structural encoding"
    decodeCoefficient = \case
      KVList [KVInteger variable, KVInteger coefficient] ->
        (, coefficient) <$> checkedInt "linear variable identity" variable
      _ -> malformed "linear coefficient has an invalid structural encoding"
    malformed = Left . arithmeticCertificateInvalid

checkedInt :: Text -> Integer -> Either KCoreTextError Int
checkedInt label value
  | toInteger decoded == value = pure decoded
  | otherwise =
      Left
        (arithmeticCertificateInvalid (label <> " is outside the portable Int range"))
  where
    decoded = fromInteger value

-- Deterministic token parser -------------------------------------------------

newtype P a = P {runP :: [Token] -> Either KCoreTextError (a, [Token])}

instance Functor P where
  fmap f (P p) = P $ \ts -> do
    (a, rest) <- p ts
    pure (f a, rest)

instance Applicative P where
  pure a = P (Right . (a,))
  P pf <*> P pa = P $ \ts -> do
    (f, rest) <- pf ts
    (a, rest') <- pa rest
    pure (f a, rest')

instance Monad P where
  P pa >>= f = P $ \ts -> do
    (a, rest) <- pa ts
    runP (f a) rest

parseKCoreText :: Text -> Either KCoreTextError KCoreFile
parseKCoreText source = do
  tokens <- lexKCore source
  (file, rest) <- runP pFile tokens
  case rest of
    token : _ -> Left (invalid ("unexpected token " <> renderToken token))
    [] -> pure ()
  pure file

renderToken :: Token -> Text
renderToken = \case
  TWord x -> x
  TInt n -> T.pack (show n)
  TString x -> T.pack (show x)
  TSym x -> x

peek :: P (Maybe Token)
peek = P $ \ts -> Right (case ts of [] -> Nothing; t : _ -> Just t, ts)

takeToken :: P Token
takeToken = P $ \case
  [] -> Left (invalid "unexpected end of KCoreText")
  t : ts -> Right (t, ts)

symbol :: Text -> P ()
symbol wanted = takeToken >>= \case
  TSym actual | actual == wanted -> pure ()
  actual -> failP ("expected '" <> wanted <> "', found " <> renderToken actual)

keyword :: Text -> P ()
keyword wanted = takeToken >>= \case
  TWord actual | actual == wanted -> pure ()
  actual -> failP ("expected '" <> wanted <> "', found " <> renderToken actual)

word :: P Text
word = takeToken >>= \case
  TWord x -> pure x
  actual -> failP ("expected identifier, found " <> renderToken actual)

integer :: P Integer
integer = takeToken >>= \case
  TInt n -> pure n
  actual -> failP ("expected integer, found " <> renderToken actual)

stringLiteral :: P Text
stringLiteral = takeToken >>= \case
  TString x -> pure x
  actual -> failP ("expected string literal, found " <> renderToken actual)

failP :: Text -> P a
failP message = P (const (Left (invalid message)))

nextIs :: Token -> P Bool
nextIs tok = (== Just tok) <$> peek

pFile :: P KCoreFile
pFile = do
  keyword "kcore"
  version <- integer
  symbol ";"
  modules <- manyWhile (Just (TWord "module") ==) pModule
  when (null modules) (failP "a KCoreText file must contain at least one module")
  pure (KCoreFile version modules)

pModule :: P KModule
pModule = do
  keyword "module"
  ref <- pGlobalRef
  metadata <- ifM (nextIs (TSym "[")) pMetadata (pure [])
  symbol "{"
  decls <- manyUntil "}" pDecl
  symbol "}"
  pure (KModule ref metadata decls)

pMetadata :: P [(Text, Text)]
pMetadata = do
  symbol "["
  entries <- sepUntil "]" "," $ do
    key <- word
    symbol "="
    value <- stringLiteral
    pure (key, value)
  symbol "]"
  pure entries

pDecl :: P KDecl
pDecl = peek >>= \case
  Just (TWord "def") -> pDef
  Just (TWord "axiom") -> pAxiom
  Just (TWord "interface") -> pInterface
  Just (TWord "associated-normalization") -> pAssociatedNormalization
  Just (TWord "data") -> pData
  Just (TWord "schema-certificate") -> KDSchemaCertificate <$> pSchemaCertificate
  Just (TWord "level-certificate") -> pLevelCertificate
  Just (TWord "representation-certificate") ->
    KDRepresentationCertificate <$> pRepresentationCertificate
  Just (TWord "extension") -> do
    keyword "extension"
    owner <- word
    version <- integer
    symbol ";"
    pure (KDExtension owner version)
  Just (TWord "decl-node") -> do
    keyword "decl-node"
    tag <- stringLiteral
    KDGeneric tag <$> pNamedValues
  Just (TWord "term-node") -> KDTermProbe <$> pTerm
  Just token -> failP ("expected declaration, found " <> renderToken token)
  Nothing -> failP "unexpected end of module"

pRepresentationCertificate :: P KRepresentationCertificate
pRepresentationCertificate = do
  keyword "representation-certificate"
  ref <- pCertificateRef
  universes <- pUniverseTelescope
  binders <- manyWhile (Just (TSym "(") ==) pBinder
  symbol "["
  keyword "checkerVersion"
  symbol "="
  checkerVersion <- integer
  symbol ","
  keyword "certificateVersion"
  symbol "="
  certificateVersion <- integer
  symbol ","
  keyword "kind"
  symbol "="
  kind <- pRepresentationCertificateKind
  symbol "]"
  keyword "for"
  target <- pTerm
  constraints <- pConstraintBlock
  payload <- pNamedValues
  pure
    KRepresentationCertificate
      { krcRef = ref
      , krcUniverses = universes
      , krcBinders = binders
      , krcCheckerVersion = checkerVersion
      , krcCertificateVersion = certificateVersion
      , krcKind = kind
      , krcTarget = target
      , krcConstraints = constraints
      , krcPayload = payload
      }

pRepresentationCertificateKind :: P KRepresentationCertificateKind
pRepresentationCertificateKind =
  word >>= \case
    "ordinal" -> pure KRepresentationOrdinal
    "exact-natural" -> pure KRepresentationExactNatural
    "refinement" -> pure KRepresentationRefinement
    actual ->
      failP
        ( "unknown representation-certificate kind '"
            <> actual
            <> "'"
        )

pDef :: P KDecl
pDef = do
  keyword "def"
  mode <- pObservationMode
  ref <- pGlobalRef
  universes <- pUniverseTelescope
  symbol ":"
  ty <- pTerm
  symbol "{"
  keyword "body"
  symbol "="
  body <- pTerm
  symbol ";"
  symbol "}"
  pure (KDDef ref mode universes ty body)

pAxiom :: P KDecl
pAxiom = do
  keyword "axiom"
  mode <- pObservationMode
  ref <- pGlobalRef
  universes <- pUniverseTelescope
  symbol ":"
  ty <- pTerm
  symbol ";"
  pure (KDAxiom ref mode universes ty)

pInterface :: P KDecl
pInterface = do
  keyword "interface"
  ref <- pGlobalRef
  universes <- pUniverseTelescope
  symbol ":"
  ty <- pTerm
  symbol ";"
  pure (KDInterface ref universes ty)

pAssociatedNormalization :: P KDecl
pAssociatedNormalization = do
  keyword "associated-normalization"
  dictionary <- pGlobalRef
  universes <- pUniverseTelescope
  field <- pFieldRef
  binders <- manyWhile (Just (TSym "(") ==) pBinder
  symbol "="
  value <- pTerm
  symbol ";"
  pure
    ( KDAssociatedNormalization
        KAssociatedNormalization
          { kanDictionary = dictionary
          , kanField = field
          , kanUniverses = universes
          , kanBinders = binders
          , kanValue = value
          }
    )

pData :: P KDecl
pData = do
  keyword "data"
  ref <- pGlobalRef
  universes <- pNominalUniverseTelescope
  binders <- manyWhile (Just (TSym "(") ==) pBinder
  symbol ":"
  result <- pTerm
  keyword "certificate"
  certificate <- pSchemaCertificateRef
  symbol "{"
  constructors <- manyWhile (Just (TWord "constructor") ==) $ do
    keyword "constructor"
    ctor <- pGlobalRef
    ctorUniverses <- pUniverseTelescope
    symbol ":"
    ty <- pTerm
    fields <- pConstructorFieldBlock
    symbol ";"
    pure (KCtorDecl ctor ctorUniverses fields ty)
  symbol "}"
  pure (KDData ref universes binders result certificate constructors)

pConstructorFieldBlock :: P [(StableRef, Int)]
pConstructorFieldBlock = do
  hasFields <- nextIs (TWord "fields")
  if not hasFields
    then pure []
    else do
      keyword "fields"
      symbol "{"
      fields <- manyWhile (\case Just (TSym "@") -> True; _ -> False) $ do
        field <- pFieldRef
        symbol "="
        index <- integer
        when (index < 0 || index > toInteger (maxBound :: Int)) $
          failP "constructor field index is outside the supported range"
        symbol ";"
        pure (field, fromInteger index)
      symbol "}"
      pure fields

pSchemaCertificate :: P KSchemaCertificate
pSchemaCertificate = do
  keyword "schema-certificate"
  certificate <- pSchemaCertificateRef
  keyword "for"
  family <- pGlobalRef
  symbol "["
  keyword "checkerVersion"
  symbol "="
  checkerVersion <- integer
  symbol ","
  keyword "typeLevelAlgebraVersion"
  symbol "="
  algebraVersion <- versionInteger
  symbol ","
  keyword "levelConstructorNormalizerVersion"
  symbol "="
  constructorNormalizerVersion <- versionInteger
  symbol ","
  keyword "levelRigidEntailmentVersion"
  symbol "="
  rigidEntailmentVersion <- versionInteger
  symbol ","
  keyword "levelPrincipalInferenceVersion"
  symbol "="
  principalInferenceVersion <- versionInteger
  symbol ","
  keyword "levelCertificateVersion"
  symbol "="
  certificateVersion <- versionInteger
  symbol ","
  keyword "signatureHash"
  symbol "="
  signatureHash <- peek >>= \case
    Just (TString _) -> stringLiteral
    _ -> word
  symbol ","
  keyword "saturationArity"
  symbol "="
  saturationInteger <- integer
  when (saturationInteger < 0 || saturationInteger > toInteger (maxBound :: Int)) $
    failP "schema-certificate saturation arity is outside the supported range"
  symbol "]"
  symbol "{"
  keyword "roles"
  symbol "="
  roles <- bracketedList pUniverseVariance
  symbol ";"
  keyword "clauseKinds"
  symbol "="
  clauseKinds <- bracketedList pNominalClauseKind
  symbol ";"
  keyword "monotoneWitnesses"
  symbol "="
  monotoneWitnesses <- bracketedList pMonotoneWitness
  symbol ";"
  symbol "}"
  pure
    KSchemaCertificate
      { kscRef = certificate
      , kscFamily = family
      , kscCheckerVersion = checkerVersion
      , kscSemanticVersions =
          TypeLevelSemanticVersions
            (fromInteger algebraVersion)
            (fromInteger constructorNormalizerVersion)
            (fromInteger rigidEntailmentVersion)
            (fromInteger principalInferenceVersion)
            (fromInteger certificateVersion)
      , kscSignatureHash = signatureHash
      , kscSaturationArity = fromInteger saturationInteger
      , kscRoles = roles
      , kscClauseKinds = clauseKinds
      , kscMonotoneWitnesses = monotoneWitnesses
      }
  where
    versionInteger = do
      value <- integer
      when (value < 0 || value > toInteger (maxBound :: Int)) $
        failP "schema-certificate semantic version is outside the supported range"
      pure value

pMonotoneWitness :: P KMonotoneWitness
pMonotoneWitness = do
  symbol "{"
  keyword "parameter"
  symbol "="
  parameterInteger <- integer
  when (parameterInteger < 0 || parameterInteger > toInteger (maxBound :: Int)) $
    failP "monotonicity witness parameter is outside the supported range"
  symbol ";"
  keyword "operator"
  symbol "="
  operator <- pTerm
  symbol ";"
  keyword "goal"
  symbol "="
  goal <- pTerm
  symbol ";"
  keyword "evidence"
  symbol "="
  evidence <- pTerm
  symbol ";"
  keyword "dependencies"
  symbol "="
  dependencies <- bracketedList pRef
  symbol ";"
  symbol "}"
  pure
    KMonotoneWitness
      { kmwParameter = fromInteger parameterInteger
      , kmwOperator = operator
      , kmwGoal = goal
      , kmwEvidence = evidence
      , kmwDependencies = dependencies
      }

bracketedList :: P a -> P [a]
bracketedList parser = symbol "[" >> sepUntil "]" "," parser <* symbol "]"

pUniverseVariance :: P UniverseVariance
pUniverseVariance = word >>= \case
  "invariant" -> pure Invariant
  "covariant" -> pure Covariant
  "irrelevant" -> pure Irrelevant
  role -> failP ("unknown universe role '" <> role <> "'")

pNominalClauseKind :: P NominalClauseKind
pNominalClauseKind = word >>= \case
  "sort_declaration" -> pure ClauseSortDeclaration
  "point_constructor" -> pure ClausePointConstructor
  "path_constructor" -> pure ClausePathConstructor
  "higher_boundary" -> pure ClauseHigherBoundary
  "quotient_equation" -> pure ClauseQuotientEquation
  "recursive_operation" -> pure ClauseRecursiveOperation
  "recursive_equation" -> pure ClauseRecursiveEquation
  "generated_projection" -> pure ClauseGeneratedProjection
  "eliminator" -> pure ClauseEliminator
  "computation_rule" -> pure ClauseComputationRule
  "truncation_rule" -> pure ClauseTruncationRule
  "extension_clause" -> pure ClauseExtension
  clause -> failP ("unknown nominal signature clause kind '" <> clause <> "'")

pLevelCertificate :: P KDecl
pLevelCertificate = do
  keyword "level-certificate"
  ref <- pCertificateRef
  universes <- pUniverseTelescope
  symbol ":"
  constraint <- pConstraintWithoutSemicolon
  constraints <- pConstraintBlock
  symbol "{"
  proof <- pLevelProof
  symbol "}"
  pure (KDLevelCertificate ref universes constraints constraint proof)

pConstraintWithoutSemicolon :: P KConstraint
pConstraintWithoutSemicolon = do
  lhs <- pLevel
  strict <- takeToken >>= \case
    TSym "<" -> pure True
    TSym "<=" -> pure False
    token -> failP ("expected '<' or '<=', found " <> renderToken token)
  KConstraint strict lhs <$> pLevel

pLevelProof :: P KLevelProof
pLevelProof = peek >>= \case
  Just (TWord "assumption") -> keyword "assumption" >> KLPAssumption . fromInteger <$> parenthesized integer <* symbol ";"
  Just (TWord "closed") -> keyword "closed" >> symbol ";" >> pure KLPClosed
  Just (TWord "arithmetic") -> keyword "arithmetic" >> KLPArithmetic . map fromInteger <$> bracketedList integer <* symbol ";"
  Just (TWord "max-least") -> keyword "max-least" >> symbol "{" >> KLPMaxLeast <$> pLevelProof <*> pLevelProof <* symbol "}"
  Just (TWord "zero-left") -> keyword "zero-left" >> KLPZero <$> pLevel <* symbol ";"
  Just (TWord "refl") -> keyword "refl" >> KLPRefl <$> pLevel <* symbol ";"
  Just (TWord "trans") -> keyword "trans" >> symbol "{" >> KLPTrans <$> pLevelProof <*> pLevelProof <* symbol "}"
  Just (TWord "succ-mono") -> keyword "succ-mono" >> symbol "{" >> KLPSuccMono <$> pLevelProof <* symbol "}"
  Just (TWord "max-left") -> keyword "max-left" >> KLPMaxLeft <$> pLevel <*> pLevel <* symbol ";"
  Just (TWord "max-right") -> keyword "max-right" >> KLPMaxRight <$> pLevel <*> pLevel <* symbol ";"
  Just (TWord "add-mono-left") -> keyword "add-mono-left" >> KLPAddMonoLeft <$> pLevel <*> bracedProof
  Just (TWord "add-mono-right") -> keyword "add-mono-right" >> KLPAddMonoRight <$> pLevel <*> bracedProof
  Just token -> failP ("expected level proof, found " <> renderToken token)
  Nothing -> failP "unexpected end of level proof"
  where
    bracedProof = symbol "{" >> pLevelProof <* symbol "}"

pUniverseTelescope :: P [UniverseRef]
pUniverseTelescope = do
  hasDot <- nextIs (TSym ".")
  if not hasDot
    then pure []
    else do
      symbol "."
      symbol "{"
      refs <- sepUntil "}" "," pUniverseRef
      symbol "}"
      pure refs

pNominalUniverseTelescope :: P [(UniverseRef, UniverseVariance)]
pNominalUniverseTelescope = do
  hasDot <- nextIs (TSym ".")
  if not hasDot
    then pure []
    else do
      symbol "."
      symbol "{"
      refs <- sepUntil "}" "," $ do
        role <- pUniverseVariance
        ref <- pUniverseRef
        pure (ref, role)
      symbol "}"
      pure refs

pConstraintBlock :: P [KConstraint]
pConstraintBlock = do
  hasWhere <- nextIs (TWord "where")
  if not hasWhere
    then pure []
    else do
      keyword "where"
      symbol "{"
      constraints <- manyUntil "}" pConstraint
      symbol "}"
      pure constraints

pConstraint :: P KConstraint
pConstraint = do
  constraint <- pConstraintWithoutSemicolon
  symbol ";"
  pure constraint

pGlobalRef :: P StableRef
pGlobalRef = do
  symbol "@"
  name <- word
  symbol "#"
  stable <- stableId
  pure (StableRef name stable)

pCertificateRef :: P StableRef
pCertificateRef = do
  ref <- pGlobalRef
  unless ("certificate." `T.isPrefixOf` srName ref) $
    failP "a certificate identity must use the @certificate. namespace"
  pure ref

pSchemaCertificateRef :: P StableRef
pSchemaCertificateRef = do
  symbol "@"
  namespace <- word
  unless (namespace == "schema") $
    failP "a schema-certificate identity must use the @schema: namespace"
  symbol ":"
  name <- word
  symbol "#"
  StableRef ("schema:" <> name) <$> stableId

pLocalRef :: P LocalRef
pLocalRef = do
  symbol "%"
  name <- word
  symbol "#"
  ident <- integer
  when (ident < 0) (failP "local identity must be nonnegative")
  pure (LocalRef name (fromInteger ident))

pUniverseRef :: P UniverseRef
pUniverseRef = do
  symbol "^"
  name <- word
  symbol "#"
  ident <- integer
  when (ident < 0) (failP "universe identity must be nonnegative")
  pure (UniverseRef name (fromInteger ident))

stableId :: P Text
stableId = takeToken >>= \case
  TInt n -> pure (T.pack (show n))
  TWord x | not (T.null x) && T.all isHexDigit x -> pure x
  token -> failP ("expected hexadecimal stable identity, found " <> renderToken token)

pBinder :: P KBinder
pBinder = do
  symbol "("
  mode <- pObservationMode
  formation <- pFormationMode
  quantity <- pQuantity
  explicitness <- pExplicitness
  access <- pAccess
  origin <- peek >>= \case
    Just (TWord "generated") -> takeToken >> pure BinderGenerated
    _ -> pure BinderSourceWritten
  ref <- pLocalRef
  symbol ":"
  ty <- pTerm
  symbol ")"
  pure (KBinder mode formation quantity explicitness access origin ref ty)

pObservationMode :: P ObservationMode
pObservationMode = takeToken >>= \case
  TWord "ordinary" -> pure Ordinary
  TWord "parametric" -> pure Parametric
  token -> failP ("every declaration and binder requires an explicit observation mode; found " <> renderToken token)

pFormationMode :: P FormationMode
pFormationMode = takeToken >>= \case
  TWord "ordinary" -> pure FormationOrdinary
  TWord "parametric" -> pure FormationParametric
  token -> failP ("every dependent binder requires an explicit formation mode; found " <> renderToken token)

pQuantity :: P KQuantity
pQuantity = takeToken >>= \case
  TInt 0 -> pure KQ0
  TInt 1 -> pure KQ1
  TWord "omega" -> pure KQOmega
  TWord "affine" -> pure KQAffine
  TWord "relevant" -> pure KQRelevant
  TWord "quantity-term" -> do
    symbol "("
    tm <- pTerm
    symbol ")"
    pure (KQTerm tm)
  token -> failP ("invalid explicit quantity " <> renderToken token)

pExplicitness :: P KExplicitness
pExplicitness = takeToken >>= \case
  TWord "explicit" -> pure KExplicit
  TWord "implicit" -> pure KImplicit
  token -> failP ("expected explicitness, found " <> renderToken token)

pAccess :: P KAccess
pAccess = takeToken >>= \case
  TWord "value" -> pure KValue
  TWord "borrow" -> do
    bracket <- nextIs (TSym "[")
    if bracket
      then do
        symbol "["
        ref <- pRef
        symbol "]"
        pure (KBorrow (Just ref))
      else pure (KBorrow Nothing)
  token -> failP ("expected access mode, found " <> renderToken token)

pRef :: P KRef
pRef = peek >>= \case
  Just (TSym "%") -> KRLocal <$> pLocalRef
  Just (TSym "@") -> KRGlobal <$> pGlobalRef
  Just token -> failP ("expected local or global reference, found " <> renderToken token)
  Nothing -> failP "expected reference"

pTerm :: P KTerm
pTerm = peek >>= \case
  Just (TSym "%") -> do
    term <- KTLocal <$> pLocalRef <*> pUniverseInstantiation
    pJuxtaposition term
  Just (TSym "@") -> do
    ref <- pGlobalRef
    inst <- pUniverseInstantiation
    pJuxtaposition (KTGlobal ref inst)
  Just (TWord "Type") -> keyword "Type" >> KTType <$> pLevel
  Just (TSym "(") -> pPiOrGrouped >>= pJuxtaposition
  Just (TWord "sigma") -> keyword "sigma" >> KTSigma <$> pBinder <*> bracedTerm
  Just (TWord "lambda") -> keyword "lambda" >> KTLambda <$> pBinder <*> bracedTerm
  Just (TWord "apply") -> do
    keyword "apply"
    f <- pTerm
    hasArguments <- nextIs (TSym "(")
    if hasArguments then KTApply f <$> pArguments else pure f
  Just (TWord "block") -> pBlock
  Just (TWord "letrec") -> pLocalRecGroup
  Just (TWord "case") -> pCase
  Just (TWord "construct") -> do
    keyword "construct"
    ref <- pGlobalRef
    universes <- pUniverseInstantiation
    KTConstruct ref universes <$> pArguments
  Just (TWord "project") -> keyword "project" >> KTProject <$> pFieldRef <*> pTerm
  Just (TWord "lift") -> pLift
  Just (TWord "schema-lift") -> pSchemaLift
  Just (TWord "ascribe") -> do
    keyword "ascribe"
    value <- pTerm
    symbol ":"
    KTAscribe value <$> pTerm
  Just (TWord "term-node") -> do
    keyword "term-node"
    tag <- stringLiteral
    fields <- pNamedValues
    pure (KTGeneric tag fields)
  Just token -> failP ("expected KCore term, found " <> renderToken token)
  Nothing -> failP "unexpected end of KCore term"

pSchemaLift :: P KTerm
pSchemaLift = do
  keyword "schema-lift"
  symbol "["
  keyword "family"
  symbol "="
  family <- pGlobalRef
  symbol ","
  keyword "from"
  symbol "="
  from <- pUniverseInstantiation
  symbol ","
  keyword "to"
  symbol "="
  to <- pUniverseInstantiation
  symbol ","
  keyword "certificate"
  symbol "="
  certificate <- pSchemaCertificateRef
  symbol ","
  keyword "roles"
  symbol "="
  roles <- bracketedList pSchemaRoleEvidence
  symbol ","
  keyword "targetArgs"
  symbol "="
  targetArguments <- pArguments
  symbol "]"
  KTSchemaLift family from to certificate roles targetArguments <$> pTerm

pSchemaRoleEvidence :: P KSchemaRoleEvidence
pSchemaRoleEvidence = word >>= \case
  "invariant" -> pure KSchemaInvariant
  "irrelevant" -> pure KSchemaIrrelevant
  "covariant" -> KSchemaCovariant <$> pEvidence
  role -> failP ("unknown schema-lift role evidence '" <> role <> "'")

-- The schema permits the compact application-spine spelling used by the
-- normative fixtures. Its arguments are explicit by construction; canonical
-- output writes the tagged parenthesized form.
pJuxtaposition :: KTerm -> P KTerm
pJuxtaposition function = peek >>= \case
  Just (TSym "%") -> do
    argument <- KTLocal <$> pLocalRef <*> pUniverseInstantiation
    pJuxtaposition (appendExplicitArgument function argument)
  Just (TSym "@") -> do
    ref <- pGlobalRef
    levels <- pUniverseInstantiation
    pJuxtaposition (appendExplicitArgument function (KTGlobal ref levels))
  _ -> pure function

appendExplicitArgument :: KTerm -> KTerm -> KTerm
appendExplicitArgument (KTApply function arguments) argument =
  KTApply function (arguments ++ [KArgument KExplicit argument])
appendExplicitArgument function argument = KTApply function [KArgument KExplicit argument]

pBlock :: P KTerm
pBlock = do
  keyword "block"
  symbol "{"
  go
  where
    go = peek >>= \case
      Just (TWord "let") -> do
        keyword "let"
        binder <- pBinder
        symbol "="
        rhs <- pTerm
        symbol ";"
        prepend (KBLet binder rhs)
      _ -> do
        result <- pTerm
        symbol "}"
        pure (KTBlock [] result)
    prepend item = do
      next <- go
      case next of
        KTBlock items result -> pure (KTBlock (item : items) result)
        _ -> failP "internal block parser invariant"

pLocalRecGroup :: P KTerm
pLocalRecGroup = do
  definitions <- pLocalRecDefinitions
  keyword "in"
  KTLetRec definitions <$> pTerm

pLocalRecDefinitions :: P [KLocalDef]
pLocalRecDefinitions = do
  keyword "letrec"
  symbol "{"
  definitions <- manyWhile (Just (TWord "def") ==) pLocalDef
  when (null definitions) (failP "letrec requires at least one local definition")
  symbol "}"
  pure definitions

pLocalDef :: P KLocalDef
pLocalDef = do
  keyword "def"
  mode <- pObservationMode
  ref <- pLocalRef
  universes <- pUniverseTelescope
  symbol ":"
  ty <- pTerm
  symbol "{"
  keyword "body"
  symbol "="
  body <- pTerm
  symbol ";"
  symbol "}"
  pure (KLocalDef ref mode universes ty body)

pCase :: P KTerm
pCase = do
  keyword "case"
  scrutinee <- pTerm
  symbol ":"
  resultType <- pTerm
  symbol "{"
  alternatives <- manyUntil "}" pCaseAlt
  when (null alternatives) (failP "case requires at least one alternative")
  symbol "}"
  pure (KTCase scrutinee resultType alternatives)

pCaseAlt :: P KCaseAlt
pCaseAlt = peek >>= \case
  Just (TWord "case") -> do
    keyword "case"
    constructor <- pGlobalRef
    universes <- pUniverseInstantiation
    bindings <- pCaseBindings
    KCaseConstructor constructor universes bindings <$> bracedTerm
  Just (TWord "default") -> keyword "default" >> KCaseDefault <$> bracedTerm
  Just (TWord "pattern") -> do
    keyword "pattern"
    pattern' <- pPattern
    guard' <- do
      guarded <- nextIs (TWord "when")
      if guarded then keyword "when" >> Just <$> pTerm else pure Nothing
    KCasePattern pattern' guard' <$> bracedTerm
  Just token -> failP ("expected case alternative, found " <> renderToken token)
  Nothing -> failP "unexpected end of case alternatives"
  where
    pCaseBindings = peek >>= \case
      Just (TSym "(") ->
        (:) . KCasePayload <$> pBinder <*> pCaseBindings
      Just (TWord "bridge") -> do
        keyword "bridge"
        binder <- pBinder
        proof <- bracedTerm
        (KCaseBridge (KConstructorBridge binder proof) :) <$> pCaseBindings
      _ -> pure []

pPiOrGrouped :: P KTerm
pPiOrGrouped = do
  symbol "("
  binderStart <- nextIs (TSym "(")
  if binderStart
    then do
      binder <- pBinder
      symbol "->"
      codomain <- pTerm
      symbol ")"
      pure (KTPi binder codomain)
    else do
      term <- pTerm
      symbol ")"
      pure term

bracedTerm :: P KTerm
bracedTerm = symbol "{" >> pTerm <* symbol "}"

pArguments :: P [KArgument]
pArguments = do
  symbol "("
  arguments <- sepUntil ")" "," $ peek >>= \case
    Just (TWord "explicit") -> KArgument <$> pExplicitness <*> pTerm
    Just (TWord "implicit") -> KArgument <$> pExplicitness <*> pTerm
    _ -> KArgument KExplicit <$> pTerm
  symbol ")"
  pure arguments

pUniverseInstantiation :: P [KLevel]
pUniverseInstantiation = do
  dot <- nextIs (TSym ".")
  if not dot
    then pure []
    else do
      symbol "."
      symbol "{"
      levels <- sepUntil "}" "," pLevel
      symbol "}"
      pure levels

pFieldRef :: P StableRef
pFieldRef = do
  symbol "@"
  keyword "field"
  symbol ":"
  name <- word
  symbol "#"
  StableRef name <$> stableId

pLift :: P KTerm
pLift = do
  keyword "lift"
  symbol "["
  from <- pLevel
  symbol "<="
  to <- pLevel
  keyword "by"
  evidence <- pEvidence
  symbol "]"
  KTLift from to evidence <$> pTerm

pEvidence :: P KEvidence
pEvidence = peek >>= \case
  Just (TSym "%") -> KELocal <$> pLocalRef
  Just (TSym "@") -> do
    ref <- pGlobalRef
    KEGlobal ref <$> pUniverseInstantiation
  Just (TWord "certificate") -> do
    keyword "certificate"
    parenthesized $ do
      ref <- pCertificateRef
      KECertificate ref <$> pUniverseInstantiation
  Just token -> failP ("expected lift evidence, found " <> renderToken token)
  Nothing -> failP "expected lift evidence"

pLevel :: P KLevel
pLevel = do
  first <- pLevelAtom
  go first
  where
    go lhs = do
      plus <- nextIs (TSym "+")
      if plus
        then symbol "+" >> pLevelAtom >>= go . KLAdd lhs
        else pure lhs

pLevelAtom :: P KLevel
pLevelAtom = peek >>= \case
  Just (TInt _) -> KLFinite <$> integer
  Just (TSym "^") -> KLUniverse <$> pUniverseRef
  Just (TSym "@") -> KLGlobal <$> pGlobalRef
  Just (TWord "succ") -> keyword "succ" >> unaryLevel KLSucc
  Just (TWord "max") -> keyword "max" >> binaryLevel KLMax
  Just (TWord "add") -> keyword "add" >> binaryLevel KLAdd
  Just (TWord "omega") -> keyword "omega" >> pure (KLGlobal (stableRefForGlobal prelTypeLevelOmega))
  Just (TWord "level-term") -> keyword "level-term" >> KLTerm <$> parenthesized pTerm
  Just token -> failP ("expected universe level, found " <> renderToken token)
  Nothing -> failP "expected universe level"
  where
    unaryLevel ctor = ctor <$> parenthesized pLevel
    binaryLevel ctor = do
      symbol "("
      lhs <- pLevel
      symbol ","
      rhs <- pLevel
      symbol ")"
      pure (ctor lhs rhs)

parenthesized :: P a -> P a
parenthesized p = symbol "(" >> p <* symbol ")"

pNamedValues :: P [(Text, KValueNode)]
pNamedValues = do
  symbol "{"
  fields <- manyUntil "}" $ do
    name <- word
    symbol "="
    value <- pValueNode
    symbol ";"
    pure (name, value)
  symbol "}"
  pure fields

decodeBuiltinTermNode :: Text -> [(Text, KValueNode)] -> Either Text KTerm
decodeBuiltinTermNode tag fields
  | tag == "impl.kappa.core.literal" = KTLiteral <$> decodeLiteral fields
  | tag == "impl.kappa.core.record-type" =
      do
        names <- required "names" fields >>= decodeTexts
        binders <- required "fields" fields >>= decodeBinders
        if length names == length binders
          then pure (KTRecordType (zip (map stableFieldRefFromReadable names) binders))
          else Left "record-type names and fields must have equal length"
  | tag == "impl.kappa.core.record-value" = do
      names <- required "names" fields >>= decodeTexts
      values <- required "values" fields >>= decodeTerms
      if length names == length values
        then pure (KTRecordValue (zip names values))
        else Left "record-value names and values must have equal length"
  | tag == "impl.kappa.core.if" =
      KTIf
        <$> (required "condition" fields >>= decodeTerm)
        <*> (required "then" fields >>= decodeTerm)
        <*> (required "else" fields >>= decodeTerm)
  | otherwise = Right (KTGeneric tag fields)
  where
    required name entries =
      maybe (Left ("term node '" <> tag <> "' is missing field '" <> name <> "'")) Right (lookup name entries)
    decodeTerm = \case KVTerm term -> Right term; _ -> Left "expected term-valued node field"
    decodeTerms = \case
      KVList values -> mapM decodeTerm values
      _ -> Left "expected list of terms"
    decodeTexts = \case
      KVList values -> mapM (\case KVText value -> Right value; _ -> Left "expected text list element") values
      _ -> Left "expected list of text values"
    decodeBinders = \case
      KVList values -> mapM decodeBinder values
      _ -> Left "expected list of binder descriptors"
    decodeBinder = \case
      KVTerm (KTPi binder (KTType (KLFinite 0))) -> Right binder
      _ -> Left "record-type fields must be explicit binder descriptors"

decodedBuiltinTermTags :: Set Text
decodedBuiltinTermTags =
  Set.fromList
    [ "impl.kappa.core.literal"
    , "impl.kappa.core.record-type"
    , "impl.kappa.core.record-value"
    , "impl.kappa.core.if"
    ]

decodeLiteral :: [(Text, KValueNode)] -> Either Text Literal
decodeLiteral fields = do
  kind <- case lookup "kind" fields of
    Just (KVText value) -> Right value
    _ -> Left "literal node requires a text 'kind' field"
  case kind of
    "int" -> LitInt <$> integerField
    "double" -> LitDouble <$> textReadField
    "string" -> LitStr <$> textField
    "scalar" -> do
      value <- textField
      case T.unpack value of
        [scalar] -> Right (LitScalar scalar)
        _ -> Left "scalar literal must contain exactly one Unicode scalar"
    "byte" -> do
      value <- integerField
      if value >= 0 && value <= 255
        then Right (LitByte (fromInteger value))
        else Left "byte literal is outside 0..255"
    "bytes" -> LitBytes . BS.pack <$> byteListField
    "grapheme" -> LitGrapheme <$> textField
    _ -> Left ("unknown literal kind '" <> kind <> "'")
  where
    valueField = maybe (Left "literal node requires a 'value' field") Right (lookup "value" fields)
    integerField = valueField >>= \case KVInteger value -> Right value; _ -> Left "literal value must be an integer"
    textField = valueField >>= \case KVText value -> Right value; _ -> Left "literal value must be text"
    textReadField = do
      raw <- textField
      maybe (Left "literal text value is malformed") Right (readMaybe (T.unpack raw))
    byteListField = valueField >>= \case
      KVList values -> mapM decodeByte values
      _ -> Left "byte-string literal value must be an integer list"
    decodeByte = \case
      KVInteger value | value >= 0 && value <= 255 -> Right (fromInteger value)
      _ -> Left "byte-string element is outside 0..255"

pValueNode :: P KValueNode
pValueNode = peek >>= \case
  Just (TWord "integer-value") ->
    keyword "integer-value" >> symbol "(" >> (KVInteger <$> integer) <* symbol ")"
  Just (TWord "string-value") ->
    keyword "string-value" >> symbol "(" >> (KVText <$> stringLiteral) <* symbol ")"
  Just (TWord "level-value") ->
    keyword "level-value" >> symbol "(" >> (KVLevel <$> pLevel) <* symbol ")"
  Just (TWord "quantity-value") ->
    keyword "quantity-value" >> symbol "(" >> (KVQuantity <$> pQuantity) <* symbol ")"
  Just (TWord "term-value") ->
    keyword "term-value" >> symbol "(" >> (KVTerm <$> pTerm) <* symbol ")"
  Just (TWord "global-ref-value") -> do
    keyword "global-ref-value"
    symbol "("
    ref <- pGlobalRef
    levels <- pUniverseInstantiation
    symbol ")"
    pure (KVGlobal ref levels)
  Just (TWord "local-ref-value") -> do
    keyword "local-ref-value"
    symbol "("
    ref <- pLocalRef
    levels <- pUniverseInstantiation
    symbol ")"
    pure (KVLocal ref levels)
  Just (TWord "ordinary") -> keyword "ordinary" >> pure (KVObservationMode Ordinary)
  Just (TWord "parametric") -> keyword "parametric" >> pure (KVObservationMode Parametric)
  Just (TWord "explicit") -> keyword "explicit" >> pure (KVExplicitness KExplicit)
  Just (TWord "implicit") -> keyword "implicit" >> pure (KVExplicitness KImplicit)
  Just (TWord "value") -> KVAccess <$> pAccess
  Just (TWord "borrow") -> KVAccess <$> pAccess
  Just (TWord "binder-value") -> do
    keyword "binder-value"
    symbol "("
    binder <- pBinder
    symbol ")"
    pure (KVBinder binder)
  Just (TWord "pattern-value") -> do
    keyword "pattern-value"
    symbol "("
    pattern' <- pPattern
    symbol ")"
    pure (KVPattern pattern')
  Just (TSym "[") -> do
    symbol "["
    values <- sepUntil "]" "," pValueNode
    symbol "]"
    pure (KVList values)
  Just token -> failP ("expected typed KCore value wrapper, found " <> renderToken token)
  Nothing -> failP "unexpected end of KCore generic value"

pPattern :: P KPattern
pPattern = do
  keyword "pattern-node"
  tag <- stringLiteral
  fields <- pNamedValues
  either failP pure (decodePatternNode tag fields)

decodePatternNode :: Text -> [(Text, KValueNode)] -> Either Text KPattern
decodePatternNode tag fields = do
  whenEither (length names /= Set.size (Set.fromList names)) "pattern node has duplicate fields"
  slot <- binderField "slot"
  exposed <- boolField "exposed"
  node' <- case tag of
    "wild" -> exact common >> pure KPNWild
    "literal" -> do
      exact (common ++ ["value"])
      value <- termField "value"
      case value of
        KTLiteral literal -> pure (KPNLiteral literal)
        _ -> Left "literal pattern value must be a typed literal term"
    "constructor" -> do
      exact (common ++ ["constructor", "existentials", "bridges", "fields"])
      (constructor, levels) <- globalField "constructor"
      KPNConstructor constructor levels
        <$> binderListField "existentials"
        <*> bridgeListField "bridges"
        <*> patternListField "fields"
    "tuple" -> exact (common ++ ["fields"]) >> KPNTuple <$> patternListField "fields"
    "record" -> do
      exact (common ++ ["names", "selected", "fields", "rest"])
      fieldNames <- textListField "names"
      selected <- boolListField "selected"
      patterns <- patternListField "fields"
      whenEither (length fieldNames /= length patterns || length selected /= length patterns)
        "record pattern names, selection bits, and fields have different arities"
      rest <- patternListField "rest" >>= \case
        [] -> pure Nothing
        [pattern'] -> pure (Just pattern')
        _ -> Left "record rest pattern requires zero or one typed pattern slot"
      pure (KPNRecord (zipWith3 (,,) (map stableFieldRefFromReadable fieldNames) selected patterns) rest)
    "inject" -> exact (common ++ ["tag", "payload"]) >> KPNInject <$> textField "tag" <*> patternField "payload"
    "inject-rest" -> do
      exact (common ++ ["excluded"])
      KPNInjectRest <$> textListField "excluded"
    "or" -> exact (common ++ ["alternatives", "permutations"]) >> KPNOr <$> patternListField "alternatives" <*> integerMatrixField "permutations"
    "as" -> exact (common ++ ["payload"]) >> KPNAs <$> patternField "payload"
    _ -> Left ("unsupported KCore pattern node '" <> tag <> "'")
  pure (KPattern slot exposed node')
  where
    names = map fst fields
    common = ["slot", "exposed"]
    exact expected =
      whenEither (Set.fromList names /= Set.fromList expected)
        ("pattern node '" <> tag <> "' requires fields " <> T.intercalate ", " expected)
    field name = maybe (Left ("pattern node is missing field '" <> name <> "'")) Right (lookup name fields)
    binderField name = field name >>= \case KVBinder binder -> Right binder; _ -> Left (name <> " must be a binder value")
    boolField name = field name >>= \case
      KVInteger 0 -> Right False
      KVInteger 1 -> Right True
      _ -> Left (name <> " must be integer-value(0) or integer-value(1)")
    termField name = field name >>= \case KVTerm term -> Right term; _ -> Left (name <> " must be a term value")
    textField name = field name >>= \case KVText value -> Right value; _ -> Left (name <> " must be a string value")
    globalField name = field name >>= \case KVGlobal ref levels -> Right (ref, levels); _ -> Left (name <> " must be a global reference value")
    patternField name = field name >>= \case KVPattern pattern' -> Right pattern'; _ -> Left (name <> " must be a pattern value")
    listField name = field name >>= \case KVList values -> Right values; _ -> Left (name <> " must be a list")
    binderListField name = listField name >>= mapM (\case KVBinder binder -> Right binder; _ -> Left (name <> " must contain only binders"))
    bridgeListField name = listField name >>= mapM (\case
      KVList [KVBinder binder, KVTerm proof] ->
        Right (KConstructorBridge binder proof)
      _ -> Left (name <> " must contain only [binder, proof] pairs"))
    patternListField name = listField name >>= mapM (\case KVPattern pattern' -> Right pattern'; _ -> Left (name <> " must contain only patterns"))
    textListField name = listField name >>= mapM (\case KVText value -> Right value; _ -> Left (name <> " must contain only strings"))
    boolListField name = listField name >>= mapM (\case
      KVInteger 0 -> Right False
      KVInteger 1 -> Right True
      _ -> Left (name <> " must contain only integer booleans"))
    integerMatrixField name = listField name >>= mapM (mapM integerValue <=< listValue)
    listValue = \case KVList values -> Right values; _ -> Left "pattern permutation must be an integer list"
    integerValue = \case KVInteger value | value >= 0 -> Right (fromInteger value); _ -> Left "pattern permutation index must be nonnegative"
    whenEither condition message = if condition then Left message else Right ()

manyWhile :: (Maybe Token -> Bool) -> P a -> P [a]
manyWhile predicate parser = do
  token <- peek
  if predicate token
    then (:) <$> parser <*> manyWhile predicate parser
    else pure []

manyUntil :: Text -> P a -> P [a]
manyUntil end parser = do
  done <- nextIs (TSym end)
  if done then pure [] else (:) <$> parser <*> manyUntil end parser

sepUntil :: Text -> Text -> P a -> P [a]
sepUntil end separator parser = do
  done <- nextIs (TSym end)
  if done
    then pure []
    else do
      first <- parser
      rest <- go
      pure (first : rest)
  where
    go = do
      comma <- nextIs (TSym separator)
      if comma
        then symbol separator >> ((:) <$> parser <*> go)
        else pure []

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM condition yes no = condition >>= \b -> if b then yes else no

-- Verification --------------------------------------------------------------

parseAndVerifyKCoreText :: Text -> Either KCoreTextError KCoreFile
parseAndVerifyKCoreText source = do
  file <- parseKCoreText source
  verifyKCoreText file
  pure file

-- | Parse and verify against the authoritative globals available at the
-- checkpoint. A textual stable reference that is neither declared by the
-- file nor present here is unavailable, regardless of its readable name.
parseAndVerifyKCoreTextWithGlobals :: EvalCtx -> Map GName GlobalDef -> Text -> Either KCoreTextError KCoreFile
parseAndVerifyKCoreTextWithGlobals ec globals source = do
  file <- parseKCoreText source
  verifyKCoreTextWithGlobals ec globals file
  pure file

parseAndVerifyKCoreTextWithEnvironment
  :: EvalCtx
  -> Map GName GlobalDef
  -> Map GName KCoreConstructorInfo
  -> Text
  -> Either KCoreTextError KCoreFile
parseAndVerifyKCoreTextWithEnvironment ec globals constructors source = do
  file <- parseKCoreText source
  verifyKCoreTextWithEnvironment ec globals constructors file
  pure file

verifyKCoreText :: KCoreFile -> Either KCoreTextError ()
verifyKCoreText =
  verifyKCoreTextWithExternal
    Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

parseAndVerifyKCoreInterface :: Text -> Either KCoreTextError KCoreInterface
parseAndVerifyKCoreInterface =
  parseAndVerifyKCoreInterfaceWithInterfaces []

parseAndVerifyKCoreInterfaceWithInterfaces
  :: [KCoreInterface]
  -> Text
  -> Either KCoreTextError KCoreInterface
parseAndVerifyKCoreInterfaceWithInterfaces interfaces source = do
  file <- parseKCoreText source
  verifyKCoreTextWithInterfaces interfaces file
  pure (interfaceFromVerifiedKCore file)

verifyKCoreTextWithInterfaces
  :: [KCoreInterface]
  -> KCoreFile
  -> Either KCoreTextError ()
verifyKCoreTextWithInterfaces interfaces file = do
  merged <- mergeKCoreInterfaces interfaces
  verifyKCoreTextWithExternal
    (kciTypes merged)
    (kciModes merged)
    (kciBodies merged)
    (kciRecordInterfaces merged)
    (kciAssociatedNormalizations merged)
    (kciConstructors merged)
    Map.empty
    (kciLevelCertificates merged)
    (kciSchemaCertificates merged)
    (kciNominalFamilies merged)
    file

verifyKCoreTextWithGlobals :: EvalCtx -> Map GName GlobalDef -> KCoreFile -> Either KCoreTextError ()
verifyKCoreTextWithGlobals ec globals = verifyKCoreTextWithEnvironment ec globals Map.empty

verifyKCoreTextWithEnvironment
  :: EvalCtx
  -> Map GName GlobalDef
  -> Map GName KCoreConstructorInfo
  -> KCoreFile
  -> Either KCoreTextError ()
verifyKCoreTextWithEnvironment ec globals constructors file = do
  externalEntries <- mapM externalEntry (Map.toList neededGlobals)
  constructorEntries <- mapM externalConstructorEntry (Map.toList neededConstructors)
  let externalTypes =
        Map.union
          (Map.fromList [(ref, signature) | (ref, _, signature, _, _, _, _) <- externalEntries])
          ( Map.fromList
              [ (ref, (universes, signature))
              | (_, ref, _, (universes, _, signature), _, _) <- constructorEntries
              ]
          )
      externalModes =
        Map.union
          (Map.fromList [(ref, mode) | (ref, mode, _, _, _, _, _) <- externalEntries])
          (Map.fromList [(ref, Ordinary) | (_, ref, _, _, _, _) <- constructorEntries])
      externalBodies = Map.fromList [(ref, body) | (ref, _, _, Just body, _, _, _) <- externalEntries]
      externalRecordInterfaces =
        Map.fromList [(ref, interface) | (ref, _, _, _, Just interface, _, _) <- externalEntries]
      externalAssociatedBodies =
        [ (ref, universes, body)
        | (ref, _, (universes, _), _, _, Just body, _) <- externalEntries
        ]
      externalConstructors =
        Map.fromList [(ref, signature) | (_, ref, _, signature, _, _) <- constructorEntries]
      externalConstructorFields =
        Map.fromList [(ref, fields) | (_, ref, _, _, fields, _) <- constructorEntries]
      externalLevelCertificates =
        Map.fromList
          [ (ref, (universes, constraints, theorem, proof))
          | (_, _, _, _, _, _, declarations) <- externalEntries
          , KDLevelCertificate ref universes constraints theorem proof <- declarations
          ]
  externalNominalEntries <- fmap catMaybes . forM (Map.toAscList neededGlobals) $ \(global, definition) ->
    case gdNominalSummary definition of
      Just summary
        | verifyNominalCumulativitySummary summary
        , let familyRef = stableRefForGlobal global
        , Just (universes, signature) <- Map.lookup familyRef externalTypes -> do
            let (allBinders, result) = splitPiTelescope signature
                binders = take (ncsSaturationArity summary) allBinders
                certificateName = unSchemaActionCertificateId (ncsCertificateId summary)
                certificateRef = stableSchemaCertificateRef certificateName
                declaredConstructors =
                  [ declaration
                  | (owner, _, _, _, _, declaration) <- constructorEntries
                  , owner == familyRef
                  ]
            dictionaryConstructors <-
              case (declaredConstructors, Map.lookup familyRef externalRecordInterfaces) of
                ([], Just (interfaceUniverses, interface)) -> do
                  unless (interfaceUniverses == universes) $
                    Left
                      ( invalid
                          ( "external nominal record interface universe telescope disagrees with "
                              <> renderStable familyRef
                          )
                      )
                  pure
                    . pure
                    =<< nominalDictionaryConstructor
                      familyRef
                      (stableRefForConstructor global)
                      universes
                      binders
                      interface
                _ -> pure declaredConstructors
            let
                family =
                  KNominalFamily
                    (zip universes (ncsRoles summary))
                    binders
                    result
                    certificateRef
                    dictionaryConstructors
            monotoneWitnesses <- kcoreMonotoneWitnesses binders summary
            let certificate =
                  KSchemaCertificate
                    { kscRef = certificateRef
                    , kscFamily = familyRef
                    , kscCheckerVersion = toInteger (ncsCheckerVersion summary)
                    , kscSemanticVersions = ncsSemanticVersions summary
                    , kscSignatureHash = kCoreNominalSignatureHash familyRef family
                    , kscSaturationArity = ncsSaturationArity summary
                    , kscRoles = ncsRoles summary
                    , kscClauseKinds = ncsClauseKinds summary
                    , kscMonotoneWitnesses = monotoneWitnesses
                    }
            pure (Just (familyRef, certificateRef, family, certificate))
      _ -> pure Nothing
  let externalNominalFamilies = Map.fromList [(familyRef, family) | (familyRef, _, family, _) <- externalNominalEntries]
      externalSchemaCertificates = Map.fromList [(certificateRef, certificate) | (_, certificateRef, _, certificate) <- externalNominalEntries]
      externalAssociatedContext =
        VerifyContext
          (Map.map (length . fst) externalTypes)
          externalTypes
          externalModes
          externalBodies
          externalRecordInterfaces
          Map.empty
          externalConstructors
          (Map.union (nominalConstructorFields externalNominalFamilies) externalConstructorFields)
          externalLevelCertificates
          externalSchemaCertificates
          externalNominalFamilies
          (Set.singleton "impl.kappa")
          []
      externalAssociatedCandidates =
        deriveAssociatedNormalizations
          externalAssociatedContext
          externalAssociatedBodies
  externalAssociatedNormalizations <-
    verifyAssociatedNormalizations
      externalAssociatedContext
      externalAssociatedCandidates
  verifyKCoreTextWithExternal externalTypes externalModes externalBodies externalRecordInterfaces externalAssociatedNormalizations externalConstructors
    externalConstructorFields externalLevelCertificates externalSchemaCertificates externalNominalFamilies file
  where
    conversionContext = CoreConversionContext (Just ec) globals constructors
    fileRefs = Set.fromList (allStableRefs file)
    initialGlobals =
      Set.fromList
        [ global
        | global <- Map.keys globals
        , stableRefForGlobal global `Set.member` fileRefs
        ]
    initialConstructors =
      Set.fromList
        [ constructor
        | constructor <- Map.keys constructors
        , stableRefForConstructor constructor `Set.member` fileRefs
        ]
    (neededGlobalNames, neededConstructorNames) =
      closeEnvironment initialGlobals initialConstructors
    neededGlobals = Map.restrictKeys globals neededGlobalNames
    neededConstructors = Map.restrictKeys constructors neededConstructorNames
    closeEnvironment selectedGlobals selectedConstructors =
      let globalTerms =
            [ globalCoreType ec definition
            | global <- Set.toList selectedGlobals
            , Just definition <- [Map.lookup global globals]
            ]
              ++ [ body
                 | global <- Set.toList selectedGlobals
                 , Just definition <- [Map.lookup global globals]
                 , gdReducible definition
                 , body <- maybeToList (gdCoreBody definition <|> (quote ec 0 <$> gdValue definition))
                 ]
              ++ [ interface
                 | global <- Set.toList selectedGlobals
                 , Just definition <- [Map.lookup global globals]
                 , isJust (gdNominalSummary definition)
                 , interface <- maybeToList (quote ec 0 <$> gdValue definition)
                 ]
          constructorTerms =
            [ kcciType info
            | constructor <- Set.toList selectedConstructors
            , Just info <- [Map.lookup constructor constructors]
            ]
          termDependencies = Set.unions (map globalsOfTerm (globalTerms ++ constructorTerms))
          -- A nominal interface freezes the selected ordinary monotonicity
          -- evidence in its schema certificate.  Those terms are not part of
          -- the family's ordinary type, so closing only over signature/body
          -- terms can omit private proof dependencies needed to replay an
          -- imported certificate.  Follow the checker-resolved identities in
          -- the witness closure; the next fixed-point iteration then follows
          -- their types and reducible bodies in the usual way.
          witnessDependencies =
            Set.fromList
              [ dependency
              | global <- Set.toList selectedGlobals
              , Just definition <- [Map.lookup global globals]
              , Just summary <- [gdNominalSummary definition]
              , witness <- nscMonotoneWitnesses (ncsClosure summary)
              , evidenceDependency <- nmwDependencies witness
              , dependency <- maybeToList (evidenceGlobal evidenceDependency)
              ]
          dependencies = Set.union termDependencies witnessDependencies
          constructorFamilies =
            Set.fromList
              [ kcciData info
              | constructor <- Set.toList selectedConstructors
              , Just info <- [Map.lookup constructor constructors]
              ]
          familyConstructors =
            Set.fromList
              [ constructor
              | (constructor, info) <- Map.toList constructors
              , kcciData info `Set.member` selectedGlobals
              ]
          nextGlobals =
            Set.union selectedGlobals
              ( Set.filter (`Map.member` globals)
                  (Set.union dependencies constructorFamilies)
              )
          nextConstructors =
            Set.unions
              [ selectedConstructors
              , familyConstructors
              , Set.filter (`Map.member` constructors) dependencies
              ]
       in if nextGlobals == selectedGlobals && nextConstructors == selectedConstructors
            then (selectedGlobals, selectedConstructors)
            else closeEnvironment nextGlobals nextConstructors
    evidenceGlobal = \case
      NominalGlobalDependency owner name -> Just (GName (ModuleName owner) name)
      NominalConstructorDependency owner name -> Just (GName (ModuleName owner) name)
      NominalLocalDependency {} -> Nothing
      -- Field identities are replayed in the context of their receiver.  The
      -- receiver's resolved owner is independently present in the canonical
      -- term dependency set, while fields are not standalone environment
      -- declarations.
      NominalFieldDependency {} -> Nothing
    externalEntry (g, gd) =
      let telescope = gdUniverses gd
          universes = [UniverseRef "u" i | i <- [0 .. dutParameterCount telescope - 1]]
          tyCore = globalCoreType ec gd
          ownerConstraints = declarationUniverseConstraints (dutParameterCount telescope) tyCore
          bodyCore =
            if gdReducible gd
              then gdCoreBody gd <|> (quote ec 0 <$> gdValue gd)
              else Nothing
          valueCore = quote ec 0 <$> gdValue gd
          interfaceCore = valueCore >>= \value ->
            if coreTermHasRecordInterface value then Just value else Nothing
          associatedCore =
            (gdCoreBody gd <|> valueCore) >>= \value ->
              if coreTermHasDictionaryValue value then Just value else Nothing
          -- Opaque nominal records (in particular trait dictionaries) retain
          -- their structural projection interface in the checked value even
          -- though their definition body is not reducible.  Its lifts need
          -- the same independently replayable certificates as signatures and
          -- bodies; omitting it here made interface conversion fail and then
          -- hid the real authority from projection verification.
          terms =
            tyCore
              : maybeToList bodyCore
              ++ maybeToList interfaceCore
              ++ maybeToList associatedCore
          closedRelations =
            Map.fromList
              [ (relation, constraint)
              | term <- terms
              , relation <- foldTerm collectLiftRelation (const []) term
              , Right constraint <- [uncurry coreLevelConstraint relation]
              , closedConstraint constraint
              , constraintProved emptyAssumptions constraint
              ]
          closedEntries =
            [ let certificateName =
                    "certificate.generated.external."
                      <> stableHex (T.pack (show relation))
                  ref = stableLevelCertificateRef certificateName
               in ( relation
                  , LiftCertificateKey (fst relation) (snd relation) []
                  , LiftCertificateUse ref []
                  , KDLevelCertificate ref [] [] theorem KLPClosed
                  )
            | (relation, theorem) <- Map.toAscList closedRelations
            ]
          closedUses = Map.fromList [(key, use) | (_, key, use, _) <- closedEntries]
          closedDeclarations = [declaration | (_, _, _, declaration) <- closedEntries]
          moduleText = case g of
            GName (ModuleName parts) _ -> T.intercalate "." parts
       in do
          (scopedDeclarations, scopedUses) <-
            renderScopedLevelCertificates moduleText closedUses g telescope ownerConstraints terms
          let certificateUses = Map.union scopedUses closedUses
          ty <- case coreToTextWithEvidenceIn conversionContext certificateUses tyCore of
            Left err ->
              Left
                err
                  { kcteMessage =
                      "while importing external signature " <> gKey g <> ": " <> kcteMessage err
                  }
            Right converted -> pure converted
          body <-
            -- External bodies are consulted only for type-head unfolding.
            -- Reducibility is the checker-owned semantic authority;
            -- inspecting the classifier for a bare Sort would incorrectly
            -- exclude parameterized type aliases. Prefer the finalized Core
            -- body so captured NbE environments never become part of the
            -- interchange. A reducible body must not silently become opaque:
            -- that would make independent definitional equality depend on
            -- whether conversion happened to fail.
            if gdReducible gd
              then case bodyCore of
                Nothing -> pure Nothing
                Just coreBody ->
                  case coreToTextAgainstWithEvidenceIn conversionContext certificateUses tyCore coreBody of
                    Left err ->
                      Left
                        err
                          { kcteMessage =
                              "while importing external reducible body " <> gKey g <> ": "
                                <> kcteMessage err
                          }
                    Right rendered -> pure (Just (universes, rendered))
              else pure Nothing
          recordInterface <- case interfaceCore of
            Nothing -> pure Nothing
            Just value ->
              case coreToTextAgainstWithEvidenceIn conversionContext certificateUses tyCore value of
                Left err ->
                  Left
                    err
                      { kcteMessage =
                          "while importing external interface " <> gKey g <> ": "
                            <> kcteMessage err
                      }
                Right rendered ->
                  pure
                    ( if hasRecordInterface rendered
                        then Just (universes, rendered)
                        else Nothing
                    )
          associatedBody <- case associatedCore of
            Nothing -> pure Nothing
            Just value ->
              case coreToTextAgainstWithEvidenceIn conversionContext certificateUses tyCore value of
                Left err ->
                  Left
                    err
                      { kcteMessage =
                          "while importing external associated normalization body "
                            <> gKey g
                            <> ": "
                            <> kcteMessage err
                      }
                Right rendered -> pure (Just rendered)
          pure
            ( stableRefForGlobal g
            , gdObservationMode gd
            , (universes, ty)
            , body
            , recordInterface
            , associatedBody
            , closedDeclarations ++ scopedDeclarations
            )
      where
        collectLiftRelation = \case
          CUniverseLift lower upper _ _ ->
            [(normalizeLevel lower, normalizeLevel upper)]
          CSchemaLift _ source target roles evidence _ _ _ _ ->
            [ (normalizeLevel lower, normalizeLevel upper)
            | (role, roleEvidence, lower, upper) <- zip4 roles evidence source target
            , role == Covariant
            , SchemaCovariantEvidence _ <- [roleEvidence]
            ]
          _ -> []
        coreLevelConstraint lower upper =
          KConstraint False <$> levelToText lower <*> levelToText upper
    externalConstructorEntry (g, KCoreConstructorInfo {..}) =
      let telescope = kcciUniverses
          universes = [UniverseRef "u" i | i <- [0 .. dutParameterCount telescope - 1]]
       in do
            ty <- coreToTextWithEvidenceIn conversionContext Map.empty kcciType
            parameterCount <-
              maybe
                (Left (invalid ("constructor family interface is unavailable for " <> gKey kcciData)))
                pure
                (familyCoreParameterCount ec globals kcciData)
            let (allBinders, result) = splitPiTelescope ty
                (parameters, payload) = splitAt parameterCount allBinders
                fieldOffset = length payload - length kcciSourceFields
            when (fieldOffset < 0) $
              Left (invalid ("constructor " <> gKey g <> " source fields exceed its checked payload telescope"))
            let fieldEntries =
                  [ (stableFieldRef field, index)
                  | (index, (_, Just field)) <- zip [fieldOffset ..] kcciSourceFields
                  ]
                fields = Map.fromList fieldEntries
            pure
              ( stableRefForGlobal kcciData
              , stableRefForConstructor g
              , (universes, ty)
              , (universes, parameters, foldr KTPi result payload)
              , fields
              , KCtorDecl
                  (stableRefForConstructor g)
                  universes
                  fieldEntries
                  (foldr KTPi result payload)
              )
    hasRecordInterface = ktermHasRecordInterface
verifyKCoreTextWithExternal
  :: Map StableRef ([UniverseRef], KTerm)
  -> Map StableRef ObservationMode
  -> Map StableRef ([UniverseRef], KTerm)
  -> Map StableRef ([UniverseRef], KTerm)
  -> Map KAssociatedNormalizationKey KAssociatedNormalization
  -> Map StableRef ([UniverseRef], [KBinder], KTerm)
  -> Map StableRef (Map StableRef Int)
  -> Map StableRef ([UniverseRef], [KConstraint], KConstraint, KLevelProof)
  -> Map StableRef KSchemaCertificate
  -> Map StableRef KNominalFamily
  -> KCoreFile
  -> Either KCoreTextError ()
verifyKCoreTextWithExternal externalTypes externalModes externalBodies externalRecordInterfaces externalAssociatedNormalizations externalConstructors externalConstructorFields externalLevelCertificates externalSchemaCertificates externalNominalFamilies file@(KCoreFile version modules) = do
  when (version /= 1) $
    Left (KCoreTextError "E_KCORE_TEXT_UNSUPPORTED_VERSION" ("unsupported KCoreText schema " <> T.pack (show version)))
  verifyStableIdentities (Map.keys externalTypes) file
  let declaredRefs = concatMap (concatMap declRefs . kmDecls) modules
      semanticOwners = map kmRef modules ++ declaredRefs
      semanticOwnerIds = map srId semanticOwners
      externalIds = Set.fromList (map srId (Map.keys externalTypes))
  when (length semanticOwnerIds /= Set.size (Set.fromList semanticOwnerIds)) $
    Left (invalid "a stable module or global identity is declared more than once in this KCoreText file")
  when (any (`Set.member` externalIds) (map srId declaredRefs)) $
    Left (invalid "a declaration stable identity collides with an imported semantic identity")
  let declaredArities = Map.fromList (concatMap moduleDeclarationArities modules)
      declaredTypes = Map.fromList (concatMap moduleDeclarationTypes modules)
      declaredModes = Map.fromList (concatMap moduleDeclarationModes modules)
      declaredBodies = Map.fromList (concatMap moduleDeclarationBodies modules)
      declaredRecordInterfaces = Map.fromList (concatMap moduleRecordInterfaces modules)
      globalTypes = Map.union declaredTypes externalTypes
      globalModes = Map.union declaredModes externalModes
      globalBodies = Map.union declaredBodies externalBodies
      recordInterfaces = Map.union declaredRecordInterfaces externalRecordInterfaces
      globalArities = Map.union declaredArities (Map.map (length . fst) externalTypes)
      constructorTypes = Map.union (Map.fromList (concatMap moduleConstructorTypes modules)) externalConstructors
      certificates =
        Map.union
          ( Map.fromList
              [ (ref, (universes, constraints, constraint, proof))
              | KModule {kmDecls = declarations} <- modules
              , KDLevelCertificate ref universes constraints constraint proof <- declarations
              ]
          )
          externalLevelCertificates
      localSchemaCertificates =
        Map.fromList
          [ (kscRef certificate, certificate)
          | KModule {kmDecls = declarations} <- modules
          , KDSchemaCertificate certificate <- declarations
          ]
      localNominalFamilies =
        Map.fromList
          [ (ref, KNominalFamily universes binders result certificate constructors)
          | KModule {kmDecls = declarations} <- modules
          , KDData ref universes binders result certificate constructors <- declarations
          ]
      schemaCertificates = Map.union localSchemaCertificates externalSchemaCertificates
      nominalFamilies = Map.union localNominalFamilies externalNominalFamilies
      constructorFields =
        Map.union (nominalConstructorFields nominalFamilies) externalConstructorFields
      externalCertificateContext =
        VerifyContext
          globalArities
          globalTypes
          globalModes
          globalBodies
          externalRecordInterfaces
          externalAssociatedNormalizations
          constructorTypes
          constructorFields
          certificates
          schemaCertificates
          nominalFamilies
          -- External certificate terms were produced by the compiler's Core
          -- conversion, whose implementation-owned generic nodes have the
          -- installed @impl.kappa@ verifier.  Local certificates are checked
          -- separately below, under the extension declarations of their own
          -- module; do not let this trusted import context authorize them.
          (Set.singleton "impl.kappa")
          []
  forM_ (Map.toAscList externalLevelCertificates) $
    \(ref, (universes, constraints, theorem, proof)) ->
      verifyLevelCertificate externalCertificateContext ref universes constraints theorem proof
  verifySchemaMonotoneWitnesses
    externalCertificateContext
    externalNominalFamilies
    externalSchemaCertificates
  -- Local mutual role replay must see imported families and certificates as
  -- fixed inputs. Restricting the fixed point to the declarations in this
  -- file makes a local family that mentions an imported covariant/invariant
  -- family appear spuriously irrelevant.
  verifySchemaCertificates
    (Map.keysSet localNominalFamilies)
    nominalFamilies
    schemaCertificates
  mapM_
    ( verifyModule
        globalArities
        globalTypes
        globalModes
        globalBodies
        recordInterfaces
        externalAssociatedNormalizations
        constructorTypes
        constructorFields
        certificates
        schemaCertificates
        nominalFamilies
    )
    modules

nominalConstructorFields :: Map StableRef KNominalFamily -> Map StableRef (Map StableRef Int)
nominalConstructorFields families =
  Map.fromList
    [ (constructor, Map.fromList fields)
    | family <- Map.elems families
    , KCtorDecl constructor _ fields _ <- knfConstructors family
    ]

verifyStableIdentities :: [StableRef] -> KCoreFile -> Either KCoreTextError ()
verifyStableIdentities externalRefs file = do
  let refs = externalRefs ++ allStableRefs file
  when (any (T.null . srId) refs) $
    Left (invalid "stable identities must be nonempty")

schemaCertificateInvalid :: Text -> KCoreTextError
schemaCertificateInvalid = KCoreTextError "E_KCORE_SCHEMA_CERTIFICATE_INVALID"

schemaLiftInvalid :: Text -> KCoreTextError
schemaLiftInvalid = KCoreTextError "E_UNIVERSE_SCHEMA_LIFT_INVALID"

verifySchemaMonotoneWitnesses
  :: VerifyContext
  -> Map StableRef KNominalFamily
  -> Map StableRef KSchemaCertificate
  -> Either KCoreTextError ()
verifySchemaMonotoneWitnesses context families certificates =
  forM_ (Map.elems certificates) $ \certificate -> do
    family <-
      maybe
        (Left (schemaCertificateInvalid "monotonicity evidence names an unavailable nominal family"))
        pure
        (Map.lookup (kscFamily certificate) families)
    let universes = map fst (knfUniverses family)
        universeIds = universeScope universes
    env <- foldM
      (\bound binder ->
        verifyFormerAndBind context universeIds (localEvidenceAssumptions emptyAssumptions bound) bound binder)
      Map.empty
      (knfBinders family)
    let assumptions = localEvidenceAssumptions emptyAssumptions env
        witnesses = kscMonotoneWitnesses certificate
        witnessKeys = [(kmwParameter witness, kmwOperator witness) | witness <- witnesses]
    unless (witnessKeys == sort (nub witnessKeys)) $
      Left (schemaCertificateInvalid "monotonicity witnesses must be unique and canonically ordered")
    forM_ witnesses $ \witness -> do
      unless (kmwParameter witness >= 0 && kmwParameter witness < length (knfUniverses family)) $
        Left (schemaCertificateInvalid "monotonicity witness parameter is outside the family universe telescope")
      verifyTerm context universeIds assumptions env (kmwOperator witness)
      verifyTerm context universeIds assumptions env (kmwGoal witness)
      verifyTerm context universeIds assumptions env (kmwEvidence witness)
      unless (goalAppliesCanonicalMonotone (kmwGoal witness) (kmwOperator witness)) $
        Left (schemaCertificateInvalid "monotonicity witness goal is not the canonical Monotone application for its operator")
      checkTerm context universeIds assumptions env (kmwEvidence witness) (kmwGoal witness)
      let actualDependencies =
            sort . nub $
              map KRGlobal (termStableRefs (kmwGoal witness) ++ termStableRefs (kmwEvidence witness))
                ++ map KRLocal (termLocalRefs (kmwGoal witness) ++ termLocalRefs (kmwEvidence witness))
      unless (kmwDependencies witness == actualDependencies) $
        Left (schemaCertificateInvalid "monotonicity witness dependency closure is incomplete or non-canonical")
  where
    goalAppliesCanonicalMonotone goal operator =
      case collectArguments [] goal of
        (KTGlobal ref _, arguments) ->
          ref == stableRefForGlobal prelMonotone
            && case reverse arguments of
                 KArgument KExplicit argument : _ -> sameKCoreType context argument operator
                 _ -> False
        _ -> False
    collectArguments arguments (KTApply function more) =
      collectArguments (more ++ arguments) function
    collectArguments arguments function = (function, arguments)

-- A schema certificate is evidence about a declaration, not an assertion to
-- trust. Replay the role closure from the normalized constructor signatures
-- and compare the declared role vector against that independently derived
-- result before any term is allowed to cite the certificate.
verifySchemaCertificates
  :: Set StableRef
  -> Map StableRef KNominalFamily
  -> Map StableRef KSchemaCertificate
  -> Either KCoreTextError ()
verifySchemaCertificates localFamilies families certificates = do
  let inferredRoles = inferKCoreNominalRoles families certificates
  forM_ (Map.toAscList certificates) $ \(certificateRef, certificate) -> do
    family <-
      maybe
        (Left (schemaCertificateInvalid "schema certificate names an unavailable nominal family"))
        pure
        (Map.lookup (kscFamily certificate) families)
    unless (kscCheckerVersion certificate == 1) $
      Left (schemaCertificateInvalid "schema certificate uses an unsupported checker version")
    unless (kscSemanticVersions certificate == currentTypeLevelSemanticVersions) $
      Left (schemaCertificateInvalid "schema certificate uses unsupported type-level semantic versions")
    let expectedSignatureHash = kCoreNominalSignatureHash (kscFamily certificate) family
    unless
      ( kscSignatureHash certificate == expectedSignatureHash
          || ( kscSignatureHash certificate == "local"
                 && kscFamily certificate `Set.member` localFamilies
             )
      ) $
      Left
        ( schemaCertificateInvalid
            ( "schema certificate signature closure hash mismatch; expected "
                <> expectedSignatureHash
                <> ", found "
                <> kscSignatureHash certificate
            )
        )
    unless (kscSaturationArity certificate == length (knfBinders family)) $
      Left (schemaCertificateInvalid "schema certificate saturation arity disagrees with the family telescope")
    let declaredRoles = map snd (knfUniverses family)
        inferred = Map.findWithDefault [] (kscFamily certificate) inferredRoles
    unless (length (kscRoles certificate) == length declaredRoles) $
      Left (schemaCertificateInvalid "schema certificate role arity disagrees with the universe telescope")
    unless (declaredRoles == kscRoles certificate) $
      Left (schemaCertificateInvalid "schema certificate roles disagree with the declaration telescope")
    unless (and (zipWith (<=) (kscRoles certificate) inferred)) $
      Left (schemaCertificateInvalid "schema certificate claims a role more permissive than independent signature replay")
    unless (knfCertificate family == certificateRef) $
      Left (schemaCertificateInvalid "schema certificate is not the certificate selected by its nominal family")
    let requiredClauseKinds =
          [ClauseSortDeclaration]
            ++ if null (knfConstructors family)
                 then []
                 else [ClausePointConstructor, ClauseEliminator, ClauseComputationRule]
    unless
      ( all (`elem` kscClauseKinds certificate) requiredClauseKinds
          && length (kscClauseKinds certificate) == length (nub (kscClauseKinds certificate))
          && all supportedNominalClause (kscClauseKinds certificate)
      ) $
      Left (schemaCertificateInvalid "schema certificate has an incomplete or unsupported signature closure")
  forM_ (Map.toAscList families) $ \(_, family) ->
    unless (Map.member (knfCertificate family) certificates) $
      Left (schemaCertificateInvalid "nominal declaration selects an unavailable schema certificate")
  where
    supportedNominalClause = \case
      ClauseSortDeclaration -> True
      ClausePointConstructor -> True
      ClausePathConstructor -> False
      ClauseHigherBoundary -> False
      ClauseQuotientEquation -> False
      ClauseRecursiveOperation -> False
      ClauseRecursiveEquation -> False
      ClauseGeneratedProjection -> True
      ClauseEliminator -> True
      ClauseComputationRule -> True
      ClauseTruncationRule -> False
      ClauseExtension -> False

-- | Independent semantic identity of the complete nominal signature carried
-- by KCoreText. Alpha-normalize universe/local binders through the same
-- canonicalizer used by semantic hashing, omit the selected certificate (it
-- is the fact being authenticated), and bind every constructor telescope and
-- named-field identity. This replaces the former self-authenticating
-- @signatureHash = local@ placeholder.
kCoreNominalSignatureHash :: StableRef -> KNominalFamily -> Text
kCoreNominalSignatureHash familyRef KNominalFamily {..} =
  stableHex
    ( "kcore-nominal-signature-v1:"
        <> renderStable familyRef
        <> ":"
        <> printDecl canonicalPayload
    )
  where
    canonicalPayload =
      canonicalizeDecl
        ( KDData
            familyRef
            knfUniverses
            knfBinders
            knfResult
            (StableRef "schema.signature-subject" "0")
            knfConstructors
        )

inferKCoreNominalRoles
  :: Map StableRef KNominalFamily
  -> Map StableRef KSchemaCertificate
  -> Map StableRef [UniverseVariance]
inferKCoreNominalRoles families certificates = fixedPoint initial
  where
    initial = Map.map (replicate . length . knfUniverses <*> const Irrelevant) families
    fixedPoint roles =
      let inferred = Map.mapWithKey (inferFamily roles) families
          tightened = Map.intersectionWith (zipWith min) roles inferred
       in if tightened == roles then roles else fixedPoint tightened
    inferFamily roles familyRef family =
      inferUniverseRoles (length (knfUniverses family))
        (concatMap (constructorRequirements roles family (familyWitnesses familyRef family)) (knfConstructors family))
    familyWitnesses familyRef family =
      case Map.lookup (knfCertificate family) certificates of
        Just certificate | kscFamily certificate == familyRef -> kscMonotoneWitnesses certificate
        _ -> []

constructorRequirements
  :: Map StableRef [UniverseVariance]
  -> KNominalFamily
  -> [KMonotoneWitness]
  -> KCtorDecl
  -> [RoleRequirement]
constructorRequirements roles family witnesses (KCtorDecl _ _ _ signature) = go signature
  where
    go (KTPi binder rest) = domainRequirements (kbType binder) ++ go rest
    go _ = []
    domainRequirements term =
      case strip term of
        KTType level -> requirementsForLevel level
        KTPi binder codomain ->
          invariantTerm (kbType binder) ++ domainRequirements codomain
        nominal
          | Just (nested, levels, _arguments) <- nominalApplication nominal
          , Just nestedRoles <- Map.lookup nested roles
          , length levels == length nestedRoles ->
              -- Schema lifts preserve a fully saturated nominal family's
              -- ordinary arguments exactly. Their classifier-universe
              -- annotations therefore do not constrain the declaration
              -- universe roles; only the nested family's certified universe
              -- spine does. This is the same rule used by source role
              -- inference for both data constructors and trait fields.
              concat (zipWith applyRole nestedRoles levels)
        nominal -> invariantTerm nominal
    strip = \case
      KTAscribe value _ -> strip value
      KTLift _ _ _ value -> strip value
      KTSchemaLift _ _ _ _ _ _ value -> strip value
      value -> value
    nominalApplication = collect []
      where
        collect arguments (KTApply function more) = collect (more ++ arguments) function
        collect arguments (KTGlobal ref levels) = Just (ref, levels, arguments)
        collect _ _ = Nothing
    applyRole role level = case role of
      Invariant -> invariantLevel level
      Covariant -> requirementsForLevel level
      Irrelevant -> []
    requirementsForLevel = \case
      KLFinite _ -> []
      KLGlobal _ -> []
      KLUniverse ref ->
        [RequireCovariant index "normalized constructor field stores a type code or witness" | index <- familyUniverseIndex ref]
      KLSucc level -> requirementsForLevel level
      KLMax left right -> requirementsForLevel left ++ requirementsForLevel right
      KLAdd left right -> requirementsForLevel left ++ requirementsForLevel right
      KLTerm term -> neutralRequirements term
    neutralRequirements term =
      [ if any (witnessMatches index term) witnesses
          then RequireCovariant index "normalized constructor field uses selected Monotone evidence"
          else RequireInvariant index "normalized constructor field uses a neutral level operation without selected Monotone evidence"
      | index <- familyTermLevelParameters family term
      ]
    witnessMatches index term witness =
      kmwParameter witness == index
        && case neutralOneHoleOperator index term of
             Just operator -> operator == kmwOperator witness
             Nothing -> False
    neutralOneHoleOperator index = \case
      KTApply operator [KArgument KExplicit argument]
        | index `notElem` familyTermLevelParameters family operator
        , argument == levelAsTerm (KLUniverse (fst (knfUniverses family !! index))) -> Just operator
      _ -> Nothing
    familyUniverseIndex ref =
      [ index
      | (index, (candidate, _)) <- zip [0 ..] (knfUniverses family)
      , urId candidate == urId ref
      ]
    invariantLevel level =
      [RequireInvariant index "normalized constructor field uses a universe under an invariant operation" | index <- familyLevelParameters family level]
    invariantTerm term =
      [RequireInvariant index "normalized constructor field uses a universe under an unverified operation" | index <- familyTermLevelParameters family term]

familyLevelParameters :: KNominalFamily -> KLevel -> [Int]
familyLevelParameters family = nub . go
  where
    parameterIndices = Map.fromList [(urId ref, index) | (index, (ref, _)) <- zip [0 ..] (knfUniverses family)]
    go = \case
      KLUniverse ref -> maybeToList (Map.lookup (urId ref) parameterIndices)
      KLSucc level -> go level
      KLMax left right -> go left ++ go right
      KLAdd left right -> go left ++ go right
      KLTerm term -> familyTermLevelParameters family term
      _ -> []

familyTermLevelParameters :: KNominalFamily -> KTerm -> [Int]
familyTermLevelParameters family = nub . go
  where
    levels = concatMap (familyLevelParameters family)
    go = \case
      KTLocal _ arguments -> levels arguments
      KTGlobal _ arguments -> levels arguments
      KTType level -> familyLevelParameters family level
      KTPi binder body -> go (kbType binder) ++ go body
      KTSigma binder body -> go (kbType binder) ++ go body
      KTLambda binder body -> go (kbType binder) ++ go body
      KTApply function arguments -> go function ++ concatMap (go . argumentTerm) arguments
      KTBlock items result -> concatMap block items ++ go result
      KTLetRec definitions result -> concatMap localDef definitions ++ go result
      KTCase scrutinee result alternatives -> go scrutinee ++ go result ++ concatMap alt alternatives
      KTConstruct _ arguments fields -> levels arguments ++ concatMap (go . argumentTerm) fields
      KTProject _ term -> go term
      KTLift from to _ term -> levels [from, to] ++ go term
      KTSchemaLift _ from to _ _ targetArguments term -> levels (from ++ to) ++ concatMap (go . argumentTerm) targetArguments ++ go term
      KTAscribe value ty -> go value ++ go ty
      KTLiteral _ -> []
      KTRecordType fields -> concatMap (go . kbType . snd) fields
      KTRecordValue fields -> concatMap (go . snd) fields
      KTIf condition yes no -> go condition ++ go yes ++ go no
      KTGeneric _ fields -> concatMap (value . snd) fields
    block (KBLet binder rhs) = go (kbType binder) ++ go rhs
    localDef definition = go (kldType definition) ++ go (kldBody definition)
    alt = \case
      KCaseDefault body -> go body
      KCaseConstructor _ arguments bindings body ->
        levels arguments
          ++ concatMap
            (\binding ->
              go (kbType (caseBindingBinder binding))
                ++ case binding of
                  KCaseBridge bridge -> go (kcbProof bridge)
                  KCasePayload {} -> [])
            bindings
          ++ go body
      KCasePattern pattern' guard' body -> concatMap (go . kbType) (kPatternDependencyBinders pattern') ++ maybe [] go guard' ++ go body
    value = \case
      KVTerm term -> go term
      KVLevel level -> familyLevelParameters family level
      KVQuantity (KQTerm term) -> go term
      KVGlobal _ arguments -> levels arguments
      KVLocal _ arguments -> levels arguments
      KVBinder binder -> go (kbType binder)
      KVPattern pattern' -> concatMap (go . kbType) (kPatternDependencyBinders pattern')
      KVList values -> concatMap value values
      _ -> []

verifyModule :: Map StableRef Int -> Map StableRef ([UniverseRef], KTerm) -> Map StableRef ObservationMode -> Map StableRef ([UniverseRef], KTerm) -> Map StableRef ([UniverseRef], KTerm) -> Map KAssociatedNormalizationKey KAssociatedNormalization -> Map StableRef ([UniverseRef], [KBinder], KTerm) -> Map StableRef (Map StableRef Int) -> Map StableRef ([UniverseRef], [KConstraint], KConstraint, KLevelProof) -> Map StableRef KSchemaCertificate -> Map StableRef KNominalFamily -> KModule -> Either KCoreTextError ()
verifyModule globalArities globalTypes globalModes globalBodies recordInterfaces externalAssociatedNormalizations constructorTypes constructorFields certificates schemaCertificates nominalFamilies KModule {..} = do
  let metadata = Map.fromList kmMetadata
      required =
        [ "languageVersion"
        , "compilerInterfaceVersion"
        , "sourceModuleIdentity"
        ]
          <> levelSemanticVersions
      missing = filter (`Map.notMember` metadata) required
  unless (null missing) $
    Left (invalid ("module metadata is missing " <> T.intercalate ", " missing))
  when (length (map fst kmMetadata) /= length (nub (map fst kmMetadata))) $
    Left (invalid "module metadata keys must be unique")
  let interfaceRefs =
        [ ref
        | KDInterface ref _ _ <- kmDecls
        ]
  unless (length interfaceRefs == Set.size (Set.fromList interfaceRefs)) $
    Left (invalid "a declaration may have at most one record interface")
  forM_
    [ (ref, universes)
    | KDInterface ref universes _ <- kmDecls
    ] $ \(ref, universes) ->
      case Map.lookup ref globalTypes of
        Nothing ->
          Left (invalid "a record interface must name an available declaration")
        Just (declarationUniverses, _) ->
          unless (length universes == length declarationUniverses) $
            Left (invalid "a record interface universe telescope disagrees with its declaration")
  requireMetadata "languageVersion" "kappa-v1"
  requireMetadata "compilerInterfaceVersion" "1"
  forM_ levelSemanticVersions $ \key ->
    case Map.lookup key metadata of
      Just "1" -> pure ()
      Just actual ->
        Left
          ( KCoreTextError
              "E_KCORE_TEXT_UNSUPPORTED_VERSION"
              ("unsupported " <> key <> " " <> actual)
          )
      Nothing ->
        Left (invalid ("module metadata is missing " <> key))
  let globals = concatMap declRefs kmDecls
  when (Set.size (Set.fromList globals) /= length globals) $
    Left (invalid "declaration global identities must be unique")
  let localAssociatedNormalizations =
        [ normalization
        | KDAssociatedNormalization normalization <- kmDecls
        ]
      localAssociatedKeys = map associatedNormalizationKey localAssociatedNormalizations
      localGlobalRefs =
        Set.fromList
          [ ref
          | declaration <- kmDecls
          , ref <- declRefs declaration
          ]
  unless (length localAssociatedKeys == Set.size (Set.fromList localAssociatedKeys)) $
    Left (invalid "an associated static member may have at most one normalization equation")
  forM_ localAssociatedNormalizations $ \normalization ->
    unless (kanDictionary normalization `Set.member` localGlobalRefs) $
      Left (invalid "an associated normalization may only be declared by its dictionary's defining module")
  let extensionEntries =
        [ (owner, extensionVersion)
        | KDExtension owner extensionVersion <- kmDecls
        ]
      extensions = Set.fromList (map fst extensionEntries)
  when (length extensionEntries /= Set.size extensions) $
    Left (invalid "each KCoreText extension owner must be declared exactly once per module")
  forM_ extensionEntries $ \(owner, extensionVersion) ->
    case Map.lookup owner supportedExtensionVersions of
      Just versions | extensionVersion `Set.member` versions -> pure ()
      _ ->
        Left
          ( invalid
              ( "unsupported KCoreText extension "
                  <> owner
                  <> " version "
                  <> tshow extensionVersion
              )
          )
  let baseContext =
        VerifyContext
          globalArities
          globalTypes
          globalModes
          globalBodies
          recordInterfaces
          externalAssociatedNormalizations
          constructorTypes
          constructorFields
          certificates
          schemaCertificates
          nominalFamilies
          extensions
          []
  verifiedAssociatedNormalizations <-
    verifyAssociatedNormalizations baseContext localAssociatedNormalizations
  let context =
        baseContext
          { vcAssociatedNormalizations =
              Map.union verifiedAssociatedNormalizations externalAssociatedNormalizations
          }
      localSchemaCertificateRefs =
        Set.fromList
          [ kscRef certificate
          | KDSchemaCertificate certificate <- kmDecls
          ]
      localSchemaCertificates =
        Map.restrictKeys schemaCertificates localSchemaCertificateRefs
  -- A certificate is an executable proof object at the interchange trust
  -- boundary.  Replay it only after this module's declared extension
  -- verifiers have been installed; otherwise implementation-owned level
  -- values are either spuriously rejected or, if globally enabled, accepted
  -- without the required declaration.
  verifySchemaMonotoneWitnesses context nominalFamilies localSchemaCertificates
  forM_ kmDecls $ \declaration ->
    case verifyDecl context declaration of
      Left err -> Left err {kcteMessage = "while verifying " <> declarationSubject declaration <> ": " <> kcteMessage err}
      Right () -> pure ()
  where
    requireMetadata key expected =
      case Map.lookup key (Map.fromList kmMetadata) of
        Just actual | actual == expected -> pure ()
        Just actual ->
          Left
            ( KCoreTextError
                "E_KCORE_TEXT_UNSUPPORTED_VERSION"
                ("unsupported " <> key <> " " <> actual <> "; expected " <> expected)
            )
        Nothing -> Left (invalid ("module metadata is missing " <> key))
    levelSemanticVersions =
      [ "typeLevelAlgebraVersion"
      , "levelConstructorNormalizerVersion"
      , "levelRigidEntailmentVersion"
      , "levelPrincipalInferenceVersion"
      , "levelCertificateVersion"
      ]

associatedNormalizationKey
  :: KAssociatedNormalization
  -> KAssociatedNormalizationKey
associatedNormalizationKey normalization =
  (kanDictionary normalization, kanField normalization)

-- | Verify associated equations in dependency order. A member type may refer
-- to an earlier associated member of the same dictionary, so each successful
-- equation becomes available to later checks. Cycles and malformed equations
-- make no progress and are rejected with the underlying type error.
verifyAssociatedNormalizations
  :: VerifyContext
  -> [KAssociatedNormalization]
  -> Either KCoreTextError (Map KAssociatedNormalizationKey KAssociatedNormalization)
verifyAssociatedNormalizations initial = go Map.empty
  where
    go accepted [] = pure accepted
    go accepted pending =
      let context =
            initial
              { vcAssociatedNormalizations =
                  Map.union accepted (vcAssociatedNormalizations initial)
              }
          attempts =
            [ (normalization, verifyAssociatedNormalization context normalization)
            | normalization <- pending
            ]
          acceptedNow =
            [ normalization
            | (normalization, Right ()) <- attempts
            ]
          rejectedNow =
            [ (normalization, err)
            | (normalization, Left err) <- attempts
            ]
       in if null acceptedNow
            then case rejectedNow of
              ((normalization, err) : _) ->
                Left
                  err
                    { kcteMessage =
                        "while verifying associated normalization for "
                          <> renderStable (kanDictionary normalization)
                          <> "."
                          <> renderFieldRef (kanField normalization)
                          <> ": "
                          <> kcteMessage err
                    }
              [] -> pure accepted
            else
              go
                ( foldr
                    (\normalization ->
                       Map.insert
                         (associatedNormalizationKey normalization)
                         normalization)
                    accepted
                    acceptedNow
                )
                (map fst rejectedNow)

verifyAssociatedNormalization
  :: VerifyContext
  -> KAssociatedNormalization
  -> Either KCoreTextError ()
verifyAssociatedNormalization context KAssociatedNormalization {..} = do
  verifyUniverseTelescope kanUniverses
  (declarationUniverses, dictionaryType0) <-
    maybe
      (Left (invalid "associated normalization names an unavailable dictionary global"))
      pure
      (Map.lookup kanDictionary (vcGlobalTypes context))
  unless (length declarationUniverses == length kanUniverses) $
    Left (invalid "associated normalization universe telescope disagrees with its dictionary")
  let universeSubstitution =
        Map.fromList
          (zip (map urId declarationUniverses) (map KLUniverse kanUniverses))
      dictionaryType =
        substituteUniverseParameters universeSubstitution dictionaryType0
      universeIds = universeScope kanUniverses
  (environment, resultType) <-
    foldM
      (bindDictionaryArgument universeIds)
      (Map.empty, dictionaryType)
      kanBinders
  case unfoldTypeHeadWithLocals context environment resultType of
    KTPi {} ->
      Left (invalid "associated normalization does not saturate its dictionary global")
    _ -> pure ()
  let receiverHead = KTGlobal kanDictionary (map KLUniverse kanUniverses)
      receiverArguments =
        [ KArgument
            (kbExplicitness binder)
            (KTLocal (kbRef binder) [])
        | binder <- kanBinders
        ]
      receiver =
        if null receiverArguments
          then receiverHead
          else KTApply receiverHead receiverArguments
      assumptions = localEvidenceAssumptions emptyAssumptions environment
  fieldBinder <-
    maybe
      (Left (invalid "associated normalization field is absent from the authenticated dictionary interface"))
      pure
      (nominalFieldBinder context kanField receiver resultType)
  unless (kAssociatedStaticMemberType context (kbType fieldBinder)) $
    Left
      ( invalid
          "only checked associated static-member fields may carry normalization equations"
      )
  checkTermObserved
    Parametric
    context
    universeIds
    assumptions
    environment
    kanValue
    (kbType fieldBinder)
  where
    bindDictionaryArgument universes (environment, functionType) binder =
      case unfoldTypeHeadWithLocals context environment functionType of
        KTPi expectedBinder codomain -> do
          let assumptions = localEvidenceAssumptions emptyAssumptions environment
          unless
            (sameBinderContractUnderIn assumptions environment context expectedBinder binder) $
            Left (invalid "associated normalization binder disagrees with the dictionary telescope")
          environment' <-
            verifyFormerAndBind context universes assumptions environment binder
          pure
            ( environment'
            , substituteLocal
                (kbRef expectedBinder)
                (KTLocal (kbRef binder) [])
                codomain
            )
        _ ->
          Left (invalid "associated normalization has more binders than its dictionary global")

declarationSubject :: KDecl -> Text
declarationSubject = \case
  KDDef ref _ _ _ _ -> renderStable ref
  KDAxiom ref _ _ _ -> renderStable ref
  KDInterface ref _ _ -> "interface for " <> renderStable ref
  KDAssociatedNormalization normalization ->
    "associated normalization for "
      <> renderStable (kanDictionary normalization)
      <> "."
      <> renderFieldRef (kanField normalization)
  KDData ref _ _ _ _ _ -> renderStable ref
  KDSchemaCertificate certificate -> renderStable (kscRef certificate)
  KDTermProbe _ -> "term probe"
  KDLevelCertificate ref _ _ _ _ -> renderStable ref
  KDRepresentationCertificate certificate -> renderStable (krcRef certificate)
  KDExtension owner _ -> "extension " <> owner
  KDGeneric tag _ -> "generic declaration " <> tag

verifyDecl :: VerifyContext -> KDecl -> Either KCoreTextError ()
verifyDecl context = \case
  KDAxiom _ _ universes ty -> verifySignature context universes ty
  KDInterface _ universes ty -> do
    verifySignature context universes ty
    unless (ktermHasRecordInterface ty) $
      Left (invalid "an interface declaration must expose a record telescope")
  KDAssociatedNormalization _ -> pure ()
  KDDef _ mode universes ty body -> do
    verifySignature context universes ty
    unless (isUnavailableBody body) $
      checkTermObserved mode context (universeScope universes) emptyAssumptions Map.empty body ty
  KDData _ roleUniverses binders result _ constructors -> do
    let universes = map fst roleUniverses
        us = universeScope universes
    env <- foldM
      (\bound binder ->
        verifyFormerAndBind context us (localEvidenceAssumptions emptyAssumptions bound) bound binder)
      Map.empty
      binders
    let assumptions = localEvidenceAssumptions emptyAssumptions env
    verifyTerm context us assumptions env result
    forM_ constructors $ \(KCtorDecl _ ctorUniverses fields ty) -> do
      verifyUniverseTelescope ctorUniverses
      let ctorScope = Set.union us (universeScope ctorUniverses)
      verifyTerm context ctorScope assumptions env ty
      let (payload, _) = splitPiTelescope ty
          fieldRefs = map fst fields
          fieldIndices = map snd fields
      unless (length fieldRefs == Set.size (Set.fromList fieldRefs)) $
        Left (invalid "constructor field identities must be unique")
      unless (length fieldIndices == Set.size (Set.fromList fieldIndices)) $
        Left (invalid "a constructor payload position may have at most one field identity")
      forM_ fields $ \(fieldRef, fieldIndex) -> do
        unless (fieldRef == stableFieldRefFromReadable (srName fieldRef)) $
          Left (invalid "constructor field identity does not match its readable name")
        unless (fieldIndex >= 0 && fieldIndex < length payload) $
          Left (invalid "constructor field index is outside its direct payload telescope")
      classifier <- inferSimple context ctorScope assumptions env ty
      case classifier of
        Just KTType {} -> pure ()
        _ -> Left (invalid "a KCore constructor signature must itself have a universe classifier")
  KDLevelCertificate ref universes constraints constraint proof ->
    verifyLevelCertificate context ref universes constraints constraint proof
  KDRepresentationCertificate certificate ->
    verifyRepresentationCertificate context certificate
  KDSchemaCertificate _ -> pure ()
  KDTermProbe term -> case term of
    KTGeneric tag _
      | tag `Set.member` malformedSchemaLiftProbeTags ->
          Left (schemaLiftInvalid ("malformed schema-lift probe '" <> tag <> "'"))
    _ -> verifyTerm context Set.empty emptyAssumptions Map.empty term
  KDExtension owner version -> do
    unless (maybe False (version `Set.member`) (Map.lookup owner supportedExtensionVersions)) $
      Left (invalid "extension declaration has no compatible registered verifier")
  KDGeneric tag fields -> do
    when (tag == "certificate-runtime-action") $
      Left (schemaCertificateInvalid "a schema certificate may not authorize a runtime transformation")
    unless (extensionOwnsTag (vcExtensions context) tag) $
      Left (invalid ("unsupported generic declaration node '" <> tag <> "'"))
    if tag == "mutual-nominal-signature"
      then verifyMutualNominalSignature fields
      else mapM_ (verifyValue context Set.empty emptyAssumptions Map.empty . snd) fields

verifyRepresentationCertificate
  :: VerifyContext
  -> KRepresentationCertificate
  -> Either KCoreTextError ()
verifyRepresentationCertificate context certificate@KRepresentationCertificate {..} =
  mapLeft representationCertificateInvalid $ do
    unless (krcCheckerVersion == 1) $
      Left "unsupported representation-certificate checker version"
    unless (krcCertificateVersion == 1) $
      Left "unsupported representation-certificate schema version"
    liftKCore (verifyUniverseTelescope krcUniverses)
    let universes = universeScope krcUniverses
    liftKCore (verifyConstraints context universes krcConstraints)
    let assumptions = constraintAssumptions krcConstraints
    environment <-
      foldM
        (\environment binder ->
          liftKCore
            (verifyFormerAndBind context universes assumptions environment binder))
        Map.empty
        krcBinders
    liftKCore
      (verifyTerm context universes assumptions environment krcTarget)
    inferredTarget <-
      liftKCore
        (inferSimple context universes assumptions environment krcTarget)
    targetClassifier <-
      maybe
        (Left "representation-certificate target has no universe classifier")
        pure
        inferredTarget
    case targetClassifier of
      KTType {} -> pure ()
      _ -> Left "representation-certificate target is not a type"
    let fieldNames = map fst krcPayload
        expected = representationCertificateFields krcKind
    unless (length fieldNames == Set.size (Set.fromList fieldNames)) $
      Left "representation-certificate payload contains duplicate fields"
    unless (Set.fromList fieldNames == expected) $
      Left
        ( "representation-certificate payload fields do not match the closed "
            <> printRepresentationCertificateKind krcKind
            <> " schema"
        )
    mapM_
      (mapLeft kcteMessage . verifyValue context universes assumptions environment . snd)
      krcPayload
    recordedTypeIdentity <- requiredCertificateText "typeIdentity" krcPayload
    unless (recordedTypeIdentity == representationCertificateTypeIdentity certificate) $
      Left "representation-certificate target type identity does not match its context"
    verifyOptionalCertificateIdentity "sourceEvidenceIdentity" krcPayload
    verifyOptionalCertificateIdentity "evidenceIdentity" krcPayload
    verifyOptionalCertificateIdentity "refinementViewEvidenceIdentity" krcPayload
    mapM_ (verifyCertificateTerm krcPayload)
      (representationCertificateTermFields krcKind)
    mapM_ (verifyCertificateSummary krcPayload)
      (representationCertificateSummaryFields krcKind)
    mapM_ (verifyCertificateFieldPaths context krcPayload)
      (representationCertificateFieldPathFields krcKind)
    verifyCertificateProfileRestrictions krcPayload
    verifyRepresentationLawTerms
      context
      universes
      assumptions
      environment
      certificate
  where
    verifyCertificateTerm fields name =
      case lookup name fields of
        Just KVTerm {} -> pure ()
        _ -> Left ("representation-certificate field '" <> name <> "' must be a term")
    verifyCertificateSummary fields name =
      case lookup name fields of
        Just (KVText summary) | not (T.null summary) -> pure ()
        _ -> Left ("representation-certificate field '" <> name <> "' must be a nonempty summary")
    liftKCore = mapLeft kcteMessage

verifyRepresentationLawTerms
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> KRepresentationCertificate
  -> Either Text ()
verifyRepresentationLawTerms
    context
    universes
    assumptions
    environment
    KRepresentationCertificate {..} =
  case krcKind of
    KRepresentationOrdinal -> do
      cardinality <- requiredTerm "cardinalityExpression"
      liftKCore
        (checkTerm
          context
          universes
          assumptions
          environment
          cardinality
          naturalType)
      let ordinalType =
            KTApply
              (KTGlobal (stableRefForGlobal prelFin) [])
              [KArgument KExplicit cardinality]
      rank <- requiredTerm "rankTerm"
      unrank <- requiredTerm "unrankTerm"
      verifyMap "rankTerm" rank krcTarget ordinalType
      verifyMap "unrankTerm" unrank ordinalType krcTarget
      unrankRank <- requiredTerm "unrankRankProof"
      verifyRoundTrip
        "unrankRankProof"
        unrankRank
        krcTarget
        rank
        unrank
      rankUnrank <- requiredTerm "rankUnrankProof"
      verifyRoundTrip
        "rankUnrankProof"
        rankUnrank
        ordinalType
        unrank
        rank
    KRepresentationExactNatural -> do
      toNatural <- requiredTerm "toNatTerm"
      fromNatural <- requiredTerm "fromNatTerm"
      verifyMap "toNatTerm" toNatural krcTarget naturalType
      verifyMap "fromNatTerm" fromNatural naturalType krcTarget
      toNatFromNat <- requiredTerm "toNatFromNatProof"
      verifyRoundTrip
        "toNatFromNatProof"
        toNatFromNat
        naturalType
        fromNatural
        toNatural
      fromNatToNat <- requiredTerm "fromNatToNatProof"
      verifyRoundTrip
        "fromNatToNatProof"
        fromNatToNat
        krcTarget
        toNatural
        fromNatural
    KRepresentationRefinement -> do
      baseType <- requiredTerm "baseType"
      liftKCore (verifyType baseType)
      baseProjection <- requiredTerm "baseProjection"
      verifyMap "baseProjection" baseProjection krcTarget baseType
      refine <- requiredTerm "refineConstructor"
      verifyRefinementConstructor refine baseType
      verifyEqualityFamily "valueAfterRefineProof" baseType
        =<< requiredTerm "valueAfterRefineProof"
      verifyEqualityFamily "refineAfterValueProof" krcTarget
        =<< requiredTerm "refineAfterValueProof"
  where
    naturalType = KTGlobal (stableRefForGlobal prelNat) []
    requiredTerm name =
      case lookup name krcPayload of
        Just (KVTerm term) -> pure term
        _ ->
          Left
            ( "representation-certificate field '"
                <> name
                <> "' must be a term"
            )
    liftKCore = mapLeft kcteMessage
    same env = sameKCoreTypeIn env context
    verifyType term = do
      classifier <-
        inferSimple context universes assumptions environment term
      case classifier of
        Just KTType {} -> pure ()
        _ -> Left (invalid "representation-certificate baseType is not a type")
    infer name term =
      liftKCore
        (inferSimple context universes assumptions environment term)
        >>= maybe
          (Left ("representation-certificate " <> name <> " has no inferred type"))
          pure
    verifyMap name term domain codomain = do
      ty <- infer name term
      case ty of
        KTPi binder result
          | same environment (kbType binder) domain
          , let environment' =
                  Map.insert (lrId (kbRef binder)) (LocalBinder binder) environment
          , same environment' result codomain ->
              pure ()
        _ ->
          Left
            ( "representation-certificate "
                <> name
                <> " does not have the certified map type"
            )
    verifyRoundTrip name proof input forward backward = do
      ty <- infer name proof
      case ty of
        KTPi binder proposition
          | same environment (kbType binder) input
          , let environment' =
                  Map.insert (lrId (kbRef binder)) (LocalBinder binder) environment
                variable = KTLocal (kbRef binder) []
                expectedLeft =
                  applyUnary backward (applyUnary forward variable)
          , Just (carrier, left, right) <- equalityOperands proposition
          , same environment' carrier input
          , same environment' left expectedLeft
          , same environment' right variable ->
              pure ()
        _ ->
          Left
            ( "representation-certificate "
                <> name
                <> " does not prove the certified round trip"
            )
    verifyRefinementConstructor term baseType = do
      ty <- infer "refineConstructor" term
      case ty of
        KTPi binder rest
          | same environment (kbType binder) baseType ->
              goRefine
                (Map.insert (lrId (kbRef binder)) (LocalBinder binder) environment)
                rest
        _ ->
          Left
            "representation-certificate refineConstructor does not accept the certified base type"
      where
        goRefine env = \case
          KTPi binder rest
            | kbQuantity binder == KQ0 ->
                goRefine
                  (Map.insert (lrId (kbRef binder)) (LocalBinder binder) env)
                  rest
          result
            | same env result krcTarget -> pure ()
          _ ->
            Left
              "representation-certificate refineConstructor has a retained non-base argument or a wrong result"
    verifyEqualityFamily name carrier proof = do
      ty <- infer name proof
      let (binders, result) = splitPiTelescope ty
          environment' =
            foldl
              (\env binder ->
                Map.insert (lrId (kbRef binder)) (LocalBinder binder) env)
              environment
              binders
      case equalityOperands result of
        Just (actualCarrier, _, _)
          | same environment' actualCarrier carrier -> pure ()
        _ ->
          Left
            ( "representation-certificate "
                <> name
                <> " is not an equality over the certified carrier"
            )
    applyUnary function argument =
      KTApply function [KArgument KExplicit argument]

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = \case
  Left err -> Left (f err)
  Right value -> Right value

representationCertificateFields
  :: KRepresentationCertificateKind
  -> Set Text
representationCertificateFields kind =
  Set.fromList $
    case kind of
      KRepresentationOrdinal ->
        [ "typeIdentity"
        , "sourceEvidenceIdentity"
        , "cardinalityExpression"
        , "rankTerm"
        , "unrankTerm"
        , "unrankRankProof"
        , "rankUnrankProof"
        , "constructorEncoding"
        , "eliminatorSimulation"
        , "erasureView"
        , "profileRestrictions"
        ]
      KRepresentationExactNatural ->
        [ "typeIdentity"
        , "evidenceIdentity"
        , "zeroConstructor"
        , "successorConstructor"
        , "recursiveField"
        , "toNatTerm"
        , "fromNatTerm"
        , "toNatFromNatProof"
        , "fromNatToNatProof"
        , "constructorSimulation"
        , "eliminatorSimulation"
        , "erasureView"
        , "profileRestrictions"
        ]
      KRepresentationRefinement ->
        [ "typeIdentity"
        , "refinementViewEvidenceIdentity"
        , "baseType"
        , "baseTypeIdentity"
        , "baseProjection"
        , "refineConstructor"
        , "retainedBaseField"
        , "erasedEvidenceFields"
        , "valueAfterRefineProof"
        , "refineAfterValueProof"
        , "eliminatorSimulation"
        , "erasureView"
        , "profileRestrictions"
        ]

representationCertificateTermFields
  :: KRepresentationCertificateKind
  -> [Text]
representationCertificateTermFields = \case
  KRepresentationOrdinal ->
    [ "cardinalityExpression"
    , "rankTerm"
    , "unrankTerm"
    , "unrankRankProof"
    , "rankUnrankProof"
    ]
  KRepresentationExactNatural ->
    [ "toNatTerm"
    , "fromNatTerm"
    , "toNatFromNatProof"
    , "fromNatToNatProof"
    ]
  KRepresentationRefinement ->
    [ "baseType"
    , "baseProjection"
    , "refineConstructor"
    , "valueAfterRefineProof"
    , "refineAfterValueProof"
    ]

representationCertificateSummaryFields
  :: KRepresentationCertificateKind
  -> [Text]
representationCertificateSummaryFields = \case
  KRepresentationOrdinal ->
    ["eliminatorSimulation"]
  KRepresentationExactNatural ->
    ["constructorSimulation", "eliminatorSimulation"]
  KRepresentationRefinement ->
    ["eliminatorSimulation"]

representationCertificateFieldPathFields
  :: KRepresentationCertificateKind
  -> [Text]
representationCertificateFieldPathFields = \case
  KRepresentationOrdinal -> ["erasureView"]
  KRepresentationExactNatural -> ["recursiveField", "erasureView"]
  KRepresentationRefinement ->
    ["retainedBaseField", "erasedEvidenceFields", "erasureView"]

requiredCertificateText
  :: Text
  -> [(Text, KValueNode)]
  -> Either Text Text
requiredCertificateText name fields =
  case lookup name fields of
    Just (KVText value) | not (T.null value) -> pure value
    _ -> Left ("representation-certificate field '" <> name <> "' must be nonempty text")

verifyOptionalCertificateIdentity
  :: Text
  -> [(Text, KValueNode)]
  -> Either Text ()
verifyOptionalCertificateIdentity name fields =
  case lookup name fields of
    Nothing -> pure ()
    Just (KVList []) -> pure ()
    Just (KVText value) | not (T.null value) -> pure ()
    Just _ ->
      Left
        ( "representation-certificate field '"
            <> name
            <> "' must be a nonempty identity or []"
        )

verifyCertificateFieldPaths
  :: VerifyContext
  -> [(Text, KValueNode)]
  -> Text
  -> Either Text ()
verifyCertificateFieldPaths context fields name =
  case lookup name fields of
    Just node -> mapM_ verifyPath =<< decodePaths node
    Nothing -> Left ("representation-certificate is missing field '" <> name <> "'")
  where
    decodePaths = \case
      KVList [KVGlobal constructor [], KVInteger index] ->
        pure [(constructor, index)]
      KVList nodes -> concat <$> mapM decodePaths nodes
      _ ->
        Left
          ( "representation-certificate field '"
              <> name
              <> "' has an invalid constructor-field path"
          )
    verifyPath (constructor, index) = do
      unless (index >= 0) $
        Left "representation-certificate constructor-field index is negative"
      fieldsForConstructor <-
        maybe
          (Left "representation-certificate field path names an unavailable constructor")
          pure
          (Map.lookup constructor (vcConstructorFields context))
      let directPayloadIndices = Set.fromList (Map.elems fieldsForConstructor)
      unless (fromInteger index `Set.member` directPayloadIndices) $
        Left "representation-certificate field path is absent from the authenticated constructor interface"

verifyCertificateProfileRestrictions
  :: [(Text, KValueNode)]
  -> Either Text ()
verifyCertificateProfileRestrictions fields =
  case lookup "profileRestrictions" fields of
    Just (KVList restrictions) -> do
      names <- mapM decode restrictions
      unless (names == sort (nub names)) $
        Left "representation-certificate profile restrictions are not canonical"
    _ -> Left "representation-certificate profileRestrictions must be a list"
  where
    decode = \case
      KVText name
        | name `Set.member` allowed -> pure name
      _ -> Left "representation-certificate profile restriction is unknown"
    allowed =
      Set.fromList
        [ "internal-values-only"
        , "exclude-dynamic-boundary"
        , "exclude-foreign-boundary"
        , "exclude-exported-abi"
        , "require-compact-finite-ordinal"
        , "require-unboxed-refinement"
        ]

representationCertificateTypeIdentity
  :: KRepresentationCertificate
  -> Text
representationCertificateTypeIdentity certificate =
  case canonicalizeDecl (KDRepresentationCertificate certificate) of
    KDRepresentationCertificate KRepresentationCertificate {..} ->
      canonicalIdentityHex
        "KCoreTypeNF"
        ( T.intercalate
            "\n"
            [ T.intercalate "," (map renderUniverse krcUniverses)
            , T.intercalate "\n" (map printBinder krcBinders)
            , T.intercalate "\n" (map printConstraint krcConstraints)
            , printTerm krcTarget
            ]
        )
    _ ->
      canonicalIdentityHex
        "KCoreTypeNF"
        (printTerm (krcTarget certificate))

malformedSchemaLiftProbeTags :: Set Text
malformedSchemaLiftProbeTags =
  Set.fromList
    [ "schema-lift"
    , "schema-lift-family-argument-mismatch"
    , "schema-lift-family-head-mismatch"
    , "unsaturated-schema-lift"
    ]

verifyMutualNominalSignature :: [(Text, KValueNode)] -> Either KCoreTextError ()
verifyMutualNominalSignature fields = do
  let field name = lookup name fields
      validGlobal = \case Just KVGlobal {} -> True; _ -> False
      validRole = \case
        Just (KVText role) -> role `elem` ["invariant", "covariant", "irrelevant"]
        _ -> False
  unless (validGlobal (field "firstFamily") && validGlobal (field "secondFamily")) $
    Left (schemaCertificateInvalid "mutual nominal signature must identify both families")
  unless (validRole (field "firstRoles") && validRole (field "secondRoles")) $
    Left (schemaCertificateInvalid "mutual nominal signature has an invalid role vector")

verifySignature :: VerifyContext -> [UniverseRef] -> KTerm -> Either KCoreTextError ()
verifySignature context universes ty = do
  verifyUniverseTelescope universes
  let scope = universeScope universes
  verifyTerm context scope emptyAssumptions Map.empty ty
  classifier <- inferSimple context scope emptyAssumptions Map.empty ty
  case classifier of
    Just KTType {} -> pure ()
    _ -> Left (invalid "a KCore declaration signature must itself have a universe classifier")

verifyUniverseTelescope :: [UniverseRef] -> Either KCoreTextError ()
verifyUniverseTelescope universes = do
  let ids = map urId universes
  when (length ids /= length (nub ids)) $
    Left (invalid "declaration universe parameters must have unique identities")

-- | A local recursive group is one semantic SCC. Its members may spell their
-- bound universe identities differently in hand-authored KCoreText, but they
-- must expose one alpha-equivalent telescope and proof-binder constraint set.
verifySharedLocalSccSchema :: [KLocalDef] -> Either KCoreTextError ()
verifySharedLocalSccSchema [] = pure ()
verifySharedLocalSccSchema (first : rest) =
  forM_ rest $ \definition ->
    unless (localSchemaKey definition == localSchemaKey first) $
      Left (invalid "local recursive SCC members must share one alpha-equivalent universe schema and proof-binder constraints")
  where
    localSchemaKey definition =
      let parameters = kldUniverses definition
          substitution =
            Map.fromList
              [ (urId parameter, KLUniverse (UniverseRef "scc" (-1 - index)))
              | (index, parameter) <- zip [0 ..] parameters
              ]
       in ( length parameters
          , sort
              [ KConstraint strict (scopeLevel substitution lower) (scopeLevel substitution upper)
              | KConstraint strict lower upper <- declarationProofConstraints (kldType definition)
              ]
          )
    scopeLevel substitution = \case
      KLUniverse ref -> Map.findWithDefault (KLUniverse ref) (urId ref) substitution
      KLSucc level -> KLSucc (scopeLevel substitution level)
      KLMax left right -> KLMax (scopeLevel substitution left) (scopeLevel substitution right)
      KLAdd left right -> KLAdd (scopeLevel substitution left) (scopeLevel substitution right)
      KLTerm term -> KLTerm (substituteUniverseParameters substitution term)
      level -> level

declarationProofConstraints :: KTerm -> [KConstraint]
declarationProofConstraints = \case
  KTPi binder codomain -> maybeToList (levelAuthorityConstraint binder) <> declarationProofConstraints codomain
  _ -> []

verifyConstraints :: VerifyContext -> Set Int -> [KConstraint] -> Either KCoreTextError ()
verifyConstraints context scope constraints = do
  mapM_
    (\constraint@(KConstraint _ lhs rhs) -> do
        verifyLevel context scope emptyAssumptions Map.empty lhs
        verifyLevel context scope emptyAssumptions Map.empty rhs
        unless (constraintIsSolverLevel constraint) $
          Left (invalid "a declaration universe constraint must normalize to the standard TypeLevel algebra")
    )
    constraints
  unless (assumptionsConsistent (constraintAssumptions constraints)) $
    Left (invalid "declaration universe constraints are inconsistent")
  where
    constraintIsSolverLevel (KConstraint _ lhs rhs) =
      case (toLevel lhs, toLevel rhs) of
        (Just _, Just _) -> True
        _ -> False

verifyAndBind :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KBinder -> Either KCoreTextError LocalEnv
verifyAndBind context universes assumptions env binder = do
  verifyBinder context universes assumptions env binder
  when (lrId (kbRef binder) `Map.member` env) $
    Left (invalid "local binder identities must be unique in scope")
  pure (Map.insert (lrId (kbRef binder)) (LocalBinder binder) env)

verifyAndBindDefinition
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> KBinder
  -> KTerm
  -> Either KCoreTextError LocalEnv
verifyAndBindDefinition context universes assumptions env binder body = do
  verifyBinder context universes assumptions env binder
  when (lrId (kbRef binder) `Map.member` env) $
    Left (invalid "local definition identities must be unique in scope")
  pure
    ( Map.insert
        (lrId (kbRef binder))
        (LocalDefinition (kbMode binder) [] (kbType binder) body)
        env
    )

-- | A dependent-former binder carries the elaborator's formation judgment as
-- untrusted checkpoint data. Replay the surface/KCore selection rule exactly;
-- accepting either direction of mismatch would let hand-written KCore choose
-- a different universe rule from source elaboration.
verifyFormerAndBind :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KBinder -> Either KCoreTextError LocalEnv
verifyFormerAndBind context universes assumptions env binder = do
  verifyBinder context universes assumptions env binder
  let selected =
        if kbMode binder == Parametric && kParametricKind context (kbType binder)
          then FormationParametric
          else FormationOrdinary
  unless (kbFormation binder == selected) $
    Left (invalid "dependent binder formation mode does not match the checked formation judgment")
  when (lrId (kbRef binder) `Map.member` env) $
    Left (invalid "local binder identities must be unique in scope")
  pure (Map.insert (lrId (kbRef binder)) (LocalBinder binder) env)

verifyBinder :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KBinder -> Either KCoreTextError ()
verifyBinder context universes assumptions env KBinder {..} = do
  verifyTerm context universes assumptions env kbType
  classifier <- inferSimple context universes assumptions env kbType
  case classifier of
    Just KTType {} -> pure ()
    _ ->
      Left
        ( invalid
            ( "a KCore binder domain must itself have a universe classifier"
                <> "; domain: "
                <> tshow kbType
                <> "; inferred classifier: "
                <> maybe "<none>" tshow classifier
            )
        )
  when (kbFormation == FormationParametric) $ do
    unless (kbMode == Parametric) $
      Left (invalid "parametric formation requires parametric observation")
    unless (kParametricKind context kbType) $
      Left (invalid "parametric formation requires a checked parametric-kind domain")
  when (kbOrigin == BinderGenerated && isNothing (levelAuthorityConstraint KBinder {..})) $
    Left (invalid "only an authenticated declaration-universe constraint binder may be marked generated")

-- | A declaration-universe constraint is part of the declaration's semantic
-- interface, not merely a consistency check at the definition site. Every
-- occurrence specializes the complete normalized block and must discharge it
-- from the lexical assumptions available at that use.
verifyInstantiatedConstraints
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> Text
  -> [UniverseRef]
  -> [KConstraint]
  -> [KLevel]
  -> Either KCoreTextError ()
verifyInstantiatedConstraints context universes assumptions env subject parameters constraints levels = do
  unless (length parameters == length levels) $
    Left (invalid (subject <> " has a malformed universe instantiation"))
  let substitution = Map.fromList (zip (map urId parameters) levels)
      specialize (KConstraint strict lower upper) =
        KConstraint strict
          (substituteUniverseLevel substitution lower)
          (substituteUniverseLevel substitution upper)
  forM_ (map specialize constraints) $ \constraint@(KConstraint strict lower upper) -> do
    verifyLevel context universes assumptions env lower
    verifyLevel context universes assumptions env upper
    case (toLevel lower, toLevel upper) of
      (Just lowerLevel, Just upperLevel) ->
        let requiredLower = if strict then normalizeLevel (LSucc lowerLevel) else lowerLevel
         in unless (proveLevelLeq assumptions requiredLower upperLevel == Proved) $
              Left
                ( invalid
                    ( subject <> " does not satisfy instantiated universe constraint "
                        <> printConstraint constraint
                    )
                )
      _ ->
        Left
          (invalid (subject <> " has a non-solver universe constraint after instantiation"))

substituteUniverseLevel :: Map Int KLevel -> KLevel -> KLevel
substituteUniverseLevel substitution = \case
  KLUniverse ref -> Map.findWithDefault (KLUniverse ref) (urId ref) substitution
  KLSucc level -> KLSucc (substituteUniverseLevel substitution level)
  KLMax left right -> KLMax (substituteUniverseLevel substitution left) (substituteUniverseLevel substitution right)
  KLAdd left right -> KLAdd (substituteUniverseLevel substitution left) (substituteUniverseLevel substitution right)
  KLTerm term -> KLTerm (substituteUniverseParameters substitution term)
  level -> level

substituteUniverseConstraint :: Map Int KLevel -> KConstraint -> KConstraint
substituteUniverseConstraint substitution (KConstraint strict lower upper) =
  KConstraint strict
    (substituteUniverseLevel substitution lower)
    (substituteUniverseLevel substitution upper)

verifySchemaLift
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> StableRef
  -> [KLevel]
  -> [KLevel]
  -> StableRef
  -> [KSchemaRoleEvidence]
  -> [KArgument]
  -> KTerm
  -> Either KCoreTextError ()
verifySchemaLift context universes assumptions env familyRef from to certificateRef roleEvidence targetArguments payload =
  mapLeftSchema $ do
    family <-
      maybe (Left (invalid "schema lift names an unavailable nominal family")) pure
        (Map.lookup familyRef (vcNominalFamilies context))
    certificate <-
      maybe (Left (invalid "schema lift names an unavailable schema certificate")) pure
        (Map.lookup certificateRef (vcSchemaCertificates context))
    unless (kscFamily certificate == familyRef && knfCertificate family == certificateRef) $
      Left (invalid "schema lift certificate does not authenticate the selected nominal family")
    let expectedRoles = kscRoles certificate
        universeParameters = map fst (knfUniverses family)
    unless (length from == length universeParameters && length to == length universeParameters) $
      Left (invalid "schema lift universe vectors do not saturate the nominal family")
    unless (length roleEvidence == length expectedRoles) $
      Left (invalid "schema lift role-evidence vector has the wrong arity")
    unless (length targetArguments == kscSaturationArity certificate) $
      Left (invalid "schema lift does not fully saturate the nominal family's ordinary arguments")
    mapM_ (verifyLevel context universes assumptions env) (from ++ to)
    let familyConstraints = declarationProofConstraints (foldr KTPi (knfResult family) (knfBinders family))
    verifyInstantiatedConstraints context universes assumptions env "schema-lift source" universeParameters familyConstraints from
    verifyInstantiatedConstraints context universes assumptions env "schema-lift target" universeParameters familyConstraints to
    verifyTerm context universes assumptions env payload
    sourceType <-
      inferSimple context universes assumptions env payload >>= maybe
        (Left (invalid "schema lift payload type cannot be inferred"))
        pure
    let (sourceHead, sourceArguments) = collectApplication (unfoldTypeHead context sourceType)
    sourceLevels <- case sourceHead of
      KTGlobal sourceFamily levels | sourceFamily == familyRef -> pure levels
      _ -> Left (invalid "schema lift payload does not have the selected nominal family head")
    unless (length sourceLevels == length from && and (zipWith sameKLevel sourceLevels from)) $
      Left (invalid "schema lift payload family arguments disagree with the declared source universe vector")
    unless (length sourceArguments == length targetArguments) $
      Left (invalid "schema lift source and target ordinary argument arities disagree")
    unless (and (zipWith sameArgument sourceArguments targetArguments)) $
      Left (invalid "schema lift changes a fully saturated ordinary family argument")
    zipWithM_ verifyRole (zip expectedRoles (zip from to)) roleEvidence
    let targetType = applyArguments (KTGlobal familyRef to) targetArguments
    targetClassifier <- inferSimple context universes assumptions env targetType
    case targetClassifier of
      Just KTType {} -> pure ()
      Just actual ->
        Left
          ( invalid
              ( "schema lift target is not a well-formed type; inferred "
                  <> printTerm actual
              )
          )
      Nothing -> Left (invalid "schema lift target type cannot be inferred")
  where
    collectApplication = go []
      where
        go arguments (KTApply function more) = go (more ++ arguments) function
        go arguments headTerm = (headTerm, arguments)
    sameArgument (KArgument sourceIcit source) (KArgument targetIcit target) =
      sourceIcit == targetIcit && sameKCoreTypeUnderIn assumptions env context source target
    applyArguments function [] = function
    applyArguments function arguments = KTApply function arguments
    verifyRole (expectedRole, (source, target)) supplied = case (expectedRole, supplied) of
      (Invariant, KSchemaInvariant) ->
        unless (sameKLevel source target) $
          Left (invalid "invariant schema parameter changed level")
      (Covariant, KSchemaCovariant evidence) ->
        verifyEvidence context universes assumptions env source target evidence
      (Irrelevant, KSchemaIrrelevant) -> pure ()
      _ -> Left (invalid "schema lift role evidence disagrees with the authenticated role vector")
    mapLeftSchema = either (Left . schemaLiftInvalid . kcteMessage) Right

verifyTerm :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KTerm -> Either KCoreTextError ()
verifyTerm context universes assumptions env =
  verifyTermScoped context universes (localEvidenceAssumptions assumptions env) env

verifyTermScoped :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KTerm -> Either KCoreTextError ()
verifyTermScoped context universes assumptions env = \case
  KTLocal ref levels -> do
    mapM_ (verifyLevel context universes assumptions env) levels
    entry <- maybe (Left (invalid ("unbound local reference " <> renderLocal ref))) Right (Map.lookup (lrId ref) env)
    let arity = case entry of
          LocalBinder _ -> 0
          LocalDefinition _ schema _ _ -> length schema
    unless (length levels == arity) $
      Left (invalid ("local " <> renderLocal ref <> " expects " <> tshow arity <> " universe arguments, found " <> tshow (length levels)))
  KTGlobal ref levels -> do
    mapM_ (verifyLevel context universes assumptions env) levels
    case Map.lookup ref (vcGlobalArities context) of
      Nothing ->
        let sameReadable =
              [ renderStable known
              | known <- Map.keys (vcGlobalArities context)
              , srName known == srName ref
              ]
            detail = case sameReadable of
              [] -> ""
              known -> "; identities with the same readable name: " <> T.intercalate ", " known
         in Left (invalid ("unavailable semantic identity " <> renderStable ref <> detail))
      Just arity ->
        unless (length levels == arity) $
          Left (invalid ("global " <> renderStable ref <> " expects " <> tshow arity <> " universe arguments, found " <> tshow (length levels)))
  KTType level -> verifyLevel context universes assumptions env level
  KTPi binder codomain -> underFormerBinder binder codomain
  KTSigma binder codomain -> underFormerBinder binder codomain
  KTLambda binder body -> underBinder binder body
  KTApply f args -> verifyTerm context universes assumptions env f >> mapM_ (verifyTerm context universes assumptions env . argumentTerm) args
  KTBlock items result -> do
    env' <- foldM verifyBlockItem env items
    verifyTerm context universes assumptions env' result
  KTLetRec definitions result -> do
    forM_ definitions (verifyUniverseTelescope . kldUniverses)
    verifySharedLocalSccSchema definitions
    let envRec =
          foldl
            (\acc KLocalDef {..} -> Map.insert (lrId kldRef) (LocalDefinition kldMode kldUniverses kldType kldBody) acc)
            env
            definitions
    when (Map.size envRec /= Map.size env + length definitions) $
      Left (invalid "local recursive definition identities must be unique in scope")
    forM_ definitions $ \KLocalDef {..} -> do
      let localScope = Set.union universes (universeScope kldUniverses)
      verifyTerm context localScope emptyAssumptions envRec kldType
      checkTermObserved kldMode context localScope emptyAssumptions envRec kldBody kldType
    verifyTerm context universes assumptions envRec result
  KTCase scrutinee resultType alternatives -> do
    verifyTerm context universes assumptions env scrutinee
    verifyTerm context universes assumptions env resultType
    scrutineeType <-
      inferSimple context universes assumptions env scrutinee >>= \case
        Just ty -> pure (unfoldTypeHeadWithLocals context env ty)
        Nothing -> Left (invalid "KCore case scrutinee type cannot be inferred")
    mapM_ (verifyCaseAlt scrutineeType resultType) alternatives
  KTConstruct ref levels args -> do
    mapM_ (verifyLevel context universes assumptions env) levels
    arity <- maybe (Left (invalid ("unavailable constructor semantic identity " <> renderStable ref))) Right (Map.lookup ref (vcGlobalArities context))
    unless (length levels == arity) $
      Left (invalid ("constructor " <> renderStable ref <> " expects " <> tshow arity <> " universe arguments, found " <> tshow (length levels)))
    mapM_ (verifyTerm context universes assumptions env . argumentTerm) args
  KTProject field term -> do
    unless (srId field == canonicalIdentityHex "KCoreField" (srName field)) $
      Left (invalid "record projection field identity does not match its readable field name")
    verifyTerm context universes assumptions env term
  KTLift from to evidence term -> do
    verifyLevel context universes assumptions env from
    verifyLevel context universes assumptions env to
    verifyEvidence context universes assumptions env from to evidence
    verifyTerm context universes assumptions env term
    sourceClassifier <- inferSimple context universes assumptions env term
    unless (maybe False (sameKCoreTypeUnderIn assumptions env context (KTType from)) sourceClassifier) $
      Left (invalid "lift payload classifier does not match its declared source level")
  KTSchemaLift family from to certificate roles targetArguments term ->
    verifySchemaLift context universes assumptions env family from to certificate roles targetArguments term
  KTAscribe value ty -> do
    verifyTerm context universes assumptions env ty
    classifier <- inferSimple context universes assumptions env ty
    case classifier of
      Just KTType {} -> pure ()
      _ -> Left (invalid "ascription target must itself have a universe classifier")
    checkTermObserved Parametric context universes assumptions env value ty
  KTLiteral _ -> requireImplExtension
  KTRecordType fields -> do
    requireImplExtension
    let identities = map fst fields
    unless (length identities == Set.size (Set.fromList identities)) $
      Left (invalid "record type field identities must be unique")
    forM_ identities $ \field ->
      unless (field == stableFieldRefFromReadable (srName field)) $
        Left (invalid "record type field identity does not match its readable name")
    _ <- foldM (verifyFormerAndBind context universes assumptions) env (map snd fields)
    pure ()
  KTRecordValue fields -> do
    requireImplExtension
    mapM_ (verifyTerm context universes assumptions env . snd) fields
  KTIf condition thenBranch elseBranch -> do
    requireImplExtension
    verifyTerm context universes assumptions env condition
    verifyTerm
      (withArithmeticBranchFact True condition context)
      universes
      assumptions
      env
      thenBranch
    verifyTerm
      (withArithmeticBranchFact False condition context)
      universes
      assumptions
      env
      elseBranch
  KTGeneric tag fields -> do
    unless (extensionOwnsTag (vcExtensions context) tag) $
      Left (invalid ("unsupported generic term node '" <> tag <> "'"))
    verifyImplGenericSchema tag fields
    case tag of
      "impl.kappa.core.do" -> verifyDo fields
      _
        | tag == intrinsicEffectTreeTag ->
            verifyIntrinsicEffectTree context universes assumptions env fields
        | tag `Set.member` decodedBuiltinTermTags -> do
            decoded <- either (Left . invalid) pure (decodeBuiltinTermNode tag fields)
            verifyTermScoped context universes assumptions env decoded
        | otherwise ->
            mapM_ (verifyValue context universes assumptions env . snd) fields
    verifyImplGenericSemantics context universes assumptions env tag fields
    case genericResultType tag fields of
      Nothing -> pure ()
      Just resultType -> do
        classifier <- inferSimple context universes assumptions env resultType
        case classifier of
          Just KTType {} -> pure ()
          _ -> Left (invalid ("generic term node '" <> tag <> "' has a result-type that is not a type"))
  where
    requireImplExtension =
      unless (extensionOwnsTag (vcExtensions context) "impl.kappa.core") $
        Left (invalid "implementation-owned KCore node requires extension impl.kappa")
    underBinder binder body = do
      env' <- verifyAndBind context universes assumptions env binder
      verifyTerm context universes assumptions env' body
    underFormerBinder binder body = do
      env' <- verifyFormerAndBind context universes assumptions env binder
      verifyTerm context universes assumptions env' body
    verifyBlockItem envHere = \case
      KBLet binder rhs -> do
        verifyBinder context universes assumptions envHere binder
        checkTermObserved (kbMode binder) context universes assumptions envHere rhs (kbType binder)
        verifyAndBindDefinition context universes assumptions envHere binder rhs
    verifyCaseAlt _ resultType (KCaseDefault body) =
      checkTermObserved Parametric context universes assumptions env body resultType
    verifyCaseAlt scrutineeType resultType (KCaseConstructor constructor levels bindings body) = do
      mapM_ (verifyLevel context universes assumptions env) levels
      (schema, parameters0, constructorType0) <-
        maybe (Left (invalid ("case constructor " <> renderStable constructor <> " is not declared in this KCore unit"))) Right
          (Map.lookup constructor (vcConstructorTypes context))
      unless (length schema == length levels) $
        Left (invalid ("case constructor " <> renderStable constructor <> " has the wrong universe arity"))
      let universeSubstitution = Map.fromList (zip (map urId schema) levels)
          parameters = map (substituteUniverseBinder universeSubstitution) parameters0
          constructorType = substituteUniverseParameters universeSubstitution constructorType0
          (payload0, constructorResult) = splitPiTelescope constructorType
      alignment <-
        maybe (Left (invalid "case constructor result does not determine its data parameters")) Right
          ( alignKConstructorResult
              True
              True
              (`Map.member` vcNominalFamilies context)
              (\ref -> Map.member (lrId ref) env)
              (sameKCoreTypeIn env context)
              parameters
              Map.empty
              constructorResult
              scrutineeType
          )
      refinedEnv <-
        installKConstructorRefinements
          context
          universes
          assumptions
          env
          (kcaLocalRefinements alignment)
      let payload =
            constructorEliminationPayload
              parameters
              payload0
              alignment
      unless (length payload == length (casePayloadBinders bindings)) $
        Left (invalid "case pattern binder count does not match the constructor payload telescope")
      env' <-
        checkCaseBindings
          refinedEnv
          payload
          (kcaPropositionalEquations alignment)
          bindings
      checkTermObserved Parametric context universes assumptions env' body resultType
      where
        checkCaseBindings envHere [] [] [] = pure envHere
        checkCaseBindings envHere expected (equation : equations) (KCaseBridge bridge : rest) = do
          unless (constructorBridgeMatchesEquation context envHere equation bridge) $
            Left
              ( invalid
                  ( "case constructor bridge does not prove the required index equation"
                      <> "\nrequired-left: "
                      <> printTerm (fst equation)
                      <> "\nrequired-right: "
                      <> printTerm (snd equation)
                      <> "\nbridge-type: "
                      <> printTerm (kbType (kcbBinder bridge))
                  )
              )
          envNext <- verifyConstructorBridge envHere bridge
          checkCaseBindings envNext expected equations rest
        checkCaseBindings _ _ [] (KCaseBridge {} : _) =
          Left (invalid "case constructor carries an unrequired propositional bridge")
        checkCaseBindings envHere (expectedBinder : expectedRest) equations (KCasePayload actualBinder : actualRest) = do
          verifyBinder context universes assumptions envHere actualBinder
          unless
            ( sameBinderContractUnderIn
                assumptions
                envHere
                context
                actualBinder
                expectedBinder
            ) $
            Left
              ( invalid
                  ( "case pattern binder does not match the constructor payload binder: actual "
                      <> T.pack (show actualBinder)
                      <> ", expected "
                      <> T.pack (show expectedBinder)
                  )
              )
          envNext <- verifyAndBind context universes assumptions envHere actualBinder
          let expectedRest' = map (renameBinderLocal (kbRef expectedBinder) (kbRef actualBinder)) expectedRest
          checkCaseBindings envNext expectedRest' equations actualRest
        checkCaseBindings _ _ _ _ =
          Left (invalid "case pattern binder or constructor-bridge count mismatch")
    verifyCaseAlt scrutineeType resultType (KCasePattern pattern' guard' body) = do
      env' <- verifyPortablePattern scrutineeType env pattern'
      mapM_ (checkBooleanTerm context universes assumptions env') guard'
      checkTermObserved Parametric context universes assumptions env' body resultType

    verifyPortablePattern expected envHere pattern' = do
      let slot = kpSlot pattern'
      verifyBinder context universes assumptions envHere slot
      unless (sameKCoreType context (kbType slot) expected) $
        Left (invalid "pattern slot type does not match the scrutinee component type")
      envNext <- verifyAndBind context universes assumptions envHere slot
      verifyPatternNode envNext pattern'

    verifyPatternField expectedBinder envHere pattern' = do
      let slot = kpSlot pattern'
      verifyBinder context universes assumptions envHere slot
      unless
        ( sameBinderContractUnderIn
            assumptions
            envHere
            context
            slot
            expectedBinder
        ) $
        Left (invalid "pattern structural slot does not match its checked telescope binder")
      envNext <- verifyAndBind context universes assumptions envHere slot
      verifyPatternNode envNext pattern'

    verifyPatternFields envHere [] [] = pure envHere
    verifyPatternFields envHere (expectedBinder : expectedRest) (pattern' : patternRest) = do
      envNext <- verifyPatternField expectedBinder envHere pattern'
      let expectedRest' = map (renameBinderLocal (kbRef expectedBinder) (kbRef (kpSlot pattern'))) expectedRest
      verifyPatternFields envNext expectedRest' patternRest
    verifyPatternFields _ _ _ = Left (invalid "pattern structural arity does not match its checked telescope")

    verifyPatternBinders envHere [] [] = pure envHere
    verifyPatternBinders envHere (expectedBinder : expectedRest) (actualBinder : actualRest) = do
      verifyBinder context universes assumptions envHere actualBinder
      unless
        ( sameBinderContractUnderIn
            assumptions
            envHere
            context
            actualBinder
            expectedBinder
        ) $
        Left (invalid "pattern binder does not match its checked telescope binder")
      envNext <- verifyAndBind context universes assumptions envHere actualBinder
      let expectedRest' = map (renameBinderLocal (kbRef expectedBinder) (kbRef actualBinder)) expectedRest
      verifyPatternBinders envNext expectedRest' actualRest
    verifyPatternBinders _ _ _ = Left (invalid "pattern binder count does not match its checked telescope")

    verifyConstructorBridge envHere bridge = do
      let binder = kcbBinder bridge
      verifyBinder context universes assumptions envHere binder
      unless
        ( kbMode binder == Ordinary
            && kbQuantity binder == KQ0
            && kbAccess binder == KValue
        ) $
        Left (invalid "constructor bridge binder must be ordinary, quantity-0, and by value")
      checkTermObserved Parametric context universes assumptions envHere
        (kcbProof bridge) (kbType binder)
      verifyAndBind context universes assumptions envHere binder

    verifyConstructorBridges envHere [] [] = pure envHere
    verifyConstructorBridges envHere (equation : equations) (bridge : bridges) = do
      unless (constructorBridgeMatchesEquation context envHere equation bridge) $
        Left (invalid "nested constructor bridge does not prove the required index equation")
      envNext <- verifyConstructorBridge envHere bridge
      verifyConstructorBridges envNext equations bridges
    verifyConstructorBridges _ _ _ =
      Left (invalid "nested constructor propositional-bridge count mismatch")

    verifyPatternNode envHere (KPattern slot exposed node') = case node' of
      KPNWild -> pure envHere
      KPNLiteral literal -> do
        unless (literalChecksAt context literal (kbType slot)) $
          Left (invalid "literal pattern does not match the scrutinee component type")
        pure envHere
      KPNTuple patterns -> case recordInterfaceHead context (kbType slot) of
        KTRecordType fields
          | length fields == length patterns -> verifyPatternFields envHere (map snd fields) patterns
          | otherwise -> Left (invalid "tuple pattern arity does not match its record telescope")
        _ -> Left (invalid "tuple pattern requires a record-telescope scrutinee type")
      KPNConstructor constructor levels existentials bridges fields -> do
        mapM_ (verifyLevel context universes assumptions envHere) levels
        (schema, parameters0, constructorType0) <-
          maybe (Left (invalid ("nested case constructor " <> renderStable constructor <> " is unavailable"))) Right
            (Map.lookup constructor (vcConstructorTypes context))
        unless (length schema == length levels) $
          Left (invalid "nested constructor pattern has the wrong universe arity")
        let universeSubstitution = Map.fromList (zip (map urId schema) levels)
            parameters = map (substituteUniverseBinder universeSubstitution) parameters0
            constructorType = substituteUniverseParameters universeSubstitution constructorType0
            (payload0, constructorResult) = splitPiTelescope constructorType
        alignment <-
          maybe (Left (invalid "nested constructor result does not determine its data parameters")) Right
            ( alignKConstructorResult
                True
                True
                (`Map.member` vcNominalFamilies context)
                (\ref -> Map.member (lrId ref) envHere)
                (sameKCoreTypeIn envHere context)
                parameters
                Map.empty
                constructorResult
                (kbType slot)
            )
        refinedEnv <-
          installKConstructorRefinements
            context
            universes
            assumptions
            envHere
            (kcaLocalRefinements alignment)
        let payload =
              constructorEliminationPayload
                parameters
                payload0
                alignment
            (expectedExistentials, expectedFields) = splitAt (length existentials) payload
        unless (length expectedExistentials == length existentials && length expectedFields == length fields) $
          Left (invalid "nested constructor pattern arity does not match its checked payload")
        envAfterExistentials <-
          verifyPatternBinders
            refinedEnv
            expectedExistentials
            existentials
        let expectedFields' = renameTelescope expectedExistentials existentials expectedFields
        envAfterBridges <-
          verifyConstructorBridges
            envAfterExistentials
            (kcaPropositionalEquations alignment)
            bridges
        verifyPatternFields envAfterBridges expectedFields' fields
      KPNRecord fields rest -> case recordInterfaceHead context (kbType slot) of
        KTRecordType expectedFields -> do
          unless (length fields == length expectedFields) $
            Left (invalid "record pattern must carry one structural slot per checked field")
          forM_ (zip fields expectedFields) $ \((field, _, _), (expectedField, _)) ->
            unless (field == expectedField) $
              Left (invalid "record pattern field identity does not match its checked telescope")
          envAfterFields <- verifyPatternFields envHere (map snd expectedFields) [pattern' | (_, _, pattern') <- fields]
          let residualSource =
                [ (expectedField, kpSlot pattern')
                | ((_, selected, pattern'), (expectedField, _)) <- zip fields expectedFields
                , not selected
                ]
          case rest of
            Nothing -> pure envAfterFields
            Just restPattern -> do
              unless (kpExposed restPattern) $
                Left (invalid "a serialized record rest slot must be body-visible")
              residual <- case recordInterfaceHead context (kbType (kpSlot restPattern)) of
                KTRecordType residualFields -> pure residualFields
                _ -> Left (invalid "record rest slot type must be a residual record telescope")
              unless (validResidualRecord envHere residualSource residual) $
                Left (invalid "record rest slot does not preserve the omitted dependent field telescope")
              verifyPortablePattern (kbType (kpSlot restPattern)) envAfterFields restPattern
        _ -> Left (invalid "record pattern requires a record-telescope scrutinee type")
      KPNInject tag payload -> do
        members <- variantMembers (kbType slot)
        memberType <- maybe (Left (invalid "variant pattern tag is not present in the scrutinee union")) Right (lookup tag members)
        verifyPortablePattern memberType envHere payload
      KPNInjectRest excluded -> do
        unless exposed $
          Left (invalid "a variant residual pattern must expose its checked slot")
        members <- variantMembers (kbType slot)
        unless (all (`elem` map fst members) excluded) $
          Left (invalid "variant residual pattern excludes an unavailable member tag")
        pure envHere
      KPNAs payload -> do
        unless exposed $
          Left (invalid "an as-pattern must expose its outer checked slot")
        verifyPortablePattern (kbType slot) envHere payload
      KPNOr alternatives permutations -> do
        case (alternatives, permutations) of
          (canonicalAlternative : _, _) | length alternatives == length permutations -> do
            environments <- mapM (verifyPortablePattern (kbType slot) envHere) alternatives
            let canonicalBinders = patternBodyBinders canonicalAlternative
            forM_ (zip alternatives permutations) $ \(alternative, permutation) -> do
              let alternativeBinders = patternBodyBinders alternative
              unless
                ( validBinderPermutation
                    envHere
                    canonicalBinders
                    alternativeBinders
                    permutation
                ) $
                Left (invalid "or-pattern alternative does not define the declared canonical binder permutation")
            case environments of
              canonicalEnvironment : _ -> pure canonicalEnvironment
              [] -> Left (invalid "or-pattern verification lost its canonical alternative")
          _ -> Left (invalid "or-pattern alternatives and permutations must be nonempty and aligned")

    variantMembers expected = case unfoldTypeHead context expected of
      KTGeneric "impl.kappa.core.variant-type" fields -> case (lookup "tags" fields, lookup "members" fields) of
        (Just (KVList tags), Just (KVList members)) -> do
          tagValues <- mapM (\case KVText tag -> pure tag; _ -> Left (invalid "variant type tag list is malformed")) tags
          memberValues <- mapM (\case KVTerm member -> pure member; _ -> Left (invalid "variant type member list is malformed")) members
          unless (length tagValues == length memberValues) $
            Left (invalid "variant type tag/member arities differ")
          pure (zip tagValues memberValues)
        _ -> Left (invalid "variant type is missing its semantic member tags")
      _ -> Left (invalid "variant pattern requires a checked variant scrutinee type")

    renameTelescope expected actual rest =
      foldl
        (\renamed (expectedBinder, actualBinder) -> map (renameBinderLocal (kbRef expectedBinder) (kbRef actualBinder)) renamed)
        rest
        (zip expected actual)
    patternBodyBinders (KPattern slot exposed node') =
      (if exposed then [slot] else []) ++ case node' of
        KPNConstructor _ _ existentials bridges fields ->
          existentials ++ map kcbBinder bridges ++ concatMap patternBodyBinders fields
        KPNTuple fields -> concatMap patternBodyBinders fields
        KPNRecord fields rest -> concatMap (\(_, _, pattern') -> patternBodyBinders pattern') fields ++ maybe [] patternBodyBinders rest
        KPNInject _ payload -> patternBodyBinders payload
        KPNOr (alternative : _) _ -> patternBodyBinders alternative
        KPNAs payload -> patternBodyBinders payload
        _ -> []

    validBinderPermutation envHere canonical alternative permutation =
      length canonical == length alternative
        && length permutation == length canonical
        && sort permutation == [0 .. length permutation - 1]
        && and
          [ sameBinderContractUnderIn
              assumptions
              envHere
              context
              canonicalBinder
              (alternative !! index)
          | (canonicalBinder, index) <- zip canonical permutation
          ]

    validResidualRecord envHere source actual = go [] source actual
      where
        go _ [] [] = True
        go renamings ((sourceField, sourceBinder) : sourceRest) ((actualField, actualBinder) : actualRest) =
          sourceField == actualField
            && sameBinderContractUnderIn
              assumptions
              envHere
              context
              actualBinder
              ( sourceBinder
                  { kbType =
                      foldl
                        (\ty (oldRef, newRef) -> renameLocal oldRef newRef ty)
                        (kbType sourceBinder)
                        renamings
                  }
              )
            && go (renamings ++ [(kbRef sourceBinder, kbRef actualBinder)]) sourceRest actualRest
        go _ _ _ = False
    verifyDo fields = do
      verifyImplGenericSchema "impl.kappa.core.do" fields
      resultType <- case lookup "result-type" fields of
        Just (KVTerm ty) -> pure ty
        _ -> Left (invalid "do node is missing its checked result type")
      verifyTerm context universes assumptions env resultType
      resultValueType <- maybe (Left (invalid "do result type is not an application of its checked monad carrier")) pure (monadicKTermResult resultType)
      items <- case lookup "items" fields of
        Just (KVList values) -> pure values
        _ -> Left (invalid "do items must be a value list")
      label <- optionalLabel fields
      _ <- verifyDoItems resultType resultValueType (maybe [] pure label) 0 env items
      pure ()
    verifyDoItems _ _ _ _ envHere [] = pure envHere
    verifyDoItems resultType resultValueType labels loopDepth envHere (value : rest) = case value of
      KVTerm (KTGeneric "impl.kappa.core.do.bind" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.bind" itemFields
        action <- requiredTerm "action" itemFields
        quantity <- requiredQuantity "quantity" itemFields
        pattern' <- requiredPattern "pattern" itemFields
        actionResult <- checkedActionResult resultType envHere action
        unless (kbQuantity (kpSlot pattern') == quantity) $
          Left (invalid "do.bind pattern root quantity does not match its serialized item quantity")
        envNext <- verifyPortablePattern actionResult envHere pattern'
        verifyDoItems resultType resultValueType labels loopDepth envNext rest
      KVTerm (KTGeneric "impl.kappa.core.do.let" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.let" itemFields
        rhs <- requiredTerm "value" itemFields
        quantity <- requiredQuantity "quantity" itemFields
        pattern' <- requiredPattern "pattern" itemFields
        verifyTerm context universes assumptions envHere rhs
        rhsType <- inferRequired envHere "do.let value" rhs
        unless (kbQuantity (kpSlot pattern') == quantity) $
          Left (invalid "do.let pattern root quantity does not match its serialized item quantity")
        envNext <- verifyPortablePattern rhsType envHere pattern'
        verifyDoItems resultType resultValueType labels loopDepth envNext rest
      KVTerm (KTGeneric "impl.kappa.core.do.letq" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.letq" itemFields
        rhs <- requiredTerm "value" itemFields
        pattern' <- requiredPattern "pattern" itemFields
        rhsType <- inferRequired envHere "do.let? value" rhs
        verifyTerm context universes assumptions envHere rhs
        envSuccess <- verifyPortablePattern rhsType envHere pattern'
        (elsePatterns, elseActions) <- optionalPatternAction itemFields
        case (elsePatterns, elseActions) of
          ([], []) -> pure ()
          ([elsePattern], [elseAction]) -> do
            envElse <- verifyPortablePattern rhsType envHere elsePattern
            _ <- checkedActionResult resultType envElse elseAction
            pure ()
          _ -> Left (invalid "do.let? else pattern/action must both be absent or singular")
        verifyDoItems resultType resultValueType labels loopDepth envSuccess rest
      KVTerm (KTGeneric "impl.kappa.core.do.return" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.return" itemFields
        returned <- requiredTerm "value" itemFields
        checkTerm context universes assumptions envHere returned resultValueType
        verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm (KTGeneric "impl.kappa.core.do.var" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.var" itemFields
        binder <- requiredBinder "binder" itemFields
        initial <- requiredTerm "initial" itemFields
        action <- requiredTerm "action" itemFields
        verifyTerm context universes assumptions envHere initial
        actionResult <- checkedActionResult resultType envHere action
        unless (sameKCoreType context actionResult (kbType binder)) $
          Left
            ( invalid
                ( "do.var binder type does not match its allocation action result (binder "
                    <> printTerm (unfoldTypeHead context (kbType binder))
                    <> ", action result "
                    <> printTerm (unfoldTypeHead context actionResult)
                    <> ")"
                )
            )
        envNext <- verifyAndBind context universes assumptions envHere binder
        verifyDoItems resultType resultValueType labels loopDepth envNext rest
      KVTerm (KTGeneric "impl.kappa.core.do.using" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.using" itemFields
        pattern' <- requiredPattern "pattern" itemFields
        acquire <- requiredTerm "acquire" itemFields
        release <- requiredTerm "release" itemFields
        resourceType <- checkedActionResult resultType envHere acquire
        releaseType <- inferRequired envHere "do.using release" release
        case unfoldTypeHead context releaseType of
          KTPi binder codomain -> do
            unless (sameKCoreType context (kbType binder) resourceType) $
              Left (invalid "do.using release domain does not match the acquired resource")
            unless (sameMonadCarrier resultType codomain) $
              Left (invalid "do.using release action uses a different monad carrier")
          _ -> Left (invalid "do.using release value is not a checked resource function")
        envNext <- verifyPortablePattern resourceType envHere pattern'
        verifyDoItems resultType resultValueType labels loopDepth envNext rest
      KVTerm (KTGeneric "impl.kappa.core.do.while" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.while" itemFields
        label <- optionalLabel itemFields
        conditionKind <- requiredText "condition-kind" itemFields
        condition <- requiredTerm "condition" itemFields
        case conditionKind of
          "pure" -> checkBooleanTerm context universes assumptions envHere condition
          "action" -> do
            conditionResult <- checkedActionResult resultType envHere condition
            unless (sameKCoreType context conditionResult (KTGlobal (stableRefForGlobal prelBool) [])) $
              Left (invalid "do.while action condition does not produce Bool")
          _ -> Left (invalid "do.while condition-kind must be 'pure' or 'action'")
        body <- requiredItems "body" itemFields
        elseItems <- optionalItemBlock "else" itemFields
        let labels' = maybe labels (: labels) label
        _ <- verifyDoItems resultType resultValueType labels' (loopDepth + 1) envHere body
        mapM_ (verifyDoItems resultType resultValueType labels loopDepth envHere) elseItems
        verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm (KTGeneric "impl.kappa.core.do.for" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.for" itemFields
        label <- optionalLabel itemFields
        pattern' <- requiredPattern "pattern" itemFields
        source <- requiredTerm "source" itemFields
        let elementType = kbType (kpSlot pattern')
        elementClassifier <- inferRequired envHere "do.for element type" elementType
        elementLevel <- case unfoldTypeHead context elementClassifier of
          KTType level -> pure level
          _ -> Left (invalid "do.for pattern slot is not classified by a universe")
        let
            sourceType =
              KTApply
                (KTGlobal (stableRefForGlobal prelList) [elementLevel])
                [KArgument KExplicit elementType]
        checkTerm context universes assumptions envHere source sourceType
        envBody <- verifyPortablePattern elementType envHere pattern'
        body <- requiredItems "body" itemFields
        elseItems <- optionalItemBlock "else" itemFields
        let labels' = maybe labels (: labels) label
        _ <- verifyDoItems resultType resultValueType labels' (loopDepth + 1) envBody body
        mapM_ (verifyDoItems resultType resultValueType labels loopDepth envHere) elseItems
        verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm (KTGeneric "impl.kappa.core.do.if" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.if" itemFields
        conditions <- requiredTerms "conditions" itemFields
        bodies <- requiredItemBlocks "bodies" itemFields
        unless (length conditions == length bodies && not (null conditions)) $
          Left (invalid "do.if conditions and bodies must be nonempty and aligned")
        mapM_ (checkBooleanTerm context universes assumptions envHere) conditions
        mapM_ (verifyDoItems resultType resultValueType labels loopDepth envHere) bodies
        optionalItemBlock "else" itemFields >>= mapM_ (verifyDoItems resultType resultValueType labels loopDepth envHere)
        verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm (KTGeneric tag itemFields)
        | tag == "impl.kappa.core.do.break" || tag == "impl.kappa.core.do.continue" -> do
            verifyImplGenericSchema tag itemFields
            label <- optionalLabel itemFields
            case label of
              Just named | named `notElem` labels -> Left (invalid "do loop control targets an out-of-scope label")
              Nothing | loopDepth == 0 -> Left (invalid "unlabeled do loop control occurs outside a loop")
              _ -> verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm (KTGeneric "impl.kappa.core.do.defer" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.defer" itemFields
        label <- optionalLabel itemFields
        case label of
          Just named | named `notElem` labels -> Left (invalid "do.defer targets an out-of-scope label")
          _ -> pure ()
        action <- requiredTerm "action" itemFields
        _ <- checkedActionResult resultType envHere action
        verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm (KTGeneric "impl.kappa.core.do.subdo" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.subdo" itemFields
        label <- optionalLabel itemFields
        nested <- requiredItems "items" itemFields
        let labels' = maybe labels (: labels) label
        _ <- verifyDoItems resultType resultValueType labels' loopDepth envHere nested
        verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm (KTGeneric "impl.kappa.core.do.assign" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.assign" itemFields
        assignedTerms <- mapM (\name -> requiredTerm name itemFields) ["ref", "rhs"]
        mapM_ (verifyTerm context universes assumptions envHere) assignedTerms
        action <- requiredTerm "action" itemFields
        _ <- checkedActionResult resultType envHere action
        verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm (KTGeneric "impl.kappa.core.do.expr" itemFields) -> do
        verifyImplGenericSchema "impl.kappa.core.do.expr" itemFields
        expression <- requiredTerm "value" itemFields
        verifyTerm context universes assumptions envHere expression
        expressionType <- inferRequired envHere "do expression" expression
        if sameMonadCarrier resultType expressionType
          then case monadicKTermResult expressionType of
            Just actionResult
              | null rest
              , not (sameKCoreType context actionResult resultValueType)
              , not (isUnitKTerm resultValueType) ->
                  Left (invalid "final do action result does not match the checked block result")
            Just _ -> pure ()
            Nothing -> Left (invalid "do action type has no result argument")
          else when (null rest) $
            checkTerm context universes assumptions envHere expression resultValueType
        verifyDoItems resultType resultValueType labels loopDepth envHere rest
      KVTerm _ -> Left (invalid "do item list contains an unsupported typed item node")
      _ -> Left (invalid "do item list contains a non-term value")

    inferRequired envHere subject term =
      inferSimple context universes assumptions envHere term >>= maybe (Left (invalid (subject <> " type cannot be inferred"))) pure

    checkedActionResult resultType envHere action = do
      verifyTerm context universes assumptions envHere action
      actionType <- inferRequired envHere "do action" action
      unless (sameMonadCarrier resultType actionType) $
        Left
          ( invalid
              ( "do action uses a different checked monad carrier (block "
                  <> printTerm (unfoldTypeHead context resultType)
                  <> ", action "
                  <> printTerm (unfoldTypeHead context actionType)
                  <> ")"
              )
          )
      maybe (Left (invalid "do action type has no result argument")) pure (monadicKTermResult actionType)

    sameMonadCarrier left right = case (monadicKTermView left, monadicKTermView right) of
      (Just (leftHead, leftPrefix, _), Just (rightHead, rightPrefix, _)) ->
        length leftPrefix == length rightPrefix
          && sameKCoreType context leftHead rightHead
          && and (zipWith sameArgument leftPrefix rightPrefix)
      _ -> False
      where
        sameArgument (KArgument leftExplicit leftTerm) (KArgument rightExplicit rightTerm) =
          leftExplicit == rightExplicit && sameKCoreType context leftTerm rightTerm

    monadicKTermView = kTermMonadicView context
    monadicKTermResult = kTermMonadicResult context

    isUnitKTerm term = case unfoldTypeHead context term of
      KTGlobal ref [] -> ref == stableRefForGlobal prelUnit
      _ -> False

    requiredTerm name fields = case lookup name fields of
      Just (KVTerm term) -> pure term
      _ -> Left (invalid ("do item field '" <> name <> "' must be a term value"))
    requiredTerms name fields = case lookup name fields of
      Just (KVList values) -> mapM (\case KVTerm term -> pure term; _ -> Left (invalid "do term list is malformed")) values
      _ -> Left (invalid ("do item field '" <> name <> "' must be a term list"))
    requiredBinder name fields = case lookup name fields of
      Just (KVBinder binder) -> pure binder
      _ -> Left (invalid ("do item field '" <> name <> "' must be a binder value"))
    requiredPattern name fields = case lookup name fields of
      Just (KVPattern pattern') -> pure pattern'
      _ -> Left (invalid ("do item field '" <> name <> "' must be a pattern value"))
    requiredQuantity name fields = case lookup name fields of
      Just (KVQuantity quantity) -> pure quantity
      _ -> Left (invalid ("do item field '" <> name <> "' must be a quantity value"))
    requiredText name fields = case lookup name fields of
      Just (KVText value) -> pure value
      _ -> Left (invalid ("do item field '" <> name <> "' must be text"))
    requiredItems name fields = case lookup name fields of
      Just (KVList values) | all isTermValue values -> pure values
      _ -> Left (invalid ("do item field '" <> name <> "' must be an item list"))
    requiredItemBlocks name fields = case lookup name fields of
      Just (KVList blocks) -> mapM (\case KVList values | all isTermValue values -> pure values; _ -> Left (invalid "do item block list is malformed")) blocks
      _ -> Left (invalid ("do item field '" <> name <> "' must be an item-block list"))
    optionalItemBlock name fields = case lookup name fields of
      Just (KVList []) -> pure []
      Just (KVList [KVList values]) | all isTermValue values -> pure [values]
      _ -> Left (invalid ("do item field '" <> name <> "' must contain zero or one item block"))
    optionalLabel fields = case lookup "label" fields of
      Just (KVList []) -> pure Nothing
      Just (KVList [KVText label]) -> pure (Just label)
      _ -> Left (invalid "do label must contain zero or one text value")
    optionalPatternAction fields = case (lookup "else-pattern" fields, lookup "else-action" fields) of
      (Just (KVList patterns), Just (KVList actions)) -> do
        patterns' <- mapM (\case KVPattern pattern' -> pure pattern'; _ -> Left (invalid "do.let? else-pattern list is malformed")) patterns
        actions' <- mapM (\case KVTerm action -> pure action; _ -> Left (invalid "do.let? else-action list is malformed")) actions
        pure (patterns', actions')
      _ -> Left (invalid "do.let? requires explicit else pattern/action lists")
    isTermValue = \case KVTerm _ -> True; _ -> False

-- | Independently derive the finite dependency set required by §30.2.0.
-- The typed verifier has already checked scope and interfaces before this is
-- called; any missing type/mode authority here is therefore a malformed
-- checkpoint, never evidence that the dependency set is empty.
kObservationDependencies
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> Maybe KTerm
  -> KTerm
  -> Either KCoreTextError KDependencySet
kObservationDependencies context universes assumptions locals expected =
  go [] (dependencyEnvFromLocals locals) expected
  where
    dependencyEnvFromLocals :: LocalEnv -> KDependencyEnv
    dependencyEnvFromLocals = Map.mapWithKey $ \ident entry -> case entry of
      LocalBinder binder -> KDependencyBinding (modeDependencies ident (kbMode binder)) Nothing entry
      LocalDefinition mode parameters _ body ->
        KDependencyBinding (modeDependencies ident mode) (Just (parameters, body)) entry

    dependencyLocalEnv = Map.map kdbEntry

    modeDependencies ident = \case
      Ordinary -> Set.empty
      Parametric -> Set.singleton (KObservationLocal ident)

    globalDependencies ref = case Map.lookup ref (vcGlobalModes context) of
      Just Ordinary -> pure Set.empty
      Just Parametric -> pure (Set.singleton (KObservationGlobal (srId ref)))
      Nothing -> dependencyFailure ("global observation metadata is unavailable for " <> renderStable ref)

    dependencyFailure reason =
      Left (invalid ("KCore observation dependency analysis failed: " <> reason))

    go path dependencyEnv wanted = \case
      KTLocal ref levels -> do
        levelDeps <- levelDependencies path dependencyEnv levels
        localBinding <- maybe
          (dependencyFailure ("local observation identity is unavailable for " <> renderLocal ref))
          pure
          (Map.lookup (lrId ref) dependencyEnv)
        pure (levelDeps `Set.union` kdbDependencies localBinding)
      KTGlobal ref levels -> do
        levelDeps <- levelDependencies path dependencyEnv levels
        globalDeps <- globalDependencies ref
        pure (levelDeps `Set.union` globalDeps)
      KTType level -> levelDependency path dependencyEnv level
      KTPi binder codomain -> formerDependencies path dependencyEnv binder codomain
      KTSigma binder codomain -> formerDependencies path dependencyEnv binder codomain
      KTLambda binder body -> do
        let origin = KObservationLocal (lrId (kbRef binder))
            dependencyEnv' = Map.insert (lrId (kbRef binder))
              (KDependencyBinding (modeDependencies (lrId (kbRef binder)) (kbMode binder)) Nothing (LocalBinder binder)) dependencyEnv
            bodyExpected = case unfoldTypeHead context <$> wanted of
              Just (KTPi expectedBinder expectedBody) ->
                Just (renameLocal (kbRef expectedBinder) (kbRef binder) expectedBody)
              _ -> Nothing
        Set.delete origin <$> go (0 : path) dependencyEnv' bodyExpected body
      application@KTApply {} -> applicationDependencies path dependencyEnv wanted application
      KTBlock items result -> do
        dependencyEnv' <- foldM (bindBlock path) dependencyEnv (zip [0 ..] items)
        go (length items : path) dependencyEnv' wanted result
      KTLetRec definitions result -> letRecDependencies path dependencyEnv definitions result wanted
      KTCase scrutinee resultType alternatives -> do
        scrutineeDeps <- go (0 : path) dependencyEnv Nothing scrutinee
        branchDeps <- forM (zip [1 ..] alternatives) $ \(index, alternative) ->
          case alternative of
            KCaseDefault body -> go (index : path) dependencyEnv (Just resultType) body
            KCaseConstructor _ _ bindings body -> do
              (dependencyEnv', bridgeDeps) <-
                foldM
                  (bindCaseBinding scrutineeDeps (index : path))
                  (dependencyEnv, Set.empty)
                  (zip [0 ..] bindings)
              bodyDeps <- go (index : path) dependencyEnv' (Just resultType) body
              pure (bridgeDeps `Set.union` bodyDeps)
            KCasePattern pattern' guard' body -> do
              let binders = kPatternDependencyBinders pattern'
                  dependencyEnv' = foldl (bindPattern scrutineeDeps (index : path)) dependencyEnv (zip [0 ..] binders)
              guardDeps <- maybe (pure Set.empty) (go (0 : index : path) dependencyEnv' Nothing) guard'
              bodyDeps <- go (1 : index : path) dependencyEnv' (Just resultType) body
              pure (guardDeps `Set.union` bodyDeps)
        pure (Set.unions (scrutineeDeps : branchDeps))
      KTConstruct ref levels arguments -> constructorDependencies path dependencyEnv ref levels arguments
      KTProject field receiver -> do
        receiverType <- inferSimple context universes assumptions (dependencyLocalEnv dependencyEnv) receiver >>= maybe
          (dependencyFailure "projection receiver type is unavailable")
          pure
        receiverDeps <- go (0 : path) dependencyEnv (Just receiverType) receiver
        binder <- maybe
          (dependencyFailure ("projection field interface is unavailable for " <> renderStable field))
          pure
          ( recordFieldBinder field (recordInterfaceHead context receiverType)
              <|> nominalFieldBinder context field receiver receiverType
          )
        pure $ case kbMode binder of
          Ordinary -> receiverDeps
          Parametric -> Set.insert (KObservationProjection (reverse path) (srId field)) receiverDeps
      KTLift _ _ _ value -> go (0 : path) dependencyEnv wanted value
      KTSchemaLift _ _ _ _ _ _ value -> go (0 : path) dependencyEnv wanted value
      KTAscribe value ty -> go (0 : path) dependencyEnv (Just ty) value
      KTLiteral _ -> pure Set.empty
      KTRecordType fields -> recordTypeDependencies path dependencyEnv fields
      KTRecordValue fields -> recordValueDependencies path dependencyEnv wanted fields
      KTIf condition thenBranch elseBranch -> do
        case knownBoolean condition of
          Just True -> go (1 : path) dependencyEnv wanted thenBranch
          Just False -> go (2 : path) dependencyEnv wanted elseBranch
          Nothing -> do
            conditionDeps <- go (0 : path) dependencyEnv Nothing condition
            thenDeps <- go (1 : path) dependencyEnv wanted thenBranch
            elseDeps <- go (2 : path) dependencyEnv wanted elseBranch
            pure (Set.unions [conditionDeps, thenDeps, elseDeps])
      KTGeneric tag fields
        | tag `Set.member` decodedBuiltinTermTags -> do
            decoded <- either (dependencyFailure . ("malformed built-in term node: " <>)) pure (decodeBuiltinTermNode tag fields)
            go path dependencyEnv wanted decoded
        | otherwise -> genericDependencies path dependencyEnv tag fields

    formerDependencies path dependencyEnv binder codomain = do
      domainDeps <- go (0 : path) dependencyEnv Nothing (kbType binder)
      let origin = KObservationLocal (lrId (kbRef binder))
          dependencyEnv' = Map.insert (lrId (kbRef binder))
            (KDependencyBinding (modeDependencies (lrId (kbRef binder)) (kbMode binder)) Nothing (LocalBinder binder)) dependencyEnv
      codomainDeps <- Set.delete origin <$> go (1 : path) dependencyEnv' Nothing codomain
      pure (domainDeps `Set.union` codomainDeps)

    bindBlock path dependencyEnv (index, KBLet binder rhs) = do
      rhsDeps <- go (index : path) dependencyEnv (Just (kbType binder)) rhs
      pure (Map.insert (lrId (kbRef binder))
        (KDependencyBinding rhsDeps (Just ([], rhs)) (LocalBinder binder)) dependencyEnv)

    letRecDependencies path dependencyEnv definitions result wanted = do
      let origins = Set.fromList [KObservationLocal (lrId (kldRef definition)) | definition <- definitions]
          recursiveEnv = foldl
            (\envHere definition ->
               Map.insert
                 (lrId (kldRef definition))
                 (KDependencyBinding
                    (Set.singleton (KObservationLocal (lrId (kldRef definition))))
                    (Just (kldUniverses definition, kldBody definition))
                    (LocalDefinition (kldMode definition) (kldUniverses definition)
                      (kldType definition) (kldBody definition)))
                 envHere)
            dependencyEnv
            definitions
      direct <- fmap Map.fromList $ forM (zip [0 ..] definitions) $ \(index, definition) -> do
        dependencies <- go (index : path) recursiveEnv (Just (kldType definition)) (kldBody definition)
        pure (KObservationLocal (lrId (kldRef definition)), dependencies)
      let expand summaries dependencies =
            Set.unions
              ( Set.difference dependencies origins
                  : [Map.findWithDefault Set.empty origin summaries | origin <- Set.toList (Set.intersection dependencies origins)]
              )
          close summaries =
            let next = Map.map (expand summaries) direct
             in if next == summaries then summaries else close next
          summaries = close (Map.map (`Set.difference` origins) direct)
          resultEnv = foldl
            (\envHere (origin, dependencies) -> case origin of
               KObservationLocal ident ->
                 let definition = do
                       localDefinition <- find ((== ident) . lrId . kldRef) definitions
                       pure (kldUniverses localDefinition, kldBody localDefinition)
                  in case find ((== ident) . lrId . kldRef) definitions of
                       Just localDefinition ->
                         Map.insert ident
                           (KDependencyBinding dependencies definition
                             (LocalDefinition (kldMode localDefinition) (kldUniverses localDefinition)
                               (kldType localDefinition) (kldBody localDefinition))) envHere
                       Nothing -> envHere
               _ -> envHere)
            dependencyEnv
            (Map.toList summaries)
      go (length definitions : path) resultEnv wanted result

    bindPattern sourceDeps path dependencyEnv (index, binder) =
      let projection = KObservationProjection (reverse (index : path)) ("pattern:" <> T.pack (show index))
          dependencies = case kbMode binder of
            Ordinary -> sourceDeps
            Parametric -> Set.insert projection sourceDeps
       in Map.insert (lrId (kbRef binder))
            (KDependencyBinding dependencies Nothing (LocalBinder binder)) dependencyEnv

    bindCaseBinding sourceDeps path (dependencyEnv, accumulated) (index, binding) =
      case binding of
        KCasePayload binder ->
          pure
            ( bindPattern sourceDeps path dependencyEnv (index, binder)
            , accumulated
            )
        KCaseBridge bridge -> do
          proofDeps <-
            go (index : path) dependencyEnv
              (Just (kbType (kcbBinder bridge)))
              (kcbProof bridge)
          let dependencies = sourceDeps `Set.union` proofDeps
          pure
            ( bindPattern dependencies path dependencyEnv
                (index, kcbBinder bridge)
            , accumulated `Set.union` proofDeps
            )

    applicationDependencies path dependencyEnv wanted application = do
      let (function, arguments) = collectApplication application
      if canonicalEvidenceIntrinsic function arguments
        then pure Set.empty
        else
          case transparentTransportArgument function arguments of
            Just value -> go path dependencyEnv wanted value
            Nothing ->
              case transparentFunctionBody dependencyEnv function of
                Just (body, bodyEnv) -> lambdaApplicationDependencies path bodyEnv wanted body arguments 0
                Nothing -> do
                  functionDeps <- go (0 : path) dependencyEnv Nothing function
                  functionType <- inferSimple context universes assumptions (dependencyLocalEnv dependencyEnv) function >>= maybe
                    (dependencyFailure "application head type is unavailable")
                    pure
                  walkArguments
                    path
                    dependencyEnv
                    functionDeps
                    (freshenKPiTelescopeForArguments arguments functionType)
                    arguments
                    0

    -- These compiler-issued witnesses carry no source or runtime information:
    -- their checked result is the canonical evidence that a fully applied
    -- resolved trait is a trait, and the canonical IsSubsingleton dictionary
    -- derived from that fact. In particular, they cannot reify their
    -- parametric type argument. Match exact stable identities and saturated
    -- implicit spines only; ordinary/user evidence follows the general rules.
    canonicalEvidenceIntrinsic
      (KTGlobal ref _)
      [KArgument KImplicit _] =
        ref == stableRefForGlobal prelIsTraitWitness
    canonicalEvidenceIntrinsic
      (KTGlobal ref _)
      [KArgument KImplicit _, KArgument KImplicit _] =
        ref == stableRefForGlobal prelTraitSubsingletonWitness
    canonicalEvidenceIntrinsic _ _ = False

    -- The checked prelude's public 'subst' and its transport intrinsic have the
    -- operational semantics of the identity function (the evaluator and both
    -- native backends use the same rule). Their type/equality arguments are
    -- erased evidence, not observable results. Recognize only the stable
    -- compiler-owned identities and their fully checked application shapes;
    -- term verification has already validated each telescope before dependency
    -- analysis reaches this point.
    transparentTransportArgument
      (KTGlobal ref _)
      [ KArgument KImplicit _
        , KArgument KImplicit _
        , KArgument KImplicit _
        , KArgument KImplicit _
        , KArgument KExplicit _
        , KArgument KExplicit value
        ]
        | ref == stableRefForGlobal prelSubst = Just value
    transparentTransportArgument
      (KTGlobal ref _)
      [ KArgument KImplicit _
        , KArgument KImplicit _
        , KArgument KExplicit value
        ]
        | ref == stableRefForGlobal (gPrel "__transport") = Just value
    transparentTransportArgument _ _ = Nothing

    transparentFunctionBody dependencyEnv = \case
      KTLocal ref levels -> do
        binding <- Map.lookup (lrId ref) dependencyEnv
        (parameters, body) <- kdbDefinition binding
        if length parameters == length levels
          then
            Just
              ( substituteUniverseParameters
                  (Map.fromList (zip (map urId parameters) levels))
                  body
              , Map.adjust
                  (\entry -> entry {kdbDefinition = Nothing})
                  (lrId ref)
                  dependencyEnv
              )
          else Nothing
      KTGlobal ref levels -> do
        mode <- Map.lookup ref (vcGlobalModes context)
        (parameters, body) <- Map.lookup ref (vcGlobalBodies context)
        if mode == Ordinary && length parameters == length levels && globalBodyAcyclic ref body
          then
            Just
              ( substituteUniverseParameters
                  (Map.fromList (zip (map urId parameters) levels))
                  body
              , dependencyEnv
              )
          else Nothing
      lambda@KTLambda {} -> Just (lambda, dependencyEnv)
      _ -> Nothing

    globalBodyAcyclic root rootBody = all (visit (Set.singleton root)) (termStableRefs rootBody)
      where
        visit active ref
          | ref `Set.member` active = False
          | otherwise = case Map.lookup ref (vcGlobalBodies context) of
              Nothing -> True
              Just (_, body) -> all (visit (Set.insert ref active)) (termStableRefs body)

    -- Transparent beta reduction follows the substitution equation directly:
    -- each lambda binder denotes the already-derived dependency set of its
    -- actual argument. This avoids retaining a temporary type dependency after
    -- a fully saturated polymorphic value function returns an ordinary value.
    lambdaApplicationDependencies path dependencyEnv wanted term [] _ =
      go path dependencyEnv wanted term
    lambdaApplicationDependencies path dependencyEnv wanted (KTLambda binder body) (KArgument explicitness argument : rest) index
      | explicitness == kbExplicitness binder = do
          argumentDeps <- go (2 * index + 1 : path) dependencyEnv (Just (kbType binder)) argument
          let dependencyEnv' =
                Map.insert
                  (lrId (kbRef binder))
                  (KDependencyBinding argumentDeps Nothing (LocalBinder binder))
                  dependencyEnv
          lambdaApplicationDependencies (2 * index + 2 : path) dependencyEnv' wanted body rest (index + 1)
    lambdaApplicationDependencies path dependencyEnv wanted term arguments _ =
      go path dependencyEnv wanted (KTApply term arguments)

    walkArguments _ _ accumulated _ [] _ = pure accumulated
    walkArguments path dependencyEnv accumulated functionType (KArgument explicitness argument : rest) index =
      case unfoldTypeHead context functionType of
        KTPi binder codomain
          | explicitness == kbExplicitness binder -> do
              argumentDeps <- go (index + 1 : path) dependencyEnv (Just (kbType binder)) argument
              let propagates =
                    kbMode binder == Parametric
                      && (kTermMentionsLocal (kbRef binder) codomain || kParametricKind context codomain)
                  accumulated' = accumulated `Set.union` if propagates then argumentDeps else Set.empty
                  resultType = substituteLocal (kbRef binder) argument codomain
              walkArguments path dependencyEnv accumulated' resultType rest (index + 1)
        _ -> dependencyFailure "application observation telescope is unavailable or has the wrong explicitness"

    constructorDependencies path dependencyEnv ref levels arguments = do
      (schema, _parameters0, constructorType0) <- maybe
        (dependencyFailure ("constructor observation telescope is unavailable for " <> renderStable ref))
        pure
        (Map.lookup ref (vcConstructorTypes context))
      unless (length schema == length levels) $
        dependencyFailure "constructor observation telescope has the wrong universe arity"
      let universeSubstitution = Map.fromList (zip (map urId schema) levels)
          constructorType =
            freshenKPiTelescopeForArguments
              arguments
              (substituteUniverseParameters universeSubstitution constructorType0)
          -- Data-family parameters are recovered from the expected constructor
          -- result by 'checkConstructor'; only the payload telescope is present
          -- in the serialized construction argument list.
      walkConstructor constructorType arguments 0
      where
        walkConstructor _ [] _ = pure Set.empty
        walkConstructor signature (KArgument explicitness argument : rest) index =
          case unfoldTypeHead context signature of
            KTPi binder codomain -> do
              unless (explicitness == kbExplicitness binder) $
                dependencyFailure "constructor observation telescope has the wrong explicitness"
              argumentDeps <- go (index : path) dependencyEnv (Just (kbType binder)) argument
              restDeps <-
                walkConstructor
                  (substituteLocal (kbRef binder) argument codomain)
                  rest
                  (index + 1)
              pure
                ( restDeps
                    `Set.union` if kbMode binder == Parametric then Set.empty else argumentDeps
                )
            _ -> dependencyFailure "constructor observation telescope has the wrong argument arity"

    recordTypeDependencies path dependencyEnv fields = do
      (dependencies, _, origins) <- foldM step (Set.empty, dependencyEnv, Set.empty) (zip [0 ..] fields)
      pure (dependencies `Set.difference` origins)
      where
        step (accumulated, envHere, origins) (index, (_, binder)) = do
          fieldDeps <- go (index : path) envHere Nothing (kbType binder)
          let origin = KObservationLocal (lrId (kbRef binder))
              envNext = Map.insert (lrId (kbRef binder))
                (KDependencyBinding (modeDependencies (lrId (kbRef binder)) (kbMode binder)) Nothing (LocalBinder binder)) envHere
          pure (accumulated `Set.union` fieldDeps, envNext, Set.insert origin origins)

    recordValueDependencies path dependencyEnv wanted fields = do
      declared <- case wanted of
        Just expectedType -> case recordInterfaceHead context expectedType of
          KTRecordType recordFields -> pure recordFields
          _ -> dependencyFailure "record value interface is unavailable"
        Nothing -> dependencyFailure "record value expected type is unavailable"
      let suppliedNames = map fst fields
          declaredNames = map (srName . fst) declared
          supplied = Map.fromList fields
      unless
        ( length suppliedNames == Set.size (Set.fromList suppliedNames)
            && Set.fromList suppliedNames == Set.fromList declaredNames
        ) $
        dependencyFailure "record value fields disagree with their checked interface"
      let orderedValues =
            [ value
            | field <- map fst declared
            , value <- maybeToList (Map.lookup (srName field) supplied)
            ]
          telescope =
            freshenKPiTelescopeForArguments
              (map (KArgument KExplicit) orderedValues)
              (foldr KTPi (KTType (KLFinite 0)) (map snd declared))
      walkRecord telescope (zip (map fst declared) orderedValues) 0
      where
        walkRecord _ [] _ = pure Set.empty
        walkRecord signature ((field, value) : rest) index =
          case unfoldTypeHead context signature of
            KTPi binder codomain -> do
              valueDeps <- go (index : path) dependencyEnv (Just (kbType binder)) value
              restDeps <-
                walkRecord
                  (substituteLocal (kbRef binder) value codomain)
                  rest
                  (index + 1)
              pure
                ( restDeps
                    `Set.union` if kbMode binder == Parametric then Set.empty else valueDeps
                )
            _ ->
              dependencyFailure
                ("record value telescope ended before field " <> srName field)

    intrinsicEffectTreeDependencies path dependencyEnv fields = do
      constructorType <- case lookup "constructor-type" fields of
        Just (KVTerm term) -> pure term
        _ -> dependencyFailure "effect-tree constructor telescope is unavailable"
      arguments <- case lookup "arguments" fields of
        Just (KVList values) -> mapM expectTerm values
        _ -> dependencyFailure "effect-tree constructor arguments are unavailable"
      let applicationArguments = map (KArgument KExplicit) arguments
      walk
        (freshenKPiTelescopeForArguments applicationArguments constructorType)
        arguments
        0
      where
        walk _ [] _ = pure Set.empty
        walk signature (argument : rest) index =
          case unfoldTypeHead context signature of
            KTPi binder codomain -> do
              argumentDeps <- go (index : path) dependencyEnv (Just (kbType binder)) argument
              restDeps <- walk (substituteLocal (kbRef binder) argument codomain) rest (index + 1)
              pure
                ( restDeps
                    `Set.union` if kbMode binder == Parametric then Set.empty else argumentDeps
                )
            _ -> dependencyFailure "effect-tree observation telescope has the wrong argument arity"
        expectTerm = \case
          KVTerm term -> pure term
          _ -> dependencyFailure "effect-tree constructor arguments contain a non-term value"

    genericDependencies path dependencyEnv tag fields = case tag of
      "impl.kappa.core.body-unavailable" -> dependencyFailure "an unavailable body reached term dependency checking"
      "impl.kappa.level-value" -> pure Set.empty
      "impl.kappa.core.arithmetic-proof" -> pure Set.empty
      "impl.kappa.core.inject" -> requiredPayload "value"
      "impl.kappa.core.seal" -> requiredPayload "value"
      "impl.kappa.core.thunk" -> requiredPayload "value"
      "impl.kappa.core.lazy" -> requiredPayload "value"
      "impl.kappa.core.force" -> requiredPayload "value"
      "impl.kappa.core.signature-type" -> requiredPayload "value"
      "impl.kappa.core.variant-type" -> requiredTermList "members"
      "impl.kappa.core.quote" -> do
        slotDeps <- requiredTermList "slots"
        pure slotDeps
      "impl.kappa.core.do" -> do
        items <- requiredItems "items"
        let resultValueType = case lookup "result-type" fields of
              Just (KVTerm resultType) -> kTermMonadicResult context resultType
              _ -> Nothing
        doItemDependencies resultValueType path dependencyEnv items
      _ | tag == intrinsicEffectTreeTag -> intrinsicEffectTreeDependencies path dependencyEnv fields
      _ | "impl.kappa.core.do." `T.isPrefixOf` tag ->
            doItemDependencies Nothing path dependencyEnv [KTGeneric tag fields]
      _ -> dependencyFailure ("generic term node has no observation rule: " <> tag)
      where
        requiredPayload name = case lookup name fields of
          Just (KVTerm term) -> go (0 : path) dependencyEnv Nothing term
          _ -> dependencyFailure ("generic node is missing term payload '" <> name <> "'")
        requiredTermList name = case lookup name fields of
          Just (KVList values) -> Set.unions <$> mapM (valueDependencies path dependencyEnv) values
          _ -> dependencyFailure ("generic node is missing term list '" <> name <> "'")
        requiredItems name = case lookup name fields of
          Just (KVList values) -> mapM expectTerm values
          _ -> dependencyFailure ("generic node is missing term list '" <> name <> "'")
        expectTerm = \case
          KVTerm term -> pure term
          _ -> dependencyFailure "a do-kernel item list contains a non-term value"

    -- Do-kernel observation is sequential and scope-sensitive.  The generic
    -- node schemas are independently verified before this calculus runs; the
    -- rules here therefore consume those stable schemas rather than guessing
    -- from rendered source names.  In particular, pattern dependencies must
    -- be installed only in the continuation/body scope that owns them.
    doItemDependencies _ _ _ [] = pure Set.empty
    doItemDependencies resultValueType path dependencyEnv (item : rest) = case item of
      KTGeneric tag fields -> case tag of
        "impl.kappa.core.do.bind" -> bindContinuation "action" "pattern"
        "impl.kappa.core.do.let" -> bindContinuation "value" "pattern"
        "impl.kappa.core.do.letq" -> do
          value <- requiredTerm "value"
          pattern' <- requiredPattern "pattern"
          valueDeps <- go (0 : path) dependencyEnv Nothing value
          let successEnv = bindSerializedPattern valueDeps (1 : path) dependencyEnv pattern'
          successDeps <- doItemDependencies resultValueType (2 : path) successEnv rest
          elseDeps <- case (lookup "else-pattern" fields, lookup "else-action" fields) of
            (Just (KVList []), Just (KVList [])) -> pure Set.empty
            (Just (KVList [KVPattern elsePattern]), Just (KVList [KVTerm elseAction])) -> do
              let elseEnv = bindSerializedPattern valueDeps (3 : path) dependencyEnv elsePattern
              go (4 : path) elseEnv Nothing elseAction
            _ -> dependencyFailure "do.letq else pattern/action fields are malformed"
          pure (Set.unions [valueDeps, successDeps, elseDeps])
        "impl.kappa.core.do.expr" -> plainContinuation ["value"]
        "impl.kappa.core.do.return" -> do
          value <- requiredTerm "value"
          direct <- go (0 : path) dependencyEnv resultValueType value
          restDeps <- doItemDependencies resultValueType (1 : path) dependencyEnv rest
          pure (direct `Set.union` restDeps)
        "impl.kappa.core.do.break" -> plainContinuation []
        "impl.kappa.core.do.continue" -> plainContinuation []
        "impl.kappa.core.do.var" -> do
          binder <- requiredBinder "binder"
          initial <- requiredTerm "initial"
          action <- requiredTerm "action"
          initialDeps <- go (0 : path) dependencyEnv Nothing initial
          actionDeps <- go (1 : path) dependencyEnv Nothing action
          let dependencyEnv' = bindSerializedBinder actionDeps (2 : path) dependencyEnv binder
          restDeps <- doItemDependencies resultValueType (3 : path) dependencyEnv' rest
          pure (Set.unions [initialDeps, actionDeps, restDeps])
        "impl.kappa.core.do.assign" -> plainContinuation ["ref", "rhs", "action"]
        "impl.kappa.core.do.using" -> bindContinuation "acquire" "pattern" >>= \scoped -> do
          release <- requiredTerm "release"
          releaseDeps <- go (3 : path) dependencyEnv Nothing release
          pure (scoped `Set.union` releaseDeps)
        "impl.kappa.core.do.while" -> do
          condition <- requiredTerm "condition"
          body <- requiredItems "body"
          elseItems <- optionalItemBlock "else"
          conditionDeps <- go (0 : path) dependencyEnv Nothing condition
          bodyDeps <- doItemDependencies resultValueType (1 : path) dependencyEnv body
          elseDeps <- maybe (pure Set.empty) (doItemDependencies resultValueType (2 : path) dependencyEnv) elseItems
          restDeps <- doItemDependencies resultValueType (3 : path) dependencyEnv rest
          pure (Set.unions [conditionDeps, bodyDeps, elseDeps, restDeps])
        "impl.kappa.core.do.for" -> do
          source <- requiredTerm "source"
          pattern' <- requiredPattern "pattern"
          body <- requiredItems "body"
          elseItems <- optionalItemBlock "else"
          sourceDeps <- go (0 : path) dependencyEnv Nothing source
          let bodyEnv = bindSerializedPattern sourceDeps (1 : path) dependencyEnv pattern'
          bodyDeps <- doItemDependencies resultValueType (2 : path) bodyEnv body
          elseDeps <- maybe (pure Set.empty) (doItemDependencies resultValueType (3 : path) dependencyEnv) elseItems
          restDeps <- doItemDependencies resultValueType (4 : path) dependencyEnv rest
          pure (Set.unions [sourceDeps, bodyDeps, elseDeps, restDeps])
        "impl.kappa.core.do.if" -> do
          conditions <- requiredTerms "conditions"
          bodies <- requiredItemBlocks "bodies"
          elseItems <- optionalItemBlock "else"
          conditionDeps <- Set.unions <$> zipWithM (\index term -> go (index : 0 : path) dependencyEnv Nothing term) [0 ..] conditions
          bodyDeps <- Set.unions <$> zipWithM (\index body -> doItemDependencies resultValueType (index : 1 : path) dependencyEnv body) [0 ..] bodies
          elseDeps <- maybe (pure Set.empty) (doItemDependencies resultValueType (2 : path) dependencyEnv) elseItems
          restDeps <- doItemDependencies resultValueType (3 : path) dependencyEnv rest
          pure (Set.unions [conditionDeps, bodyDeps, elseDeps, restDeps])
        "impl.kappa.core.do.defer" -> plainContinuation ["action"]
        "impl.kappa.core.do.subdo" -> do
          nested <- requiredItems "items"
          nestedDeps <- doItemDependencies resultValueType (0 : path) dependencyEnv nested
          restDeps <- doItemDependencies resultValueType (1 : path) dependencyEnv rest
          pure (nestedDeps `Set.union` restDeps)
        _ -> dependencyFailure ("unknown do-kernel observation schema: " <> tag)
        where
          bindContinuation valueField patternField = do
            value <- requiredTerm valueField
            pattern' <- requiredPattern patternField
            valueDeps <- go (0 : path) dependencyEnv Nothing value
            let dependencyEnv' = bindSerializedPattern valueDeps (1 : path) dependencyEnv pattern'
            restDeps <- doItemDependencies resultValueType (2 : path) dependencyEnv' rest
            pure (valueDeps `Set.union` restDeps)
          plainContinuation termFields = do
            direct <- Set.unions <$> zipWithM (\index field -> requiredTerm field >>= go (index : path) dependencyEnv Nothing) [0 ..] termFields
            restDeps <- doItemDependencies resultValueType (length termFields : path) dependencyEnv rest
            pure (direct `Set.union` restDeps)
          requiredTerm name = case lookup name fields of
            Just (KVTerm term) -> pure term
            _ -> dependencyFailure ("do-kernel node is missing term field '" <> name <> "'")
          requiredTerms name = case lookup name fields of
            Just (KVList values) -> mapM expectTerm values
            _ -> dependencyFailure ("do-kernel node is missing term-list field '" <> name <> "'")
          requiredPattern name = case lookup name fields of
            Just (KVPattern pattern') -> pure pattern'
            _ -> dependencyFailure ("do-kernel node is missing pattern field '" <> name <> "'")
          requiredBinder name = case lookup name fields of
            Just (KVBinder binder) -> pure binder
            _ -> dependencyFailure ("do-kernel node is missing binder field '" <> name <> "'")
          requiredItems name = case lookup name fields of
            Just (KVList values) -> mapM expectTerm values
            _ -> dependencyFailure ("do-kernel node is missing item-list field '" <> name <> "'")
          requiredItemBlocks name = case lookup name fields of
            Just (KVList values) -> mapM expectItemBlock values
            _ -> dependencyFailure ("do-kernel node is missing item-block-list field '" <> name <> "'")
          optionalItemBlock name = case lookup name fields of
            Just (KVList []) -> pure Nothing
            Just (KVList [value]) -> Just <$> expectItemBlock value
            _ -> dependencyFailure ("do-kernel node has malformed optional item block '" <> name <> "'")
          expectTerm = \case
            KVTerm term -> pure term
            _ -> dependencyFailure "a do-kernel term list contains a non-term value"
          expectItemBlock = \case
            KVList values -> mapM expectTerm values
            _ -> dependencyFailure "a do-kernel item block is not a term list"
      _ -> dependencyFailure "a do-kernel item is not an implementation-owned generic node"

    bindSerializedPattern sourceDeps path dependencyEnv pattern' =
      foldl
        (bindPattern sourceDeps path)
        dependencyEnv
        (zip [0 ..] (kPatternDependencyBinders pattern'))

    bindSerializedBinder sourceDeps path dependencyEnv binder =
      bindPattern sourceDeps path dependencyEnv (0, binder)

    valueDependencies path dependencyEnv = \case
      KVTerm term -> go path dependencyEnv Nothing term
      KVLevel level -> levelDependency path dependencyEnv level
      value -> valueNodeDependencies path dependencyEnv value

    valueNodeDependencies path dependencyEnv = \case
      KVTerm term -> go path dependencyEnv Nothing term
      KVLevel level -> levelDependency path dependencyEnv level
      KVQuantity (KQTerm term) -> go path dependencyEnv Nothing term
      KVQuantity _ -> pure Set.empty
      KVLocal ref levels -> go path dependencyEnv Nothing (KTLocal ref levels)
      KVGlobal ref levels -> go path dependencyEnv Nothing (KTGlobal ref levels)
      KVBinder binder -> go path dependencyEnv Nothing (kbType binder)
      KVPattern pattern' -> Set.unions <$> mapM (go path dependencyEnv Nothing . kbType) (kPatternDependencyBinders pattern')
      KVList values -> Set.unions <$> mapM (valueNodeDependencies path dependencyEnv) values
      _ -> pure Set.empty

    levelDependencies path dependencyEnv = fmap Set.unions . mapM (levelDependency path dependencyEnv)
    levelDependency path dependencyEnv = \case
      KLSucc level -> levelDependency path dependencyEnv level
      KLMax left right -> Set.union <$> levelDependency (0 : path) dependencyEnv left <*> levelDependency (1 : path) dependencyEnv right
      KLAdd left right -> Set.union <$> levelDependency (0 : path) dependencyEnv left <*> levelDependency (1 : path) dependencyEnv right
      KLTerm term -> go path dependencyEnv Nothing term
      _ -> pure Set.empty

    collectApplication = collect []
      where
        collect arguments (KTApply function more) = collect (more ++ arguments) function
        collect arguments function = (function, arguments)

    knownBoolean = \case
      KTConstruct ref _ []
        | ref == stableRefForConstructor prelTrue -> Just True
        | ref == stableRefForConstructor prelFalse -> Just False
      KTAscribe value _ -> knownBoolean value
      _ -> Nothing

kTermMonadicView :: VerifyContext -> KTerm -> Maybe (KTerm, [KArgument], KArgument)
kTermMonadicView context term = case collect [] (unfoldTypeHead context term) of
  (_, []) -> Nothing
  (headTerm, arguments) -> case reverse arguments of
    resultArgument : reversedPrefix -> Just (headTerm, reverse reversedPrefix, resultArgument)
    [] -> Nothing
  where
    collect arguments (KTApply function more) = collect (more ++ arguments) function
    collect arguments headTerm = (headTerm, arguments)

kTermMonadicResult :: VerifyContext -> KTerm -> Maybe KTerm
kTermMonadicResult context term = do
  (_, _, resultArgument) <- kTermMonadicView context term
  pure (argumentTerm resultArgument)

-- A KCore codomain is a parametric kind exactly by the normalized grammar of
-- §11.1.2.3B; quantity/access are independent and therefore checked here too.
kParametricKind :: VerifyContext -> KTerm -> Bool
kParametricKind context term = case unfoldTypeHead context term of
  KTType _ -> True
  KTPi binder codomain ->
    kbMode binder == Parametric
      && kbQuantity binder == KQ0
      && kbAccess binder == KValue
      && kParametricKind context (kbType binder)
      && kParametricKind context codomain
  _ -> False

-- | Independent §11.1.6/§14.2.1 classification for associated static-member
-- types. Unlike 'kParametricKind', this descends through arbitrary checked Pi
-- binders because @(n : Nat) -> Type@ is a compile-time function space even
-- though it is not a v1 parametric kind.
kAssociatedStaticMemberType :: VerifyContext -> KTerm -> Bool
kAssociatedStaticMemberType context = go
  where
    go term =
      case unfoldTypeHead context term of
        KTType {} -> True
        KTPi _ codomain -> go codomain
        normalized ->
          case collectApplication normalized of
            (KTGlobal ref _, _) ->
              ref `Set.member` associatedStaticCarrierIdentities
            _ -> False

    associatedStaticCarrierIdentities =
      Set.fromList
        (map stableRefForGlobal associatedStaticCarrierGlobals)

    collectApplication = collect []
      where
        collect arguments (KTApply function more) =
          collect (more ++ arguments) function
        collect arguments headTerm = (headTerm, arguments)

kTermMentionsLocal :: LocalRef -> KTerm -> Bool
kTermMentionsLocal target = Set.member (lrId target) . kTermLocalIds

kTermLocalIds :: KTerm -> Set Int
kTermLocalIds = \case
  KTLocal ref _ -> Set.singleton (lrId ref)
  KTGlobal _ levels -> levelIds levels
  KTType level -> levelIds [level]
  KTPi binder body -> binderIds binder `Set.union` kTermLocalIds body
  KTSigma binder body -> binderIds binder `Set.union` kTermLocalIds body
  KTLambda binder body -> binderIds binder `Set.union` kTermLocalIds body
  KTApply function arguments -> kTermLocalIds function `Set.union` Set.unions [kTermLocalIds term | KArgument _ term <- arguments]
  KTBlock items result -> Set.unions (kTermLocalIds result : [binderIds binder `Set.union` kTermLocalIds rhs | KBLet binder rhs <- items])
  KTLetRec definitions result -> Set.unions (kTermLocalIds result : [binderIdsFromLocal definition | definition <- definitions])
  KTCase scrutinee result alternatives -> Set.unions [kTermLocalIds scrutinee, kTermLocalIds result, Set.unions (map alternativeIds alternatives)]
  KTConstruct _ levels arguments -> levelIds levels `Set.union` Set.unions [kTermLocalIds term | KArgument _ term <- arguments]
  KTProject _ receiver -> kTermLocalIds receiver
  KTLift from to _ value -> levelIds [from, to] `Set.union` kTermLocalIds value
  KTSchemaLift _ from to _ roles targetArguments value ->
    levelIds (from ++ to)
      `Set.union` Set.unions (map schemaRoleIds roles)
      `Set.union` Set.unions (map (kTermLocalIds . argumentTerm) targetArguments)
      `Set.union` kTermLocalIds value
  KTAscribe value ty -> kTermLocalIds value `Set.union` kTermLocalIds ty
  KTLiteral _ -> Set.empty
  KTRecordType fields -> Set.unions [binderIds binder | (_, binder) <- fields]
  KTRecordValue fields -> Set.unions [kTermLocalIds value | (_, value) <- fields]
  KTIf condition yes no -> Set.unions (map kTermLocalIds [condition, yes, no])
  KTGeneric _ fields -> Set.unions [valueIds value | (_, value) <- fields]
  where
    binderIds binder = Set.insert (lrId (kbRef binder)) (kTermLocalIds (kbType binder))
    binderIdsFromLocal definition =
      Set.insert (lrId (kldRef definition)) (kTermLocalIds (kldType definition) `Set.union` kTermLocalIds (kldBody definition))
    alternativeIds = \case
      KCaseDefault body -> kTermLocalIds body
      KCaseConstructor _ levels bindings body ->
        levelIds levels
          `Set.union` Set.unions
            ( kTermLocalIds body
                : [ binderIds (caseBindingBinder binding)
                      `Set.union` case binding of
                        KCaseBridge bridge -> kTermLocalIds (kcbProof bridge)
                        KCasePayload {} -> Set.empty
                  | binding <- bindings
                  ]
            )
      KCasePattern pattern' guard' body -> Set.unions (kTermLocalIds body : maybe [] (pure . kTermLocalIds) guard' ++ map binderIds (kPatternDependencyBinders pattern'))
    valueIds = \case
      KVTerm term -> kTermLocalIds term
      KVLevel level -> levelIds [level]
      KVQuantity (KQTerm term) -> kTermLocalIds term
      KVLocal ref levels -> Set.insert (lrId ref) (levelIds levels)
      KVBinder binder -> binderIds binder
      KVPattern pattern' -> Set.unions (map binderIds (kPatternDependencyBinders pattern'))
      KVList values -> Set.unions (map valueIds values)
      _ -> Set.empty
    schemaRoleIds = \case
      KSchemaCovariant evidence -> evidenceIds evidence
      _ -> Set.empty
    evidenceIds = \case
      KELocal ref -> Set.singleton (lrId ref)
      KEGlobal _ levels -> levelIds levels
      KECertificate _ levels -> levelIds levels
    levelIds = Set.unions . map (\case
      KLSucc level -> levelIds [level]
      KLMax left right -> levelIds [left, right]
      KLAdd left right -> levelIds [left, right]
      KLTerm term -> kTermLocalIds term
      _ -> Set.empty)

kPatternDependencyBinders :: KPattern -> [KBinder]
kPatternDependencyBinders (KPattern slot _ node) = slot : case node of
  KPNConstructor _ _ existentials bridges fields ->
    existentials ++ map kcbBinder bridges ++ concatMap kPatternDependencyBinders fields
  KPNTuple fields -> concatMap kPatternDependencyBinders fields
  KPNRecord fields rest -> concatMap (kPatternDependencyBinders . (\(_, _, pattern') -> pattern')) fields ++ maybe [] kPatternDependencyBinders rest
  KPNInject _ payload -> kPatternDependencyBinders payload
  KPNOr (alternative : _) _ -> kPatternDependencyBinders alternative
  KPNAs payload -> kPatternDependencyBinders payload
  _ -> []

recordFieldBinder :: StableRef -> KTerm -> Maybe KBinder
recordFieldBinder field = \case
  KTRecordType fields -> snd <$> find ((== field) . fst) fields
  _ -> Nothing

checkTerm :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KTerm -> KTerm -> Either KCoreTextError ()
checkTerm = checkTermObserved Ordinary

checkTermObserved :: ObservationMode -> VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KTerm -> KTerm -> Either KCoreTextError ()
checkTermObserved = checkTermObservedAtBoundary True

checkTermObservedAtBoundary :: Bool -> ObservationMode -> VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KTerm -> KTerm -> Either KCoreTextError ()
checkTermObservedAtBoundary enforceBoundary observation context universes assumptions env actual expected = do
  verifyTerm context universes assumptions env actual
  case (actual, expected') of
    (KTGeneric tag fields, _)
      | tag `Set.member` decodedBuiltinTermTags -> do
          decoded <- either (Left . invalid) pure (decodeBuiltinTermNode tag fields)
          checkTermObservedAtBoundary enforceBoundary observation context universes assumptions env decoded expected'
    (KTGeneric "impl.kappa.core.arithmetic-proof" fields, _)
      | Just resultType <- genericResultType "impl.kappa.core.arithmetic-proof" fields
      , Just domain <- arithmeticDomainField fields
      , arithmeticCheckedPropositionsMatch
          context
          assumptions
          env
          []
          domain
          resultType
          expected' ->
          pure ()
    (KTLambda binder body, KTPi expectedBinder codomain) -> do
      unless
        ( sameBinderContractUnderIn
            assumptions
            env
            context
            binder
            expectedBinder
        ) $
        Left
          ( invalid
              ( "lambda binder does not match its declared Pi binder (actual "
                  <> printBinder binder
                  <> ", expected "
                  <> printBinder expectedBinder
                  <> ")"
              )
          )
      env' <- verifyAndBind context universes assumptions env binder
      -- A lambda binder discharges the dependency of ordinary payloads whose
      -- types mention it; it does not turn returning the parametric type code
      -- itself into a parametric sink.  Preserve the declaration's demanded
      -- observation mode while descending so
      -- @def ordinary bad (parametric A : Type) : Type = A@ is rejected,
      -- while @id (parametric A : Type) (x : A) : A = x@ remains valid.
      checkTermObservedAtBoundary False observation context universes assumptions env' body
        (renameLocal (kbRef expectedBinder) (kbRef binder) codomain)
    (KTConstruct ref levels arguments, _) ->
      checkConstructor context universes assumptions env ref levels arguments expected expected'
    (KTLocal ref _, KTType _) | observation == Ordinary -> case Map.lookup (lrId ref) env of
      Just (LocalBinder binder) | kbMode binder == Parametric ->
        Left (KCoreTextError "E_PARAMETRIC_TYPE_PROMOTION" "a parametric local cannot be returned as an ordinary type-code value")
      _ -> compareInferred
    (KTLift from to evidence value, KTType expectedLevel) -> do
      unless (to == expectedLevel) $
        Left (invalid "lift target does not match the expected classifier")
      verifyEvidence context universes (localEvidenceAssumptions assumptions env) env from to evidence
      inferred <- inferSimple context universes assumptions env value
      unless (maybe False (\ty -> sameKCoreTypeIn env context ty (KTType from)) inferred) $
        Left (invalid "lift source classifier does not match the lifted term")
    (KTAscribe value ty, _) -> do
      unless (sameKCoreTypeIn env context ty expected') (Left (invalid "ascription does not match expected type"))
      checkTermObservedAtBoundary False observation context universes assumptions env value ty
    (KTLiteral literal, _) ->
      unless (literalChecksAt context literal expected') compareInferred
    (KTRecordValue fields, _) ->
      case recordInterfaceView context expected' of
        (owner, KTRecordType recordFields) ->
          checkRecordValue context universes assumptions env owner fields recordFields
        _ -> Left (invalid "record value expected type has no exported structural record interface")
    (KTBlock items result, _) -> do
      -- Blocks are checked bidirectionally: their result is checked at the
      -- enclosing expected type after extending the environment with each
      -- verified let. Inferring the whole block first loses constructor-facet
      -- information when a type and its nullary constructor share one stable
      -- identity (for example @Unit@).
      env' <- foldM extendBlockEnv env items
      checkTermObservedAtBoundary False observation context universes assumptions env' result expected'
    (KTLetRec definitions result, _) -> do
      -- Local definitions have already been checked by 'verifyTerm' above.
      -- The enclosing expected type belongs to the letrec result, not to any
      -- definition body, so retain that direction instead of routing the
      -- result through the deliberately partial 'inferSimple'.
      let envRec =
            foldl
              (\acc KLocalDef {..} ->
                 Map.insert
                   (lrId kldRef)
                   (LocalDefinition kldMode kldUniverses kldType kldBody)
                   acc)
              env
              definitions
      checkTermObservedAtBoundary False observation context universes assumptions envRec result expected'
    (KTIf condition thenBranch elseBranch, _) -> do
      checkBooleanTerm context universes assumptions env condition
      checkTermObservedAtBoundary
        False
        observation
        (withArithmeticBranchFact True condition context)
        universes
        assumptions
        env
        thenBranch
        expected'
      checkTermObservedAtBoundary
        False
        observation
        (withArithmeticBranchFact False condition context)
        universes
        assumptions
        env
        elseBranch
        expected'
    _ -> compareInferred
  when (enforceBoundary && observation == Ordinary) $ do
    rejectObservationDependencies env actual expected'
    checkOrdinaryTerminalTypeResult env actual expected'
  where
    expected' = unfoldTypeHeadWithLocals context env expected
    rejectObservationDependencies envHere termHere expectedHere = do
      rawDependencies <-
        kObservationDependencies context universes assumptions envHere (Just expectedHere) termHere
      dependencies <-
        kClassifierRelativeDependencies
          context
          universes
          assumptions
          envHere
          expectedHere
          rawDependencies
      unless (Set.null dependencies) $
        Left
          ( KCoreTextError
              "E_PARAMETRIC_TYPE_PROMOTION"
              ( "a term with parametric observation dependencies cannot enter an ordinary KCore position; dependencies: "
                  <> T.pack (show (Set.toAscList dependencies))
              )
          )
    checkOrdinaryTerminalTypeResult envHere termHere expectedHere =
      case (termHere, unfoldTypeHead context expectedHere) of
        (KTLambda binder body, KTPi expectedBinder codomain)
          | sameBinderContractUnderIn
              assumptions
              envHere
              context
              binder
              expectedBinder -> do
              envNext <- verifyAndBind context universes assumptions envHere binder
              checkOrdinaryTerminalTypeResult
                envNext
                body
                (renameLocal (kbRef expectedBinder) (kbRef binder) codomain)
        (KTBlock items result, expectedResult) -> do
          envNext <- foldM extendBlockEnv envHere items
          checkOrdinaryTerminalTypeResult envNext result expectedResult
        (KTLetRec definitions result, expectedResult) -> do
          let envNext =
                foldl
                  (\acc KLocalDef {..} ->
                    Map.insert
                      (lrId kldRef)
                      (LocalDefinition kldMode kldUniverses kldType kldBody)
                      acc)
                  envHere
                  definitions
          checkOrdinaryTerminalTypeResult envNext result expectedResult
        (KTAscribe value ty, _) -> checkOrdinaryTerminalTypeResult envHere value ty
        (_, KTType _) -> rejectObservationDependencies envHere termHere expectedHere
        _ -> pure ()
    extendBlockEnv envHere (KBLet binder rhs) =
      verifyAndBindDefinition context universes assumptions envHere binder rhs
    compareInferred = do
      inferred <- inferSimple context universes assumptions env actual
      case inferred of
        Just ty | sameKCoreTypeIn env context ty expected' -> pure ()
        Just ty ->
          Left
            ( invalid
                ( "KCore term does not have its declared type (inferred "
                    <> printTerm ty
                    <> ", expected "
                    <> printTerm expected'
                    <> ")"
                )
            )
        Nothing ->
          Left
            ( invalid
                ( "KCore checkpoint verification could not infer the term's declared type for "
                    <> printTerm actual
                    <> " (expected "
                    <> printTerm expected'
                    <> ")"
                )
            )

checkConstructor :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> StableRef -> [KLevel] -> [KArgument] -> KTerm -> KTerm -> Either KCoreTextError ()
checkConstructor context universes assumptions env ref levels arguments _expectedSurface expected = do
  (schema, parameters0, constructorType0) <-
    maybe (Left (invalid ("constructor signature is unavailable for " <> renderStable ref))) Right
      (Map.lookup ref (vcConstructorTypes context))
  unless (length schema == length levels) $
    Left (invalid "constructor universe instantiation has the wrong arity")
  let universeSubstitution = Map.fromList (zip (map urId schema) levels)
      parameters = map (substituteUniverseBinder universeSubstitution) parameters0
      constructorType = substituteUniverseParameters universeSubstitution constructorType0
      (payloadBinders0, result0) = splitPiTelescope constructorType
      allBinders = parameters ++ payloadBinders0
      parameterIds = Set.fromList (map (lrId . kbRef) parameters)
  let expectedConstructorResult = expected
      expectedConstructorShape =
        stripClassifierLifts expectedConstructorResult
  parameterSubstitution <-
    maybe
      ( Left
          ( invalid
              ( "constructor expected result supplies "
                  <> T.pack (show (length (snd (collectApplication expectedConstructorResult))))
                  <> " family arguments for a "
                  <> T.pack (show (length parameters))
                  <> "-parameter data telescope"
              )
          )
      )
      Right
      (alignConstructorParameters parameters expectedConstructorShape)
  inferredSubstitution <-
    maybe
      ( Left
          ( invalid
              ( "constructor " <> renderStable ref
                  <> " result does not determine its data parameters (result "
                  <> printTerm result0
                  <> ", expected "
                  <> printTerm expectedConstructorResult
                  <> ")"
              )
          )
      )
      Right
      (matchConstructorResult assumptions env context allBinders parameterSubstitution result0 expectedConstructorShape)
  let indexedPayload = Map.withoutKeys inferredSubstitution parameterIds
      payloadRequirements =
        [ Map.lookup (lrId (kbRef binder)) indexedPayload
        | binder <- payloadBinders0
        ]
      specializedPayloadTelescope =
        substituteKTermParameters
          parameters
          parameterSubstitution
          (foldr KTPi result0 payloadBinders0)
      (payloadBinders, result) =
        splitPiTelescope
          ( freshenKPiTelescopeForArguments
              arguments
              specializedPayloadTelescope
          )
  instantiatedResult <-
    case checkPayload payloadRequirements payloadBinders arguments result of
      Left err ->
        Left
          err
            { kcteMessage =
                kcteMessage err
                  <> "\nwhile checking constructor "
                  <> renderStable ref
            }
      Right value -> Right value
  unless (sameKCoreTypeUnderIn assumptions env context instantiatedResult expectedConstructorResult) $
    Left
      ( invalid
          ( "constructor result does not match the expected type"
              <> "\ninstantiated-constructor-result: "
              <> printTerm instantiatedResult
              <> "\nexpected-constructor-result: "
              <> printTerm expectedConstructorResult
              <> "\nactive-branch-facts: "
              <> T.intercalate
                "\n"
                [ (if truth then "true: " else "false: ")
                    <> printTerm condition
                | (truth, condition) <- vcArithmeticBranchFacts context
                ]
          )
      )
  where
    checkPayload [] [] [] result = pure result
    checkPayload (required : requirements) (binder : binders) (KArgument explicitness argument : rest) result = do
      unless (explicitness == kbExplicitness binder) $
        Left (invalid "constructor argument explicitness does not match its binder")
      checkTermObserved (kbMode binder) context universes assumptions env argument (kbType binder)
      forM_ required $ \fixed ->
        unless (sameKCoreTypeUnderIn assumptions env context fixed argument) $
          Left (invalid "constructor argument does not satisfy the index fixed by its expected result")
      checkPayload
        requirements
        (map (renameBinderType (kbRef binder) argument) binders)
        rest
        (substituteLocal (kbRef binder) argument result)
    checkPayload _ _ _ _ = Left (invalid "constructor argument count does not match its payload telescope")
    renameBinderType old replacement binder = binder {kbType = substituteLocal old replacement (kbType binder)}

    -- A saturated nominal result carries one argument for every data
    -- parameter, including parameters refined away by a GADT constructor
    -- result (for example equality's @y@ in @refl : x = x@).  Seed those
    -- identities from the expected family instance, then let
    -- 'matchConstructorResult' verify every constructor refinement and infer
    -- constructor-local indices.  Recovering parameters only from variable
    -- occurrences in the result rejects valid indexed constructors and cannot
    -- distinguish an omitted parameter from a refinement.
    alignConstructorParameters binders result = do
      let (_, resultArguments) = collectApplication result
      guard (length binders == length resultArguments)
      pure . Map.fromList $
        [ (lrId (kbRef binder), argument)
        | (binder, KArgument _ argument) <- zip binders resultArguments
        ]

    collectApplication = go []
      where
        go collected (KTApply function more) = go (more ++ collected) function
        go collected function = (function, collected)

substituteUniverseBinder :: Map Int KLevel -> KBinder -> KBinder
substituteUniverseBinder substitution binder =
  binder {kbType = substituteUniverseParameters substitution (kbType binder)}

splitPiTelescope :: KTerm -> ([KBinder], KTerm)
splitPiTelescope = go []
  where
    go binders (KTPi binder body) = go (binders ++ [binder]) body
    go binders result = (binders, result)

-- | A cumulative classifier lift changes which universe classifies a type
-- code, not the nominal type denoted by that code. Constructor result
-- matching needs the latter shape. The enclosing 'checkTermObserved' call has
-- already verified the lift evidence; schema lifts are deliberately retained
-- because they select a different nominal universe instance.
stripClassifierLifts :: KTerm -> KTerm
stripClassifierLifts = \case
  KTLift _ _ _ inner -> stripClassifierLifts inner
  term -> term

data KConstructorAlignment = KConstructorAlignment
  { kcaParameterSubstitution :: !(Map Int KTerm)
  , kcaLocalRefinements :: ![(LocalRef, KTerm)]
  , kcaPropositionalEquations :: ![(KTerm, KTerm)]
  }

-- | Align a checked constructor result with a demanded family instance.
-- Construction passes @allowRefinements = False@: a constructor cannot make
-- an arbitrary demanded index true. Pattern elimination passes @True@ and may
-- orient a repeated constructor parameter onto an acyclic local definition
-- already present in the branch environment. This is the generic GADT rule;
-- no data or constructor spelling participates.
alignKConstructorResult
  :: Bool
  -> Bool
  -> (StableRef -> Bool)
  -> (LocalRef -> Bool)
  -> (KTerm -> KTerm -> Bool)
  -> [KBinder]
  -> Map Int KTerm
  -> KTerm
  -> KTerm
  -> Maybe KConstructorAlignment
alignKConstructorResult allowRefinements allowPropositional nominalFamily localAvailable sameTerm parameters initial =
  \patternTerm actualTerm ->
    finalize
      <$> go
        (KConstructorAlignment initial [] [])
        patternTerm
        actualTerm
  where
    parameterIds = Set.fromList (map (lrId . kbRef) parameters)

    finalize alignment =
      alignment
        { kcaParameterSubstitution =
            fmap
              (applyRefinements (kcaLocalRefinements alignment))
              (kcaParameterSubstitution alignment)
        , kcaPropositionalEquations =
            [ ( finalizeDeclarationTerm alignment lhs
              , finalizeSpecializedTerm alignment rhs
              )
            | (lhs, rhs) <- kcaPropositionalEquations alignment
            ]
        }

    go alignment patternTerm0 actualTerm0 =
      let rawPatternTerm = stripClassifierLifts patternTerm0
          patternTerm =
            substituteKTermParameters
              parameters
              (kcaParameterSubstitution alignment)
              rawPatternTerm
          actualTerm =
            applyRefinements
              (kcaLocalRefinements alignment)
              (stripClassifierLifts actualTerm0)
       in case rawPatternTerm of
            KTLocal ref [] | lrId ref `Set.member` parameterIds ->
              case Map.lookup (lrId ref) (kcaParameterSubstitution alignment) of
                Nothing ->
                  Just
                    alignment
                      { kcaParameterSubstitution =
                          Map.insert
                            (lrId ref)
                            actualTerm
                            (kcaParameterSubstitution alignment)
                      }
                Just prior
                  | equivalentSpecialized alignment prior actualTerm ->
                      Just alignment
                  | otherwise ->
                      refine alignment actualTerm prior
            _ | equivalentSpecialized alignment patternTerm actualTerm ->
                  Just alignment
            -- Recurse over declaration-owned result syntax, not its
            -- specialized copy. The latter contains caller-owned terms; a
            -- second substitution can mistake a call-site local for an
            -- unrelated family parameter with the same presentation id.
            _ -> alignStructured alignment rawPatternTerm actualTerm

    alignStructured alignment patternTerm actualTerm =
      case nominalApplication patternTerm of
        Just (patternRef, patternLevels, patternArgs)
          | nominalFamily patternRef ->
              case nominalApplication actualTerm of
                Just (actualRef, actualLevels, actualArgs)
                  | patternRef == actualRef
                  , length patternLevels == length actualLevels
                  , and (zipWith sameKLevel patternLevels actualLevels)
                  , length patternArgs == length actualArgs ->
                      foldM matchArgument alignment (zip patternArgs actualArgs)
                _ -> Nothing
        _ -> case patternTerm of
          KTGlobal patternRef patternLevels -> case actualTerm of
              KTGlobal actualRef actualLevels
                | patternRef == actualRef
                , length patternLevels == length actualLevels
                , and (zipWith sameKLevel patternLevels actualLevels) ->
                    Just alignment
              _ -> Nothing
          KTConstruct patternConstructor patternLevels patternArguments ->
              case actualTerm of
                KTConstruct actualConstructor actualLevels actualArguments
                  | patternConstructor == actualConstructor
                  , length patternLevels == length actualLevels
                  , and (zipWith sameKLevel patternLevels actualLevels)
                  , length patternArguments == length actualArguments ->
                      foldM
                        matchArgument
                        alignment
                        (zip patternArguments actualArguments)
                _ -> Nothing
          KTType patternLevel -> case actualTerm of
              KTType actualLevel
                | sameKLevel patternLevel actualLevel -> Just alignment
              _ -> Nothing
          _ ->
            refine alignment actualTerm patternTerm
              <|> recordPropositionalEquation alignment patternTerm actualTerm

    matchArgument alignment (KArgument patternExplicit patternTerm, KArgument actualExplicit actualTerm)
      | patternExplicit == actualExplicit =
          go alignment patternTerm actualTerm
      | otherwise = Nothing

    -- Both sides originate at the constructor use site. They are already
    -- specialized and must not be passed through the declaration-parameter
    -- substitution again: independent KCore scopes may reuse the same local
    -- presentation ids.
    equivalentSpecialized alignment lhs rhs =
      sameTerm
        (applyRefinements (kcaLocalRefinements alignment) lhs)
        (applyRefinements (kcaLocalRefinements alignment) rhs)

    finalizeDeclarationTerm alignment =
      applyRefinements (kcaLocalRefinements alignment)
        . substituteKTermParameters
            parameters
            (kcaParameterSubstitution alignment)

    -- The right endpoint of a recorded propositional equation comes from the
    -- constructor use site. It is already specialized and may reuse numeric
    -- presentation ids from the declaration telescope; applying the
    -- declaration substitution again would rewrite unrelated caller locals.
    finalizeSpecializedTerm alignment =
      applyRefinements (kcaLocalRefinements alignment)

    refine alignment preferred replacement
      | not allowRefinements = Nothing
      | otherwise =
          orient alignment preferred replacement
            <|> orient alignment replacement preferred

    orient alignment candidate replacement = case candidate of
      KTLocal ref []
        | localAvailable ref
        , lrId ref `Set.notMember` kTermLocalIds replacement ->
            case lookup (lrId ref) [(lrId existing, value) | (existing, value) <- kcaLocalRefinements alignment] of
              Just existing
                | equivalentSpecialized alignment existing replacement ->
                    Just alignment
                | otherwise -> Nothing
              Nothing ->
                Just
                  alignment
                    { kcaLocalRefinements =
                        kcaLocalRefinements alignment ++ [(ref, replacement)]
                    }
      _ -> Nothing

    recordPropositionalEquation alignment lhs rhs
      | not allowPropositional = Nothing
      | otherwise =
          Just
            alignment
              { kcaPropositionalEquations =
                  kcaPropositionalEquations alignment ++ [(lhs, rhs)]
              }

    nominalApplication term =
      case collectApplication term of
        (KTGlobal ref levels, arguments) -> Just (ref, levels, arguments)
        _ -> Nothing

    collectApplication = goApplication []
      where
        goApplication arguments (KTApply function more) =
          goApplication (more ++ arguments) function
        goApplication arguments headTerm = (headTerm, arguments)

    applyRefinements refinements term =
      foldl
        (\current (ref, replacement) -> substituteLocal ref replacement current)
        term
        refinements

-- | Authenticate a serialized propositional constructor bridge against the
-- exact unresolved equation produced by independent nominal-result
-- alignment. The bridge is ordinary standard equality evidence; its proof and
-- carrier are checked separately by 'verifyConstructorBridge'. Matching the
-- endpoints here prevents a valid but unrelated erased proof from admitting a
-- constructor branch.
constructorBridgeMatchesEquation
  :: VerifyContext
  -> LocalEnv
  -> (KTerm, KTerm)
  -> KConstructorBridge
  -> Bool
constructorBridgeMatchesEquation context env (expectedLeft, expectedRight) bridge =
  constructorBridgeMatchesEquationWith
    (sameKCoreTypeIn env context)
    (expectedLeft, expectedRight)
    bridge

constructorBridgeMatchesEquationWith
  :: (KTerm -> KTerm -> Bool)
  -> (KTerm, KTerm)
  -> KConstructorBridge
  -> Bool
constructorBridgeMatchesEquationWith sameTerm (expectedLeft, expectedRight) bridge =
  case equalityEndpoints (kbType (kcbBinder bridge)) of
    Just (actualLeft, actualRight) ->
      sameTerm expectedLeft actualLeft
        && sameTerm expectedRight actualRight
    Nothing -> False
  where
    equalityEndpoints term =
      case collectApplication (stripClassifierLifts term) of
        (KTGlobal equalityRef _, arguments)
          | equalityRef == stableRefForGlobal prelEqType
          , [KArgument KImplicit _, KArgument KExplicit left, KArgument KExplicit right] <- arguments ->
              Just (left, right)
        _ -> Nothing

    collectApplication = goApplication []
      where
        goApplication arguments (KTApply function more) =
          goApplication (more ++ arguments) function
        goApplication arguments headTerm = (headTerm, arguments)

-- | Build the branch telescope after constructor-result alignment. Family
-- parameters determined by the scrutinee are substituted away. Parameters
-- absent from the constructor result remain genuine implicit quantity-0
-- constructor existentials and precede the source payload, matching the source
-- checker's skolem telescope. Their domains and observation/formation modes
-- come from the authenticated family telescope; only the constructor-parameter
-- quantity and icity differ from the family's explicit application telescope.
-- Keeping them here is required even when no runtime field mentions them:
-- later dependent payload types and bridge proofs may still refer to their
-- lexical identities.
constructorEliminationPayload
  :: [KBinder]
  -> [KBinder]
  -> KConstructorAlignment
  -> [KBinder]
constructorEliminationPayload parameters payload alignment =
  fst
    ( splitPiTelescope
        ( substituteKTermParameters
            parameters
            substitution
            (foldr KTPi (KTType (KLFinite 0)) (undetermined ++ payload))
        )
    )
  where
    substitution = kcaParameterSubstitution alignment
    undetermined =
      [ binder
          { kbQuantity = KQ0
          , kbExplicitness = KImplicit
          , kbAccess = KValue
          }
      | binder <- parameters
      , Map.notMember (lrId (kbRef binder)) substitution
      ]

-- | Independently validate and install constructor-forced local equations.
-- The target must already be a local binder in the branch environment, the
-- replacement must check at that binder's type, and schema-bearing local
-- definitions are never rewritten. Alignment has already performed the
-- occurs check; replay repeats the typing boundary before conversion may use
-- the equation.
installKConstructorRefinements
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> [(LocalRef, KTerm)]
  -> Either KCoreTextError LocalEnv
installKConstructorRefinements context universes assumptions =
  foldM install
  where
    install env (ref, replacement) =
      case Map.lookup (lrId ref) env of
        Just (LocalBinder binder) -> do
          checkTermObserved
            (kbMode binder)
            context
            universes
            assumptions
            env
            replacement
            (kbType binder)
          pure
            ( Map.insert
                (lrId ref)
                ( LocalDefinition
                    (kbMode binder)
                    []
                    (kbType binder)
                    replacement
                )
                env
            )
        Just (LocalDefinition mode [] ty prior)
          | sameKCoreTypeIn env context prior replacement ->
              pure
                ( Map.insert
                    (lrId ref)
                    (LocalDefinition mode [] ty prior)
                    env
                )
        Just (LocalDefinition _ _ _ _) ->
          Left
            ( invalid
                "constructor refinement cannot rewrite a schema-bearing local definition"
            )
        Nothing ->
          Left
            ( invalid
                "constructor refinement targets a local outside the branch environment"
            )

matchConstructorResult
  :: Assumptions
  -> LocalEnv
  -> VerifyContext
  -> [KBinder]
  -> Map Int KTerm
  -> KTerm
  -> KTerm
  -> Maybe (Map Int KTerm)
matchConstructorResult assumptions env context parameters initial patternTerm actualTerm =
  kcaParameterSubstitution
    <$> alignKConstructorResult
      False
      False
      (`Map.member` vcNominalFamilies context)
      (const False)
      (sameKCoreTypeUnderIn assumptions env context)
      parameters
      initial
      patternTerm
      actualTerm

inferSimple :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KTerm -> Either KCoreTextError (Maybe KTerm)
inferSimple context universes assumptions env =
  inferSimpleScoped context universes (localEvidenceAssumptions assumptions env) env

inferSimpleScoped :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KTerm -> Either KCoreTextError (Maybe KTerm)
inferSimpleScoped context universes assumptions env = \case
  KTLocal ref levels -> pure $ do
    entry <- Map.lookup (lrId ref) env
    case entry of
      LocalBinder binder
        | null levels -> Just (kbType binder)
        | otherwise -> Nothing
      LocalDefinition _ parameters ty _
        | length parameters == length levels ->
            Just (substituteUniverseParameters (Map.fromList (zip (map urId parameters) levels)) ty)
        | otherwise -> Nothing
  KTGlobal ref levels ->
    case Map.lookup ref (vcGlobalTypes context) of
      Nothing ->
        Left
          ( invalid
              ( "KCore global signature is unavailable for "
                  <> renderStable ref
              )
          )
      Just (parameters, ty)
        | length parameters == length levels ->
            pure
              ( Just
                  ( substituteUniverseParameters
                      (Map.fromList (zip (map urId parameters) levels))
                      ty
                  )
              )
        | otherwise ->
            Left
              ( invalid
                  ( "KCore global universe arity mismatch for "
                      <> renderStable ref
                      <> ": expected "
                      <> T.pack (show (length parameters))
                      <> ", got "
                      <> T.pack (show (length levels))
                  )
              )
  KTType level -> pure (Just (KTType (KLSucc level)))
  KTPi binder codomain -> inferFormer binder codomain
  KTSigma binder codomain -> inferFormer binder codomain
  KTLambda binder body -> do
    env' <- verifyAndBind context universes assumptions env binder
    fmap (KTPi binder) <$> inferSimple context universes assumptions env' body
  KTApply fun arguments -> do
    initial <- inferSimple context universes assumptions env fun
    case applyArguments initial arguments of
      Left err ->
        Left
          err
            { kcteMessage =
                kcteMessage err
                  <> "\nwhile inferring application "
                  <> printTerm fun
                  <> " to "
                  <> T.pack (show arguments)
            }
      Right result -> Right result
  KTBlock items result -> do
    env' <- foldM bindItem env items
    inferSimple context universes assumptions env' result
  KTLetRec definitions result ->
    let envRec =
          foldl
            (\acc KLocalDef {..} -> Map.insert (lrId kldRef) (LocalDefinition kldMode kldUniverses kldType kldBody) acc)
            env
            definitions
     in inferSimple context universes assumptions envRec result
  KTCase _ resultType _ -> pure (Just resultType)
  KTConstruct ref levels arguments -> do
    case Map.lookup ref (vcConstructorTypes context) of
      Just (_, parameters, _)
        | not (null parameters) ->
            -- Family parameters are intentionally omitted from KCore
            -- constructor occurrences and recovered bidirectionally from the
            -- demanded result in 'checkConstructor'. Without that expected
            -- result, a parameterized constructor has no principal type.
            pure Nothing
      _ -> do
        initial <- inferSimple context universes assumptions env (KTGlobal ref levels)
        case applyArguments initial arguments of
          Left err ->
            Left
              err
                { kcteMessage =
                    kcteMessage err
                      <> "\nwhile inferring constructor "
                      <> renderStable ref
                      <> " with arguments "
                      <> tshow arguments
                }
          Right result -> Right result
  projected@(KTProject field record) -> do
    recordType <- inferSimple context universes assumptions env record
    case
        recordType >>= \ty ->
          projectRecordField field record (recordInterfaceHead context ty)
            <|> projectNominalField context field record ty of
      Just projectedType -> pure (Just projectedType)
      Nothing ->
        let normalized = unfoldTypeHeadWithLocals context env projected
         in if normalized /= projected
              then inferSimple context universes assumptions env normalized
              else pure Nothing
  KTAscribe _ ty -> pure (Just ty)
  KTLift _ to _ _ -> pure (Just (KTType to))
  KTSchemaLift family _ to _ _ targetArguments _ ->
    pure . Just $
      if null targetArguments then KTGlobal family to else KTApply (KTGlobal family to) targetArguments
  KTLiteral literal -> pure (Just (literalKType literal))
  KTRecordType fields -> inferRecordType (map snd fields)
  KTRecordValue _ -> pure Nothing
  KTIf condition thenBranch elseBranch -> do
    checkBooleanTerm context universes assumptions env condition
    thenType <-
      inferSimple
        (withArithmeticBranchFact True condition context)
        universes
        assumptions
        env
        thenBranch
    elseType <-
      inferSimple
        (withArithmeticBranchFact False condition context)
        universes
        assumptions
        env
        elseBranch
    pure $ case (thenType, elseType) of
      (Just lhs, Just rhs) | sameKCoreTypeIn env context lhs rhs -> Just lhs
      _ -> Nothing
  KTGeneric tag fields
    | tag `Set.member` decodedBuiltinTermTags -> do
        decoded <- either (Left . invalid) pure (decodeBuiltinTermNode tag fields)
        inferSimple context universes assumptions env decoded
  KTGeneric "impl.kappa.level-value" _ ->
    pure (Just (KTGlobal typeLevelStableRef []))
  KTGeneric "impl.kappa.core.signature-type" fields ->
    case lookup "value" fields of
      Just (KVTerm value) -> inferSimple context universes assumptions env value
      _ -> pure Nothing
  KTGeneric "impl.kappa.core.variant-type" fields ->
    case lookup "members" fields of
      Just (KVList members) -> do
        classifiers <- forM members $ \case
          KVTerm member -> inferSimple context universes assumptions env member
          _ -> pure Nothing
        pure $ do
          levels <- mapM (\case Just (KTType level) -> Just level; _ -> Nothing) classifiers
          Just (KTType (foldr KLMax (KLFinite 0) levels))
      _ -> pure Nothing
  KTGeneric tag fields -> pure (genericResultType tag fields)
  where
    inferFormer binder codomain = do
      domainSort <- inferSimple context universes assumptions env (kbType binder)
      env' <- verifyAndBind context universes assumptions env binder
      codomainSort <- inferSimple context universes assumptions env' codomain
      pure $ case (domainSort, codomainSort) of
        (Just (KTType lhs), Just (KTType rhs)) ->
          Just (KTType (if kbFormation binder == FormationParametric then rhs else KLMax lhs rhs))
        _ -> Nothing
    inferRecordType = goRecord env (KLFinite 0)
      where
        goRecord _ level [] = pure (Just (KTType level))
        goRecord envHere level (binder : rest) = do
          classifier <- inferSimple context universes assumptions envHere (kbType binder)
          envNext <- verifyAndBind context universes assumptions envHere binder
          case classifier of
            Just (KTType fieldLevel) ->
              goRecord
                envNext
                (if kbFormation binder == FormationParametric then level else KLMax level fieldLevel)
                rest
            _ -> pure Nothing
    applyArguments initial arguments =
      foldM
        applyArgument
        (fmap (freshenKPiTelescopeForArguments arguments) initial)
        arguments
    applyArgument Nothing _ = pure Nothing
    applyArgument (Just functionType) (KArgument explicitness argument) = case unfoldTypeHeadWithLocals context env functionType of
      KTPi binder codomain -> do
        unless (explicitness == kbExplicitness binder) $
          Left
            ( invalid
                ( "application explicitness "
                    <> tshow explicitness
                    <> " does not match the next Pi binder "
                    <> printBinder binder
                    <> " in "
                    <> printTerm (unfoldTypeHeadWithLocals context env functionType)
                )
            )
        checkTermObserved (kbMode binder) context universes assumptions env argument (kbType binder)
        pure (Just (substituteLocal (kbRef binder) argument codomain))
      _ -> Left (invalid "KCore application has a non-function head")
    bindItem envHere = \case
      KBLet binder rhs -> do
        checkTermObserved (kbMode binder) context universes assumptions envHere rhs (kbType binder)
        verifyAndBindDefinition context universes assumptions envHere binder rhs

projectRecordField :: StableRef -> KTerm -> KTerm -> Maybe KTerm
projectRecordField field record recordType =
  case freshenKTermBindersAgainst (kTermLocalIds record) recordType of
    KTRecordType fields -> go [] fields
    _ -> Nothing
  where
    go _ [] = Nothing
    go substitutions ((fieldRef, binder) : rest)
      | fieldRef == field =
          Just
            ( substituteGlobalTerm
                (stableRefForGlobal prelThis)
                record
                ( foldl
                    (\ty (ref, replacement) -> substituteLocal ref replacement ty)
                    (kbType binder)
                    substitutions
                )
            )
      | otherwise =
          let projected = KTProject fieldRef record
           in go (substitutions ++ [(kbRef binder, projected)]) rest

-- A trait dictionary is an opaque nominal family at use sites, so its
-- projections cannot rely on delta reduction.  The KCore data declaration
-- carries one checked structural dictionary constructor instead.  Recover the
-- field telescope from that constructor only after proving that its result is
-- the fully saturated scrutinee family instance.
projectNominalField :: VerifyContext -> StableRef -> KTerm -> KTerm -> Maybe KTerm
projectNominalField context field record recordType =
  kbType <$> nominalFieldBinder context field record recordType

nominalFieldBinder :: VerifyContext -> StableRef -> KTerm -> KTerm -> Maybe KBinder
nominalFieldBinder context field record recordType = do
  let receiverType = stripClassifierLifts (unfoldTypeHead context recordType)
  (familyRef, levels, arguments) <- nominalApplication receiverType
  family <- Map.lookup familyRef (vcNominalFamilies context)
  let universeParameters = map fst (knfUniverses family)
      parameters0 = knfBinders family
  guard (length levels == length universeParameters)
  guard (length arguments == length parameters0)
  parameterSubstitution <- matchParameters parameters0 arguments
  KCtorDecl _ constructorUniverses fields constructorType0 <-
    case knfConstructors family of
      [constructor] -> Just constructor
      _ -> Nothing
  -- A genuinely constructor-local universe schema cannot be reconstructed
  -- from a projection. Ordinary data constructors repeat their family's
  -- declaration telescope, however, and that instantiation is determined
  -- exactly by the receiver's nominal application.
  guard (null constructorUniverses || constructorUniverses == universeParameters)
  targetIndex <- lookup field fields
  let universeSubstitution = Map.fromList (zip (map urId universeParameters) levels)
      constructorUniverseSubstitution =
        Map.fromList (zip (map urId constructorUniverses) levels)
      constructorType =
        substituteUniverseParameters
          constructorUniverseSubstitution
          (substituteUniverseParameters universeSubstitution constructorType0)
      substituteParameters = substituteKTermParameters parameters0 parameterSubstitution
      (payload0, constructorResult0) = splitPiTelescope constructorType
      payload =
        [ binder {kbType = substituteParameters (kbType binder)}
        | binder <- payload0
        ]
      constructorResult = substituteParameters constructorResult0
  guard (sameKCoreType context constructorResult receiverType)
  projectPayload targetIndex (Map.fromList [(index, fieldRef) | (fieldRef, index) <- fields]) 0 [] payload
  where
    nominalApplication = go []
      where
        go arguments (KTApply function more) = go (more ++ arguments) function
        go arguments (KTGlobal ref levels) = Just (ref, levels, arguments)
        go _ _ = Nothing

    matchParameters parameters arguments =
      fmap Map.fromList . forM (zip parameters arguments) $ \(parameter, KArgument explicitness argument) -> do
        guard (kbExplicitness parameter == explicitness)
        pure (lrId (kbRef parameter), argument)

    projectPayload _ _ _ _ [] = Nothing
    projectPayload targetIndex fieldByIndex index substitutions (binder : rest)
      | index == targetIndex =
          Just
            binder
              { kbType =
                  substituteGlobalTerm
                    (stableRefForGlobal prelThis)
                    record
                    (applySubstitutions substitutions (kbType binder))
              }
      | otherwise =
          case Map.lookup index fieldByIndex of
            Nothing -> Nothing
            Just priorField ->
              projectPayload targetIndex fieldByIndex (index + 1)
                (substitutions ++ [(kbRef binder, KTProject priorField record)]) rest

    applySubstitutions substitutions ty =
      foldl
        (\body (ref, replacement) -> substituteLocal ref replacement body)
        ty
        substitutions

sameBinderContractUnderIn
  :: Assumptions
  -> LocalEnv
  -> VerifyContext
  -> KBinder
  -> KBinder
  -> Bool
sameBinderContractUnderIn assumptions env context =
  sameBinderContractWith
    (sameKCoreTypeUnderIn assumptions env context)

sameBinderContractWith
  :: (KTerm -> KTerm -> Bool)
  -> KBinder
  -> KBinder
  -> Bool
sameBinderContractWith sameType a b =
  kbMode a == kbMode b
    && kbFormation a == kbFormation b
    && kbQuantity a == kbQuantity b
    && kbExplicitness a == kbExplicitness b
    && kbAccess a == kbAccess b
    && kbOrigin a == kbOrigin b
    -- A dependent binder scopes over the following telescope/body, never over
    -- its own domain. Renaming its presentation identity inside the domain can
    -- capture an unrelated outer local with the same independently
    -- canonicalized numeric ID.
    && sameType (kbType a) (kbType b)

sameKCoreType :: VerifyContext -> KTerm -> KTerm -> Bool
sameKCoreType context =
  sameKCoreTypeWith emptyAssumptions sameKLevel context Map.empty

sameKCoreTypeIn :: LocalEnv -> VerifyContext -> KTerm -> KTerm -> Bool
sameKCoreTypeIn env context =
  sameKCoreTypeWith emptyAssumptions sameKLevel context env

sameKCoreTypeUnderIn
  :: Assumptions
  -> LocalEnv
  -> VerifyContext
  -> KTerm
  -> KTerm
  -> Bool
sameKCoreTypeUnderIn assumptions env context =
  sameKCoreTypeWith assumptions sameLevelUnder context env
  where
    sameLevelUnder lhs rhs = case (toLevel lhs, toLevel rhs) of
      (Just lhs', Just rhs') ->
        proveLevelLeq assumptions lhs' rhs' == Proved
          && proveLevelLeq assumptions rhs' lhs' == Proved
      _ -> lhs == rhs

sameKCoreTypeWith
  :: Assumptions
  -> (KLevel -> KLevel -> Bool)
  -> VerifyContext
  -> LocalEnv
  -> KTerm
  -> KTerm
  -> Bool
sameKCoreTypeWith assumptions sameLevel context env lhs0 rhs0 =
  same lhs0 rhs0
  where
    -- Try congruence before delta-unfolding. Besides avoiding needless
    -- expansion of matching applications, this preserves canonical
    -- representation equivalences in their arguments (notably logical Nat
    -- constructors versus compact Nat literals) instead of burying them
    -- inside the neutral case tree of a recursive definition.
    same lhs rhs =
      surfaceCongruent lhs rhs
        || contextualBooleanCongruent lhs rhs
        || contextualArithmeticCongruent lhs rhs
        || alphaCongruent lhs rhs
        || go
          (unfoldTypeHeadWithLocals context env lhs)
          (unfoldTypeHeadWithLocals context env rhs)
    alphaCongruent lhs rhs =
      canonicalizeScoped lhs == canonicalizeScoped rhs
    canonicalizeScoped term =
      evalState
        (canonicalTerm Map.empty term)
        (CanonState nextLocal canonicalFreeLocals)
    canonicalFreeLocals =
      Map.mapWithKey
        (\identity _ -> LocalRef "__free" identity)
        env
    nextLocal =
      maybe 0 ((+ 1) . fst) (Map.lookupMax canonicalFreeLocals)
    contextualBooleanCongruent lhs rhs =
      case (contextualBooleanValue lhs, contextualBooleanValue rhs) of
        (Just lhsValue, Just rhsValue) -> lhsValue == rhsValue
        _ -> False
    -- A checked true branch on exact integer equality refines its logical
    -- operands. This is ordinary contextual conversion, not a property of
    -- @refl@: any indexed constructor may rely on the same branch equation.
    -- Compare endpoints with branch facts disabled so the evidence cannot
    -- authenticate itself circularly.
    contextualArithmeticCongruent lhs rhs =
      any
        (\(truth, condition) ->
           truth
             && maybe
               False
               (\(left, right) ->
                  (sameWithoutBranchFacts lhs left && sameWithoutBranchFacts rhs right)
                    || (sameWithoutBranchFacts lhs right && sameWithoutBranchFacts rhs left))
               (checkedIntegerEqualityOperands condition))
        ( concatMap
            (uncurry (branchFactConsequences 16))
            (vcArithmeticBranchFacts context)
        )
    sameWithoutBranchFacts =
      sameKCoreTypeWith
        assumptions
        sameLevel
        (context {vcArithmeticBranchFacts = []})
        env
    checkedIntegerEqualityOperands condition = do
      let normalized =
            unfoldTypeHeadWithLocals
              (context {vcArithmeticBranchFacts = []})
              env
              (stripArithmeticTermWrappers condition)
          (headTerm, arguments) = collectKApplication normalized
          explicit =
            [ argument
            | KArgument KExplicit argument <- arguments
            ]
      operation <- kTermHeadGlobal headTerm
      guard (trustedIntPrimitiveRef "eqInt" operation)
      (left, right) <- lastTwo explicit
      normalizeLogicalOperands left right
    normalizeLogicalOperands left right =
      case
          ( trustedUnaryIntPrimitivePayload "natToInt" left
          , trustedUnaryIntPrimitivePayload "natToInt" right
          )
        of
          (Just lhs, Just rhs) -> Just (lhs, rhs)
          (Just lhs, Nothing)
            | integerLiteralKTermValue right >= Just 0 ->
                Just (lhs, right)
          (Nothing, Just rhs)
            | integerLiteralKTermValue left >= Just 0 ->
                Just (left, rhs)
          (Nothing, Nothing) -> Just (left, right)
          _ -> Nothing
    contextualBooleanValue term =
      let normalized = unfoldTypeHeadWithLocals context env term
       in booleanConstructorValueHere normalized
            <|> contextualBranchValueHere term
            <|> contextualBranchValueHere normalized
            <|> levelConstraintBooleanValue term
    booleanConstructorValueHere = \case
      KTConstruct constructor _ []
        | constructor == stableRefForConstructor prelTrue -> Just True
        | constructor == stableRefForConstructor prelFalse -> Just False
      _ -> Nothing
    contextualBranchValueHere condition
      | branchFactAvailable context env True condition = Just True
      | branchFactAvailable context env False condition = Just False
      | otherwise = Nothing
    levelConstraintBooleanValue relation = do
      boolean <-
        authenticatedTypeLevelBoolean
          context
          assumptions
          env
          relation
      case boolean of
        TypeLevelBooleanLiteral truth -> pure truth
        TypeLevelBooleanConstraint lower upper ->
          case
              proveLevelLeq
                (localEvidenceAssumptions assumptions env)
                lower
                upper
            of
              Proved -> Just True
              Disproved -> Just False
              _ -> Nothing
    surfaceCongruent lhs rhs =
      case (projectionEliminator lhs, projectionEliminator rhs) of
        (Just lhsProjection, Just rhsProjection) ->
          sameProjectionEliminator lhsProjection rhsProjection
        _ -> case (lhs, rhs) of
          (KTApply lhsFunction lhsArguments, KTApply rhsFunction rhsArguments) ->
            length lhsArguments == length rhsArguments
              && same lhsFunction rhsFunction
              && and (zipWith sameArgument lhsArguments rhsArguments)
          _ ->
            case (termAsLevel lhs, termAsLevel rhs) of
              (Just lhsLevel, Just rhsLevel) -> sameLevel lhsLevel rhsLevel
              _ ->
                case (logicalNaturalValue lhs, logicalNaturalValue rhs) of
                  (Just lhsNatural, Just rhsNatural) -> lhsNatural == rhsNatural
                  _ -> False
    -- Re-elaboration may attach differently normalized erased annotations to
    -- the same nominal projection. In the verified one-alternative form, the
    -- eliminator's computation is completely determined by the selected
    -- payload position; annotation syntax is not computational evidence.
    projectionEliminator = \case
      KTCase scrutinee resultType
        [KCaseConstructor constructor levels bindings (KTLocal selected [])] -> do
          payloadIndex <-
            findIndexBy
              ((== selected) . kbRef)
              (casePayloadBinders bindings)
          pure
            (scrutinee, resultType, constructor, levels, payloadIndex)
      _ -> Nothing
    sameProjectionEliminator
      (lhsScrutinee, lhsResult, lhsConstructor, lhsLevels, lhsIndex)
      (rhsScrutinee, rhsResult, rhsConstructor, rhsLevels, rhsIndex) =
        lhsConstructor == rhsConstructor
          && lhsIndex == rhsIndex
          && length lhsLevels == length rhsLevels
          && and (zipWith sameLevel lhsLevels rhsLevels)
          && same lhsScrutinee rhsScrutinee
          && same lhsResult rhsResult
    findIndexBy predicate = goIndex 0
      where
        goIndex _ [] = Nothing
        goIndex index (value : rest)
          | predicate value = Just index
          | otherwise = goIndex (index + 1) rest
    go (KTType lhs) (KTType rhs) = sameLevel lhs rhs
    go (KTGlobal lhs levelsL) (KTGlobal rhs levelsR) =
      lhs == rhs
        && length levelsL == length levelsR
        && and (zipWith sameLevel levelsL levelsR)
    go (KTLocal lhs levelsL) (KTLocal rhs levelsR) =
      lhs == rhs
        && length levelsL == length levelsR
        && and (zipWith sameLevel levelsL levelsR)
    -- Logical Nat constructors and their exact compact literal form denote
    -- one canonical value language (§28.2/NFR-1). KCore replay must recognize
    -- that representation identity independently; otherwise a checked proof
    -- over Nat.Zero cannot transport an index written with literal 0.
    go lhs rhs
      | Just lhsNatural <- logicalNaturalValue lhs
      , Just rhsNatural <- logicalNaturalValue rhs =
          lhsNatural == rhsNatural
    -- Classifier lifts are proof-irrelevant type-code coercions. Their
    -- evidence is verified at the term boundary, but the lifted code denotes
    -- the same type for conversion and binder identity (§30.2.1A).
    go (KTLift _ _ _ value) rhs = same value rhs
    go lhs (KTLift _ _ _ value) = same lhs value
    go (KTPi lhsBinder lhsBody) (KTPi rhsBinder rhsBody) =
      sameBinder lhsBinder rhsBinder
        && sameBinderBodies lhsBinder lhsBody rhsBinder rhsBody
    go (KTSigma lhsBinder lhsBody) (KTSigma rhsBinder rhsBody) =
      sameBinder lhsBinder rhsBinder
        && sameBinderBodies lhsBinder lhsBody rhsBinder rhsBody
    go (KTLambda lhsBinder lhsBody) (KTLambda rhsBinder rhsBody) =
      sameBinder lhsBinder rhsBinder
        && sameBinderBodies lhsBinder lhsBody rhsBinder rhsBody
    go
      (KTCase lhsScrutinee lhsResult lhsAlternatives)
      (KTCase rhsScrutinee rhsResult rhsAlternatives) =
        same lhsScrutinee rhsScrutinee
          && same lhsResult rhsResult
          && length lhsAlternatives == length rhsAlternatives
          && and (zipWith sameCaseAlternative lhsAlternatives rhsAlternatives)
    go lhs@KTApply {} rhs@KTApply {} =
      let (lhsFunction, lhsArguments) = collectApplication lhs
          (rhsFunction, rhsArguments) = collectApplication rhs
       in length lhsArguments == length rhsArguments
            && same lhsFunction rhsFunction
            && and (zipWith sameArgument lhsArguments rhsArguments)
    go (KTConstruct lhsConstructor lhsLevels lhsArguments) (KTConstruct rhsConstructor rhsLevels rhsArguments) =
      lhsConstructor == rhsConstructor
        && length lhsLevels == length rhsLevels
        && and (zipWith sameLevel lhsLevels rhsLevels)
        && length lhsArguments == length rhsArguments
        && and (zipWith sameArgument lhsArguments rhsArguments)
    -- A neutral conditional is definitionally congruent in all three
    -- components. Calling 'same' recursively is important: a branch may
    -- itself become reducible after dictionary projection, case reduction,
    -- or a known Boolean condition even when the outer condition is neutral.
    go (KTIf lhsCondition lhsThen lhsElse) (KTIf rhsCondition rhsThen rhsElse) =
      same lhsCondition rhsCondition
        && same lhsThen rhsThen
        && same lhsElse rhsElse
    go (KTRecordType lhsFields) (KTRecordType rhsFields) = sameFields lhsFields rhsFields
    go lhs rhs = lhs == rhs
    sameArgument (KArgument lhsExplicitness lhsTerm) (KArgument rhsExplicitness rhsTerm) =
      lhsExplicitness == rhsExplicitness
        && same lhsTerm rhsTerm
    sameBinder = sameBinderContractWith same
    sameBinderBodies lhsBinder lhsBody rhsBinder rhsBody =
      let fresh = freshAlphaRef [lhsBody, rhsBody]
       in same
            (renameLocal (kbRef lhsBinder) fresh lhsBody)
            (renameLocal (kbRef rhsBinder) fresh rhsBody)
    sameCaseAlternative (KCaseDefault lhsBody) (KCaseDefault rhsBody) =
      same lhsBody rhsBody
    sameCaseAlternative
      (KCaseConstructor lhsRef lhsLevels lhsBindings lhsBody)
      (KCaseConstructor rhsRef rhsLevels rhsBindings rhsBody) =
        lhsRef == rhsRef
          && length lhsLevels == length rhsLevels
          && and (zipWith sameLevel lhsLevels rhsLevels)
          && sameCaseBindings lhsBindings lhsBody rhsBindings rhsBody
    sameCaseAlternative lhs@(KCasePattern {}) rhs@(KCasePattern {}) =
      canonicalizeCaseAlternative lhs == canonicalizeCaseAlternative rhs
    sameCaseAlternative _ _ = False
    sameCaseBindings [] lhsBody [] rhsBody = same lhsBody rhsBody
    sameCaseBindings
      (lhsBinding : lhsRest)
      lhsBody
      (rhsBinding : rhsRest)
      rhsBody
      | sameCaseBinding lhsBinding rhsBinding =
          let lhsBinder = caseBindingBinder lhsBinding
              rhsBinder = caseBindingBinder rhsBinding
              fresh =
                freshAlphaRef
                  ( lhsBody
                      : rhsBody
                      : concatMap caseBindingTerms (lhsRest ++ rhsRest)
                  )
           in sameCaseBindings
                (map (renameCaseBindingReferences (kbRef lhsBinder) fresh) lhsRest)
                (renameLocal (kbRef lhsBinder) fresh lhsBody)
                (map (renameCaseBindingReferences (kbRef rhsBinder) fresh) rhsRest)
                (renameLocal (kbRef rhsBinder) fresh rhsBody)
    sameCaseBindings _ _ _ _ = False
    sameCaseBinding (KCasePayload lhsBinder) (KCasePayload rhsBinder) =
      sameBinder lhsBinder rhsBinder
    sameCaseBinding (KCaseBridge lhsBridge) (KCaseBridge rhsBridge) =
      sameBinder (kcbBinder lhsBridge) (kcbBinder rhsBridge)
        && same (kcbProof lhsBridge) (kcbProof rhsBridge)
    sameCaseBinding _ _ = False
    caseBindingTerms binding =
      kbType (caseBindingBinder binding)
        : case binding of
            KCasePayload _ -> []
            KCaseBridge bridge -> [kcbProof bridge]
    renameCaseBindingReferences old new =
      mapKCaseBinding
        (renameBinderReferences old new)
        (renameLocal old new)
    renameBinderReferences old new binder =
      binder
        { kbType = renameLocal old new (kbType binder)
        , kbAccess = renameAccessReference old new (kbAccess binder)
        }
    renameAccessReference old new = \case
      KBorrow (Just (KRLocal ref))
        | ref == old -> KBorrow (Just (KRLocal new))
      access -> access
    canonicalizeCaseAlternative alternative =
      case
          evalState
            (canonicalTerm Map.empty (KTCase canonicalUnit canonicalUnit [alternative]))
            (CanonState nextLocal canonicalFreeLocals)
        of
          KTCase _ _ [canonical] -> canonical
          _ -> alternative
    canonicalUnit = KTGlobal (stableRefForGlobal prelUnit) []
    collectApplication = goApplication []
      where
        goApplication arguments (KTApply function more) = goApplication (more ++ arguments) function
        goApplication arguments headTerm = (headTerm, arguments)
    sameFields [] [] = True
    sameFields ((lhsField, lhs) : lhsRest) ((rhsField, rhs) : rhsRest) =
      lhsField == rhsField
        && sameBinderContractWith same lhs rhs
        && let fresh =
                 freshAlphaRef
                   ( map (kbType . snd) lhsRest
                       ++ map (kbType . snd) rhsRest
                   )
            in sameFields
                 [ (field, renameBinderLocal (kbRef lhs) fresh binder)
                 | (field, binder) <- lhsRest
                 ]
                 [ (field, renameBinderLocal (kbRef rhs) fresh binder)
                 | (field, binder) <- rhsRest
                 ]
    sameFields _ _ = False
    freshAlphaRef terms =
      let used =
            Map.keysSet env
              `Set.union` Set.unions (map kTermLocalIds terms)
          identity =
            if Set.null used
              then 0
              else Set.findMax used + 1
       in LocalRef "__alpha" identity
    logicalNaturalValue = logicalNaturalKTermValue

renameBinderLocal :: LocalRef -> LocalRef -> KBinder -> KBinder
renameBinderLocal old new binder = binder {kbType = renameLocal old new (kbType binder)}

unfoldTypeHead :: VerifyContext -> KTerm -> KTerm
unfoldTypeHead context = unfoldTypeHeadWithLocals context Map.empty

unfoldTypeHeadWithLocals :: VerifyContext -> LocalEnv -> KTerm -> KTerm
unfoldTypeHeadWithLocals context env = go (Set.empty, Set.empty)
  where
    go (seenGlobals, seenLocals) term@(KTLocal ref levels)
      | lrId ref `Set.member` seenLocals = term
      | Just (LocalDefinition _ parameters _ body) <- Map.lookup (lrId ref) env
      , length parameters == length levels =
          go
            (seenGlobals, Set.insert (lrId ref) seenLocals)
            (substituteUniverseParameters (Map.fromList (zip (map urId parameters) levels)) body)
    go (seenGlobals, seenLocals) term@(KTGlobal ref levels)
      | ref `Set.member` seenGlobals = term
      | Just (parameters, body) <- Map.lookup ref (vcGlobalBodies context)
      , length parameters == length levels =
          go
            (Set.insert ref seenGlobals, seenLocals)
            (substituteUniverseParameters (Map.fromList (zip (map urId parameters) levels)) body)
    go seen (KTApply function arguments)
      | Just reduced <- reduceKCorePrimitiveApplication function arguments =
          go seen reduced
      | otherwise =
          let arguments' =
                [ KArgument explicitness (go seen argument)
                | KArgument explicitness argument <- arguments
                ]
           in case reduceKCorePrimitiveApplication function arguments' of
                Just reduced -> go seen reduced
                Nothing ->
                  let function' = go seen function
                   in case reduceKCorePrimitiveApplication function' arguments' of
                        Just reduced -> go seen reduced
                        Nothing -> apply seen function' arguments'
    go seen (KTProject field receiver) =
      case reduceAssociatedNormalization field receiver of
        Just value -> go seen value
        Nothing ->
          let receiver' = go seen receiver
           in case reduceKTermProjection context field receiver' of
                Just value -> go seen value
                Nothing -> KTProject field receiver'
    go seen (KTIf condition thenBranch elseBranch) =
      let condition' = go seen condition
          knownBranch =
            kBooleanConstructorValue condition'
              <|> contextualBranchValue condition'
       in case knownBranch of
            Just True -> go seen thenBranch
            Just False -> go seen elseBranch
            Nothing -> KTIf condition' thenBranch elseBranch
    go seen (KTCase scrutinee resultType alternatives) =
      let scrutinee' = go seen scrutinee
       in case scrutinee' of
            KTIf condition thenBranch elseBranch ->
              go
                seen
                ( KTIf
                    condition
                    (KTCase thenBranch resultType alternatives)
                    (KTCase elseBranch resultType alternatives)
                )
            _ -> case reduceKnownKCase scrutinee' alternatives of
              Just body -> go seen body
              Nothing -> KTCase scrutinee' resultType alternatives
    go seen (KTBlock items result) = reduceBlock seen items result
    go seen (KTAscribe value _) = go seen value
    go seen generic@(KTGeneric tag fields)
      | tag == "impl.kappa.core.force"
      , Just reduced <- reduceImmediateForce fields =
          go seen reduced
      | tag `Set.member` decodedBuiltinTermTags =
          case decodeBuiltinTermNode tag fields of
            Right decoded -> go seen decoded
            Left _ -> generic
    go _ term = term

    -- Reducible aliases are ordinary checked definitions. Their KCore bodies
    -- therefore use the same lambda/application representation as source
    -- functions, and head normalization must beta-reduce an applied alias
    -- before clients compare carriers or expose a Pi/record head.
    apply seen (KTLambda binder body) (argument : rest) =
      apply seen (go seen (substituteLocal (kbRef binder) (argumentTerm argument) body)) rest
    apply seen function arguments
      | Just reduced <- reduceKCorePrimitiveApplication function arguments =
          go seen reduced
    apply _ function [] = function
    apply _ function arguments = KTApply function arguments

    -- Checked block lets are ordinary zeta-redexes. Reducing the residual
    -- block is required for branch-local computation through generated
    -- dictionary/projection scaffolding.
    reduceBlock seen [] result = go seen result
    reduceBlock seen (KBLet binder rhs : rest) result =
      let rhs' = go seen rhs
          substitute = substituteLocal (kbRef binder) rhs'
          rest' =
            [ KBLet
                nextBinder {kbType = substitute (kbType nextBinder)}
                (substitute nextRhs)
            | KBLet nextBinder nextRhs <- rest
            ]
       in reduceBlock seen rest' (substitute result)

    reduceAssociatedNormalization field receiver = do
      (dictionary, levels, arguments) <- dictionaryApplication receiver
      normalization <-
        Map.lookup
          (dictionary, field)
          (vcAssociatedNormalizations context)
      guard (length levels == length (kanUniverses normalization))
      guard (length arguments == length (kanBinders normalization))
      guard
        ( and
            [ explicitness == kbExplicitness binder
            | (KArgument explicitness _, binder) <-
                zip arguments (kanBinders normalization)
            ]
        )
      let universeSubstitution =
            Map.fromList
              (zip (map urId (kanUniverses normalization)) levels)
          specializedTelescope =
            substituteUniverseParameters
              universeSubstitution
              ( foldr
                  KTPi
                  (kanValue normalization)
                  (kanBinders normalization)
              )
          (binders, value) =
            splitPiTelescope
              ( freshenKPiTelescopeForArguments
                  arguments
                  specializedTelescope
              )
      pure
        ( foldl
            (\body (binder, argument) ->
               substituteLocal
                 (kbRef binder)
                 (argumentTerm argument)
                 body)
            value
            (zip binders arguments)
        )

    dictionaryApplication = collect []
      where
        collect arguments (KTApply function more) =
          collect (more ++ arguments) function
        collect arguments (KTGlobal ref levels) =
          Just (ref, levels, arguments)
        collect _ _ = Nothing

    contextualBranchValue condition
      | branchFactAvailable context env True condition = Just True
      | branchFactAvailable context env False condition = Just False
      | otherwise = Nothing

    -- Typed suspension nodes retain their checked result type for replay, but
    -- an immediate force of an immediate thunk/lazy value is still an
    -- ordinary definitional redex. The generic-node schema has already been
    -- verified before conversion asks this normalizer to compare terms.
    reduceImmediateForce fields = do
      KVTerm suspended <- lookup "value" fields
      case stripArithmeticTermWrappers suspended of
        KTGeneric tag suspensionFields
          | tag == "impl.kappa.core.thunk"
              || tag == "impl.kappa.core.lazy" ->
              case lookup "value" suspensionFields of
                Just (KVTerm payload) -> Just payload
                _ -> Nothing
        _ -> Nothing

-- | Projection from an already constructed checked value is ordinary
-- definitional computation. Structural records carry readable field names
-- directly; nominal dictionaries and records use the checked constructor
-- field map from their data declaration. This is intentionally
-- identity-driven: no source/member spelling can authorize a reduction.
reduceKTermProjection
  :: VerifyContext
  -> StableRef
  -> KTerm
  -> Maybe KTerm
reduceKTermProjection context field = \case
  KTRecordValue fields -> lookup (srName field) fields
  KTConstruct constructor _ arguments -> do
    fieldPositions <- Map.lookup constructor (vcConstructorFields context)
    position <- Map.lookup field fieldPositions
    guard (position >= 0)
    argumentTerm <$> listToMaybe (drop position arguments)
  _ -> Nothing

-- | Reduce a checked case whose scrutinee is already a constructor. Constructor
-- identities and the checked payload binders are the only authority; guarded
-- pattern alternatives remain neutral.
reduceKnownKCase :: KTerm -> [KCaseAlt] -> Maybe KTerm
reduceKnownKCase scrutinee = select
  where
    select [] = Nothing
    select (KCaseDefault body : _) = Just body
    select (KCasePattern {} : _) = Nothing
    select (alternative@(KCaseConstructor expected _ bindings _) : rest) =
      case scrutinee of
        KTConstruct actual _ arguments
          | expected /= actual -> select rest
          | length (casePayloadBinders bindings) == length arguments ->
              case freshenCaseAlternativeForArguments arguments alternative of
                KCaseConstructor _ _ freshBindings freshBody ->
                  instantiateBindings freshBody freshBindings arguments
                _ -> Nothing
          | otherwise -> Nothing
        _ -> Nothing

    instantiateBindings result [] [] = Just result
    instantiateBindings result (KCaseBridge bridge : rest) arguments =
      instantiateBindings
        (substituteLocal (kbRef (kcbBinder bridge)) (kcbProof bridge) result)
        rest
        arguments
    instantiateBindings result (KCasePayload binder : rest) (argument : arguments) =
      instantiateBindings
        (substituteLocal (kbRef binder) (argumentTerm argument) result)
        rest
        arguments
    instantiateBindings _ _ _ = Nothing

    -- KCore declarations and use sites are canonicalized independently, so
    -- their presentation-local ids are not globally unique. Freshen the
    -- complete alternative as one scope before substituting payloads.
    freshenCaseAlternativeForArguments arguments alternative =
      case
          freshenKTermBindersAgainst
            ( Set.unions
                [ kTermLocalIds argument
                | KArgument _ argument <- arguments
                ]
            )
            (KTCase canonicalUnit canonicalUnit [alternative])
        of
          KTCase _ _ [freshAlternative] -> freshAlternative
          _ -> alternative
      where
        canonicalUnit = KTGlobal (stableRefForGlobal prelUnit) []

kBooleanConstructorValue :: KTerm -> Maybe Bool
kBooleanConstructorValue = \case
  KTConstruct constructor _ []
    | constructor == stableRefForConstructor prelTrue -> Just True
    | constructor == stableRefForConstructor prelFalse -> Just False
  _ -> Nothing

-- | One independently replayable source-computation step for the primitive
-- vocabulary that can occur in KCore classifiers.
reduceKCorePrimitiveApplication :: KTerm -> [KArgument] -> Maybe KTerm
reduceKCorePrimitiveApplication function arguments =
  reduceExactTypeLevelPrimitiveApplication function arguments
    <|> reduceExactIntegerPrimitiveApplication function arguments
    <|> reduceExactIntegerConversionApplication function arguments
    <|> reduceLogicalNaturalApplication function arguments

-- Closed TypeLevel primitives use the same canonical level algebra as the
-- universe solver. The stable declaration identity and closedness check are
-- both required: neutral/open level terms remain unreduced.
reduceExactTypeLevelPrimitiveApplication
  :: KTerm
  -> [KArgument]
  -> Maybe KTerm
reduceExactTypeLevelPrimitiveApplication function arguments = do
  guard
    ( function
        == KTGlobal (stableRefForGlobal prelCompareTypeLevel) []
    )
  (left, right) <- case arguments of
    [KArgument KExplicit lhs, KArgument KExplicit rhs] -> Just (lhs, rhs)
    _ -> Nothing
  lhs <- typeLevelTerm [] left
  rhs <- typeLevelTerm [] right
  ordering <- compareClosedLevel lhs rhs
  pure
    ( KTConstruct
        (stableRefForConstructor (prelOrdering ordering))
        []
        []
    )

-- Closed integer primitives are part of the independently replayable
-- classifier computation language. This mirrors the evaluator's exact
-- Integer semantics and deliberately leaves partial division/modulo by zero
-- neutral.
reduceExactIntegerPrimitiveApplication
  :: KTerm
  -> [KArgument]
  -> Maybe KTerm
reduceExactIntegerPrimitiveApplication function arguments = do
  operation <- case function of
    KTGlobal ref [] -> Just ref
    _ -> Nothing
  (left, right) <- case arguments of
    [KArgument KExplicit lhs, KArgument KExplicit rhs] -> Just (lhs, rhs)
    _ -> Nothing
  lhs <- integerLiteralKTermValue left
  rhs <- integerLiteralKTermValue right
  let exact name = operation == stableRefForGlobal (gPrel name)
      integer value = KTLiteral (LitInt value)
      boolean truth =
        KTConstruct
          (stableRefForConstructor (if truth then prelTrue else prelFalse))
          []
          []
  if exact "addInt"
    then pure (integer (lhs + rhs))
    else if exact "subInt"
      then pure (integer (lhs - rhs))
      else if exact "mulInt"
        then pure (integer (lhs * rhs))
        else if exact "divInt" && rhs /= 0
          then pure (integer (lhs `quot` rhs))
          else if exact "modInt" && rhs /= 0
            then pure (integer (lhs `rem` rhs))
            else if exact "eqInt"
              then pure (boolean (lhs == rhs))
              else if exact "ltInt"
                then pure (boolean (lhs < rhs))
                else if exact "leInt"
                  then pure (boolean (lhs <= rhs))
                  else Nothing

-- Exact integer conversion primitives compute definitionally on literal
-- payloads. Replaying these equations is required when one checked path has
-- already normalized a Nat literal while another retains its authenticated
-- @natToInt@ bridge. Stable global identity, arity, and the partial
-- @intToNat@ domain are all checked here; readable names alone grant no
-- authority.
reduceExactIntegerConversionApplication
  :: KTerm
  -> [KArgument]
  -> Maybe KTerm
reduceExactIntegerConversionApplication function arguments = do
  operation <- case function of
    KTGlobal ref [] -> Just ref
    _ -> Nothing
  operand <- case arguments of
    [KArgument KExplicit argument] -> Just argument
    _ -> Nothing
  let exact name = operation == stableRefForGlobal (gPrel name)
  value <- integerLiteralKTermValue operand
  guard (exact "natOfInt" || ((exact "natToInt" || exact "intToNat") && value >= 0))
  pure (KTLiteral (LitInt value))

integerLiteralKTermValue :: KTerm -> Maybe Integer
integerLiteralKTermValue = \case
  KTLiteral (LitInt value) -> Just value
  generic@(KTGeneric tag fields)
    | tag `Set.member` decodedBuiltinTermTags ->
        case decodeBuiltinTermNode tag fields of
          Right decoded
            | decoded /= generic -> integerLiteralKTermValue decoded
          _ -> Nothing
  _ -> Nothing

-- | One source computation step for the canonical logical-Nat operations.
-- The KCore verifier cannot depend on evaluator state or imported definition
-- bodies, so it replays the §28.2 equations from stable declaration and
-- constructor identities. This is deliberately only definitional reduction:
-- right identity, commutativity, and other algebraic laws stay out.
reduceLogicalNaturalApplication :: KTerm -> [KArgument] -> Maybe KTerm
reduceLogicalNaturalApplication function arguments = do
  operation <- case function of
    KTGlobal ref [] -> Just ref
    _ -> Nothing
  (left, right) <- case arguments of
    [KArgument KExplicit lhs, KArgument KExplicit rhs] -> Just (lhs, rhs)
    _ -> Nothing
  if operation == stableRefForGlobal prelNatAdd
    then case logicalNaturalKTermView left of
      Just LogicalNatZero -> Just right
      Just (LogicalNatSucc predecessor) ->
        Just
          ( logicalNaturalKTermSucc
              ( KTApply
                  (KTGlobal operation [])
                  [KArgument KExplicit predecessor, KArgument KExplicit right]
              )
          )
      Nothing -> Nothing
    else if operation == stableRefForGlobal prelNatMultiply
      then case logicalNaturalKTermView left of
        Just LogicalNatZero -> Just logicalNaturalKTermZero
        Just (LogicalNatSucc predecessor) ->
          Just
            ( KTApply
                (KTGlobal (stableRefForGlobal prelNatAdd) [])
                [ KArgument KExplicit right
                , KArgument KExplicit
                    ( KTApply
                        (KTGlobal operation [])
                        [KArgument KExplicit predecessor, KArgument KExplicit right]
                    )
                ]
            )
        Nothing -> Nothing
      else if operation == stableRefForGlobal prelNatCompare
        then reduceCompare left right
        else Nothing
  where
    reduceCompare left right =
      case (logicalNaturalKTermView left, logicalNaturalKTermView right) of
        (Just LogicalNatZero, Just LogicalNatZero) -> ordering EQ
        (Just LogicalNatZero, Just LogicalNatSucc {}) -> ordering LT
        (Just LogicalNatSucc {}, Just LogicalNatZero) -> ordering GT
        (Just (LogicalNatSucc leftPred), Just (LogicalNatSucc rightPred)) ->
          Just
            ( KTApply
                (KTGlobal (stableRefForGlobal prelNatCompare) [])
                [KArgument KExplicit leftPred, KArgument KExplicit rightPred]
            )
        _ -> Nothing
    ordering =
      Just
        . (\constructor -> KTConstruct (stableRefForConstructor constructor) [] [])
        . prelOrdering

data LogicalNaturalKTermView
  = LogicalNatZero
  | LogicalNatSucc !KTerm

logicalNaturalKTermView :: KTerm -> Maybe LogicalNaturalKTermView
logicalNaturalKTermView = \case
  generic@(KTGeneric tag fields)
    | tag `Set.member` decodedBuiltinTermTags ->
        case decodeBuiltinTermNode tag fields of
          Right decoded
            | decoded /= generic -> logicalNaturalKTermView decoded
          _ -> Nothing
  KTLiteral (LitInt value)
    | value == 0 -> Just LogicalNatZero
    | value > 0 -> Just (LogicalNatSucc (KTLiteral (LitInt (value - 1))))
  KTConstruct constructor [] []
    | constructor == stableRefForConstructor prelNatZero ->
        Just LogicalNatZero
  KTConstruct constructor [] [KArgument KExplicit predecessor]
    | constructor == stableRefForConstructor prelNatSucc ->
        Just (LogicalNatSucc predecessor)
  _ -> Nothing

logicalNaturalKTermValue :: KTerm -> Maybe Integer
logicalNaturalKTermValue term =
  case logicalNaturalKTermView term of
    Just LogicalNatZero -> Just 0
    Just (LogicalNatSucc predecessor) ->
      (+ 1) <$> logicalNaturalKTermValue predecessor
    Nothing -> Nothing

logicalNaturalKTermZero :: KTerm
logicalNaturalKTermZero =
  KTConstruct (stableRefForConstructor prelNatZero) [] []

logicalNaturalKTermSucc :: KTerm -> KTerm
logicalNaturalKTermSucc predecessor =
  KTConstruct
    (stableRefForConstructor prelNatSucc)
    []
    [KArgument KExplicit predecessor]

-- Opaque trait heads are not definitionally equal to their dictionary record
-- representation, but record construction and projection still need the
-- exported structural interface. Keep that authority separate from
-- 'vcGlobalBodies' so interface checking cannot accidentally make an opaque
-- declaration reducible.
recordInterfaceView :: VerifyContext -> KTerm -> (Maybe StableRef, KTerm)
recordInterfaceView context term =
  case unfoldTypeHead context term of
    record@KTRecordType {} -> (Nothing, record)
    normalized ->
      case collect normalized of
        (KTGlobal ref levels, arguments) ->
          case importedInterface ref levels arguments of
            Just view -> (Just ref, view)
            Nothing ->
              maybe
                (Nothing, normalized)
                (\view -> (Just ref, view))
                (nominalTraitInterface ref levels arguments normalized)
        _ -> (Nothing, normalized)
  where
    importedInterface ref levels arguments = do
      (parameters, interface) <- Map.lookup ref (vcRecordInterfaces context)
      guard (length parameters == length levels)
      let specialized =
            substituteUniverseParameters
              (Map.fromList (zip (map urId parameters) levels))
              interface
      applyInterface specialized arguments

    -- Local trait declarations do not pass through the imported-global
    -- record-interface table. Their independently checked nominal family and
    -- synthetic dictionary constructor are nevertheless a complete
    -- structural interface (§14.3.1A). Derive that interface only when the
    -- replayed schema certificate authenticates generated projections, the
    -- constructor is universe-closed relative to the family, and its field
    -- map is a total permutation of the payload telescope.
    nominalTraitInterface ref levels arguments expected = do
      guard (isTraitEvidenceInterface context ref)
      family <- Map.lookup ref (vcNominalFamilies context)
      let universeParameters = map fst (knfUniverses family)
          parameters = knfBinders family
      guard (length universeParameters == length levels)
      guard (length parameters == length arguments)
      parameterSubstitution <-
        fmap Map.fromList . forM (zip parameters arguments) $ \(parameter, KArgument explicitness argument) -> do
          guard (kbExplicitness parameter == explicitness)
          pure (lrId (kbRef parameter), argument)
      KCtorDecl _ constructorUniverses fields constructorType0 <-
        case knfConstructors family of
          [constructor] -> Just constructor
          _ -> Nothing
      guard (null constructorUniverses)
      let universeSubstitution =
            Map.fromList (zip (map urId universeParameters) levels)
          constructorType =
            substituteUniverseParameters universeSubstitution constructorType0
          substituteParameters =
            substituteKTermParameters parameters parameterSubstitution
          (payload0, constructorResult0) = splitPiTelescope constructorType
          payload =
            [ binder {kbType = substituteParameters (kbType binder)}
            | binder <- payload0
            ]
          constructorResult = substituteParameters constructorResult0
          fieldByIndex = Map.fromList [(index, field) | (field, index) <- fields]
      guard (sameKCoreType context constructorResult expected)
      guard (Map.size fieldByIndex == length fields)
      guard (Map.keys fieldByIndex == [0 .. length payload - 1])
      pure
        ( KTRecordType
            [ (field, binder)
            | (index, binder) <- zip [0 ..] payload
            , Just field <- [Map.lookup index fieldByIndex]
            ]
        )

    collect = go []
      where
        go arguments (KTApply function more) = go (more ++ arguments) function
        go arguments headTerm = (headTerm, arguments)
    applyInterface result [] =
      case result of
        record@KTRecordType {} -> Just record
        _ -> Nothing
    applyInterface (KTLambda binder body) (argument@(KArgument explicitness _) : rest)
      | kbExplicitness binder == explicitness =
          applyInterface (substituteLocal (kbRef binder) (argumentTerm argument) body) rest
    applyInterface _ _ = Nothing

recordInterfaceHead :: VerifyContext -> KTerm -> KTerm
recordInterfaceHead context = snd . recordInterfaceView context

isTraitEvidenceInterface :: VerifyContext -> StableRef -> Bool
isTraitEvidenceInterface context owner =
  case Map.lookup owner (vcNominalFamilies context) of
    Nothing -> False
    Just family ->
      maybe
        False
        (elem ClauseGeneratedProjection . kscClauseKinds)
        (Map.lookup (knfCertificate family) (vcSchemaCertificates context))

checkBooleanTerm :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KTerm -> Either KCoreTextError ()
checkBooleanTerm context universes assumptions env term = do
  verifyTerm context universes assumptions env term
  inferred <- inferSimple context universes assumptions env term
  case unfoldTypeHead context <$> inferred of
    Just (KTGlobal ref _) | ref == stableRefForGlobal prelBool -> pure ()
    _ -> Left (invalid "KCore conditional guard does not have Bool type")

literalKType :: Literal -> KTerm
literalKType = \case
  LitInt _ -> KTGlobal (stableRefForGlobal prelInt) []
  LitDouble _ -> KTGlobal (stableRefForGlobal prelDouble) []
  LitStr _ -> KTGlobal (stableRefForGlobal prelString) []
  LitScalar _ -> KTGlobal (stableRefForGlobal prelUnicodeScalar) []
  LitByte _ -> KTGlobal (stableRefForGlobal prelByte) []
  LitBytes _ -> KTGlobal (stableRefForGlobal (gPrel "Bytes")) []
  LitGrapheme _ -> KTGlobal (stableRefForGlobal prelGrapheme) []

literalChecksAt :: VerifyContext -> Literal -> KTerm -> Bool
literalChecksAt context literal expected =
  sameKCoreType context (literalKType literal) expected
    || case literal of
      LitInt _ -> expected `elem` map (\g -> KTGlobal (stableRefForGlobal g) []) [gPrel "Nat", gPrel "Integer"]
      _ -> False

checkRecordValue ::
  VerifyContext ->
  Set Int ->
  Assumptions ->
  LocalEnv ->
  Maybe StableRef ->
  [(Text, KTerm)] ->
  [(StableRef, KBinder)] ->
  Either KCoreTextError ()
checkRecordValue context universes assumptions env owner fields recordFields = do
  let names = map fst fields
      expectedNames = map (srName . fst) recordFields
  unless
    ( length names == Set.size (Set.fromList names)
        && Set.fromList names == Set.fromList expectedNames
    ) $
    Left (invalid "record value fields do not match the expected dependent record telescope")
  _ <- foldM checkField [] recordFields
  pure ()
  where
    checkField substitutions (field, binder) = do
      value <- maybe
        (Left (invalid ("record value is missing field " <> srName field)))
        pure
        (lookup (srName field) fields)
      let expected =
            foldl
              (\ty (ref, replacement) -> substituteLocal ref replacement ty)
              (kbType binder)
              substitutions
      -- Each field is checked at its declared observation mode. The enclosing
      -- record dependency calculation separately propagates ordinary-field
      -- dependencies and seals parametric fields; using Parametric here for
      -- every field would allow a nested ordinary field to launder a
      -- parametric witness.
      if
        | kbMode binder == Ordinary
        , Just trait <- owner
        , isTraitEvidenceInterface context trait
        , KTPi {} <- unfoldTypeHead context expected ->
            checkTraitBehaviorField value expected
        | otherwise ->
            checkTermObserved (kbMode binder) context universes assumptions env value expected
      pure (substitutions ++ [(kbRef binder, value)])

    -- Spec §14.3.1A permits an ordinary callable supplied by authenticated
    -- trait evidence to depend on the trait's static indices when those
    -- indices are already represented by the callable's checked classifier.
    -- This is not a generic record escape hatch: the nominal owner is
    -- authenticated by its replayed schema certificate, non-callable fields
    -- retain the ordinary empty-dependency boundary, and any unrelated
    -- dependency remains an error.
    checkTraitBehaviorField value expected = do
      checkTermObservedAtBoundary False Ordinary context universes assumptions env value expected
      valueDependencies0 <-
        kObservationDependencies context universes assumptions env (Just expected) value
      residual <-
        kClassifierRelativeDependencies
          context
          universes
          assumptions
          env
          expected
          valueDependencies0
      unless (Set.null residual) $
        Left
          ( KCoreTextError
              "E_PARAMETRIC_TYPE_PROMOTION"
              ( "a trait behavior field depends on parametric origins absent from its checked classifier; dependencies: "
                  <> T.pack (show (Set.toAscList residual))
              )
          )

-- | Remove parametric origins already represented by a checked classifier.
-- This is the KCoreText form of §30.2.0 classifier-relative observation: a
-- runtime value of @List A@ or @m A@ does not thereby reify the static code
-- @A@. The dependency analysis remains fail-closed because an unavailable
-- classifier dependency is an error, not an empty set.
kClassifierRelativeDependencies
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> KTerm
  -> KDependencySet
  -> Either KCoreTextError KDependencySet
kClassifierRelativeDependencies context universes assumptions env classifier dependencies = do
  classifierDependencies <-
    kObservationDependencies context universes assumptions env Nothing classifier
  pure (dependencies `Set.difference` classifierDependencies)

sameKLevel :: KLevel -> KLevel -> Bool
sameKLevel lhs rhs = case (toLevel lhs, toLevel rhs) of
  (Just lhs', Just rhs') -> normalizeLevel lhs' == normalizeLevel rhs'
  _ -> lhs == rhs

sameKLevels :: [KLevel] -> [KLevel] -> Bool
sameKLevels left right =
  length left == length right && and (zipWith sameKLevel left right)

sameSchemaRoleShapes :: [KSchemaRoleEvidence] -> [KSchemaRoleEvidence] -> Bool
sameSchemaRoleShapes left right =
  length left == length right && and (zipWith sameRole left right)
  where
    sameRole KSchemaInvariant KSchemaInvariant = True
    sameRole KSchemaCovariant {} KSchemaCovariant {} = True
    sameRole KSchemaIrrelevant KSchemaIrrelevant = True
    sameRole _ _ = False

renameLocal :: LocalRef -> LocalRef -> KTerm -> KTerm
renameLocal old new = go
  where
    go = \case
      KTLocal ref levels | ref == old -> KTLocal new (map goLevel levels)
      term@KTLocal {} -> term
      KTGlobal ref levels -> KTGlobal ref (map goLevel levels)
      KTType level -> KTType (goLevel level)
      KTPi binder body -> KTPi (goBinder binder) (if kbRef binder == old then body else go body)
      KTSigma binder body -> KTSigma (goBinder binder) (if kbRef binder == old then body else go body)
      KTLambda binder body -> KTLambda (goBinder binder) (if kbRef binder == old then body else go body)
      KTApply f args -> KTApply (go f) [KArgument ic (go term) | KArgument ic term <- args]
      KTBlock items result -> KTBlock (map goBlockItem items) (go result)
      KTLetRec definitions result -> KTLetRec (map goLocalDef definitions) (go result)
      KTCase scrutinee resultType alternatives -> KTCase (go scrutinee) (go resultType) (map goCaseAlt alternatives)
      KTConstruct ref levels args -> KTConstruct ref (map goLevel levels) [KArgument ic (go term) | KArgument ic term <- args]
      KTProject ref term -> KTProject ref (go term)
      KTLift from to evidence term -> KTLift (goLevel from) (goLevel to) (goEvidence evidence) (go term)
      KTSchemaLift family from to certificate roles targetArguments term ->
        KTSchemaLift family (map goLevel from) (map goLevel to) certificate
          (map goSchemaRole roles) [KArgument icit (go argument) | KArgument icit argument <- targetArguments] (go term)
      KTAscribe value ty -> KTAscribe (go value) (go ty)
      KTLiteral literal -> KTLiteral literal
      KTRecordType fields -> KTRecordType [(field, goBinder binder) | (field, binder) <- fields]
      KTRecordValue fields -> KTRecordValue [(name, go value) | (name, value) <- fields]
      KTIf condition thenBranch elseBranch -> KTIf (go condition) (go thenBranch) (go elseBranch)
      KTGeneric tag fields -> KTGeneric tag [(name, goValue value) | (name, value) <- fields]
    goBinder binder = binder {kbType = go (kbType binder)}
    goLevel = \case
      KLSucc x -> KLSucc (goLevel x)
      KLMax a b -> KLMax (goLevel a) (goLevel b)
      KLAdd a b -> KLAdd (goLevel a) (goLevel b)
      KLTerm term -> KLTerm (go term)
      other -> other
    goEvidence = \case
      KELocal ref -> KELocal (if ref == old then new else ref)
      KEGlobal ref levels -> KEGlobal ref (map goLevel levels)
      KECertificate ref levels -> KECertificate ref (map goLevel levels)
    goSchemaRole = \case
      KSchemaInvariant -> KSchemaInvariant
      KSchemaIrrelevant -> KSchemaIrrelevant
      KSchemaCovariant evidence -> KSchemaCovariant (goEvidence evidence)
    goValue = \case
      KVTerm term -> KVTerm (go term)
      KVLevel level -> KVLevel (goLevel level)
      KVQuantity (KQTerm term) -> KVQuantity (KQTerm (go term))
      KVAccess (KBorrow (Just (KRLocal ref))) -> KVAccess (KBorrow (Just (KRLocal (if ref == old then new else ref))))
      KVGlobal ref levels -> KVGlobal ref (map goLevel levels)
      KVLocal ref levels -> KVLocal (if ref == old then new else ref) (map goLevel levels)
      KVBinder binder -> KVBinder (goBinder binder)
      KVPattern pattern' -> KVPattern (goPattern pattern')
      KVList values -> KVList (map goValue values)
      other -> other
    goPattern = mapKPattern goBinder goLevel go
    goBlockItem = \case
      KBLet binder rhs -> KBLet (goBinder binder) (go rhs)
    goLocalDef definition = definition {kldType = go (kldType definition), kldBody = if kldRef definition == old then kldBody definition else go (kldBody definition)}
    goCaseAlt = \case
      KCaseDefault body -> KCaseDefault (go body)
      KCaseConstructor ref levels bindings body ->
        KCaseConstructor ref (map goLevel levels)
          (map (mapKCaseBinding goBinder go) bindings) (go body)
      KCasePattern pattern' guard' body -> KCasePattern (goPattern pattern') (fmap go guard') (go body)

substituteLocal :: LocalRef -> KTerm -> KTerm -> KTerm
substituteLocal old replacement =
  go
    . freshenKTermBindersAgainst
        (Set.insert (lrId old) (kTermLocalIds replacement))
  where
    go = \case
      KTLocal ref [] | ref == old -> replacement
      term@(KTLocal ref _) | ref == old -> term
      term@KTLocal {} -> term
      KTGlobal ref levels -> KTGlobal ref (map goLevel levels)
      KTType level -> KTType (goLevel level)
      KTPi binder body -> KTPi (goBinder binder) (if kbRef binder == old then body else go body)
      KTSigma binder body -> KTSigma (goBinder binder) (if kbRef binder == old then body else go body)
      KTLambda binder body -> KTLambda (goBinder binder) (if kbRef binder == old then body else go body)
      KTApply fun args -> KTApply (go fun) [KArgument ic (go term) | KArgument ic term <- args]
      KTBlock items result -> KTBlock (map goBlockItem items) (go result)
      KTLetRec definitions result -> KTLetRec (map goLocalDef definitions) (go result)
      KTCase scrutinee resultType alternatives -> KTCase (go scrutinee) (go resultType) (map goCaseAlt alternatives)
      KTConstruct ref levels args -> KTConstruct ref (map goLevel levels) [KArgument ic (go term) | KArgument ic term <- args]
      KTProject ref term -> KTProject ref (go term)
      KTLift from to evidence term -> KTLift (goLevel from) (goLevel to) (goEvidence evidence) (go term)
      KTSchemaLift family from to certificate roles targetArguments term ->
        KTSchemaLift family (map goLevel from) (map goLevel to) certificate
          (map goSchemaRole roles) [KArgument icit (go argument) | KArgument icit argument <- targetArguments] (go term)
      KTAscribe value ty -> KTAscribe (go value) (go ty)
      KTLiteral literal -> KTLiteral literal
      KTRecordType fields -> KTRecordType [(field, goBinder binder) | (field, binder) <- fields]
      KTRecordValue fields -> KTRecordValue [(name, go value) | (name, value) <- fields]
      KTIf condition thenBranch elseBranch -> KTIf (go condition) (go thenBranch) (go elseBranch)
      KTGeneric tag fields -> KTGeneric tag [(name, goValue value) | (name, value) <- fields]
    goBinder binder = binder {kbType = go (kbType binder)}
    goLevel = \case
      KLSucc level -> KLSucc (goLevel level)
      KLMax lhs rhs -> KLMax (goLevel lhs) (goLevel rhs)
      KLAdd lhs rhs -> KLAdd (goLevel lhs) (goLevel rhs)
      KLTerm term -> KLTerm (go term)
      level -> level
    goEvidence = \case
      KELocal ref
        | ref == old -> case replacement of
            KTLocal replacementRef _ -> KELocal replacementRef
            KTGlobal replacementRef levels -> KEGlobal replacementRef (map goLevel levels)
            _ -> KELocal ref
        | otherwise -> KELocal ref
      KEGlobal ref levels -> KEGlobal ref (map goLevel levels)
      KECertificate ref levels -> KECertificate ref (map goLevel levels)
    goSchemaRole = \case
      KSchemaInvariant -> KSchemaInvariant
      KSchemaIrrelevant -> KSchemaIrrelevant
      KSchemaCovariant evidence -> KSchemaCovariant (goEvidence evidence)
    goValue = \case
      KVTerm term -> KVTerm (go term)
      KVLevel level -> KVLevel (goLevel level)
      KVQuantity (KQTerm term) -> KVQuantity (KQTerm (go term))
      KVGlobal ref levels -> KVGlobal ref (map goLevel levels)
      KVLocal ref levels -> KVLocal ref (map goLevel levels)
      KVBinder binder -> KVBinder (goBinder binder)
      KVPattern pattern' -> KVPattern (goPattern pattern')
      KVList values -> KVList (map goValue values)
      value -> value
    goPattern = mapKPattern goBinder goLevel go
    goBlockItem = \case
      KBLet binder rhs -> KBLet (goBinder binder) (go rhs)
    goLocalDef definition = definition {kldType = go (kldType definition), kldBody = if kldRef definition == old then kldBody definition else go (kldBody definition)}
    goCaseAlt = \case
      KCaseDefault body -> KCaseDefault (go body)
      KCaseConstructor ref levels bindings body ->
        KCaseConstructor ref (map goLevel levels)
          (map (mapKCaseBinding goBinder go) bindings) (go body)
      KCasePattern pattern' guard' body -> KCasePattern (goPattern pattern') (fmap go guard') (go body)

substituteGlobalTerm :: StableRef -> KTerm -> KTerm -> KTerm
substituteGlobalTerm old replacement = go
  where
    go = \case
      KTGlobal ref [] | ref == old -> replacement
      KTLocal ref levels -> KTLocal ref (map goLevel levels)
      KTGlobal ref levels -> KTGlobal ref (map goLevel levels)
      KTType level -> KTType (goLevel level)
      KTPi binder body -> KTPi (goBinder binder) (go body)
      KTSigma binder body -> KTSigma (goBinder binder) (go body)
      KTLambda binder body -> KTLambda (goBinder binder) (go body)
      KTApply function arguments -> KTApply (go function) [KArgument explicitness (go argument) | KArgument explicitness argument <- arguments]
      KTBlock items result -> KTBlock (map goBlockItem items) (go result)
      KTLetRec definitions result -> KTLetRec (map goLocalDef definitions) (go result)
      KTCase scrutinee resultType alternatives -> KTCase (go scrutinee) (go resultType) (map goCaseAlt alternatives)
      KTConstruct ref levels arguments -> KTConstruct ref (map goLevel levels) [KArgument explicitness (go argument) | KArgument explicitness argument <- arguments]
      KTProject ref record -> KTProject ref (go record)
      KTLift from to evidence inner -> KTLift (goLevel from) (goLevel to) (goEvidence evidence) (go inner)
      KTSchemaLift family from to certificate roles targetArguments term ->
        KTSchemaLift family (map goLevel from) (map goLevel to) certificate
          (map goSchemaRole roles) [KArgument icit (go argument) | KArgument icit argument <- targetArguments] (go term)
      KTAscribe value ty -> KTAscribe (go value) (go ty)
      KTLiteral literal -> KTLiteral literal
      KTRecordType fields -> KTRecordType [(field, goBinder binder) | (field, binder) <- fields]
      KTRecordValue fields -> KTRecordValue [(name, go value) | (name, value) <- fields]
      KTIf condition thenBranch elseBranch -> KTIf (go condition) (go thenBranch) (go elseBranch)
      KTGeneric tag fields -> KTGeneric tag [(name, goValue value) | (name, value) <- fields]
    goBinder binder = binder {kbType = go (kbType binder)}
    goLevel = \case
      KLSucc level -> KLSucc (goLevel level)
      KLMax lhs rhs -> KLMax (goLevel lhs) (goLevel rhs)
      KLAdd lhs rhs -> KLAdd (goLevel lhs) (goLevel rhs)
      KLTerm term -> KLTerm (go term)
      level -> level
    goEvidence = \case
      KELocal ref -> KELocal ref
      KEGlobal ref levels
        | ref == old -> case replacement of
            KTGlobal replacementRef replacementLevels -> KEGlobal replacementRef (map goLevel replacementLevels)
            KTLocal replacementRef _ -> KELocal replacementRef
            _ -> KEGlobal ref (map goLevel levels)
        | otherwise -> KEGlobal ref (map goLevel levels)
      KECertificate ref levels -> KECertificate ref (map goLevel levels)
    goSchemaRole = \case
      KSchemaInvariant -> KSchemaInvariant
      KSchemaIrrelevant -> KSchemaIrrelevant
      KSchemaCovariant evidence -> KSchemaCovariant (goEvidence evidence)
    goValue = \case
      KVTerm term -> KVTerm (go term)
      KVLevel level -> KVLevel (goLevel level)
      KVQuantity (KQTerm term) -> KVQuantity (KQTerm (go term))
      KVGlobal ref levels -> KVGlobal ref (map goLevel levels)
      KVLocal ref levels -> KVLocal ref (map goLevel levels)
      KVBinder binder -> KVBinder (goBinder binder)
      KVPattern pattern' -> KVPattern (mapKPattern goBinder goLevel go pattern')
      KVList values -> KVList (map goValue values)
      value -> value
    goBlockItem (KBLet binder rhs) = KBLet (goBinder binder) (go rhs)
    goLocalDef definition =
      definition
        { kldType = go (kldType definition)
        , kldBody = go (kldBody definition)
        }
    goCaseAlt = \case
      KCaseDefault body -> KCaseDefault (go body)
      KCaseConstructor ref levels bindings body ->
        KCaseConstructor ref (map goLevel levels)
          (map (mapKCaseBinding goBinder go) bindings) (go body)
      KCasePattern pattern' guard' body ->
        KCasePattern (mapKPattern goBinder goLevel go pattern') (fmap go guard') (go body)

substituteUniverseParameters :: Map Int KLevel -> KTerm -> KTerm
substituteUniverseParameters substitution = go
  where
    go = \case
      KTLocal ref levels -> KTLocal ref (map goLevel levels)
      KTGlobal ref levels -> KTGlobal ref (map goLevel levels)
      KTType level -> KTType (goLevel level)
      KTPi binder body -> KTPi (goBinder binder) (go body)
      KTSigma binder body -> KTSigma (goBinder binder) (go body)
      KTLambda binder body -> KTLambda (goBinder binder) (go body)
      KTApply fun args -> KTApply (go fun) [KArgument ic (go term) | KArgument ic term <- args]
      KTBlock items result -> KTBlock (map goBlockItem items) (go result)
      KTLetRec definitions result -> KTLetRec (map goLocalDef definitions) (go result)
      KTCase scrutinee resultType alternatives -> KTCase (go scrutinee) (go resultType) (map goCaseAlt alternatives)
      KTConstruct ref levels args -> KTConstruct ref (map goLevel levels) [KArgument ic (go term) | KArgument ic term <- args]
      KTProject ref term -> KTProject ref (go term)
      KTLift from to evidence term -> KTLift (goLevel from) (goLevel to) (goEvidence evidence) (go term)
      KTSchemaLift family from to certificate roles targetArguments term ->
        KTSchemaLift family (map goLevel from) (map goLevel to) certificate
          (map goSchemaRole roles) [KArgument icit (go argument) | KArgument icit argument <- targetArguments] (go term)
      KTAscribe value ty -> KTAscribe (go value) (go ty)
      KTLiteral literal -> KTLiteral literal
      KTRecordType fields -> KTRecordType [(field, goBinder binder) | (field, binder) <- fields]
      KTRecordValue fields -> KTRecordValue [(name, go value) | (name, value) <- fields]
      KTIf condition thenBranch elseBranch -> KTIf (go condition) (go thenBranch) (go elseBranch)
      KTGeneric tag fields -> KTGeneric tag [(name, goValue value) | (name, value) <- fields]
    goBinder binder = binder {kbType = go (kbType binder)}
    goLevel = \case
      KLUniverse ref -> Map.findWithDefault (KLUniverse ref) (urId ref) substitution
      KLSucc level -> KLSucc (goLevel level)
      KLMax lhs rhs -> KLMax (goLevel lhs) (goLevel rhs)
      KLAdd lhs rhs -> KLAdd (goLevel lhs) (goLevel rhs)
      KLTerm term -> KLTerm (go term)
      level -> level
    goEvidence = \case
      KELocal ref -> KELocal ref
      KEGlobal ref levels -> KEGlobal ref (map goLevel levels)
      KECertificate ref levels -> KECertificate ref (map goLevel levels)
    goSchemaRole = \case
      KSchemaInvariant -> KSchemaInvariant
      KSchemaIrrelevant -> KSchemaIrrelevant
      KSchemaCovariant evidence -> KSchemaCovariant (goEvidence evidence)
    goValue = \case
      KVTerm term -> KVTerm (go term)
      KVLevel level -> KVLevel (goLevel level)
      KVQuantity (KQTerm term) -> KVQuantity (KQTerm (go term))
      KVGlobal ref levels -> KVGlobal ref (map goLevel levels)
      KVLocal ref levels -> KVLocal ref (map goLevel levels)
      KVBinder binder -> KVBinder (goBinder binder)
      KVPattern pattern' -> KVPattern (goPattern pattern')
      KVList values -> KVList (map goValue values)
      value -> value
    goPattern = mapKPattern goBinder goLevel go
    goBlockItem = \case
      KBLet binder rhs -> KBLet (goBinder binder) (go rhs)
    goLocalDef definition = definition {kldType = go (kldType definition), kldBody = go (kldBody definition)}
    goCaseAlt = \case
      KCaseDefault body -> KCaseDefault (go body)
      KCaseConstructor ref levels bindings body ->
        KCaseConstructor ref (map goLevel levels)
          (map (mapKCaseBinding goBinder go) bindings) (go body)
      KCasePattern pattern' guard' body -> KCasePattern (goPattern pattern') (fmap go guard') (go body)

verifyValue :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KValueNode -> Either KCoreTextError ()
verifyValue context universes assumptions env = \case
  KVTerm term -> verifyTerm context universes assumptions env term
  KVLevel level -> verifyLevel context universes assumptions env level
  KVQuantity (KQTerm term) -> verifyTerm context universes assumptions env term
  KVAccess (KBorrow (Just (KRLocal ref))) ->
    unless (lrId ref `Map.member` env) (Left (invalid "generic access mode references an out-of-scope local region"))
  KVAccess (KBorrow (Just (KRGlobal ref))) ->
    unless (ref `Map.member` vcGlobalArities context) (Left (invalid "generic access mode references an unavailable global region"))
  KVGlobal ref levels -> do
    mapM_ (verifyLevel context universes assumptions env) levels
    arity <- maybe (Left (invalid "generic value references an unavailable global")) Right (Map.lookup ref (vcGlobalArities context))
    unless (length levels == arity) $
      Left (invalid "generic global value has the wrong universe arity")
  KVLocal ref levels -> do
    mapM_ (verifyLevel context universes assumptions env) levels
    entry <- maybe (Left (invalid "generic value references an out-of-scope local")) Right (Map.lookup (lrId ref) env)
    let arity = case entry of
          LocalBinder _ -> 0
          LocalDefinition _ schema _ _ -> length schema
    unless (length levels == arity) $
      Left (invalid "generic local value has the wrong universe arity")
  KVBinder binder -> verifyBinder context universes assumptions env binder
  KVPattern _ -> Left (invalid "a pattern value is only valid in a typed case or do-item schema")
  KVList values -> mapM_ (verifyValue context universes assumptions env) values
  _ -> pure ()

verifyLevel :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KLevel -> Either KCoreTextError ()
verifyLevel context scope assumptions env = \case
  KLFinite n -> when (n < 0) (Left (invalid "universe levels must be nonnegative"))
  KLGlobal ref -> do
    unless (ref `Map.member` vcGlobalArities context) $
      Left (invalid ("unavailable TypeLevel semantic identity " <> renderStable ref))
    inferred <- inferSimple context scope assumptions env (KTGlobal ref [])
    unless (inferred == Just (KTGlobal typeLevelStableRef [])) $
      Left (invalid "a global used as a level must have the exact std TypeLevel semantic identity")
  KLUniverse ref -> unless (urId ref `Set.member` scope) (Left (invalid ("unbound universe reference " <> renderUniverse ref)))
  KLSucc level -> recur level
  KLMax lhs rhs -> recur lhs >> recur rhs
  KLAdd lhs rhs -> recur lhs >> recur rhs
  KLTerm term -> do
    verifyTerm context scope assumptions env term
    inferred <- inferSimple context scope assumptions env term
    unless (inferred == Just (KTGlobal typeLevelStableRef [])) $
      Left (invalid "level-term must have the exact std TypeLevel semantic identity")
    verifyLevelTermAdmissibility context env term
  where
    recur = verifyLevel context scope assumptions env

-- | Independently replay the §11.1.1 level-admissibility obligations that are
-- not implied by ordinary typing. KCoreText carries no termination
-- certificate for a local recursive group, so such a producer is rejected
-- fail-closed. Pure acyclic definitions, applications, projections, cases,
-- and immutable lets remain admissible; effect/generic implementation nodes
-- cannot become neutral atoms without a typed admissibility rule owned by
-- their extension.
verifyLevelTermAdmissibility :: VerifyContext -> LocalEnv -> KTerm -> Either KCoreTextError ()
verifyLevelTermAdmissibility context = go Set.empty Set.empty
  where
    go activeGlobals activeLocals env = \case
      KTLocal ref levels ->
        case Map.lookup (lrId ref) env of
          Just (LocalDefinition _ parameters _ body) -> do
            unless (length parameters == length levels) $
              Left (invalid "level-term local definition has the wrong universe arity")
            when (lrId ref `Set.member` activeLocals) $
              Left (invalid "level-term totality is not established for a recursive local definition")
            let substitution = Map.fromList (zip (map urId parameters) levels)
            go activeGlobals (Set.insert (lrId ref) activeLocals) env
              (substituteUniverseParameters substitution body)
          _ -> pure ()
      KTGlobal ref levels ->
        case Map.lookup ref (vcGlobalBodies context) of
          Just (parameters, body) -> do
            unless (length parameters == length levels) $
              Left (invalid "level-term global definition has the wrong universe arity")
            when (ref `Set.member` activeGlobals) $
              Left (invalid "level-term totality is not established for a recursive global definition")
            let substitution = Map.fromList (zip (map urId parameters) levels)
            go (Set.insert ref activeGlobals) activeLocals env
              (substituteUniverseParameters substitution body)
          Nothing -> pure ()
      KTType _ -> pure ()
      KTPi binder codomain -> underBinder binder codomain
      KTSigma binder codomain -> underBinder binder codomain
      KTLambda binder body -> underBinder binder body
      KTApply function arguments ->
        go activeGlobals activeLocals env function
          >> mapM_ (go activeGlobals activeLocals env . argumentTerm) arguments
      KTBlock items result -> do
        env' <- foldM checkLet env items
        go activeGlobals activeLocals env' result
      KTLetRec {} ->
        Left (invalid "level-term totality is not established for a local recursive group")
      KTCase scrutinee resultType alternatives -> do
        go activeGlobals activeLocals env scrutinee
        go activeGlobals activeLocals env resultType
        mapM_ checkAlternative alternatives
      KTConstruct _ _ arguments ->
        mapM_ (go activeGlobals activeLocals env . argumentTerm) arguments
      KTProject _ receiver -> go activeGlobals activeLocals env receiver
      KTLift _ _ _ payload -> go activeGlobals activeLocals env payload
      KTSchemaLift _ _ _ _ _ targetArguments payload ->
        mapM_ (go activeGlobals activeLocals env . argumentTerm) targetArguments
          >> go activeGlobals activeLocals env payload
      KTAscribe value ty ->
        go activeGlobals activeLocals env value
          >> go activeGlobals activeLocals env ty
      KTLiteral _ -> pure ()
      KTRecordType fields -> foldM checkRecordBinder env (map snd fields) >> pure ()
      KTRecordValue fields -> mapM_ (go activeGlobals activeLocals env . snd) fields
      KTIf condition yes no ->
        mapM_ (go activeGlobals activeLocals env) [condition, yes, no]
      KTGeneric "impl.kappa.level-value" _ -> pure ()
      KTGeneric tag _ ->
        Left
          ( invalid
              ( "level-term stability/totality is not authenticated for implementation node "
                  <> tag
              )
          )
      where
        underBinder binder body = do
          go activeGlobals activeLocals env (kbType binder)
          go activeGlobals activeLocals
            (Map.insert (lrId (kbRef binder)) (LocalBinder binder) env)
            body
        checkLet envHere (KBLet binder rhs) = do
          go activeGlobals activeLocals envHere rhs
          pure (Map.insert (lrId (kbRef binder)) (LocalBinder binder) envHere)
        checkRecordBinder envHere binder = do
          go activeGlobals activeLocals envHere (kbType binder)
          pure (Map.insert (lrId (kbRef binder)) (LocalBinder binder) envHere)
        checkAlternative = \case
          KCaseConstructor _ _ bindings body -> do
            env' <- foldM bindCase env bindings
            go activeGlobals activeLocals env' body
          KCaseDefault body -> go activeGlobals activeLocals env body
          KCasePattern pattern' guard body -> do
            let patternEnv = bindPattern pattern' env
            mapM_ (go activeGlobals activeLocals patternEnv) guard
            go activeGlobals activeLocals patternEnv body
        bindAll binders env0 =
          foldl
            (\envHere binder -> Map.insert (lrId (kbRef binder)) (LocalBinder binder) envHere)
            env0
            binders
        bindPattern pattern' = bindAll (patternBinders pattern')
        bindCase envHere binding = do
          case binding of
            KCaseBridge bridge ->
              go activeGlobals activeLocals envHere (kcbProof bridge)
            KCasePayload {} -> pure ()
          let binder = caseBindingBinder binding
          go activeGlobals activeLocals envHere (kbType binder)
          pure
            (Map.insert (lrId (kbRef binder)) (LocalBinder binder) envHere)

    patternBinders pattern' = kpSlot pattern' : nodeBinders (kpNode pattern')
    nodeBinders = \case
      KPNConstructor _ _ existentials bridges fields ->
        existentials ++ map kcbBinder bridges ++ concatMap patternBinders fields
      KPNTuple fields -> concatMap patternBinders fields
      KPNRecord fields rest -> concatMap (\(_, _, field) -> patternBinders field) fields ++ maybe [] patternBinders rest
      KPNInject _ payload -> patternBinders payload
      KPNOr alternatives _ -> concatMap patternBinders alternatives
      KPNAs payload -> patternBinders payload
      _ -> []

typeLevelStableRef :: StableRef
typeLevelStableRef = stableRefForGlobal prelTypeLevel

verifyEvidence :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KLevel -> KLevel -> KEvidence -> Either KCoreTextError ()
verifyEvidence context universes ambientAssumptions env lower upper = \case
  KELocal ref -> do
    entry <- maybe (Left (invalid "lift evidence local is out of scope")) Right (Map.lookup (lrId ref) env)
    case entry of
      LocalBinder binder -> case levelAuthorityConstraint binder of
        Just constraint -> requireConstraintAuthority constraint
        Nothing ->
          Left
            ( invalid
                "lift evidence local must be an ordinary-observation, ordinary-formation, implicit, quantity-zero value proof binder"
            )
      LocalDefinition {} -> Left (invalid "schema-bearing local definitions must be instantiated before use as lift evidence")
  KEGlobal ref levels -> do
    (parameters, evidenceType) <-
      maybe
        (Left (invalid "lift evidence global is not declared in this KCore environment"))
        Right
        (Map.lookup ref (vcGlobalTypes context))
    unless (length parameters == length levels) $
      Left (invalid "lift evidence global has the wrong universe arity")
    requireLevelAuthority (substituteUniverseParameters (Map.fromList (zip (map urId parameters) levels)) evidenceType)
  KECertificate ref levels ->
    case Map.lookup ref (vcLevelCertificates context) of
      Just (parameters, constraints, constraint, proof) -> do
        unless (length parameters == length levels) $
          Left (KCoreTextError "E_KCORE_LEVEL_CERTIFICATE_INVALID" "lift certificate has the wrong universe arity")
        verifyInstantiatedConstraints context universes ambientAssumptions env
          ("lift certificate " <> renderStable ref) parameters constraints levels
        verifyLevelCertificate context ref parameters constraints constraint proof
        let substitution = Map.fromList (zip (map urId parameters) levels)
            specialized = substituteUniverseConstraint substitution constraint
        unless (constraintAuthorizesLift specialized) $
          Left (KCoreTextError "E_KCORE_LEVEL_CERTIFICATE_INVALID" "lift certificate proves different specialized endpoints")
      _ -> Left (KCoreTextError "E_KCORE_LEVEL_CERTIFICATE_INVALID" "lift certificate is unavailable or does not prove the asserted relation")
  where
    requireLevelAuthority evidenceType = case canonicalLevelConstraint evidenceType of
      Just constraint -> requireConstraintAuthority constraint
      _ ->
        Left
          (invalid
            ( "lift evidence does not establish the asserted level relation "
                <> printLevel lower <> " <= " <> printLevel upper
                <> "; found " <> printTerm evidenceType
            ))

    requireConstraintAuthority constraint
      | constraintAuthorizesLift constraint = pure ()
      | otherwise =
          Left
            ( invalid
                ( "lift evidence does not establish the asserted level relation "
                    <> printLevel lower <> " <= " <> printLevel upper
                )
            )

    -- The selected authority must itself establish this lift. Ambient facts
    -- may validate the authority's schema instantiation, but they cannot be
    -- combined with one selected proof to manufacture evidence for a stronger
    -- theorem. Multi-assumption derivations are represented by level
    -- certificates. Replay the ordinary level solver from the selected
    -- proposition alone so consequences such as succ-monotonicity remain
    -- available without trusting an opaque solver result.
    constraintAuthorizesLift constraint =
      case (toLevel lower, toLevel upper) of
        (Just lowerLevel, Just upperLevel) ->
          proveLevelLeq (constraintAssumptions [constraint]) lowerLevel upperLevel == Proved
        _ -> constraintMatchesLift constraint lower upper

constraintMatchesLift :: KConstraint -> KLevel -> KLevel -> Bool
constraintMatchesLift (KConstraint _ lhs rhs) lower upper =
  sameKLevel lhs lower
    && sameKLevel rhs upper

verifyLevelCertificate :: VerifyContext -> StableRef -> [UniverseRef] -> [KConstraint] -> KConstraint -> KLevelProof -> Either KCoreTextError ()
verifyLevelCertificate context ref universes constraints constraint proof =
  mapLeftCertificate $ do
    unless ("certificate." `T.isPrefixOf` srName ref) $
      Left (invalid "a level certificate must use the certificate semantic namespace")
    verifyUniverseTelescope universes
    let scope = universeScope universes
        assumptions = constraintAssumptions constraints
    verifyConstraints context scope constraints
    verifyConstraintLevels context scope assumptions Map.empty constraint
    case proof of
      KLPClosed -> do
        unless (null universes && null constraints && closedConstraint constraint && constraintProved emptyAssumptions constraint) $
          Left (invalid "closed certificate does not prove its stated level relation")
      KLPArithmetic dependencies ->
        verifyArithmeticLevelProof constraints constraint dependencies
      _ -> do
        derived <- deriveLevelProof context scope assumptions Map.empty constraints proof
        unless (sameConstraint derived constraint) $
          Left (invalid "level certificate proof tree proves a different relation")
  where
    mapLeftCertificate = either (Left . KCoreTextError "E_KCORE_LEVEL_CERTIFICATE_INVALID" . kcteMessage) Right

verifyArithmeticLevelProof :: [KConstraint] -> KConstraint -> [Int] -> Either KCoreTextError ()
verifyArithmeticLevelProof constraints theorem dependencies = do
  when (length dependencies /= Set.size (Set.fromList dependencies)) $
    Left (invalid "arithmetic level proof contains duplicate assumption indices")
  selected <- forM dependencies $ \index ->
    case drop index constraints of
      constraint : _ | index >= 0 -> pure constraint
      _ -> Left (invalid "arithmetic level proof references an unavailable assumption")
  unless (constraintProved (constraintAssumptions selected) theorem) $
    Left (invalid "arithmetic assumptions do not entail the stated level relation")

deriveLevelProof :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> [KConstraint] -> KLevelProof -> Either KCoreTextError KConstraint
deriveLevelProof context scope assumptions env constraints = \case
  KLPAssumption index ->
    case drop index constraints of
      constraint : _ -> pure constraint
      [] -> Left (invalid "level proof references an unavailable assumption")
  KLPClosed -> Left (invalid "closed proof is valid only as the complete proof of a closed certificate")
  KLPArithmetic _ -> Left (invalid "arithmetic proof is valid only as the complete proof of a level certificate")
  KLPMaxLeast leftProof rightProof -> do
    left <- deriveLevelProof context scope assumptions env constraints leftProof
    right <- deriveLevelProof context scope assumptions env constraints rightProof
    let KConstraint leftStrict leftLower leftUpper = left
        KConstraint rightStrict rightLower rightUpper = right
    unless (sameKLevel leftUpper rightUpper) $
      Left (invalid "max-least proof arms have different upper bounds")
    pure (KConstraint (leftStrict || rightStrict) (KLMax leftLower rightLower) leftUpper)
  KLPZero upper -> do
    verifyLevel context scope assumptions env upper
    pure (KConstraint False (KLFinite 0) upper)
  KLPRefl level -> do
    verifyLevel context scope assumptions env level
    pure (KConstraint False level level)
  KLPTrans leftProof rightProof -> do
    left <- deriveLevelProof context scope assumptions env constraints leftProof
    right <- deriveLevelProof context scope assumptions env constraints rightProof
    let KConstraint leftStrict lhs middle = left
        KConstraint rightStrict middle' rhs = right
    unless (sameKLevel middle middle') $
      Left (invalid "transitive level proof has mismatched intermediate levels")
    pure (KConstraint (leftStrict || rightStrict) lhs rhs)
  KLPSuccMono child -> do
    KConstraint strict lhs rhs <- deriveLevelProof context scope assumptions env constraints child
    pure (KConstraint strict (KLSucc lhs) (KLSucc rhs))
  KLPMaxLeft lhs rhs -> do
    verifyLevel context scope assumptions env lhs
    verifyLevel context scope assumptions env rhs
    pure (KConstraint False lhs (KLMax lhs rhs))
  KLPMaxRight lhs rhs -> do
    verifyLevel context scope assumptions env lhs
    verifyLevel context scope assumptions env rhs
    pure (KConstraint False rhs (KLMax lhs rhs))
  KLPAddMonoLeft fixed child -> do
    verifyLevel context scope assumptions env fixed
    KConstraint strict lhs rhs <- deriveLevelProof context scope assumptions env constraints child
    pure (KConstraint strict (KLAdd fixed lhs) (KLAdd fixed rhs))
  KLPAddMonoRight fixed child -> do
    verifyLevel context scope assumptions env fixed
    KConstraint strict lhs rhs <- deriveLevelProof context scope assumptions env constraints child
    pure (KConstraint strict (KLAdd lhs fixed) (KLAdd rhs fixed))

verifyConstraintLevels :: VerifyContext -> Set Int -> Assumptions -> LocalEnv -> KConstraint -> Either KCoreTextError ()
verifyConstraintLevels context scope assumptions env (KConstraint _ lhs rhs) =
  verifyLevel context scope assumptions env lhs >> verifyLevel context scope assumptions env rhs

sameConstraint :: KConstraint -> KConstraint -> Bool
sameConstraint (KConstraint strictA lhsA rhsA) (KConstraint strictB lhsB rhsB) =
  strictA == strictB && sameKLevel lhsA lhsB && sameKLevel rhsA rhsB

constraintProved :: Assumptions -> KConstraint -> Bool
constraintProved assumptions (KConstraint strict lhs rhs) =
  levelProved assumptions (if strict then KLSucc lhs else lhs) rhs

closedConstraint :: KConstraint -> Bool
closedConstraint (KConstraint _ lhs rhs) = closedLevel lhs && closedLevel rhs

closedLevel :: KLevel -> Bool
closedLevel = \case
  KLFinite _ -> True
  KLGlobal ref -> ref == stableRefForGlobal prelTypeLevelOmega
  KLSucc level -> closedLevel level
  KLMax lhs rhs -> closedLevel lhs && closedLevel rhs
  KLAdd lhs rhs -> closedLevel lhs && closedLevel rhs
  _ -> False

levelLeStableRef :: StableRef
levelLeStableRef = stableRefForGlobal (GName (ModuleName ["std", "typelevel"]) "LevelLe")

localEvidenceAssumptions :: Assumptions -> LocalEnv -> Assumptions
localEvidenceAssumptions = Map.foldl' add
  where
    add assumptions = \case
      LocalBinder binder -> case levelAuthorityConstraint binder of
        Just (KConstraint strict lhs rhs) -> case (toLevel lhs, toLevel rhs) of
          (Just lhs', Just rhs') ->
            insertAssumption (if strict then levelSucc lhs' else lhs') rhs' assumptions
          _ -> assumptions
        Nothing -> assumptions
      LocalDefinition {} -> assumptions

-- | The only local authority for rigid level entailment is the ordinary Core
-- proof-binder mechanism from §§11.1.2.2/11.1.2.6: an ordinary, implicit,
-- quantity-zero value binder with ordinary formation. Merely assigning a
-- comparison proposition to an ordinary/runtime binder must not add an
-- assumption or authorize a lift.
levelAuthorityConstraint :: KBinder -> Maybe KConstraint
levelAuthorityConstraint binder
  | kbMode binder == Ordinary
  , kbFormation binder == FormationOrdinary
  , kbQuantity binder == KQ0
  , kbExplicitness binder == KImplicit
  , kbAccess binder == KValue = canonicalLevelConstraint (kbType binder)
  | otherwise = Nothing

canonicalLevelConstraint :: KTerm -> Maybe KConstraint
canonicalLevelConstraint = \case
  KTApply (KTGlobal relation _) [KArgument KExplicit lhs, KArgument KExplicit rhs]
    | relation == levelLeStableRef -> KConstraint False <$> termAsLevel lhs <*> termAsLevel rhs
  _ -> Nothing

termAsLevel :: KTerm -> Maybe KLevel
termAsLevel = \case
  local@KTLocal {} -> Just (KLTerm local)
  KTGeneric "impl.kappa.level-value" [("level", KVLevel level)] -> Just level
  KTGlobal ref []
    | ref == stableRefForGlobal prelTypeLevelZero -> Just (KLFinite 0)
    | ref == stableRefForGlobal prelTypeLevelOmega -> Just (KLGlobal ref)
  KTApply (KTGlobal ref []) [KArgument KExplicit argument]
    | ref == stableRefForGlobal prelTypeLevelSucc -> KLSucc <$> termAsLevel argument
  KTApply (KTGlobal ref []) [KArgument KExplicit lhs, KArgument KExplicit rhs]
    | ref == stableRefForGlobal prelTypeLevelMax -> KLMax <$> termAsLevel lhs <*> termAsLevel rhs
    | ref == stableRefForGlobal prelTypeLevelAdd -> KLAdd <$> termAsLevel lhs <*> termAsLevel rhs
  _ -> Nothing

levelAsTerm :: KLevel -> KTerm
levelAsTerm = \case
  KLTerm term -> term
  KLFinite 0 -> KTGlobal (stableRefForGlobal prelTypeLevelZero) []
  KLGlobal ref -> KTGlobal ref []
  KLSucc level -> KTApply (KTGlobal (stableRefForGlobal prelTypeLevelSucc) []) [KArgument KExplicit (levelAsTerm level)]
  KLMax lhs rhs ->
    KTApply (KTGlobal (stableRefForGlobal prelTypeLevelMax) []) [KArgument KExplicit (levelAsTerm lhs), KArgument KExplicit (levelAsTerm rhs)]
  KLAdd lhs rhs ->
    KTApply (KTGlobal (stableRefForGlobal prelTypeLevelAdd) []) [KArgument KExplicit (levelAsTerm lhs), KArgument KExplicit (levelAsTerm rhs)]
  level -> KTGeneric "impl.kappa.level-value" [("level", KVLevel level)]

constraintAssumptions :: [KConstraint] -> Assumptions
constraintAssumptions = foldl add emptyAssumptions
  where
    add assumptions (KConstraint strict lhs rhs) = case (toLevel lhs, toLevel rhs) of
      (Just lhs', Just rhs') -> insertAssumption (if strict then levelSucc lhs' else lhs') rhs' assumptions
      _ -> assumptions

levelProved :: Assumptions -> KLevel -> KLevel -> Bool
levelProved assumptions lhs rhs = case (toLevel lhs, toLevel rhs) of
  (Just lhs', Just rhs') -> proveLevelLeq assumptions lhs' rhs' == Proved
  _ -> False

toLevel :: KLevel -> Maybe Level
toLevel = \case
  KLFinite n -> Just (finiteLevel n)
  KLGlobal ref | ref == stableRefForGlobal prelTypeLevelOmega -> Just LOmega
  KLUniverse ref -> Just (LParam (urId ref))
  KLSucc level -> levelSucc <$> toLevel level
  KLMax lhs rhs -> levelMax <$> toLevel lhs <*> toLevel rhs
  KLAdd lhs rhs -> levelAdd <$> toLevel lhs <*> toLevel rhs
  KLTerm (KTLocal ref []) -> Just (LVar (lrId ref))
  KLTerm term -> do
    level <- termAsLevel term
    case level of
      KLTerm term' | term' == term -> Nothing
      _ -> toLevel level
  _ -> Nothing

universeScope :: [UniverseRef] -> Set Int
universeScope = Set.fromList . map urId

argumentTerm :: KArgument -> KTerm
argumentTerm (KArgument _ term) = term

declRefs :: KDecl -> [StableRef]
declRefs = \case
  KDDef ref _ _ _ _ -> [ref]
  KDAxiom ref _ _ _ -> [ref]
  KDInterface {} -> []
  KDAssociatedNormalization {} -> []
  KDData ref _ _ _ _ constructors -> ref : [ctor | KCtorDecl ctor _ _ _ <- constructors]
  KDLevelCertificate ref _ _ _ _ -> [ref]
  KDRepresentationCertificate certificate -> [krcRef certificate]
  KDSchemaCertificate certificate -> [kscRef certificate]
  KDTermProbe _ -> []
  KDExtension _ _ -> []
  KDGeneric _ _ -> []

moduleDeclarationArities :: KModule -> [(StableRef, Int)]
moduleDeclarationArities KModule {..} = concatMap declArities kmDecls
  where
    declArities = \case
      KDDef ref _ universes _ _ -> [(ref, length universes)]
      KDAxiom ref _ universes _ -> [(ref, length universes)]
      KDInterface {} -> []
      KDAssociatedNormalization {} -> []
      KDData ref universes _ _ _ constructors ->
        (ref, length universes) : [(ctor, length ctorUniverses) | KCtorDecl ctor ctorUniverses _ _ <- constructors]
      KDLevelCertificate {} -> []
      KDRepresentationCertificate {} -> []
      KDSchemaCertificate {} -> []
      KDTermProbe {} -> []
      KDExtension {} -> []
      KDGeneric _ _ -> []

moduleDeclarationTypes :: KModule -> [(StableRef, ([UniverseRef], KTerm))]
moduleDeclarationTypes KModule {..} = concatMap declTypes kmDecls
  where
    declTypes = \case
      KDDef ref _ universes ty _ -> [(ref, (universes, ty))]
      KDAxiom ref _ universes ty -> [(ref, (universes, ty))]
      KDInterface {} -> []
      KDAssociatedNormalization {} -> []
      KDData ref universes binders result _ constructors ->
        (ref, (map fst universes, foldr KTPi result binders))
          : [(ctor, (ctorUniverses, ty)) | KCtorDecl ctor ctorUniverses _ ty <- constructors]
      KDLevelCertificate {} -> []
      KDRepresentationCertificate {} -> []
      KDSchemaCertificate {} -> []
      KDTermProbe {} -> []
      KDExtension {} -> []
      KDGeneric _ _ -> []

moduleDeclarationModes :: KModule -> [(StableRef, ObservationMode)]
moduleDeclarationModes KModule {..} = concatMap declModes kmDecls
  where
    declModes = \case
      KDDef ref mode _ _ _ -> [(ref, mode)]
      KDAxiom ref mode _ _ -> [(ref, mode)]
      KDInterface {} -> []
      KDAssociatedNormalization {} -> []
      KDData ref _ _ _ _ constructors ->
        (ref, Ordinary) : [(constructor, Ordinary) | KCtorDecl constructor _ _ _ <- constructors]
      KDLevelCertificate {} -> []
      KDRepresentationCertificate {} -> []
      KDSchemaCertificate {} -> []
      KDTermProbe {} -> []
      KDExtension {} -> []
      KDGeneric _ _ -> []

moduleConstructorTypes :: KModule -> [(StableRef, ([UniverseRef], [KBinder], KTerm))]
moduleConstructorTypes KModule {..} = concatMap constructors kmDecls
  where
    constructors = \case
      KDData _ _ parameters _ _ declarations ->
        [ (ref, (universes, parameters, ty))
        | KCtorDecl ref universes _ ty <- declarations
        ]
      _ -> []

moduleDeclarationBodies :: KModule -> [(StableRef, ([UniverseRef], KTerm))]
moduleDeclarationBodies KModule {..} = concatMap declBodies kmDecls
  where
    declBodies = \case
      KDDef ref _ universes _ body
        | not (isUnavailableBody body) -> [(ref, (universes, body))]
      _ -> []

moduleRecordInterfaces :: KModule -> [(StableRef, ([UniverseRef], KTerm))]
moduleRecordInterfaces KModule {..} =
  [ (ref, (universes, ty))
  | KDInterface ref universes ty <- kmDecls
  ]

moduleAssociatedNormalizations
  :: KModule
  -> [(KAssociatedNormalizationKey, KAssociatedNormalization)]
moduleAssociatedNormalizations KModule {..} =
  [ (associatedNormalizationKey normalization, normalization)
  | KDAssociatedNormalization normalization <- kmDecls
  ]

interfaceFromVerifiedKCore :: KCoreFile -> KCoreInterface
interfaceFromVerifiedKCore (KCoreFile _ modules) =
  KCoreInterface
    { kciTypes = Map.fromList (concatMap moduleDeclarationTypes modules)
    , kciModes = Map.fromList (concatMap moduleDeclarationModes modules)
    , kciBodies = Map.fromList (concatMap moduleDeclarationBodies modules)
    , kciRecordInterfaces = Map.fromList (concatMap moduleRecordInterfaces modules)
    , kciAssociatedNormalizations =
        Map.fromList (concatMap moduleAssociatedNormalizations modules)
    , kciConstructors = Map.fromList (concatMap moduleConstructorTypes modules)
    , kciLevelCertificates =
        Map.fromList
          [ (ref, (universes, constraints, theorem, proof))
          | KModule {kmDecls = declarations} <- modules
          , KDLevelCertificate ref universes constraints theorem proof <- declarations
          ]
    , kciRepresentationCertificates =
        Map.fromList
          [ (krcRef certificate, certificate)
          | KModule {kmDecls = declarations} <- modules
          , KDRepresentationCertificate certificate <- declarations
          ]
    , kciSchemaCertificates =
        Map.fromList
          [ (kscRef certificate, certificate)
          | KModule {kmDecls = declarations} <- modules
          , KDSchemaCertificate certificate <- declarations
          ]
    , kciNominalFamilies =
        Map.fromList
          [ (ref, KNominalFamily universes binders result certificate constructors)
          | KModule {kmDecls = declarations} <- modules
          , KDData ref universes binders result certificate constructors <- declarations
          ]
    }

mergeKCoreInterfaces :: [KCoreInterface] -> Either KCoreTextError KCoreInterface
mergeKCoreInterfaces = foldM merge emptyKCoreInterface
  where
    merge left right =
      KCoreInterface
        <$> mergeMap "global type" (kciTypes left) (kciTypes right)
        <*> mergeMap "observation mode" (kciModes left) (kciModes right)
        <*> mergeMap "transparent body" (kciBodies left) (kciBodies right)
        <*> mergeMap "record interface" (kciRecordInterfaces left) (kciRecordInterfaces right)
        <*> mergeAssociated
          (kciAssociatedNormalizations left)
          (kciAssociatedNormalizations right)
        <*> mergeMap "constructor interface" (kciConstructors left) (kciConstructors right)
        <*> mergeMap "level certificate" (kciLevelCertificates left) (kciLevelCertificates right)
        <*> mergeMap
          "representation certificate"
          (kciRepresentationCertificates left)
          (kciRepresentationCertificates right)
        <*> mergeMap "schema certificate" (kciSchemaCertificates left) (kciSchemaCertificates right)
        <*> mergeMap "nominal family" (kciNominalFamilies left) (kciNominalFamilies right)
    mergeMap label left right
      | Set.null overlap = pure (Map.union left right)
      | otherwise =
          Left
            ( invalid
                ( "imported KCore interfaces contain duplicate "
                    <> label
                    <> " identity "
                    <> T.intercalate ", " (map renderStable (Set.toAscList overlap))
                )
            )
      where
        overlap = Set.intersection (Map.keysSet left) (Map.keysSet right)
    mergeAssociated left right
      | Set.null overlap = pure (Map.union left right)
      | otherwise =
          Left
            ( invalid
                ( "imported KCore interfaces contain duplicate associated normalization identity "
                    <> T.intercalate
                      ", "
                      [ renderStable dictionary <> "." <> renderFieldRef field
                      | (dictionary, field) <- Set.toAscList overlap
                      ]
                )
            )
      where
        overlap = Set.intersection (Map.keysSet left) (Map.keysSet right)

emptyKCoreInterface :: KCoreInterface
emptyKCoreInterface =
  KCoreInterface
    Map.empty
    Map.empty
    Map.empty
    Map.empty
    Map.empty
    Map.empty
    Map.empty
    Map.empty
    Map.empty
    Map.empty

isUnavailableBody :: KTerm -> Bool
isUnavailableBody = \case
  KTGeneric "impl.kappa.core.body-unavailable" _ -> True
  _ -> False

ktermHasRecordInterface :: KTerm -> Bool
ktermHasRecordInterface = \case
  KTLambda _ body -> ktermHasRecordInterface body
  KTLift _ _ _ body -> ktermHasRecordInterface body
  KTSchemaLift _ _ _ _ _ _ body -> ktermHasRecordInterface body
  KTAscribe body _ -> ktermHasRecordInterface body
  KTRecordType {} -> True
  KTGeneric "impl.kappa.core.record-type" fields ->
    case decodeBuiltinTermNode "impl.kappa.core.record-type" fields of
      Right KTRecordType {} -> True
      _ -> False
  _ -> False

-- Keep the source-side selection in lockstep with
-- 'ktermHasRecordInterface'.  This predicate selects checked values that are
-- semantic record interfaces; it does not try to recognize records by a
-- declaration name or by inspecting an arbitrary runtime value.
coreTermHasRecordInterface :: Term -> Bool
coreTermHasRecordInterface = \case
  CLamM _ _ _ _ body -> coreTermHasRecordInterface body
  CUniverseLift _ _ _ body -> coreTermHasRecordInterface body
  CSchemaLift _ _ _ _ _ _ _ _ body -> coreTermHasRecordInterface body
  CRecordTQ {} -> True
  _ -> False

-- Checked instance dictionaries are lambda telescopes ending in a record
-- value. Their ordinary method bodies remain private; this predicate merely
-- selects candidates from which erased parametric field equations can be
-- extracted and independently replayed.
coreTermHasDictionaryValue :: Term -> Bool
coreTermHasDictionaryValue = \case
  CLamM _ _ _ _ body -> coreTermHasDictionaryValue body
  CUniverseLift _ _ _ body -> coreTermHasDictionaryValue body
  CSchemaLift _ _ _ _ _ _ _ _ body -> coreTermHasDictionaryValue body
  CRecordV {} -> True
  _ -> False

-- Extension declarations select an already-installed verifier; they never
-- register arbitrary semantics supplied by the untrusted file. The example
-- verifier is intentionally payload-agnostic and exists only for the
-- canonical extension round-trip contract in the unit suite.
supportedExtensionVersions :: Map Text (Set Integer)
supportedExtensionVersions =
  Map.fromList
    [ ("impl.kappa", Set.singleton 1)
    , ("example.vendor", Set.singleton 1)
    , ("nominal-mutual-signatures", Set.singleton 1)
    ]

extensionOwnsTag :: Set Text -> Text -> Bool
extensionOwnsTag extensions tag =
  case
      [ owner
      | owner <- Set.toList extensions
      , owner `Map.member` supportedExtensionVersions
      , tag == owner
          || (owner <> ".") `T.isPrefixOf` tag
          || (owner == "nominal-mutual-signatures" && tag == "mutual-nominal-signature")
      ]
    of
      [_] -> True
      _ -> False

genericResultType :: Text -> [(Text, KValueNode)] -> Maybe KTerm
genericResultType tag fields
  | tag `Set.member` typedImplGenericTags = case [term | ("result-type", KVTerm term) <- fields] of
      [term] -> Just term
      _ -> Nothing
  | otherwise = Nothing

-- | Replay the typing rule of every implementation-owned generic node whose
-- serialized @result-type@ can otherwise become untrusted typing authority.
-- Schema validation proves only field shape; this function proves that the
-- payload actually constructs the declared result.
verifyImplGenericSemantics
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> Text
  -> [(Text, KValueNode)]
  -> Either KCoreTextError ()
verifyImplGenericSemantics context universes assumptions env tag fields =
  case tag of
    "impl.kappa.core.arithmetic-proof" ->
      verifyArithmeticCertificate context universes assumptions env fields
    "impl.kappa.core.variant-type" -> verifyVariantType
    "impl.kappa.core.signature-type" -> verifySignatureType
    "impl.kappa.core.inject" -> do
      resultType <- requiredResultType
      payload <- requiredTerm "value"
      memberType <- variantMember resultType =<< requiredText "tag"
      checkTerm context universes assumptions env payload memberType
    "impl.kappa.core.seal" -> do
      resultType <- requiredResultType
      payload <- requiredTerm "value"
      labels <- requiredTexts "labels"
      (expectedLabels, payloadType) <- signatureView resultType
      unless (labels == expectedLabels) $
        Left (invalid "sealed package labels do not match its declared signature type")
      checkTerm context universes assumptions env payload payloadType
    "impl.kappa.core.thunk" -> verifySuspension prelThunk
    "impl.kappa.core.lazy" -> verifySuspension prelNeed
    "impl.kappa.core.quote" -> verifyQuote
    "impl.kappa.core.force" -> do
      resultType <- requiredResultType
      value <- requiredTerm "value"
      valueType <- inferSimple context universes assumptions env value >>= maybe
        (Left (invalid "force payload type cannot be inferred"))
        pure
      payloadType <-
        maybe
          (Left (invalid "force payload is not a Thunk or Need value"))
          pure
          (unaryTypeApplication prelThunk valueType <|> unaryTypeApplication prelNeed valueType)
      unless (sameKCoreTypeUnderIn assumptions env context payloadType resultType) $
        Left (invalid "force result-type does not match its suspension payload type")
    -- The do and intrinsic effect-tree nodes have dedicated complete replay
    -- above. Untyped implementation nodes do not claim a result type.
    _
      | tag == "impl.kappa.core.do" || tag == intrinsicEffectTreeTag -> pure ()
      | tag `Set.member` typedImplGenericTags ->
          Left (invalid ("typed generic node '" <> tag <> "' has no semantic verifier"))
      | otherwise -> pure ()
  where
    requiredResultType = requiredTerm "result-type"

    requiredTerm name = case lookup name fields of
      Just (KVTerm term) -> pure term
      _ -> Left (invalid ("generic node field '" <> name <> "' must be a term value"))

    requiredValue name =
      maybe (Left (invalid ("generic node is missing field '" <> name <> "'"))) pure (lookup name fields)

    requiredList name = case lookup name fields of
      Just (KVList values) -> pure values
      _ -> Left (invalid ("generic node field '" <> name <> "' must be a list"))

    requiredText name = case lookup name fields of
      Just (KVText value) -> pure value
      _ -> Left (invalid ("generic node field '" <> name <> "' must be text"))

    requiredTexts name = case lookup name fields of
      Just (KVList values) -> mapM (\case KVText value -> pure value; _ -> Left (invalid ("generic node field '" <> name <> "' must contain only text"))) values
      _ -> Left (invalid ("generic node field '" <> name <> "' must be a text list"))

    requiredTerms name = case lookup name fields of
      Just (KVList values) -> mapM (\case KVTerm value -> pure value; _ -> Left (invalid ("generic node field '" <> name <> "' must contain only terms"))) values
      _ -> Left (invalid ("generic node field '" <> name <> "' must be a term list"))

    verifySuspension constructor = do
      resultType <- requiredResultType
      payload <- requiredTerm "value"
      payloadType <- maybe
        (Left (invalid "suspension result-type has the wrong semantic constructor"))
        pure
        (unaryTypeApplication constructor resultType)
      checkTerm context universes assumptions env payload payloadType

    verifyQuote = do
      resultType <- requiredResultType
      unless (maybe False (const True) (unaryTypeApplication prelSyntax resultType)) $
        Left (invalid "syntax quote result-type is not a Syntax application")
      syntaxValue <- requiredValue "syntax"
      expression <- decodeSyntaxData syntaxValue :: Either KCoreTextError Expr
      originValue <- requiredValue "origin"
      _ <- decodeSyntaxData originValue :: Either KCoreTextError Span
      captures <- requiredList "captures"
      captureEntries <- forM captures $ \case
        KVList [KVText hygienic, KVText original, KVLocal ref levels]
          | not (T.null hygienic) && not (T.null original) -> do
              verifyValue context universes assumptions env (KVLocal ref levels)
              pure (hygienic, original, ref)
        _ -> Left (invalid "syntax quote capture must contain hygienic/original names and one local identity")
      let captureRefs = [ref | (_, _, ref) <- captureEntries]
          hygienicNames = [hygienic | (hygienic, _, _) <- captureEntries]
          originalNames = [original | (_, original, _) <- captureEntries]
          bound = Set.fromList (boundNamesIn expression)
          freeNames =
            Set.fromList
              [ nameText occurrence
              | occurrence <- freeVarOccurrences expression
              , nameText occurrence `Set.notMember` bound
              ]
      unless (length captureRefs == Set.size (Set.fromList captureRefs)) $
        Left (invalid "syntax quote captures the same local identity more than once")
      unless
        ( length hygienicNames == Set.size (Set.fromList hygienicNames)
            && length originalNames == Set.size (Set.fromList originalNames)
            && all (`Set.member` freeNames) hygienicNames
        ) $
        Left (invalid "syntax quote capture names do not match its hygienic free occurrences")
      slots <- requiredTerms "slots"
      forM_ slots $ \slot -> do
        slotType <- inferSimple context universes assumptions env slot >>= maybe
          (Left (invalid "syntax quote splice-slot type cannot be inferred"))
          pure
        unless (maybe False (const True) (unaryTypeApplication prelSyntax slotType)) $
          Left (invalid "syntax quote splice slot is not a Syntax value")
      let holes = sort (queryExprs (\case EQuoteHole index _ -> ([index], False); _ -> ([], True)) expression)
      unless (holes == [0 .. length slots - 1]) $
        Left (invalid "syntax quote holes and serialized splice slots are not one-to-one")

    unaryTypeApplication constructor ty =
      case unfoldTypeHead context ty of
        KTApply (KTGlobal ref _) [KArgument KExplicit payload]
          | ref == stableRefForGlobal constructor -> Just payload
        _ -> Nothing

    verifyVariantType = do
      tags <- requiredTexts "tags"
      members <- requiredTerms "members"
      unless (length tags == length members && length tags == Set.size (Set.fromList tags)) $
        Left (invalid "variant type tags must be unique and correspond one-for-one with members")
      forM_ members $ \member ->
        inferSimple context universes assumptions env member >>= \case
          Just KTType {} -> pure ()
          _ -> Left (invalid "variant member must itself have a universe classifier")

    variantMember resultType tag =
      case unfoldTypeHead context resultType of
        KTGeneric "impl.kappa.core.variant-type" resultFields -> do
          tags <- valuesText "tags" resultFields
          members <- valuesTerm "members" resultFields
          unless (length tags == length members && length tags == Set.size (Set.fromList tags)) $
            Left (invalid "injection result has a malformed variant interface")
          maybe (Left (invalid "injection tag is absent from its result variant")) pure (lookup tag (zip tags members))
        _ -> Left (invalid "injection result-type is not a variant type")

    verifySignatureType = do
      labels <- requiredTexts "labels"
      _ <- requiredTerm "value"
      unless (length labels == Set.size (Set.fromList labels)) $
        Left (invalid "signature labels must be unique")

    signatureView resultType =
      case unfoldTypeHead context resultType of
        KTGeneric "impl.kappa.core.signature-type" resultFields -> do
          labels <- valuesText "labels" resultFields
          payloadType <- valueTerm "value" resultFields
          unless (length labels == Set.size (Set.fromList labels)) $
            Left (invalid "signature labels must be unique")
          pure (labels, payloadType)
        _ -> Left (invalid "sealed package result-type is not a signature type")

    valuesText name values = case lookup name values of
      Just (KVList entries) -> mapM (\case KVText value -> pure value; _ -> Left (invalid "malformed text list in generic type interface")) entries
      _ -> Left (invalid ("generic type interface is missing '" <> name <> "'"))

    valuesTerm name values = case lookup name values of
      Just (KVList entries) -> mapM (\case KVTerm value -> pure value; _ -> Left (invalid "malformed term list in generic type interface")) entries
      _ -> Left (invalid ("generic type interface is missing '" <> name <> "'"))

    valueTerm name values = case lookup name values of
      Just (KVTerm value) -> pure value
      _ -> Left (invalid ("generic type interface is missing term field '" <> name <> "'"))

arithmeticDomainField :: [(Text, KValueNode)] -> Maybe ArithmeticDomain
arithmeticDomainField fields =
  case lookup "domain" fields of
    Just (KVText "Natural") -> Just ArithmeticNatural
    Just (KVText "Integer") -> Just ArithmeticInteger
    Just (KVText "TypeLevel") -> Just ArithmeticTypeLevel
    Just (KVText "ProviderLaw") -> Just ArithmeticProviderLaw
    _ -> Nothing

verifyArithmeticCertificate
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> [(Text, KValueNode)]
  -> Either KCoreTextError ()
verifyArithmeticCertificate context universes assumptions env fields =
  mapLeftArithmetic $ do
    version <- case lookup "version" fields of
      Just (KVInteger value) -> pure value
      _ -> invalidArithmetic "certificate version must be an integer"
    unless (version == 2) $
      invalidArithmetic "certificate version is unsupported"
    domain <-
      maybe
        (invalidArithmetic "certificate arithmetic domain is unsupported")
        pure
        (arithmeticDomainField fields)
    providers <- requiredList "providers" >>= mapM verifyProvider
    unless (providers == sort providers && length providers == Set.size (Set.fromList providers)) $
      invalidArithmetic "provider evidence must be unique and canonically ordered"
    variableEntries <- requiredList "variables" >>= mapM verifyArithmeticVariable
    let variableIdentities = map fst variableEntries
    unless
      ( variableIdentities == sort variableIdentities
          && length variableIdentities == Set.size (Set.fromList variableIdentities)
      ) $
      invalidArithmetic "arithmetic-variable identities must be unique and canonically ordered"
    goalTerm <- requiredTerm "result-type"
    replayGoalTerm <- requiredTerm "replay-goal"
    let providerEvidence =
          [(kapTrait provider, kapEvidence provider) | provider <- providers]
    verifyTerm context universes assumptions env goalTerm
    verifyTerm context universes assumptions env replayGoalTerm
    unless
      ( arithmeticReplayPropositionMatches
          context
          assumptions
          env
          providerEvidence
          domain
          goalTerm
          replayGoalTerm
      ) $
      invalidArithmetic
        ( "certificate replay goal is not definitionally equal to its checked result type"
            <> "\nchecked-normal: "
            <> printTerm (unfoldTypeHeadWithLocals context env goalTerm)
            <> "\nreplay-normal: "
            <> printTerm (unfoldTypeHeadWithLocals context env replayGoalTerm)
            <> "\nchecked-arithmetic: "
            <> T.pack
              ( show
                  ( arithmeticFormulaFromCheckedKTerm
                      context
                      env
                      providerEvidence
                      domain
                      goalTerm
                  )
              )
            <> "\nchecked-transparent-head: "
            <> maybe
              "<no checked transparent reduction>"
              printTerm
              ( do
                  condition <- booleanEqualityPayload goalTerm
                  unfoldTransparentKApplication context env condition
              )
            <> "\nreplay-arithmetic: "
            <> T.pack
              (show (arithmeticFormulaFromKTerm domain replayGoalTerm))
            <> "\nchecked-arithmetic-operands: "
            <> arithmeticCheckedOperandDebug context env goalTerm
        )
    replayNode <- case lookup "replay" fields of
      Just encoded -> pure encoded
      Nothing -> invalidArithmetic "certificate replay is missing"
    case domain of
      ArithmeticTypeLevel -> do
        unless (null variableEntries) $
          invalidArithmetic "TypeLevel certificates cannot declare value-arithmetic variables"
        assumptionEntries <-
          requiredList "assumptions"
            >>= mapM
              ( decodeTypeLevelAssumption
                  [(kapTrait provider, kapEvidence provider) | provider <- providers]
              )
        unless (map fst assumptionEntries == sort (map fst assumptionEntries)) $
          invalidArithmetic "arithmetic assumptions must be canonically ordered"
        expectedReplay <- maybe
          (invalidArithmetic "TypeLevel certificate goal is not derivable from its recorded assumptions")
          pure
          ( deriveTypeLevelReplay
              [(kapTrait provider, kapEvidence provider) | provider <- providers]
              (map snd assumptionEntries)
              replayGoalTerm
          )
        unless (replayNode == expectedReplay) $
          invalidArithmetic "TypeLevel certificate replay does not match the independently derived goal"
      ArithmeticProviderLaw -> do
        unless (null variableEntries) $
          invalidArithmetic "provider-law certificates cannot declare value-arithmetic variables"
        provider <- case providers of
          [selected@KArithmeticProvider {kapIdentity = Just _, kapTheory = Just _, kapLaw = Just _}] ->
            pure selected
          _ ->
            invalidArithmetic
              "provider-law certificate must select exactly one normalization-provider artifact"
        law <- maybe
          (invalidArithmetic "provider-law certificate is missing its law identity")
          pure
          (kapLaw provider)
        proof <-
          requiredList "assumptions" >>= \case
            [entry] ->
              verifyProviderLawAssumption provider goalTerm entry
            _ ->
              invalidArithmetic
                "provider-law certificate must contain exactly one checked law proof"
        unless (kTermHeadGlobal (fst (collectKApplication proof)) == Just law) $
          invalidArithmetic "provider-law proof is not headed by the recorded law identity"
        let proofArguments =
              [ argument
              | KArgument _ argument <- snd (collectKApplication proof)
              ]
        unless (kapEvidence provider `elem` proofArguments) $
          invalidArithmetic "provider-law proof does not use the selected evidence closure"
        providerIdentity <- maybe
          (invalidArithmetic "provider-law certificate is missing its provider identity")
          pure
          (kapIdentity provider)
        let expectedReplay =
              KVList
                [ KVText "provider-law"
                , KVText (srName providerIdentity)
                , KVText (srId providerIdentity)
                , KVTerm proof
                ]
        unless (replayNode == expectedReplay) $
          invalidArithmetic "provider-law replay does not match its checked provider proof"
      _ -> do
        assumptionEntries <-
          requiredList "assumptions"
            >>= mapM (decodeAssumption providerEvidence domain)
        unless (assumptionEntries == sort assumptionEntries) $
          invalidArithmetic "arithmetic assumptions must be canonically ordered"
        goal <- maybe
          (invalidArithmetic "certificate goal is outside the authenticated arithmetic fragment")
          pure
          (arithmeticFormulaFromKTerm domain replayGoalTerm)
        let variableContext =
              Map.fromList (zip variableIdentities [0 ..])
            canonicalNaturalSet =
              Set.fromList
                [ index
                | (index, (_, kind)) <- zip [0 ..] variableEntries
                , kind == ArithmeticVariableNatural
                ]
        canonicalGoal <- maybe
          (invalidArithmetic "certificate goal refers to a variable outside its recorded context")
          pure
          (reindexArithmeticFormula variableContext goal)
        canonicalAssumptions <- maybe
          (invalidArithmetic "certificate assumption refers to a variable outside its recorded context")
          pure
          ( traverse
              (\(truth, formula) ->
                (truth,) <$> reindexArithmeticFormula variableContext formula)
              (map snd assumptionEntries)
          )
        replay <- decodeArithmeticFormulaReplay replayNode
        semantics <- maybe
          (invalidArithmetic "TypeLevel certificate reached the value-arithmetic replay path")
          pure
          (arithmeticReplaySemantics domain)
        let derivedReplay =
              deriveArithmeticFormulaReplayWithAssumptions
                semantics
                canonicalNaturalSet
                canonicalAssumptions
                True
                canonicalGoal
        unless (derivedReplay == Just replay) $
          invalidArithmetic
            ( "certificate replay does not independently derive from its context and goal"
                <> "; goal="
                <> T.pack (show canonicalGoal)
                <> "; assumptions="
                <> T.pack (show canonicalAssumptions)
                <> "; expected="
                <> T.pack (show derivedReplay)
                <> "; encoded="
                <> T.pack (show replay)
            )
  where
    invalidArithmetic = Left . arithmeticCertificateInvalid
    mapLeftArithmetic =
      either
        (Left . arithmeticCertificateInvalid . kcteMessage)
        Right

    requiredList name = case lookup name fields of
      Just (KVList values) -> pure values
      _ -> invalidArithmetic ("certificate field '" <> name <> "' must be a list")

    requiredTerm name = case lookup name fields of
      Just (KVTerm term) -> pure term
      _ -> invalidArithmetic ("certificate field '" <> name <> "' must be a term")

    verifyProvider = \case
      KVList [KVText readable, KVText identity, KVTerm evidence] -> do
        let trait = StableRef readable identity
        unless (trait `Map.member` vcGlobalArities context) $
          invalidArithmetic "provider trait identity is unavailable"
        verifyTerm context universes assumptions env evidence
        evidenceType <- inferSimple context universes assumptions env evidence >>= maybe
          (invalidArithmetic "provider evidence type cannot be inferred")
          pure
        unless (kTermHeadGlobal (unfoldTypeHead context evidenceType) == Just trait) $
          invalidArithmetic "provider evidence does not implement its recorded trait identity"
        pure
          KArithmeticProvider
            { kapIdentity = Nothing
            , kapTheory = Nothing
            , kapTrait = trait
            , kapLaw = Nothing
            , kapNormalFormVersion = Nothing
            , kapProviderVersion = Nothing
            , kapCheckerVersion = Nothing
            , kapEvidence = evidence
            }
      KVList
        [ KVText "normalization"
        , KVText providerReadable
        , KVText providerIdentity
        , KVText theoryName
        , KVText traitReadable
        , KVText traitIdentity
        , KVText lawReadable
        , KVText lawIdentity
        , KVInteger normalFormVersion
        , KVInteger providerVersion
        , KVInteger checkerVersion
        , KVTerm evidence
        ] -> do
          theory <- case theoryName of
            "Monoid" -> pure ArithmeticMonoid
            "CommutativeMonoid" -> pure ArithmeticCommutativeMonoid
            _ -> invalidArithmetic "normalization provider has an unsupported theory kind"
          let providerRef = StableRef providerReadable providerIdentity
              trait = StableRef traitReadable traitIdentity
              law = StableRef lawReadable lawIdentity
              provider =
                KArithmeticProvider
                  { kapIdentity = Just providerRef
                  , kapTheory = Just theory
                  , kapTrait = trait
                  , kapLaw = Just law
                  , kapNormalFormVersion = Just normalFormVersion
                  , kapProviderVersion = Just providerVersion
                  , kapCheckerVersion = Just checkerVersion
                  , kapEvidence = evidence
                  }
          unless (provider `elem` standardNormalizationProviders evidence) $
            invalidArithmetic
              "normalization provider descriptor does not match an authenticated standard artifact"
          verifyTerm context universes assumptions env evidence
          evidenceType <- inferSimple context universes assumptions env evidence >>= maybe
            (invalidArithmetic "provider evidence type cannot be inferred")
            pure
          unless (kTermHeadGlobal (unfoldTypeHead context evidenceType) == Just trait) $
            invalidArithmetic "provider evidence does not implement its recorded trait identity"
          pure provider
      _ -> invalidArithmetic "provider entry must contain a stable trait identity and evidence term"

    verifyProviderLawAssumption provider goal = \case
      KVList
        [ KVInteger 1
        , KVTerm proposition
        , KVTerm replayProposition
        , KVList [KVText "proof", KVTerm sourceProposition, KVTerm evidence]
        ] -> do
          unless
            ( replayProposition == goal
                && sourceProposition == proposition
            ) $
            invalidArithmetic "provider-law proof has a different proposition"
          verifyTerm context universes assumptions env proposition
          mapLeftArithmetic
            (checkTermObserved Parametric context universes assumptions env evidence proposition)
          unless
            ( providerLawReplayMatches
                context
                assumptions
                env
                provider
                evidence
                proposition
                replayProposition
            ) $
            invalidArithmetic
              ( "provider-law replay proposition is not the authenticated normalization of its checked law"
                  <> "\nchecked-law: "
                  <> printTerm proposition
                  <> "\nreplay-goal: "
                  <> printTerm replayProposition
              )
          pure evidence
      _ ->
        invalidArithmetic
          "provider-law assumption must be one positive proof of the declared goal"

    verifyArithmeticVariable = \case
      KVList [KVText kindName, KVTerm term] -> case stripArithmeticTermWrappers term of
        KTLocal ref [] -> do
          kind <- case kindName of
            "Natural" -> pure ArithmeticVariableNatural
            "Integer" -> pure ArithmeticVariableInteger
            _ -> invalidArithmetic "arithmetic variable has an unknown carrier kind"
          verifyTerm context universes assumptions env term
          inferred <- inferSimple context universes assumptions env term >>= maybe
            (invalidArithmetic "arithmetic variable type cannot be inferred")
            pure
          let expectedTypes = case kind of
                ArithmeticVariableNatural ->
                  [KTGlobal (stableRefForGlobal prelNat) []]
                ArithmeticVariableInteger ->
                  [ KTGlobal (stableRefForGlobal prelInteger) []
                  , KTGlobal (stableRefForGlobal prelInt) []
                  ]
          unless
            (any (sameKCoreTypeUnderIn assumptions env context inferred) expectedTypes) $
            invalidArithmetic "arithmetic variable carrier disagrees with its recorded kind"
          pure (lrId ref, kind)
        _ -> invalidArithmetic "arithmetic-variable entry must be a monomorphic local identity"
      _ -> invalidArithmetic "arithmetic-variable entry must contain a carrier kind and local term"

    decodeAssumption providerEvidence domain = \case
      KVList [KVInteger polarity, KVTerm proposition, KVTerm replayProposition, source]
        | polarity == 0 || polarity == 1 -> do
            verifyTerm context universes assumptions env proposition
            verifyTerm context universes assumptions env replayProposition
            unless
              ( arithmeticReplayPropositionMatches
                  context
                  assumptions
                  env
                  providerEvidence
                  domain
                  proposition
                  replayProposition
              ) $
              invalidArithmetic
                ( "arithmetic assumption replay proposition is not definitionally equal to its checked proposition"
                    <> "\nchecked-proposition: "
                    <> printTerm proposition
                    <> "\nreplay-proposition: "
                    <> printTerm replayProposition
                    <> "\nchecked-arithmetic: "
                    <> T.pack
                      ( show
                          ( arithmeticFormulaFromCheckedKTerm
                              context
                              env
                              providerEvidence
                              domain
                              proposition
                          )
                      )
                    <> "\nreplay-arithmetic: "
                    <> T.pack
                      (show (arithmeticFormulaFromKTerm domain replayProposition))
                )
            verifyAssumptionSource
              providerEvidence
              domain
              (polarity == 1)
              proposition
              source
            formula <- maybe
              (invalidArithmetic "arithmetic assumption is outside the authenticated fragment")
              pure
              (arithmeticFormulaFromKTerm domain replayProposition)
            pure
              ( (polarity, proposition, replayProposition)
              , (polarity == 1, formula)
              )
      _ ->
        invalidArithmetic
          "arithmetic assumption must contain a Boolean polarity, proposition, and checked source"

    decodeTypeLevelAssumption providers = \case
      KVList [KVInteger polarity, KVTerm proposition, KVTerm replayProposition, source]
        | polarity == 0 || polarity == 1 -> do
            verifyTerm context universes assumptions env proposition
            verifyTerm context universes assumptions env replayProposition
            unless
              (sameKCoreTypeUnderIn assumptions env context proposition replayProposition) $
              invalidArithmetic
                "TypeLevel assumption replay proposition is not definitionally equal to its checked proposition"
            verifyAssumptionSource
              providers
              ArithmeticTypeLevel
              (polarity == 1)
              proposition
              source
            constraint <- maybe
              (invalidArithmetic "TypeLevel assumption is outside the authenticated comparison fragment")
              pure
              (typeLevelAssumptionConstraint providers (polarity == 1) replayProposition)
            pure ((polarity, proposition, replayProposition), constraint)
      _ ->
        invalidArithmetic
          "arithmetic assumption must contain a Boolean polarity, proposition, and checked source"

    verifyAssumptionSource providerEvidence domain truth proposition = \case
      KVList [KVText "proof", KVTerm sourceProposition, KVTerm evidence] -> do
        unless truth $
          invalidArithmetic "a proof-backed arithmetic assumption cannot assert a false proposition"
        verifyTerm context universes assumptions env sourceProposition
        unless (sourceProposition == proposition) $
          invalidArithmetic "arithmetic assumption proof has a different proposition"
        verifyArithmeticEvidence
          providerEvidence
          domain
          sourceProposition
          evidence
      KVList [KVText "conversion", KVTerm sourceProposition] -> do
        unless truth $
          invalidArithmetic "a conversion-backed arithmetic assumption cannot assert a false proposition"
        verifyTerm context universes assumptions env sourceProposition
        unless (sourceProposition == proposition) $
          invalidArithmetic "arithmetic conversion source has a different proposition"
        (_, lhs, rhs) <- maybe
          (invalidArithmetic "arithmetic conversion source is not ordinary equality")
          pure
          (equalityOperands sourceProposition)
        unless (sameKCoreTypeUnderIn assumptions env context lhs rhs) $
          invalidArithmetic
            "arithmetic conversion source endpoints are not definitionally equal in the verified branch environment"
      KVList [KVText "branch", KVInteger branchPolarity, KVTerm condition]
        | branchPolarity == 0 || branchPolarity == 1 -> do
            checkBooleanTerm context universes assumptions env condition
            let branchTruth = branchPolarity == 1
            unless (branchTruth == truth) $
              invalidArithmetic "arithmetic branch source polarity disagrees with its assumption"
            unless (branchFactAvailable context env branchTruth condition) $
              invalidArithmetic
                ( "arithmetic branch source is not in scope at this certificate"
                    <> "\nrecorded-branch-source: "
                    <> printTerm condition
                    <> "\nactive-branch-facts: "
                    <> T.intercalate
                      "\n"
                      [ (if activeTruth then "true: " else "false: ")
                          <> printTerm activeCondition
                      | (activeTruth, activeCondition) <-
                          vcArithmeticBranchFacts context
                      ]
                )
            payload <- maybe
              (invalidArithmetic "arithmetic branch source does not establish a Boolean proposition")
              pure
              (booleanEqualityPayload proposition)
            unless
              (sameKCoreTypeUnderIn assumptions env context payload condition) $
              invalidArithmetic
                "arithmetic branch source is not definitionally equal to its recorded proposition"
      _ -> invalidArithmetic "arithmetic assumption source is malformed"

    verifyArithmeticEvidence providerEvidence domain proposition evidence =
      case
          checkTermObserved
            Parametric
            context
            universes
            assumptions
            env
            evidence
            proposition
        of
          Right () -> pure ()
          Left original ->
            case domain of
              ArithmeticNatural -> bridge original
              ArithmeticInteger -> bridge original
              ArithmeticTypeLevel -> Left original
              ArithmeticProviderLaw -> Left original
      where
        bridge original = do
          evidenceType <-
            inferSimple context universes assumptions env evidence
              >>= maybe (Left original) pure
          unless
            ( arithmeticCheckedPropositionsMatch
                context
                assumptions
                env
                providerEvidence
                domain
                evidenceType
                proposition
            ) $
            invalidArithmetic
              ( "arithmetic assumption evidence does not prove its recorded proposition"
                  <> "\nevidence-type: "
                  <> printTerm evidenceType
                  <> "\nrecorded-proposition: "
                  <> printTerm proposition
                  <> "\nevidence-arithmetic: "
                  <> T.pack
                    ( show
                        ( arithmeticFormulaFromCheckedKTerm
                            context
                            env
                            providerEvidence
                            domain
                            evidenceType
                        )
                    )
                  <> "\nrecorded-arithmetic: "
                  <> T.pack
                    ( show
                        ( arithmeticFormulaFromCheckedKTerm
                            context
                            env
                            providerEvidence
                            domain
                            proposition
                        )
                    )
              )

-- | Relate the exact checked proposition to the canonical proposition used by
-- arithmetic replay.  Selected standard operations are ordinary dictionary
-- applications in checked KCore, while replay deliberately uses the compact
-- primitive vocabulary understood by the independent solver.  They need not
-- be definitionally equal.  The bridge is nevertheless narrow: the checked
-- term has already passed KCore typing, operation recognition uses exact
-- standard semantic identities and carriers, and transparent reduction uses
-- only bodies admitted to 'vcGlobalBodies'.
arithmeticReplayPropositionMatches
  :: VerifyContext
  -> Assumptions
  -> LocalEnv
  -> [(StableRef, KTerm)]
  -> ArithmeticDomain
  -> KTerm
  -> KTerm
  -> Bool
arithmeticReplayPropositionMatches context assumptions env providers domain checked replayed =
  sameKCoreTypeUnderIn assumptions env context checked replayed
    || case domain of
      ArithmeticNatural -> fromMaybe False sameArithmeticFormula
      ArithmeticInteger -> fromMaybe False sameArithmeticFormula
      ArithmeticTypeLevel -> False
      ArithmeticProviderLaw -> False
  where
    sameArithmeticFormula = do
      checkedFormula <-
        arithmeticFormulaFromCheckedKTerm context env providers domain checked
      replayedFormula <- arithmeticFormulaFromKTerm domain replayed
      pure (checkedFormula == replayedFormula)

-- | Compare two independently checked arithmetic propositions. Unlike
-- 'arithmeticReplayPropositionMatches', neither side is required to use the
-- canonical replay vocabulary: both may be authenticated selected operations
-- whose dictionaries were retained in KCore.
arithmeticCheckedPropositionsMatch
  :: VerifyContext
  -> Assumptions
  -> LocalEnv
  -> [(StableRef, KTerm)]
  -> ArithmeticDomain
  -> KTerm
  -> KTerm
  -> Bool
arithmeticCheckedPropositionsMatch context assumptions env providers domain left right =
  sameKCoreTypeUnderIn assumptions env context left right
    || case domain of
      ArithmeticNatural -> fromMaybe False sameArithmeticFormula
      ArithmeticInteger -> fromMaybe False sameArithmeticFormula
      ArithmeticTypeLevel -> False
      ArithmeticProviderLaw -> False
  where
    sameArithmeticFormula = do
      leftFormula <-
        arithmeticFormulaFromCheckedKTerm context env providers domain left
      rightFormula <-
        arithmeticFormulaFromCheckedKTerm context env providers domain right
      pure (leftFormula == rightFormula)

arithmeticCheckedOperandDebug
  :: VerifyContext
  -> LocalEnv
  -> KTerm
  -> Text
arithmeticCheckedOperandDebug context env proposition =
  fromMaybe "<not a Boolean equality over a binary application>" $ do
    condition <- booleanEqualityPayload proposition
    let (_, arguments) =
          collectKApplication (stripArithmeticTermWrappers condition)
        explicit = [argument | KArgument KExplicit argument <- arguments]
    (lhs, rhs) <- lastTwo explicit
    pure
      ( "lhs="
          <> printTerm (unfoldTypeHeadWithLocals context env lhs)
          <> "; rhs="
          <> printTerm (unfoldTypeHeadWithLocals context env rhs)
      )

arithmeticFormulaFromCheckedKTerm
  :: VerifyContext
  -> LocalEnv
  -> [(StableRef, KTerm)]
  -> ArithmeticDomain
  -> KTerm
  -> Maybe AFormula
arithmeticFormulaFromCheckedKTerm context env providers domain proposition =
  ( AAtom
      <$> arithmeticFactFromKTermWith
        (arithmeticExpressionFromCheckedKTerm context env providers)
        domain
        proposition
  )
    <|> arithmeticFormulaFromKTerm domain proposition
    <|> do
      (wanted, condition) <- booleanLiteralEqualityPayload proposition
      formula <-
        arithmeticBooleanFormulaFromCheckedKTerm context env providers domain condition
      pure (if wanted then formula else ANot formula)

arithmeticBooleanFormulaFromCheckedKTerm
  :: VerifyContext
  -> LocalEnv
  -> [(StableRef, KTerm)]
  -> ArithmeticDomain
  -> KTerm
  -> Maybe AFormula
arithmeticBooleanFormulaFromCheckedKTerm context env providers domain =
  go (48 :: Int)
  where
    go fuel term =
      arithmeticBooleanFormulaLayer
        (go fuel)
        ( arithmeticPrimitiveComparisonFactFromCheckedKTerm
            context
            env
            providers
            domain
        )
        term
        <|> unfoldSelectedTerm fuel term

    -- Follow the exact checked function and evidence selected by elaboration.
    -- Standard dictionaries reduce to the trusted primitive vocabulary;
    -- custom or opaque evidence remains outside the portable arithmetic
    -- fragment instead of inheriting standard semantics from an operation
    -- spelling alone.
    unfoldSelectedTerm fuel term
      | fuel <= 0 = Nothing
      | otherwise =
          let stripped = stripArithmeticTermWrappers term
           in ( go (fuel - 1)
                  =<< unfoldTransparentKApplication context env stripped
              )
                <|> let reduced =
                          unfoldTypeHeadWithLocals context env stripped
                     in if reduced == stripped
                          then Nothing
                          else go (fuel - 1) reduced

arithmeticPrimitiveComparisonFactFromCheckedKTerm
  :: VerifyContext
  -> LocalEnv
  -> [(StableRef, KTerm)]
  -> ArithmeticDomain
  -> KTerm
  -> Maybe AFact
arithmeticPrimitiveComparisonFactFromCheckedKTerm context env providers domain term = do
  let (headTerm, arguments) =
        collectKApplication (stripArithmeticTermWrappers term)
      explicit = [argument | KArgument KExplicit argument <- arguments]
      logicalExpression =
        arithmeticExpressionFromCheckedKTerm context env providers domain
  (comparison, operand) <-
    ( do
        comparison <- primitiveComparison headTerm
        pure
          ( comparison
          , arithmeticPrimitiveComparisonOperandWith
              (arithmeticExpressionFromCheckedKTerm context env providers)
              domain
          )
    )
      <|> ( do
              comparison <- selectedComparison headTerm arguments
              pure (comparison, logicalExpression)
          )
  (lhs, rhs) <- lastTwo explicit
  AFact comparison
    <$> operand lhs
    <*> operand rhs
  where
    primitiveComparison headTerm = do
      operation <- kTermHeadGlobal headTerm
      if trustedIntPrimitiveRef "ltInt" operation
        then Just ACmpLt
        else if trustedIntPrimitiveRef "leInt" operation
          then Just ACmpLe
          else if trustedIntPrimitiveRef "eqInt" operation
            then Just ACmpEq
            else Nothing

    selectedComparison headTerm arguments = do
      let implicit = [argument | KArgument KImplicit argument <- arguments]
      (comparison, trait, dictionary) <-
        case stripArithmeticTermWrappers headTerm of
          KTGlobal operation _ -> do
            (comparison', trait') <- comparisonDescriptor operation
            _carrier : dictionary' : _ <- pure implicit
            pure (comparison', trait', dictionary')
          KTProject field dictionary -> do
            (comparison', trait') <- fieldComparisonDescriptor field
            pure (comparison', trait', dictionary)
          _ -> Nothing
      guard (providerContains trait dictionary providers)
      pure comparison

    comparisonDescriptor operation
      | operation == stableRefForGlobal (gPrel "==") =
          Just (ACmpEq, stableRefForGlobal (gPrel "Eq"))
      | operation == stableRefForGlobal (gPrel "<") =
          Just (ACmpLt, stableRefForGlobal prelOrd)
      | operation == stableRefForGlobal (gPrel "<=") =
          Just (ACmpLe, stableRefForGlobal prelOrd)
      | otherwise = Nothing

    fieldComparisonDescriptor field
      | field == stableFieldRef "==" =
          Just (ACmpEq, stableRefForGlobal (gPrel "Eq"))
      | field == stableFieldRef "<" =
          Just (ACmpLt, stableRefForGlobal prelOrd)
      | field == stableFieldRef "<=" =
          Just (ACmpLe, stableRefForGlobal prelOrd)
      | otherwise = Nothing

arithmeticExpressionFromCheckedKTerm
  :: VerifyContext
  -> LocalEnv
  -> [(StableRef, KTerm)]
  -> ArithmeticDomain
  -> KTerm
  -> Maybe AExpr
arithmeticExpressionFromCheckedKTerm context env providers domain = go (24 :: Int)
  where
    go fuel term
      | fuel <= 0 = Nothing
      | KTLocal ref levels <- stripped
      , Just (LocalDefinition _ parameters _ body) <-
          Map.lookup (lrId ref) env
      , length parameters == length levels =
          go
            (fuel - 1)
            ( substituteUniverseParameters
                (Map.fromList (zip (map urId parameters) levels))
                body
            )
      | Just expression <- arithmeticExpressionFromKTerm domain term =
          Just expression
      | Just expression <- selectedArithmeticExpression fuel stripped =
          Just expression
      | KTIf condition thenTerm elseTerm <-
          stripped =
          AIf
            <$> arithmeticBooleanFormulaFromCheckedKTerm
              context
              env
              providers
              domain
              condition
            <*> go (fuel - 1) thenTerm
            <*> go (fuel - 1) elseTerm
      | Just reduced <-
          unfoldTransparentKApplication context env stripped =
          go (fuel - 1) reduced
      | otherwise =
          let reduced =
                unfoldTypeHeadWithLocals
                  context
                  env
                  stripped
           in if reduced == stripped
                then Nothing
                else go (fuel - 1) reduced
      where
        stripped = stripArithmeticTermWrappers term

    selectedArithmeticExpression fuel term = do
      let (headTerm, arguments) = collectKApplication term
          explicit = [argument | KArgument KExplicit argument <- arguments]
          implicit = [argument | KArgument KImplicit argument <- arguments]
          binary constructor = do
            (lhs, rhs) <- lastTwo explicit
            constructor <$> go (fuel - 1) lhs <*> go (fuel - 1) rhs
      (constructor, trait, dictionary) <-
        case stripArithmeticTermWrappers headTerm of
          KTGlobal operation _ -> do
            (constructor', trait') <- operationDescriptor operation
            _carrier : dictionary' : _ <- pure implicit
            pure (constructor', trait', dictionary')
          KTProject field dictionary -> do
            (constructor', trait') <- fieldOperationDescriptor field
            pure (constructor', trait', dictionary)
          _ -> Nothing
      guard (providerContains trait dictionary providers)
      binary constructor

    operationDescriptor operation
      | operation
          `elem`
            [ stableRefForGlobal (gPrel "+")
            , stableRefForGlobal (gPrel "add")
            ] =
          Just (AAdd, stableRefForGlobal (gPrel "Add"))
      | operation
          `elem`
            [ stableRefForGlobal (gPrel "*")
            , stableRefForGlobal (gPrel "multiply")
            ] =
          Just (AMul, stableRefForGlobal (gPrel "Mul"))
      | operation
          `elem`
            [ stableRefForGlobal (gPrel "-")
            , stableRefForGlobal (gPrel "subtract")
            ] =
          Just (ASub, stableRefForGlobal (gPrel "CheckedSub"))
      | operation
          `elem`
            [ stableRefForGlobal (gPrel "/")
            , stableRefForGlobal (gPrel "divide")
            ] =
          Just (ADiv, stableRefForGlobal (gPrel "CheckedDiv"))
      | operation
          `elem`
            [ stableRefForGlobal (gPrel "%")
            , stableRefForGlobal (gPrel "modulo")
            ] =
          Just (AMod, stableRefForGlobal (gPrel "CheckedMod"))
      | otherwise = Nothing

    fieldOperationDescriptor field
      | field == stableFieldRef "add" =
          Just (AAdd, stableRefForGlobal (gPrel "Add"))
      | field == stableFieldRef "multiply" =
          Just (AMul, stableRefForGlobal (gPrel "Mul"))
      | field == stableFieldRef "subtract" =
          Just (ASub, stableRefForGlobal (gPrel "CheckedSub"))
      | field == stableFieldRef "divide" =
          Just (ADiv, stableRefForGlobal (gPrel "CheckedDiv"))
      | field == stableFieldRef "modulo" =
          Just (AMod, stableRefForGlobal (gPrel "CheckedMod"))
      | otherwise = Nothing

-- | Relate the proposition checked by a standard provider law to the
-- certificate's canonical replay proposition.  Equality is accepted directly
-- when no representation change occurred.  The only non-definitional bridge
-- currently installed is the authenticated Nat additive provider: the exact
-- law identity and evidence term have already been checked above, and this
-- function independently reifies the law result's selected addition as the
-- canonical Nat expression used by the arithmetic verifier.
providerLawReplayMatches
  :: VerifyContext
  -> Assumptions
  -> LocalEnv
  -> KArithmeticProvider
  -> KTerm
  -> KTerm
  -> KTerm
  -> Bool
providerLawReplayMatches context assumptions env provider proof checked replayed =
  sameKCoreTypeUnderIn assumptions env context checked replayed
    || fromMaybe False canonicalNatReplay
  where
    canonicalNatReplay = do
      law <- kapLaw provider
      guard
        ( law
            `elem`
              [ stableRefForGlobal
                  (gPrel "AdditiveMonoid.addLeftIdentity")
              , stableRefForGlobal
                  (gPrel "AdditiveMonoid.addRightIdentity")
              , stableRefForGlobal
                  (gPrel "CommutativeAdditiveMonoid.addCommutative")
              ]
        )
      guard (kTermHeadGlobal (fst (collectKApplication proof)) == Just law)
      (carrier, checkedLhs, checkedRhs) <- equalityOperands checked
      guard
        ( stripArithmeticTermWrappers carrier
            == KTGlobal (stableRefForGlobal prelNat) []
        )
      checkedLeft <- providerExpression checkedLhs
      checkedRight <- providerExpression checkedRhs
      (_, replayedLhs, replayedRhs) <- equalityOperands replayed
      replayedLeft <- providerExpression replayedLhs
      replayedRight <- providerExpression replayedRhs
      pure
        ( AFact ACmpEq checkedLeft checkedRight
            == AFact ACmpEq replayedLeft replayedRight
        )

    -- Primitive Nat operations use the portable arithmetic decoder. An
    -- overloaded operation is admitted only when its semantic identity is a
    -- member bound by this provider and its dictionary is a projection rooted
    -- in the exact recorded provider evidence. A same-spelled operation from
    -- another closure therefore remains opaque.
    providerExpression term =
      arithmeticExpressionFromKTerm ArithmeticNatural term
        <|> do
          let (operation, arguments) =
                collectKApplication (stripArithmeticTermWrappers term)
              explicit =
                [ argument
                | KArgument KExplicit argument <- arguments
                ]
              implicit =
                [ argument
                | KArgument KImplicit argument <- arguments
                ]
          dictionary <-
            case stripArithmeticTermWrappers operation of
              KTGlobal operationRef _
                | operationRef
                    `elem`
                      [ stableRefForGlobal (gPrel "+")
                      , stableRefForGlobal (gPrel "add")
                      , stableRefForGlobal (gPrel "Add.add")
                      ]
                , _carrier : selected : _ <- implicit ->
                    Just selected
              KTProject field selected
                | field == stableFieldRef "add" ->
                    Just selected
              _ -> Nothing
          guard (providerClosureContains (kapEvidence provider) dictionary)
          (left, right) <- lastTwo explicit
          AAdd <$> providerExpression left <*> providerExpression right

    providerClosureContains root candidate
      | stripArithmeticTermWrappers candidate
          == stripArithmeticTermWrappers root =
          True
      | otherwise =
          case stripArithmeticTermWrappers candidate of
            KTProject _ receiver ->
              providerClosureContains root receiver
            _ -> False

arithmeticFactFromKTerm :: ArithmeticDomain -> KTerm -> Maybe AFact
arithmeticFactFromKTerm =
  arithmeticFactFromKTermWith arithmeticExpressionFromKTerm

arithmeticFactFromKTermWith
  :: (ArithmeticDomain -> KTerm -> Maybe AExpr)
  -> ArithmeticDomain
  -> KTerm
  -> Maybe AFact
arithmeticFactFromKTermWith expression domain proposition = do
  (headTerm, arguments) <- pure (collectKApplication (stripArithmeticTermWrappers proposition))
  headRef <- kTermHeadGlobal headTerm
  guard (headRef == stableRefForGlobal prelEqType)
  let explicit = [term | KArgument KExplicit term <- arguments]
      implicit = [term | KArgument KImplicit term <- arguments]
  (lhs, rhs) <- lastTwo explicit
  carrier <- listToMaybe implicit
  if arithmeticCarrier domain carrier
    then
      AFact ACmpEq
        <$> expression domain lhs
        <*> expression domain rhs
    else if boolCarrier carrier
      then
        ( arithmeticBooleanFactFromKTerm domain lhs
            <* guard (isTrueKTerm rhs)
        )
          <|> ( arithmeticBooleanFactFromKTerm domain rhs
                  <* guard (isTrueKTerm lhs)
              )
      else Nothing
  where
    arithmeticCarrier ArithmeticNatural term =
      stripArithmeticTermWrappers term == KTGlobal (stableRefForGlobal prelNat) []
    arithmeticCarrier ArithmeticInteger term =
      stripArithmeticTermWrappers term
        `elem`
          [ KTGlobal (stableRefForGlobal prelInteger) []
          , KTGlobal (stableRefForGlobal prelInt) []
          ]
    -- Type-level comparison certificates have their own authenticated
    -- constraint decoder above. They are never value-arithmetic facts.
    arithmeticCarrier ArithmeticTypeLevel _ = False
    arithmeticCarrier ArithmeticProviderLaw _ = False
    boolCarrier term =
      stripArithmeticTermWrappers term == KTGlobal (stableRefForGlobal prelBool) []

arithmeticFormulaFromKTerm
  :: ArithmeticDomain
  -> KTerm
  -> Maybe AFormula
arithmeticFormulaFromKTerm domain proposition =
  AAtom <$> arithmeticFactFromKTerm domain proposition
    <|> do
      (wanted, condition) <- booleanLiteralEqualityPayload proposition
      formula <- arithmeticBooleanFormulaFromKTerm domain condition
      pure (if wanted then formula else ANot formula)

arithmeticBooleanFormulaFromKTerm
  :: ArithmeticDomain
  -> KTerm
  -> Maybe AFormula
arithmeticBooleanFormulaFromKTerm domain = recurse
  where
    recurse =
      arithmeticBooleanFormulaLayer
        recurse
        (arithmeticBooleanFactFromKTerm domain)

arithmeticBooleanFormulaLayer
  :: (KTerm -> Maybe AFormula)
  -> (KTerm -> Maybe AFact)
  -> KTerm
  -> Maybe AFormula
arithmeticBooleanFormulaLayer recurse atom term =
  case stripArithmeticTermWrappers term of
    candidate
      | isTrueKTerm candidate -> Just (ATruth True)
      | isFalseKTerm candidate -> Just (ATruth False)
    KTIf condition thenTerm elseTerm
      | isTrueKTerm thenTerm
      , isFalseKTerm elseTerm ->
          recurse condition
      | isFalseKTerm thenTerm
      , isTrueKTerm elseTerm ->
          ANot <$> recurse condition
      | isFalseKTerm elseTerm ->
          AAnd <$> recurse condition <*> recurse thenTerm
      | isTrueKTerm thenTerm ->
          AOr <$> recurse condition <*> recurse elseTerm
    application -> do
      let (headTerm, arguments) = collectKApplication application
          explicit = [argument | KArgument KExplicit argument <- arguments]
          binary constructor = do
            (lhs, rhs) <- lastTwo explicit
            constructor <$> recurse lhs <*> recurse rhs
      case kTermHeadGlobal headTerm of
        Just operation
          | operation == stableRefForGlobal prelAnd -> binary AAnd
          | operation == stableRefForGlobal prelOr -> binary AOr
          | operation == stableRefForGlobal prelNot -> do
              argument <- listToMaybe (reverse explicit)
              ANot <$> recurse argument
        _ -> AAtom <$> atom application

booleanEqualityPayload :: KTerm -> Maybe KTerm
booleanEqualityPayload proposition = do
  (truth, condition) <- booleanLiteralEqualityPayload proposition
  guard truth
  pure condition

-- | Artifact-side decoder for an exact equality between one checked Bool term
-- and one resolved prelude Bool constructor. The verifier combines this shape
-- with 'branchFactAvailable'; the shape alone is not proof authority.
booleanLiteralEqualityPayload :: KTerm -> Maybe (Bool, KTerm)
booleanLiteralEqualityPayload proposition = do
  let (headTerm, arguments) =
        collectKApplication (stripArithmeticTermWrappers proposition)
      explicit = [term | KArgument KExplicit term <- arguments]
      implicit = [term | KArgument KImplicit term <- arguments]
  guard (kTermHeadGlobal headTerm == Just (stableRefForGlobal prelEqType))
  carrier <- listToMaybe implicit
  guard
    ( stripArithmeticTermWrappers carrier
        == KTGlobal (stableRefForGlobal prelBool) []
    )
  (lhs, rhs) <- lastTwo explicit
  case (boolLiteral lhs, boolLiteral rhs) of
    (_, Just truth) -> Just (truth, lhs)
    (Just truth, _) -> Just (truth, rhs)
    _ -> Nothing
  where
    boolLiteral candidate
      | isTrueKTerm candidate = Just True
      | isFalseKTerm candidate = Just False
      | otherwise = Nothing

branchFactAvailable :: VerifyContext -> LocalEnv -> Bool -> KTerm -> Bool
branchFactAvailable context env truth condition =
  any
    (\(factTruth, factCondition) ->
       factTruth == truth
         && branchConditionsEquivalent factCondition condition)
    ( concatMap
        (uncurry (branchFactConsequences 16))
        (vcArithmeticBranchFacts context)
    )
  where
    contextWithoutBranchFacts =
      context {vcArithmeticBranchFacts = []}

    branchConditionsEquivalent left right =
      sameKCoreTypeIn env contextWithoutBranchFacts left right
        || any
          (sameArithmeticCondition left right)
          [ArithmeticNatural, ArithmeticInteger]

    sameArithmeticCondition left right domain =
      let leftFormula =
            arithmeticBooleanFormulaFromCheckedKTerm
              contextWithoutBranchFacts
              env
              []
              domain
              left
          rightFormula =
            arithmeticBooleanFormulaFromCheckedKTerm
              contextWithoutBranchFacts
              env
              []
              domain
              right
       in case (leftFormula, rightFormula)
        of
          (Just leftFormula, Just rightFormula) ->
            leftFormula == rightFormula
          _ -> False

-- | Polarity-safe consequences of a checked KCore Boolean branch. This is the
-- artifact-side twin of the elaborator's branch decomposition: true
-- conjunctions, false disjunctions, and negations only. It never chooses a
-- disjunct or a failed conjunct.
branchFactConsequences :: Int -> Bool -> KTerm -> [(Bool, KTerm)]
branchFactConsequences fuel truth term
  | fuel <= 0 = [(truth, term)]
  | otherwise =
      (truth, term) : case stripArithmeticTermWrappers term of
        KTIf condition thenTerm elseTerm
          | truth
          , isFalseTerm elseTerm ->
              branchFactConsequences (fuel - 1) True condition
                ++ branchFactConsequences (fuel - 1) True thenTerm
          | not truth
          , isTrueTerm thenTerm ->
              branchFactConsequences (fuel - 1) False condition
                ++ branchFactConsequences (fuel - 1) False elseTerm
          | isFalseTerm thenTerm
          , isTrueTerm elseTerm ->
              branchFactConsequences (fuel - 1) (not truth) condition
        application ->
          let (headTerm, arguments) = collectKApplication application
              explicit = [argument | KArgument KExplicit argument <- arguments]
           in case (kTermHeadGlobal headTerm, explicit) of
                (Just operation, operands)
                  | operation == stableRefForGlobal prelAnd
                  , truth
                  , Just (lhs, rhs) <- lastTwo operands ->
                      branchFactConsequences (fuel - 1) True lhs
                        ++ branchFactConsequences (fuel - 1) True (booleanThunkPayload rhs)
                  | operation == stableRefForGlobal prelOr
                  , not truth
                  , Just (lhs, rhs) <- lastTwo operands ->
                      branchFactConsequences (fuel - 1) False lhs
                        ++ branchFactConsequences (fuel - 1) False (booleanThunkPayload rhs)
                  | operation == stableRefForGlobal prelNot
                  , Just argument <- listToMaybe (reverse operands) ->
                      branchFactConsequences (fuel - 1) (not truth) argument
                _ -> []
  where
    -- The checked short-circuit operators take their second Boolean in the
    -- canonical typed thunk node. Their polarity-safe branch consequence is
    -- about that payload, not the suspension wrapper. The operator's stable
    -- identity above and the verified KCore node schema jointly authorize
    -- this unwrap.
    booleanThunkPayload candidate =
      case stripArithmeticTermWrappers candidate of
        KTGeneric "impl.kappa.core.thunk" fields ->
          case lookup "value" fields of
            Just (KVTerm payload) -> payload
            _ -> candidate
        _ -> candidate

arithmeticBooleanFactFromKTerm :: ArithmeticDomain -> KTerm -> Maybe AFact
arithmeticBooleanFactFromKTerm domain term =
  case stripArithmeticTermWrappers term of
    KTIf condition thenTerm elseTerm
      | isFalseKTerm thenTerm
      , isTrueKTerm elseTerm ->
          arithmeticBooleanFactFromKTerm domain condition >>= negateFact
    application -> do
      let (headTerm, arguments) = collectKApplication application
          explicit = [argument | KArgument KExplicit argument <- arguments]
      headRef <- kTermHeadGlobal headTerm
      (lhs, rhs) <- lastTwo explicit
      comparison <-
        if trustedIntPrimitiveRef "ltInt" headRef
          then Just ACmpLt
          else if trustedIntPrimitiveRef "leInt" headRef
            then Just ACmpLe
            else if trustedIntPrimitiveRef "eqInt" headRef
              then Just ACmpEq
              else Nothing
      AFact comparison
        <$> arithmeticPrimitiveComparisonOperand domain lhs
        <*> arithmeticPrimitiveComparisonOperand domain rhs

-- | Decode one operand of an integer comparison without conflating the
-- logical Nat and Integer certificate domains.  Standard Nat comparison
-- lowers through the checked @natToInt@ bridge on both operands. Integer
-- comparison may contain such a bridge only for a closed non-negative
-- constant; admitting an open Nat there would let the same primitive
-- proposition replay in two arithmetic domains.
arithmeticPrimitiveComparisonOperand
  :: ArithmeticDomain
  -> KTerm
  -> Maybe AExpr
arithmeticPrimitiveComparisonOperand =
  arithmeticPrimitiveComparisonOperandWith arithmeticExpressionFromKTerm

arithmeticPrimitiveComparisonOperandWith
  :: (ArithmeticDomain -> KTerm -> Maybe AExpr)
  -> ArithmeticDomain
  -> KTerm
  -> Maybe AExpr
arithmeticPrimitiveComparisonOperandWith expression domain operand =
  case domain of
    ArithmeticNatural ->
      decode PrimitiveComparisonNatural
    ArithmeticInteger ->
      decode PrimitiveComparisonInteger
    ArithmeticTypeLevel -> Nothing
    ArithmeticProviderLaw -> Nothing
  where
    decode selected =
      decodePrimitiveComparisonOperand
        (trustedUnaryIntPrimitivePayload "natToInt")
        ( \logical ->
            expression
              ( case logical of
                  PrimitiveComparisonNatural -> ArithmeticNatural
                  PrimitiveComparisonInteger -> ArithmeticInteger
              )
        )
        selected
        operand

trustedUnaryIntPrimitivePayload :: Text -> KTerm -> Maybe KTerm
trustedUnaryIntPrimitivePayload operation term = do
  let (headTerm, arguments) =
        collectKApplication (stripArithmeticTermWrappers term)
      explicit = [argument | KArgument KExplicit argument <- arguments]
  headRef <- kTermHeadGlobal headTerm
  guard (trustedIntPrimitiveRef operation headRef)
  case explicit of
    [payload] -> Just payload
    _ -> Nothing

-- KCore uses the checked public identity. Internal @__prim@ quotes are
-- canonicalized back to this identity while finalizing Core and are never
-- admitted as an artifact compatibility form.
trustedIntPrimitiveRef :: Text -> StableRef -> Bool
trustedIntPrimitiveRef operation ref =
  ref == stableRefForGlobal (gPrel operation)

arithmeticExpressionFromKTerm :: ArithmeticDomain -> KTerm -> Maybe AExpr
arithmeticExpressionFromKTerm domain term0 =
  case stripArithmeticTermWrappers term0 of
    KTLiteral (LitInt value)
      | domain == ArithmeticInteger || value >= 0 -> Just (AConst value)
    KTLocal ref [] -> Just (AVar (lrId ref))
    KTConstruct constructor [] []
      | domain == ArithmeticNatural
      , constructor == stableRefForConstructor prelNatZero ->
          Just (AConst 0)
    KTConstruct constructor [] [KArgument _ argument]
      | domain == ArithmeticNatural
      , constructor == stableRefForConstructor prelNatSucc ->
          AAdd (AConst 1) <$> recurse argument
    KTIf condition thenTerm elseTerm ->
      AIf
        <$> arithmeticBooleanFormulaFromKTerm domain condition
        <*> recurse thenTerm
        <*> recurse elseTerm
    application@KTApply {} -> arithmeticApplication application
    _ -> Nothing
  where
    recurse = arithmeticExpressionFromKTerm domain
    arithmeticApplication application = do
      let (headTerm, arguments) = collectKApplication application
          explicit = [argument | KArgument KExplicit argument <- arguments]
          implicit = [argument | KArgument KImplicit argument <- arguments]
          binary constructor = do
            (lhs, rhs) <- lastTwo explicit
            constructor <$> recurse lhs <*> recurse rhs
          unary constructor = do
              argument <- listToMaybe (reverse explicit)
              constructor <$> recurse argument
      headRef <- kTermHeadGlobal headTerm
      if domain == ArithmeticNatural
          && headRef == stableRefForGlobal (gPrel "zero")
          && null explicit
          && listToMaybe implicit
            == Just (KTGlobal (stableRefForGlobal prelNat) [])
        then Just (AConst 0)
        else if domain == ArithmeticNatural && headRef == stableRefForGlobal prelNatAdd
        then binary AAdd
        else if domain == ArithmeticNatural && headRef == stableRefForGlobal prelNatMultiply
          then binary AMul
          else case primitiveArithmeticOperation headRef of
            Just ("add", 2) -> binary AAdd
            Just ("subtract", 2) -> binary ASub
            Just ("multiply", 2) -> binary AMul
            Just ("divide", 2) -> binary ADiv
            Just ("modulo", 2) -> binary AMod
            Just ("negate", 1) -> unary ANeg
            Just ("identity", 1) -> unary id
            _ -> Nothing

primitiveArithmeticOperation :: StableRef -> Maybe (Text, Int)
primitiveArithmeticOperation ref
  | primitive "addInt" = Just ("add", 2)
  | primitive "subInt" = Just ("subtract", 2)
  | primitive "mulInt" = Just ("multiply", 2)
  | primitive "divInt" = Just ("divide", 2)
  | primitive "modInt" = Just ("modulo", 2)
  | primitive "negInt" = Just ("negate", 1)
  | primitive "natToInt" = Just ("identity", 1)
  | primitive "natOfInt" = Just ("identity", 1)
  | primitive "intToNat" = Just ("identity", 1)
  | otherwise = Nothing
  where
    primitive operation = trustedIntPrimitiveRef operation ref

negateArithmeticFact :: AFact -> Maybe AFact
negateArithmeticFact = \case
  AFact ACmpLt lhs rhs -> Just (AFact ACmpLe rhs lhs)
  AFact ACmpLe lhs rhs -> Just (AFact ACmpLt rhs lhs)
  AFact ACmpEq lhs rhs -> Just (AFact ACmpNe lhs rhs)
  AFact ACmpNe lhs rhs -> Just (AFact ACmpEq lhs rhs)

collectKApplication :: KTerm -> (KTerm, [KArgument])
collectKApplication = go []
  where
    go arguments (KTApply function more) = go (more ++ arguments) function
    go arguments headTerm = (headTerm, arguments)

-- | Expose a checked transparent definition application without recursively
-- normalizing its arguments. Arithmetic certificate verification uses this
-- bounded head reduction to preserve authenticated selected operations and
-- finite @if@ structure while expanding ordinary helpers and selected
-- dictionary methods. Only universe substitution, beta reduction, and
-- projection from checked values participate; branch facts and general
-- conversion are deliberately unavailable here.
--
-- Returning 'Nothing' unless at least one lambda is beta-reduced prevents an
-- unsaturated definition from becoming an ambient rewrite rule.
unfoldTransparentKApplication
  :: VerifyContext
  -> LocalEnv
  -> KTerm
  -> Maybe KTerm
unfoldTransparentKApplication context env term = do
  guard (not (null (snd (collectKApplication term))))
  (reduced, didBeta) <-
    reduceHead (48 :: Int) Set.empty Set.empty term
  guard didBeta
  guard (reduced /= term)
  pure reduced
  where
    reduceHead fuel seenGlobals seenLocals candidate
      | fuel <= 0 = Just (candidate, False)
      | otherwise =
          case candidate of
            KTLocal ref levels
              | lrId ref `Set.notMember` seenLocals -> do
                  LocalDefinition _ parameters _ body <-
                    Map.lookup (lrId ref) env
                  guard (length parameters == length levels)
                  reduceHead
                    (fuel - 1)
                    seenGlobals
                    (Set.insert (lrId ref) seenLocals)
                    ( substituteUniverseParameters
                        (Map.fromList (zip (map urId parameters) levels))
                        body
                    )
            KTLocal {} -> Just (candidate, False)
            KTGlobal ref levels
              | ref `Set.notMember` seenGlobals -> do
                  (parameters, body) <- Map.lookup ref (vcGlobalBodies context)
                  guard (length parameters == length levels)
                  reduceHead
                    (fuel - 1)
                    (Set.insert ref seenGlobals)
                    seenLocals
                    ( substituteUniverseParameters
                        (Map.fromList (zip (map urId parameters) levels))
                        body
                    )
            KTGlobal {} -> Just (candidate, False)
            KTApply function arguments -> do
              reducedFunction <-
                reduceHead
                  (fuel - 1)
                  seenGlobals
                  seenLocals
                  function
              apply
                (fuel - 1)
                seenGlobals
                seenLocals
                (snd reducedFunction)
                (fst reducedFunction)
                arguments
            KTProject field receiver -> do
              (reducedReceiver, receiverBeta) <-
                reduceHead
                  (fuel - 1)
                  seenGlobals
                  seenLocals
                  receiver
              case reduceKTermProjection context field reducedReceiver of
                Nothing ->
                  pure
                    ( KTProject field reducedReceiver
                    , receiverBeta
                    )
                Just value -> do
                  (reducedValue, nestedBeta) <-
                    reduceHead
                      (fuel - 1)
                      seenGlobals
                      seenLocals
                      value
                  pure
                    ( reducedValue
                    , receiverBeta || nestedBeta
                    )
            KTIf condition thenBranch elseBranch -> do
              case kBooleanConstructorValue condition of
                Just True -> pure (thenBranch, False)
                Just False -> pure (elseBranch, False)
                Nothing -> do
                  (reducedThen, thenBeta) <-
                    reduceHead
                      (fuel - 1)
                      seenGlobals
                      seenLocals
                      thenBranch
                  (reducedElse, elseBeta) <-
                    reduceHead
                      (fuel - 1)
                      seenGlobals
                      seenLocals
                      elseBranch
                  pure
                    ( KTIf condition reducedThen reducedElse
                    , thenBeta || elseBeta
                    )
            KTCase scrutinee resultType alternatives -> do
              (reducedScrutinee, scrutineeBeta) <-
                reduceHead
                  (fuel - 1)
                  seenGlobals
                  seenLocals
                  scrutinee
              case reduceKnownKCase reducedScrutinee alternatives of
                Nothing ->
                  pure
                    ( KTCase reducedScrutinee resultType alternatives
                    , scrutineeBeta
                    )
                Just body -> do
                  (reducedBody, bodyBeta) <-
                    reduceHead
                      (fuel - 1)
                      seenGlobals
                      seenLocals
                      body
                  pure (reducedBody, scrutineeBeta || bodyBeta)
            KTAscribe value _ ->
              reduceHead
                (fuel - 1)
                seenGlobals
                seenLocals
                value
            _ -> Just (candidate, False)

    apply fuel seenGlobals seenLocals didBeta function arguments =
      case (function, arguments) of
        (KTLambda binder body, argument : rest)
          | kbExplicitness binder == argumentExplicitness argument ->
              let substituted =
                    substituteLocal
                      (kbRef binder)
                      (argumentTerm argument)
                      body
               in do
                    (nextFunction, _) <-
                      reduceHead
                        (fuel - 1)
                        seenGlobals
                        seenLocals
                        substituted
                    if null rest
                      then pure (nextFunction, True)
                      else
                        apply
                          (fuel - 1)
                          seenGlobals
                          seenLocals
                          True
                          nextFunction
                          rest
        _ ->
          pure
            ( if null arguments
                then function
                else KTApply function arguments
            , didBeta
            )

    argumentExplicitness (KArgument explicitness _) = explicitness

kTermHeadGlobal :: KTerm -> Maybe StableRef
kTermHeadGlobal term =
  case stripArithmeticTermWrappers term of
    KTGlobal ref _ -> Just ref
    KTApply function _ -> kTermHeadGlobal function
    _ -> Nothing

stripArithmeticTermWrappers :: KTerm -> KTerm
stripArithmeticTermWrappers = \case
  KTAscribe term _ -> stripArithmeticTermWrappers term
  KTLift _ _ _ term -> stripArithmeticTermWrappers term
  KTSchemaLift _ _ _ _ _ _ term -> stripArithmeticTermWrappers term
  generic@(KTGeneric tag fields)
    | tag `Set.member` decodedBuiltinTermTags ->
        case decodeBuiltinTermNode tag fields of
          Right decoded
            | decoded /= generic -> stripArithmeticTermWrappers decoded
          _ -> generic
  term -> term

data TypeLevelBoolean
  = TypeLevelBooleanLiteral !Bool
  | TypeLevelBooleanConstraint !Level !Level
  deriving stock (Eq, Ord, Show)

-- | Replay one first-class TypeLevel proposition through the same canonical
-- level language used by the universe solver. Provider evidence is consulted
-- only for generic trait-member applications; direct std.typelevel operation
-- identities are self-authenticating.
deriveTypeLevelReplay
  :: [(StableRef, KTerm)]
  -> [(Level, Level)]
  -> KTerm
  -> Maybe KValueNode
deriveTypeLevelReplay providers assumptionPairs proposition = do
  goalEncoding <- proveGoal
  pure
    ( KVList
        [ KVText "type-level-proposition"
        , goalEncoding
        , KVList
            [ KVList [encodeTypeLevel lower, encodeTypeLevel upper]
            | (lower, upper) <- canonicalAssumptions
            ]
        ]
    )
  where
    assumptions =
      foldr (uncurry insertAssumption) emptyAssumptions canonicalAssumptions
    canonicalAssumptions =
      sort . nub $
        [ (normalizeLevel lower, normalizeLevel upper)
        | (lower, upper) <- assumptionPairs
        ]

    proveGoal = do
      (carrier, lhs, rhs) <- equalityOperands proposition
      if isTypeLevelCarrier carrier
        then do
          lhsLevel <- typeLevelTerm providers lhs
          rhsLevel <- typeLevelTerm providers rhs
          guard (proveLevelEq assumptions lhsLevel rhsLevel == Proved)
          pure
            ( KVList
                [ KVText "value-equality"
                , encodeTypeLevel (normalizeLevel lhsLevel)
                , encodeTypeLevel (normalizeLevel rhsLevel)
                ]
            )
        else do
          guard (isBoolCarrier carrier)
          lhsBoolean <- typeLevelBoolean providers lhs
          rhsBoolean <- typeLevelBoolean providers rhs
          guard (booleanEqual lhsBoolean rhsBoolean)
          pure
            ( KVList
                [ KVText "boolean-equality"
                , encodeTypeLevelBoolean lhsBoolean
                , encodeTypeLevelBoolean rhsBoolean
                ]
            )

    booleanEqual lhs rhs =
      canonicalBoolean lhs == canonicalBoolean rhs
        || case (booleanTruth lhs, booleanTruth rhs) of
             (Just left, Just right) -> left == right
             _ -> False

    canonicalBoolean = \case
      TypeLevelBooleanLiteral truth -> Left truth
      TypeLevelBooleanConstraint lower upper ->
        Right (normalizeLevel lower, normalizeLevel upper)

    booleanTruth = \case
      TypeLevelBooleanLiteral truth -> Just truth
      TypeLevelBooleanConstraint lower upper ->
        case proveLevelLeq assumptions lower upper of
          Proved -> Just True
          Disproved -> Just False
          _ -> Nothing

typeLevelAssumptionConstraint
  :: [(StableRef, KTerm)]
  -> Bool
  -> KTerm
  -> Maybe (Level, Level)
typeLevelAssumptionConstraint providers truth proposition = do
  (carrier, lhs, rhs) <- equalityOperands proposition
  guard (isBoolCarrier carrier)
  comparison <-
    (typeLevelBoolean providers lhs <* guard (isTrueTerm rhs))
      <|> (typeLevelBoolean providers rhs <* guard (isTrueTerm lhs))
  case comparison of
    TypeLevelBooleanLiteral actual ->
      guard (actual == truth) >> pure (LZero, LZero)
    TypeLevelBooleanConstraint lower upper
      | truth -> pure (normalizeLevel lower, normalizeLevel upper)
      | otherwise -> pure (levelSucc (normalizeLevel upper), normalizeLevel lower)

typeLevelBoolean
  :: [(StableRef, KTerm)]
  -> KTerm
  -> Maybe TypeLevelBoolean
typeLevelBoolean providers term
  | isTrueTerm term = Just (TypeLevelBooleanLiteral True)
  | isFalseTerm term = Just (TypeLevelBooleanLiteral False)
  | Just () <- finiteBelowOmega term = Just (TypeLevelBooleanLiteral True)
  | otherwise = do
      let (headTerm, arguments) =
            collectKApplication (stripArithmeticTermWrappers term)
          explicit = [argument | KArgument KExplicit argument <- arguments]
          implicit = [argument | KArgument KImplicit argument <- arguments]
      relation <- kTermHeadGlobal headTerm
      strict <-
        if relation == stableRefForGlobal (gPrel "<")
          then Just True
          else if relation == stableRefForGlobal (gPrel "<=")
            then Just False
            else Nothing
      carrier : dictionary : _ <- pure implicit
      guard (isTypeLevelCarrier carrier)
      guard (providerContains (stableRefForGlobal (gPrel "Ord")) dictionary providers)
      (lhs, rhs) <- lastTwo explicit
      lower <- typeLevelTerm providers lhs
      upper <- typeLevelTerm providers rhs
      pure
        ( TypeLevelBooleanConstraint
            (normalizeLevel (if strict then levelSucc lower else lower))
            (normalizeLevel upper)
        )
  where
    finiteBelowOmega candidate = do
      let (headTerm, arguments) =
            collectKApplication (stripArithmeticTermWrappers candidate)
          explicit = [argument | KArgument KExplicit argument <- arguments]
          implicit = [argument | KArgument KImplicit argument <- arguments]
      relation <- kTermHeadGlobal headTerm
      guard (relation == stableRefForGlobal (gPrel "<"))
      carrier : dictionary : _ <- pure implicit
      guard (isTypeLevelCarrier carrier)
      guard (providerContains (stableRefForGlobal (gPrel "Ord")) dictionary providers)
      (lower, upper) <- lastTwo explicit
      guard (isFiniteTypeLevelTerm lower && isOmegaTypeLevelTerm upper)

-- | Decode a TypeLevel comparison only after independently checking that the
-- selected dictionary really implements the canonical @Ord TypeLevel@
-- instance interface. The comparison term supplies the candidate evidence;
-- its inferred type, rather than its source spelling or global name,
-- authorizes the portable level solver.
authenticatedTypeLevelBoolean
  :: VerifyContext
  -> Assumptions
  -> LocalEnv
  -> KTerm
  -> Maybe TypeLevelBoolean
authenticatedTypeLevelBoolean context assumptions env term = do
  intrinsicTypeLevelBoolean term <|> selectedTypeLevelBoolean term
  where
    selectedTypeLevelBoolean candidate = do
      let (_, arguments) =
            collectKApplication (stripArithmeticTermWrappers candidate)
          implicit =
            [argument | KArgument KImplicit argument <- arguments]
      carrier : dictionary : _ <- pure implicit
      guard (isTypeLevelCarrier carrier)
      dictionaryType <-
        case inferSimple context Set.empty assumptions env dictionary of
          Right (Just inferred) -> Just inferred
          _ -> Nothing
      let (traitHead, traitArguments) =
            collectKApplication
              (stripArithmeticTermWrappers dictionaryType)
      guard
        ( kTermHeadGlobal traitHead
            == Just (stableRefForGlobal prelOrd)
        )
      [KArgument _ dictionaryCarrier] <- pure traitArguments
      guard
        ( sameKCoreTypeUnderIn
            assumptions
            env
            context
            dictionaryCarrier
            (KTGlobal (stableRefForGlobal prelTypeLevel) [])
        )
      typeLevelBoolean
        [(stableRefForGlobal prelOrd, dictionary)]
        candidate

    -- The checked TypeLevel ordering implementation is an opaque primitive
    -- followed by an ordinary Ordering eliminator.  KCore must replay that
    -- eliminator by exact semantic identities; otherwise a generic
    -- constructor such as an equality introduction cannot validate a
    -- definitionally true level comparison.
    intrinsicTypeLevelBoolean = \case
      KTCase scrutinee resultType alternatives -> do
        guard
          ( stripArithmeticTermWrappers resultType
              == KTGlobal (stableRefForGlobal prelBool) []
          )
        let (headTerm, arguments) =
              collectKApplication (stripArithmeticTermWrappers scrutinee)
            explicit =
              [argument | KArgument KExplicit argument <- arguments]
        guard
          ( kTermHeadGlobal headTerm
              == Just (stableRefForGlobal prelCompareTypeLevel)
          )
        (lhsTerm, rhsTerm) <- lastTwo explicit
        lhs <- typeLevelTerm [] lhsTerm
        rhs <- typeLevelTerm [] rhsTerm
        branches <- traverse orderingBooleanBranch alternatives
        lt <- lookup (stableRefForConstructor prelLT) branches
        eq <- lookup (stableRefForConstructor prelEQ) branches
        gt <- lookup (stableRefForConstructor prelGT) branches
        case (lt, eq, gt) of
          (True, True, False) ->
            pure (TypeLevelBooleanConstraint lhs rhs)
          (True, False, False) ->
            pure (TypeLevelBooleanConstraint (levelSucc lhs) rhs)
          (False, False, True) ->
            pure (TypeLevelBooleanConstraint (levelSucc rhs) lhs)
          (False, True, True) ->
            pure (TypeLevelBooleanConstraint rhs lhs)
          (truth1, truth2, truth3)
            | truth1 == truth2 && truth2 == truth3 ->
                pure (TypeLevelBooleanLiteral truth1)
          _ -> Nothing
      _ -> Nothing

    orderingBooleanBranch = \case
      KCaseConstructor constructor _ [] body -> do
        truth <-
          if isTrueTerm body
            then Just True
            else if isFalseTerm body then Just False else Nothing
        pure (constructor, truth)
      _ -> Nothing

typeLevelTerm :: [(StableRef, KTerm)] -> KTerm -> Maybe Level
typeLevelTerm providers term0 =
  direct (stripArithmeticTermWrappers term0) <|> selectedOperation
  where
    term = stripArithmeticTermWrappers term0
    direct = \case
      KTLocal ref [] -> Just (LVar (lrId ref))
      KTGeneric "impl.kappa.level-value" [("level", KVLevel level)] ->
        toLevel level
      KTGlobal ref []
        | ref == stableRefForGlobal prelTypeLevelZero -> Just LZero
        | ref == stableRefForGlobal prelTypeLevelOne -> Just (finiteLevel (1 :: Integer))
        | ref == stableRefForGlobal prelTypeLevelOmega -> Just LOmega
      KTApply (KTGlobal ref []) [KArgument KExplicit (KTLiteral (LitInt value))]
        | ref == stableRefForGlobal prelTypeLevelFromInteger
        , value >= 0 -> Just (finiteLevel value)
      KTApply (KTGlobal ref []) [KArgument KExplicit argument]
        | ref == stableRefForGlobal prelTypeLevelSucc ->
            levelSucc <$> typeLevelTerm providers argument
      KTApply (KTGlobal ref []) [KArgument KExplicit lhs, KArgument KExplicit rhs]
        | ref == stableRefForGlobal prelTypeLevelAdd ->
            levelAdd <$> typeLevelTerm providers lhs <*> typeLevelTerm providers rhs
        | ref == stableRefForGlobal prelTypeLevelMax ->
            levelMax <$> typeLevelTerm providers lhs <*> typeLevelTerm providers rhs
      _ -> Nothing

    selectedOperation = do
      let (headTerm, arguments) = collectKApplication term
          explicit = [argument | KArgument KExplicit argument <- arguments]
          implicit = [argument | KArgument KImplicit argument <- arguments]
      carrier : dictionary : _ <- pure implicit
      guard (isTypeLevelCarrier carrier)
      operation <- kTermHeadGlobal headTerm
      if operation == stableRefForGlobal (gPrel "add")
          && providerContains (stableRefForGlobal (gPrel "Add")) dictionary providers
        then do
          (lhs, rhs) <- lastTwo explicit
          levelAdd <$> typeLevelTerm providers lhs <*> typeLevelTerm providers rhs
        else if operation == stableRefForGlobal (gPrel "max")
          && providerContains (stableRefForGlobal (gPrel "Max")) dictionary providers
          then do
            (lhs, rhs) <- lastTwo explicit
            levelMax <$> typeLevelTerm providers lhs <*> typeLevelTerm providers rhs
          else if operation == stableRefForGlobal (gPrel "succ")
            && providerContains (stableRefForGlobal (gPrel "Successor")) dictionary providers
            then do
              argument <- listToMaybe (reverse explicit)
              levelSucc <$> typeLevelTerm providers argument
            else Nothing

equalityOperands :: KTerm -> Maybe (KTerm, KTerm, KTerm)
equalityOperands proposition = do
  let (headTerm, arguments) =
        collectKApplication (stripArithmeticTermWrappers proposition)
      explicit = [argument | KArgument KExplicit argument <- arguments]
      implicit = [argument | KArgument KImplicit argument <- arguments]
  guard (kTermHeadGlobal headTerm == Just (stableRefForGlobal prelEqType))
  carrier <- listToMaybe implicit
  (lhs, rhs) <- lastTwo explicit
  pure (carrier, lhs, rhs)

providerContains :: StableRef -> KTerm -> [(StableRef, KTerm)] -> Bool
providerContains trait evidence =
  any (\(candidateTrait, candidateEvidence) -> candidateTrait == trait && candidateEvidence == evidence)

isTypeLevelCarrier :: KTerm -> Bool
isTypeLevelCarrier term =
  stripArithmeticTermWrappers term
    == KTGlobal (stableRefForGlobal prelTypeLevel) []

isBoolCarrier :: KTerm -> Bool
isBoolCarrier term =
  stripArithmeticTermWrappers term
    == KTGlobal (stableRefForGlobal prelBool) []

isTrueTerm :: KTerm -> Bool
isTrueTerm term =
  stripArithmeticTermWrappers term
    == KTConstruct (stableRefForConstructor prelTrue) [] []

isFalseTerm :: KTerm -> Bool
isFalseTerm term =
  stripArithmeticTermWrappers term
    == KTConstruct (stableRefForConstructor prelFalse) [] []

isOmegaTypeLevelTerm :: KTerm -> Bool
isOmegaTypeLevelTerm term =
  stripArithmeticTermWrappers term
    == KTGlobal (stableRefForGlobal prelTypeLevelOmega) []

isFiniteTypeLevelTerm :: KTerm -> Bool
isFiniteTypeLevelTerm term =
  case collectKApplication (stripArithmeticTermWrappers term) of
    (KTGlobal ref [], [_])
      | ref == stableRefForGlobal prelTypeLevelFromInteger -> True
    _ -> False

encodeTypeLevelBoolean :: TypeLevelBoolean -> KValueNode
encodeTypeLevelBoolean = \case
  TypeLevelBooleanLiteral truth ->
    KVList [KVText "literal", KVInteger (if truth then 1 else 0)]
  TypeLevelBooleanConstraint lower upper ->
    KVList
      [ KVText "constraint"
      , encodeTypeLevel (normalizeLevel lower)
      , encodeTypeLevel (normalizeLevel upper)
      ]

encodeTypeLevel :: Level -> KValueNode
encodeTypeLevel = \case
  LZero -> KVList [KVText "zero"]
  LFinite value -> KVList [KVText "finite", KVInteger value]
  LOmega -> KVList [KVText "omega"]
  LSucc level -> KVList [KVText "successor", encodeTypeLevel level]
  LAdd lhs rhs -> KVList [KVText "add", encodeTypeLevel lhs, encodeTypeLevel rhs]
  LMax lhs rhs -> KVList [KVText "maximum", encodeTypeLevel lhs, encodeTypeLevel rhs]
  LVar variable -> KVList [KVText "local", KVInteger (toInteger variable)]
  LParam parameter -> KVList [KVText "universe", KVInteger (toInteger parameter)]
  LField field name ->
    KVList [KVText "field", KVInteger (toInteger field), KVText name]
  LProjection root fields ->
    KVList
      [ KVText "projection"
      , KVInteger (toInteger root)
      , KVList (map KVText fields)
      ]
  LNeutral atom ->
    KVList [KVText "neutral", KVText (neutralLevelTermDigestFromAtom atom)]
  LMeta meta ->
    KVList [KVText "meta", KVInteger (toInteger meta)]

neutralLevelTermDigestFromAtom :: NeutralLevelAtom -> Text
neutralLevelTermDigestFromAtom = \case
  NeutralLevelTermAtom digest _ -> digest
  NeutralLevelSymbol identity arguments ->
    sha256Hex
      ( "KAPPA:v1:NeutralLevelSymbol:"
          <> identity
          <> ":"
          <> T.intercalate "," (map renderLevel arguments)
      )

isTrueKTerm :: KTerm -> Bool
isTrueKTerm term =
  stripArithmeticTermWrappers term
    == KTConstruct (stableRefForConstructor prelTrue) [] []

isFalseKTerm :: KTerm -> Bool
isFalseKTerm term =
  stripArithmeticTermWrappers term
    == KTConstruct (stableRefForConstructor prelFalse) [] []

lastTwo :: [a] -> Maybe (a, a)
lastTwo values = case reverse values of
  rhs : lhs : _ -> Just (lhs, rhs)
  _ -> Nothing

typedImplGenericTags :: Set Text
typedImplGenericTags =
  Set.fromList
    [ "impl.kappa.core.arithmetic-proof"
    , "impl.kappa.core.inject"
    , "impl.kappa.core.seal"
    , "impl.kappa.core.thunk"
    , "impl.kappa.core.lazy"
    , "impl.kappa.core.quote"
    , "impl.kappa.core.force"
    , "impl.kappa.core.do"
    , intrinsicEffectTreeTag
    ]

verifyImplGenericSchema :: Text -> [(Text, KValueNode)] -> Either KCoreTextError ()
verifyImplGenericSchema tag fields = do
  when (length names /= Set.size (Set.fromList names)) $
    Left (invalid ("generic term node '" <> tag <> "' has duplicate fields"))
  case Map.lookup tag schemas of
    Nothing -> Left (invalid ("unsupported impl.kappa generic term node '" <> tag <> "'"))
    Just expected ->
      unless (Set.fromList names == Set.fromList expected) $
        Left
          ( invalid
              ( "generic term node '" <> tag <> "' requires fields "
                  <> T.intercalate ", " expected
              )
          )
  case tag of
    "impl.kappa.core.do.assign" -> case lookup "monadic" fields of
      Just (KVInteger value) | value == 0 || value == 1 -> pure ()
      _ -> Left (invalid "do.assign monadic field must be integer-value(0) or integer-value(1)")
    _ -> pure ()
  where
    names = map fst fields
    typed rest = "result-type" : rest
    schemas =
      Map.fromList
        [ ("impl.kappa.core.literal", ["kind", "value"])
        , ("impl.kappa.core.arithmetic-proof", typed ["replay-goal", "version", "domain", "providers", "variables", "assumptions", "replay"])
        , ("impl.kappa.core.record-type", ["names", "fields"])
        , ("impl.kappa.core.record-value", ["names", "values"])
        , ("impl.kappa.core.if", ["condition", "then", "else"])
        , ("impl.kappa.core.body-unavailable", [])
        , ("impl.kappa.level-value", ["level"])
        , ("impl.kappa.core.variant-type", ["tags", "members"])
        , ("impl.kappa.core.inject", typed ["tag", "value"])
        , ("impl.kappa.core.seal", typed ["labels", "value"])
        , ("impl.kappa.core.signature-type", ["labels", "value"])
        , ("impl.kappa.core.thunk", typed ["value"])
        , ("impl.kappa.core.lazy", typed ["value"])
        , ("impl.kappa.core.quote", typed ["syntax", "captures", "origin", "slots"])
        , ("impl.kappa.core.force", typed ["value"])
        , ("impl.kappa.core.do", typed ["label", "items"])
        , ("impl.kappa.core.do.bind", ["action", "quantity", "pattern"])
        , ("impl.kappa.core.do.let", ["quantity", "pattern", "value"])
        , ("impl.kappa.core.do.letq", ["pattern", "value", "else-pattern", "else-action"])
        , ("impl.kappa.core.do.expr", ["value"])
        , ("impl.kappa.core.do.return", ["value"])
        , ("impl.kappa.core.do.break", ["label"])
        , ("impl.kappa.core.do.continue", ["label"])
        , ("impl.kappa.core.do.var", ["binder", "initial", "action"])
        , ("impl.kappa.core.do.assign", ["ref", "monadic", "rhs", "action"])
        , ("impl.kappa.core.do.while", ["label", "condition-kind", "condition", "body", "else"])
        , ("impl.kappa.core.do.for", ["label", "pattern", "source", "body", "else"])
        , ("impl.kappa.core.do.if", ["conditions", "bodies", "else"])
        , ("impl.kappa.core.do.defer", ["label", "action"])
        , ("impl.kappa.core.do.using", ["pattern", "acquire", "release"])
        , ("impl.kappa.core.do.subdo", ["label", "items"])
        , (intrinsicEffectTreeTag, typed ["constructor", "constructor-type", "arguments"])
        ]

intrinsicEffectTreeTag :: Text
intrinsicEffectTreeTag = "impl.kappa.core.effect-tree-constructor"

-- | Independently replay the typed contract of the two implementation-owned
-- effect-tree constructors. They are not source data constructors and hence
-- have no entry in the portable constructor table; accepting their serialized
-- telescope without this identity-and-shape check would turn an untrusted
-- annotation into typing authority.
verifyIntrinsicEffectTree
  :: VerifyContext
  -> Set Int
  -> Assumptions
  -> LocalEnv
  -> [(Text, KValueNode)]
  -> Either KCoreTextError ()
verifyIntrinsicEffectTree context universes assumptions env fields = do
  (constructor, levels) <- case lookup "constructor" fields of
    Just (KVGlobal ref instantiation) -> pure (ref, instantiation)
    _ -> Left (invalid "effect-tree constructor identity must be a global-ref value")
  unless (null levels) $
    Left (invalid "effect-tree intrinsics do not accept declaration-universe arguments")
  constructorType <- requiredTerm "constructor-type"
  resultType <- requiredTerm "result-type"
  arguments <- case lookup "arguments" fields of
    Just (KVList values) -> mapM expectTerm values
    _ -> Left (invalid "effect-tree constructor arguments must be a term-value list")
  verifyType constructorType "constructor telescope"
  verifyType resultType "result type"
  residual <-
    applyArguments
      ( freshenKPiTelescopeForArguments
          (map (KArgument KExplicit) arguments)
          constructorType
      )
      arguments
  unless (sameType residual resultType) $
    Left (invalid "effect-tree constructor telescope does not produce its declared result type")
  if constructor == stableRefForConstructor prelEffPure
    then verifyPureShape constructorType resultType
    else if constructor == stableRefForConstructor prelEffOp
      then verifyOperationShape constructorType resultType arguments
      else Left (invalid "effect-tree constructor identity is not compiler-owned")
  where
    sameType = sameKCoreTypeUnderIn assumptions env context
    requiredTerm name = case lookup name fields of
      Just (KVTerm term) -> pure term
      _ -> Left (invalid ("effect-tree field '" <> name <> "' must be a term value"))
    expectTerm = \case
      KVTerm term -> pure term
      _ -> Left (invalid "effect-tree constructor arguments must contain only term values")
    verifyType term label = do
      verifyTerm context universes assumptions env term
      inferSimple context universes assumptions env term >>= \case
        Just KTType {} -> pure ()
        _ -> Left (invalid ("effect-tree " <> label <> " is not a type"))
    applyArguments signature [] = pure signature
    applyArguments signature (argument : rest) =
      case unfoldTypeHead context signature of
        KTPi binder codomain -> do
          unless (kbExplicitness binder == KExplicit) $
            Left (invalid "effect-tree intrinsic telescope must be explicit")
          checkTermObserved (kbMode binder) context universes assumptions env argument (kbType binder)
          applyArguments (substituteLocal (kbRef binder) argument codomain) rest
        _ -> Left (invalid "effect-tree constructor argument count exceeds its telescope")
    splitPis = go []
      where
        go binders (KTPi binder codomain) = go (binders ++ [binder]) codomain
        go binders result = (binders, result)
    effResult term =
      case collectApplication (unfoldTypeHead context term) of
        (KTGlobal ref _, [KArgument KExplicit row, KArgument KExplicit result])
          | ref == stableRefForGlobal prelEff -> Just (row, result)
        _ -> Nothing
    verifyPureShape constructorType resultType = do
      let (binders, result) = splitPis constructorType
      unless (length binders == 1 && sameType result resultType) $
        Left (invalid "__EffPure must have one payload binder and return the declared Eff result")
      (_, payloadType) <- maybe (Left (invalid "__EffPure result must be an Eff type")) pure (effResult result)
      case binders of
        [payload]
          | kbMode payload == Ordinary
          , kbQuantity payload == KQ1
          , sameType (kbType payload) payloadType -> pure ()
        _ -> Left (invalid "__EffPure payload contract does not match its Eff result")
    verifyOperationShape constructorType resultType arguments = do
      let (binders, result) = splitPis constructorType
      (row, operationResult) <- maybe (Left (invalid "__EffOp result must be an Eff type")) pure (effResult result)
      unless (length binders == 4 && sameType result resultType) $
        Left (invalid "__EffOp must have label, operation, payload, and resumption binders")
      case (binders, arguments) of
        ([labelBinder, operationBinder, _, resumeBinder], labelArgument : _ : _ : _) -> do
          unless (plainType (kbType labelBinder) prelEffLabel && kbMode labelBinder == Ordinary) $
            Left (invalid "__EffOp label binder must be ordinary EffLabel")
          unless (plainType (kbType operationBinder) prelString && kbMode operationBinder == Ordinary) $
            Left (invalid "__EffOp operation binder must be ordinary String")
          unless (kbMode resumeBinder == Ordinary && kbQuantity resumeBinder == KQ1) $
            Left (invalid "__EffOp resumption binder must be ordinary and linear")
          case unfoldTypeHead context (kbType resumeBinder) of
            KTPi resumeArgument resumeResult -> do
              unless (kbMode resumeArgument == Ordinary && kbQuantity resumeArgument == KQ1) $
                Left (invalid "__EffOp resume payload must be ordinary and linear")
              unless (sameType (kbType resumeArgument) operationResult) $
                Left (invalid "__EffOp resume payload type does not match the operation result")
              unless (sameType resumeResult result) $
                Left (invalid "__EffOp resumption does not return to the enclosing Eff computation")
            _ -> Left (invalid "__EffOp resumption field is not a function")
          rowLabel <- effectRowLabel row
          unless (sameType rowLabel labelArgument) $
            Left (invalid "__EffOp runtime label does not match its declared effect row")
        _ -> Left (invalid "__EffOp argument list does not match its intrinsic telescope")
    effectRowLabel row =
      case collectApplication (unfoldTypeHead context row) of
        (KTGlobal cons _, [KArgument KExplicit label, KArgument KExplicit _, KArgument KExplicit tailRow])
          | cons == stableRefForGlobal prelEffRowCons
          , plainType tailRow prelEffRowNil -> pure label
        _ -> Left (invalid "__EffOp result row must be the selected single-label effect row")
    plainType term global = case unfoldTypeHead context term of
      KTGlobal ref _ -> ref == stableRefForGlobal global
      _ -> False
    collectApplication = go []
      where
        go arguments (KTApply function more) = go (more ++ arguments) function
        go arguments headTerm = (headTerm, arguments)

allStableRefs :: KCoreFile -> [StableRef]
allStableRefs (KCoreFile _ modules) = concatMap moduleRefs modules
  where
    moduleRefs KModule {..} = kmRef : concatMap declAllRefs kmDecls
    declAllRefs = \case
      KDDef ref _ _ ty body -> ref : termRefs ty ++ termRefs body
      KDAxiom ref _ _ ty -> ref : termRefs ty
      KDInterface ref _ ty -> ref : termRefs ty
      KDAssociatedNormalization normalization ->
        kanDictionary normalization
          : kanField normalization
          : concatMap (termRefs . kbType) (kanBinders normalization)
          ++ termRefs (kanValue normalization)
      KDData ref _ binders result certificate constructors ->
        ref : concatMap (termRefs . kbType) binders ++ termRefs result
          ++ [certificate]
          ++ concat [[ctor] ++ termRefs ty | KCtorDecl ctor _ _ ty <- constructors]
      KDLevelCertificate ref _ constraints constraint proof ->
        ref : concatMap constraintRefs constraints ++ constraintRefs constraint ++ proofRefs proof
      KDRepresentationCertificate certificate ->
        krcRef certificate
          : concatMap (termRefs . kbType) (krcBinders certificate)
          ++ concatMap constraintRefs (krcConstraints certificate)
          ++ termRefs (krcTarget certificate)
          ++ concatMap (valueRefs . snd) (krcPayload certificate)
      KDExtension {} -> []
      KDGeneric _ fields -> concatMap (valueRefs . snd) fields
      KDSchemaCertificate certificate -> [kscRef certificate, kscFamily certificate]
      KDTermProbe term -> termRefs term
    constraintRefs (KConstraint _ lhs rhs) = levelRefs lhs ++ levelRefs rhs
    termRefs = \case
      KTLocal _ levels -> concatMap levelRefs levels
      KTGlobal ref levels -> ref : concatMap levelRefs levels
      KTType level -> levelRefs level
      KTPi binder body -> termRefs (kbType binder) ++ termRefs body
      KTSigma binder body -> termRefs (kbType binder) ++ termRefs body
      KTLambda binder body -> termRefs (kbType binder) ++ termRefs body
      KTApply f args -> termRefs f ++ concatMap (termRefs . argumentTerm) args
      KTBlock items result -> concatMap blockItemRefs items ++ termRefs result
      KTLetRec definitions result -> concat [termRefs (kldType definition) ++ termRefs (kldBody definition) | definition <- definitions] ++ termRefs result
      KTCase scrutinee resultType alternatives -> termRefs scrutinee ++ termRefs resultType ++ concatMap caseAltRefs alternatives
      KTConstruct ref levels args -> ref : concatMap levelRefs levels ++ concatMap (termRefs . argumentTerm) args
      KTProject ref term -> ref : termRefs term
      KTLift from to evidence term -> levelRefs from ++ levelRefs to ++ evidenceRefs evidence ++ termRefs term
      KTSchemaLift family from to certificate roles targetArguments term ->
        family : certificate : concatMap levelRefs (from ++ to)
          ++ concatMap schemaRoleRefs roles
          ++ concatMap (termRefs . argumentTerm) targetArguments
          ++ termRefs term
      KTAscribe value ty -> termRefs value ++ termRefs ty
      KTLiteral literal -> termRefs (literalKType literal)
      KTRecordType fields -> map fst fields ++ concatMap (termRefs . kbType . snd) fields
      KTRecordValue fields -> concatMap (termRefs . snd) fields
      KTIf condition thenBranch elseBranch -> termRefs condition ++ termRefs thenBranch ++ termRefs elseBranch
      KTGeneric _ fields -> concatMap (valueRefs . snd) fields
    schemaRoleRefs = \case
      KSchemaCovariant evidence -> evidenceRefs evidence
      _ -> []
    levelRefs = \case
      KLGlobal ref -> [ref]
      KLSucc level -> levelRefs level
      KLMax lhs rhs -> levelRefs lhs ++ levelRefs rhs
      KLAdd lhs rhs -> levelRefs lhs ++ levelRefs rhs
      KLTerm term -> termRefs term
      _ -> []
    evidenceRefs = \case
      KEGlobal ref levels -> ref : concatMap levelRefs levels
      KECertificate ref levels -> ref : concatMap levelRefs levels
      _ -> []
    valueRefs = \case
      KVTerm term -> termRefs term
      KVLevel level -> levelRefs level
      KVQuantity (KQTerm term) -> termRefs term
      KVAccess (KBorrow (Just (KRGlobal ref))) -> [ref]
      KVGlobal ref levels -> ref : concatMap levelRefs levels
      KVBinder binder -> termRefs (kbType binder)
      KVPattern pattern' -> patternRefs pattern'
      KVList values -> concatMap valueRefs values
      _ -> []
    patternRefs (KPattern slot _ node') = termRefs (kbType slot) ++ case node' of
      KPNWild -> []
      KPNLiteral literal -> termRefs (literalKType literal)
      KPNConstructor ref levels existentials bridges fields ->
        ref
          : concatMap levelRefs levels
            ++ concatMap (termRefs . kbType) existentials
            ++ concatMap
              (\bridge -> termRefs (kbType (kcbBinder bridge)) ++ termRefs (kcbProof bridge))
              bridges
            ++ concatMap patternRefs fields
      KPNTuple fields -> concatMap patternRefs fields
      KPNRecord fields rest ->
        [field | (field, _, _) <- fields]
          ++ concatMap (\(_, _, pattern') -> patternRefs pattern') fields
          ++ maybe [] patternRefs rest
      KPNInject _ payload -> patternRefs payload
      KPNInjectRest _ -> []
      KPNOr alternatives _ -> concatMap patternRefs alternatives
      KPNAs payload -> patternRefs payload
    blockItemRefs = \case
      KBLet binder rhs -> termRefs (kbType binder) ++ termRefs rhs
    caseAltRefs = \case
      KCaseDefault body -> termRefs body
      KCaseConstructor ref levels bindings body ->
        ref
          : concatMap levelRefs levels
            ++ concatMap
              (\binding ->
                termRefs (kbType (caseBindingBinder binding))
                  ++ case binding of
                    KCaseBridge bridge -> termRefs (kcbProof bridge)
                    KCasePayload {} -> [])
              bindings
            ++ termRefs body
      KCasePattern pattern' guard' body -> patternRefs pattern' ++ maybe [] termRefs guard' ++ termRefs body
    proofRefs = \case
      KLPAssumption _ -> []
      KLPClosed -> []
      KLPArithmetic _ -> []
      KLPMaxLeast left right -> proofRefs left ++ proofRefs right
      KLPZero level -> levelRefs level
      KLPRefl level -> levelRefs level
      KLPTrans lhs rhs -> proofRefs lhs ++ proofRefs rhs
      KLPSuccMono proof -> proofRefs proof
      KLPMaxLeft lhs rhs -> levelRefs lhs ++ levelRefs rhs
      KLPMaxRight lhs rhs -> levelRefs lhs ++ levelRefs rhs
      KLPAddMonoLeft level proof -> levelRefs level ++ proofRefs proof
      KLPAddMonoRight level proof -> levelRefs level ++ proofRefs proof

-- Canonicalization ----------------------------------------------------------

canonicalizeKCoreFile :: KCoreFile -> KCoreFile
canonicalizeKCoreFile (KCoreFile version modules) =
  KCoreFile version (map canonicalizeModule (sortOn kmRef modules))

canonicalizeModule :: KModule -> KModule
canonicalizeModule module0@KModule {..} =
  let declarations = dependencyOrder kmDecls
      familyScopes = canonicalFamilyScopes declarations
   in module0
        { kmMetadata = sortOn fst kmMetadata
        , kmDecls = map (canonicalizeDeclWithFamilyScopes familyScopes) declarations
        }

-- Emit declaration SCCs in dependency order and sort every recursive SCC by
-- authoritative stable identity. Greedily breaking a cycle one declaration at
-- a time is not canonical: doing so can make another member spuriously ready
-- and interleave one SCC according to traversal order.
dependencyOrder :: [KDecl] -> [KDecl]
dependencyOrder declarations = concatMap flatten orderedSccs
  where
    indexed = zip [0 :: Int ..] declarations
    keyOf index declaration = (declCanonicalKey declaration, index)
    graphKey index declaration = Down (keyOf index declaration)
    owners =
      Map.fromList
        [ (srId ref, graphKey index declaration)
        | (index, declaration) <- indexed
        , ref <- declRefs declaration
        ]
    nodes =
      [ ( declaration
        , graphKey index declaration
        , nub
            [ owner
            | reference <- declReferenceUses declaration
            , Just owner <- [Map.lookup (srId reference) owners]
            , owner /= graphKey index declaration
            ]
        )
      | (index, declaration) <- indexed
      ]
    orderedSccs = stronglyConnComp nodes
    flatten = \case
      AcyclicSCC declaration -> [declaration]
      CyclicSCC members -> sortOn declCanonicalKey members

declCanonicalKey :: KDecl -> (Text, Text)
declCanonicalKey declaration = case sortOn srId (declRefs declaration) of
  ref : _ -> (srId ref, "")
  [] -> case declaration of
    KDExtension owner version -> ("extension", owner <> ":" <> tshow version)
    KDGeneric tag _ -> ("generic", tag)
    KDInterface ref _ _ -> ("interface", srId ref)
    KDAssociatedNormalization normalization ->
      ( "associated-normalization"
      , srId (kanDictionary normalization) <> ":" <> srId (kanField normalization)
      )
    _ -> ("", "")

declReferenceUses :: KDecl -> [StableRef]
declReferenceUses = \case
  KDDef _ _ _ ty body -> termStableRefs ty ++ termStableRefs body
  KDAxiom _ _ _ ty -> termStableRefs ty
  KDInterface ref _ ty -> ref : termStableRefs ty
  KDAssociatedNormalization KAssociatedNormalization {..} ->
    kanDictionary
      : kanField
      : concatMap (termStableRefs . kbType) kanBinders
      ++ termStableRefs kanValue
  KDData _ _ binders result certificate constructors ->
    concatMap (termStableRefs . kbType) binders
      ++ termStableRefs result
      ++ [certificate]
      ++ concatMap (\(KCtorDecl _ _ fields ty) -> map fst fields ++ termStableRefs ty) constructors
  KDLevelCertificate _ _ constraints constraint proof ->
    concatMap constraintStableRefs constraints ++ constraintStableRefs constraint ++ levelProofStableRefs proof
  KDRepresentationCertificate certificate ->
    concatMap (termStableRefs . kbType) (krcBinders certificate)
      ++ concatMap constraintStableRefs (krcConstraints certificate)
      ++ termStableRefs (krcTarget certificate)
      ++ concatMap (valueStableRefs . snd) (krcPayload certificate)
  KDSchemaCertificate certificate ->
    kscFamily certificate
      : concatMap
          (\witness -> termStableRefs (kmwOperator witness) ++ termStableRefs (kmwGoal witness) ++ termStableRefs (kmwEvidence witness))
          (kscMonotoneWitnesses certificate)
  KDTermProbe term -> termStableRefs term
  KDExtension {} -> []
  KDGeneric _ fields -> concatMap (valueStableRefs . snd) fields

constraintStableRefs :: KConstraint -> [StableRef]
constraintStableRefs (KConstraint _ lhs rhs) = levelStableRefs lhs ++ levelStableRefs rhs

termStableRefs :: KTerm -> [StableRef]
termStableRefs = \case
  KTLocal _ levels -> concatMap levelStableRefs levels
  KTGlobal ref levels -> ref : concatMap levelStableRefs levels
  KTType level -> levelStableRefs level
  KTPi binder body -> termStableRefs (kbType binder) ++ termStableRefs body
  KTSigma binder body -> termStableRefs (kbType binder) ++ termStableRefs body
  KTLambda binder body -> termStableRefs (kbType binder) ++ termStableRefs body
  KTApply fun args -> termStableRefs fun ++ concatMap (termStableRefs . argumentTerm) args
  KTBlock items result -> concatMap blockItemStableRefs items ++ termStableRefs result
  KTLetRec definitions result -> concat [termStableRefs (kldType definition) ++ termStableRefs (kldBody definition) | definition <- definitions] ++ termStableRefs result
  KTCase scrutinee resultType alternatives -> termStableRefs scrutinee ++ termStableRefs resultType ++ concatMap caseAltStableRefs alternatives
  KTConstruct ref levels args -> ref : concatMap levelStableRefs levels ++ concatMap (termStableRefs . argumentTerm) args
  KTProject ref term -> ref : termStableRefs term
  KTLift from to evidence term -> levelStableRefs from ++ levelStableRefs to ++ evidenceStableRefs evidence ++ termStableRefs term
  KTSchemaLift family from to certificate roles targetArguments term ->
    family : certificate : concatMap levelStableRefs (from ++ to)
      ++ concatMap schemaRoleStableRefs roles
      ++ concatMap (termStableRefs . argumentTerm) targetArguments
      ++ termStableRefs term
  KTAscribe value ty -> termStableRefs value ++ termStableRefs ty
  KTLiteral literal -> termStableRefs (literalKType literal)
  KTRecordType fields -> map fst fields ++ concatMap (termStableRefs . kbType . snd) fields
  KTRecordValue fields -> concatMap (termStableRefs . snd) fields
  KTIf condition thenBranch elseBranch -> termStableRefs condition ++ termStableRefs thenBranch ++ termStableRefs elseBranch
  KTGeneric _ fields -> concatMap (valueStableRefs . snd) fields

termLocalRefs :: KTerm -> [LocalRef]
termLocalRefs = \case
  KTLocal ref levels -> ref : concatMap levelLocalRefs levels
  KTGlobal _ levels -> concatMap levelLocalRefs levels
  KTType level -> levelLocalRefs level
  KTPi binder body -> termLocalRefs (kbType binder) ++ termLocalRefs body
  KTSigma binder body -> termLocalRefs (kbType binder) ++ termLocalRefs body
  KTLambda binder body -> termLocalRefs (kbType binder) ++ termLocalRefs body
  KTApply function arguments -> termLocalRefs function ++ concatMap (termLocalRefs . argumentTerm) arguments
  KTBlock items result ->
    concatMap (\case KBLet binder rhs -> termLocalRefs (kbType binder) ++ termLocalRefs rhs) items
      ++ termLocalRefs result
  KTLetRec definitions result ->
    concatMap (\definition -> termLocalRefs (kldType definition) ++ termLocalRefs (kldBody definition)) definitions
      ++ termLocalRefs result
  KTCase scrutinee result alternatives ->
    termLocalRefs scrutinee ++ termLocalRefs result ++ concatMap alternativeLocals alternatives
  KTConstruct _ levels arguments ->
    concatMap levelLocalRefs levels ++ concatMap (termLocalRefs . argumentTerm) arguments
  KTProject _ record -> termLocalRefs record
  KTLift from to _ term -> levelLocalRefs from ++ levelLocalRefs to ++ termLocalRefs term
  KTSchemaLift _ from to _ _ targetArguments term ->
    concatMap levelLocalRefs (from ++ to)
      ++ concatMap (termLocalRefs . argumentTerm) targetArguments
      ++ termLocalRefs term
  KTAscribe value ty -> termLocalRefs value ++ termLocalRefs ty
  KTLiteral _ -> []
  KTRecordType fields -> concatMap (termLocalRefs . kbType . snd) fields
  KTRecordValue fields -> concatMap (termLocalRefs . snd) fields
  KTIf condition yes no -> termLocalRefs condition ++ termLocalRefs yes ++ termLocalRefs no
  KTGeneric _ fields -> concatMap (valueLocalRefs . snd) fields
  where
    alternativeLocals = \case
      KCaseDefault body -> termLocalRefs body
      KCaseConstructor _ levels bindings body ->
        concatMap levelLocalRefs levels
          ++ concatMap
            (\binding ->
              termLocalRefs (kbType (caseBindingBinder binding))
                ++ case binding of
                  KCaseBridge bridge -> termLocalRefs (kcbProof bridge)
                  KCasePayload {} -> [])
            bindings
          ++ termLocalRefs body
      KCasePattern _ guard' body -> maybe [] termLocalRefs guard' ++ termLocalRefs body

levelLocalRefs :: KLevel -> [LocalRef]
levelLocalRefs = \case
  KLSucc level -> levelLocalRefs level
  KLMax left right -> levelLocalRefs left ++ levelLocalRefs right
  KLAdd left right -> levelLocalRefs left ++ levelLocalRefs right
  KLTerm term -> termLocalRefs term
  _ -> []

valueLocalRefs :: KValueNode -> [LocalRef]
valueLocalRefs = \case
  KVTerm term -> termLocalRefs term
  KVLevel level -> levelLocalRefs level
  KVQuantity (KQTerm term) -> termLocalRefs term
  KVAccess (KBorrow (Just (KRLocal ref))) -> [ref]
  KVLocal ref levels -> ref : concatMap levelLocalRefs levels
  KVBinder binder -> termLocalRefs (kbType binder)
  KVList values -> concatMap valueLocalRefs values
  _ -> []

schemaRoleStableRefs :: KSchemaRoleEvidence -> [StableRef]
schemaRoleStableRefs = \case
  KSchemaCovariant evidence -> evidenceStableRefs evidence
  _ -> []

levelStableRefs :: KLevel -> [StableRef]
levelStableRefs = \case
  KLGlobal ref -> [ref]
  KLSucc level -> levelStableRefs level
  KLMax lhs rhs -> levelStableRefs lhs ++ levelStableRefs rhs
  KLAdd lhs rhs -> levelStableRefs lhs ++ levelStableRefs rhs
  KLTerm term -> termStableRefs term
  _ -> []

evidenceStableRefs :: KEvidence -> [StableRef]
evidenceStableRefs = \case
  KEGlobal ref levels -> ref : concatMap levelStableRefs levels
  KECertificate ref levels -> ref : concatMap levelStableRefs levels
  _ -> []

valueStableRefs :: KValueNode -> [StableRef]
valueStableRefs = \case
  KVTerm term -> termStableRefs term
  KVLevel level -> levelStableRefs level
  KVQuantity (KQTerm term) -> termStableRefs term
  KVAccess (KBorrow (Just (KRGlobal ref))) -> [ref]
  KVGlobal ref levels -> ref : concatMap levelStableRefs levels
  KVBinder binder -> termStableRefs (kbType binder)
  KVPattern pattern' -> patternStableRefs pattern'
  KVList values -> concatMap valueStableRefs values
  _ -> []

patternStableRefs :: KPattern -> [StableRef]
patternStableRefs (KPattern slot _ node') = termStableRefs (kbType slot) ++ case node' of
  KPNWild -> []
  KPNLiteral literal -> termStableRefs (literalKType literal)
  KPNConstructor ref levels existentials bridges fields ->
    ref
      : concatMap levelStableRefs levels
        ++ concatMap (termStableRefs . kbType) existentials
        ++ concatMap
          (\bridge ->
            termStableRefs (kbType (kcbBinder bridge))
              ++ termStableRefs (kcbProof bridge))
          bridges
        ++ concatMap patternStableRefs fields
  KPNTuple fields -> concatMap patternStableRefs fields
  KPNRecord fields rest ->
    [field | (field, _, _) <- fields]
      ++ concatMap (\(_, _, pattern') -> patternStableRefs pattern') fields
      ++ maybe [] patternStableRefs rest
  KPNInject _ payload -> patternStableRefs payload
  KPNInjectRest _ -> []
  KPNOr alternatives _ -> concatMap patternStableRefs alternatives
  KPNAs payload -> patternStableRefs payload

blockItemStableRefs :: KBlockItem -> [StableRef]
blockItemStableRefs = \case
  KBLet binder rhs -> termStableRefs (kbType binder) ++ termStableRefs rhs

caseAltStableRefs :: KCaseAlt -> [StableRef]
caseAltStableRefs = \case
  KCaseDefault body -> termStableRefs body
  KCaseConstructor ref levels bindings body ->
    ref
      : concatMap levelStableRefs levels
        ++ concatMap
          (\binding ->
            termStableRefs (kbType (caseBindingBinder binding))
              ++ case binding of
                KCaseBridge bridge -> termStableRefs (kcbProof bridge)
                KCasePayload {} -> [])
          bindings
        ++ termStableRefs body
  KCasePattern pattern' guard' body -> patternStableRefs pattern' ++ maybe [] termStableRefs guard' ++ termStableRefs body

levelProofStableRefs :: KLevelProof -> [StableRef]
levelProofStableRefs = \case
  KLPAssumption _ -> []
  KLPClosed -> []
  KLPArithmetic _ -> []
  KLPMaxLeast left right -> levelProofStableRefs left ++ levelProofStableRefs right
  KLPZero level -> levelStableRefs level
  KLPRefl level -> levelStableRefs level
  KLPTrans lhs rhs -> levelProofStableRefs lhs ++ levelProofStableRefs rhs
  KLPSuccMono proof -> levelProofStableRefs proof
  KLPMaxLeft lhs rhs -> levelStableRefs lhs ++ levelStableRefs rhs
  KLPMaxRight lhs rhs -> levelStableRefs lhs ++ levelStableRefs rhs
  KLPAddMonoLeft level proof -> levelStableRefs level ++ levelProofStableRefs proof
  KLPAddMonoRight level proof -> levelStableRefs level ++ levelProofStableRefs proof

data CanonState = CanonState
  { canonNextLocal :: !Int
  , canonLocals :: !(Map Int LocalRef)
  }

data CanonFamilyScope = CanonFamilyScope
  { cfsUniverses :: !(Map Int UniverseRef)
  , cfsLocals :: !CanonState
  }

canonicalFamilyScopes :: [KDecl] -> Map StableRef CanonFamilyScope
canonicalFamilyScopes declarations =
  Map.fromList
    [ (ref, familyScope roleUniverses binders)
    | KDData ref roleUniverses binders _ _ _ <- declarations
    ]
  where
    familyScope roleUniverses binders =
      let (_, universeMap) = canonicalUniverses (map fst roleUniverses)
          localState =
            execState
              (mapM_ (canonicalBinder universeMap) binders)
              (CanonState 0 Map.empty)
       in CanonFamilyScope universeMap localState

canonicalizeDecl :: KDecl -> KDecl
canonicalizeDecl = canonicalizeDeclWithFamilyScopes Map.empty

canonicalizeDeclWithFamilyScopes :: Map StableRef CanonFamilyScope -> KDecl -> KDecl
canonicalizeDeclWithFamilyScopes familyScopes declaration =
  evalState (go declaration) (CanonState 0 Map.empty)
  where
    go = \case
      KDDef ref mode universes ty body -> do
        let (universes', universeMap) = canonicalUniverses universes
        ty' <- canonicalTerm universeMap ty
        body' <- canonicalTerm universeMap body
        pure (KDDef ref mode universes' ty' body')
      KDAxiom ref mode universes ty -> do
        let (universes', universeMap) = canonicalUniverses universes
        KDAxiom ref mode universes' <$> canonicalTerm universeMap ty
      KDInterface ref universes ty -> do
        let (universes', universeMap) = canonicalUniverses universes
        KDInterface ref universes' <$> canonicalTerm universeMap ty
      KDAssociatedNormalization normalization -> do
        let (universes', universeMap) =
              canonicalUniverses (kanUniverses normalization)
        withLocalScope $ do
          binders' <- mapM (canonicalBinder universeMap) (kanBinders normalization)
          value' <- canonicalTerm universeMap (kanValue normalization)
          pure
            ( KDAssociatedNormalization
                normalization
                  { kanUniverses = universes'
                  , kanBinders = binders'
                  , kanValue = value'
                  }
            )
      KDData ref roleUniverses binders result certificate constructors -> do
        let (universes', universeMap) = canonicalUniverses (map fst roleUniverses)
            roles = map snd roleUniverses
        withLocalScope $ do
          binders' <- mapM (canonicalBinder universeMap) binders
          result' <- canonicalTerm universeMap result
          constructors' <- forM constructors $ \(KCtorDecl ctor ctorUniverses fields ty) -> do
            let (ctorUniverses', ctorMap) = canonicalUniverses ctorUniverses
                ctorUniverseMap = Map.union ctorMap universeMap
            KCtorDecl ctor ctorUniverses' (sortOn snd fields) <$> canonicalTerm ctorUniverseMap ty
          pure (KDData ref (zip universes' roles) binders' result' certificate constructors')
      KDLevelCertificate ref universes constraints constraint proof -> do
        let (universes', universeMap) = canonicalUniverses universes
            (constraints', indexMap) = canonicalConstraintBlock universeMap constraints
            constraint' = canonicalConstraint universeMap constraint
        pure
          ( KDLevelCertificate
              ref
              universes'
              constraints'
              constraint'
              (canonicalLevelProof indexMap constraints' constraint' proof)
          )
      KDRepresentationCertificate certificate -> do
        let (universes', universeMap) =
              canonicalUniverses (krcUniverses certificate)
            (constraints', _) =
              canonicalConstraintBlock universeMap (krcConstraints certificate)
        withLocalScope $ do
          binders' <-
            mapM (canonicalBinder universeMap) (krcBinders certificate)
          target' <- canonicalTerm universeMap (krcTarget certificate)
          payload' <-
            mapM
              (\(name, value) ->
                (name,) <$> canonicalValue universeMap value)
              (krcPayload certificate)
          pure
            ( KDRepresentationCertificate
                certificate
                  { krcUniverses = universes'
                  , krcBinders = binders'
                  , krcConstraints = constraints'
                  , krcTarget = target'
                  , krcPayload = sortOn fst payload'
                  }
            )
      KDSchemaCertificate certificate ->
        KDSchemaCertificate <$> case Map.lookup (kscFamily certificate) familyScopes of
          Nothing -> pure (canonicalizeSchemaCertificate certificate)
          Just CanonFamilyScope {..} ->
            pure
              ( evalState
                  (canonicalizeSchemaCertificateM cfsUniverses certificate)
                  cfsLocals
              )
      KDTermProbe term -> KDTermProbe <$> canonicalTerm Map.empty term
      KDExtension owner version -> pure (KDExtension owner version)
      KDGeneric tag fields -> KDGeneric tag <$> mapM (\(name, value) -> (name,) <$> canonicalValue Map.empty value) fields

    canonicalizeSchemaCertificate certificate =
      certificate
        { kscMonotoneWitnesses = sortWitnesses (kscMonotoneWitnesses certificate)
        }

    canonicalizeSchemaCertificateM universes certificate = do
      witnesses <- mapM (canonicalizeMonotoneWitness universes) (kscMonotoneWitnesses certificate)
      pure certificate {kscMonotoneWitnesses = sortWitnesses witnesses}

    canonicalizeMonotoneWitness universes witness = do
      operator <- canonicalTerm universes (kmwOperator witness)
      goal <- canonicalTerm universes (kmwGoal witness)
      evidence <- canonicalTerm universes (kmwEvidence witness)
      dependencies <- sort . nub <$> mapM canonicalDependency (kmwDependencies witness)
      pure
        witness
          { kmwOperator = operator
          , kmwGoal = goal
          , kmwEvidence = evidence
          , kmwDependencies = dependencies
          }

    canonicalDependency = \case
      KRGlobal ref -> pure (KRGlobal ref)
      KRLocal ref -> KRLocal <$> canonicalLocalUse ref

    sortWitnesses =
      sortOn
        (\witness -> (kmwParameter witness, kmwOperator witness, kmwGoal witness, kmwDependencies witness))

canonicalUniverses :: [UniverseRef] -> ([UniverseRef], Map Int UniverseRef)
canonicalUniverses refs =
  let canonical = [UniverseRef "u" index | index <- [0 .. length refs - 1]]
   in (canonical, Map.fromList [(urId old, new) | (old, new) <- zip refs canonical])

-- Local universe identities share the term-level namespace with enclosing
-- declaration/local telescopes in KCoreText. Allocate a source-independent
-- fresh range so alpha-renaming cannot affect canonical text and a nested
-- telescope cannot alias an outer universe parameter.
freshCanonicalUniverses :: Map Int UniverseRef -> Int -> [UniverseRef]
freshCanonicalUniverses scope count =
  [UniverseRef "u" ident | ident <- take count available]
  where
    used = Set.fromList (map urId (Map.elems scope))
    available = filter (`Set.notMember` used) [0 ..]

canonicalConstraint :: Map Int UniverseRef -> KConstraint -> KConstraint
canonicalConstraint universes (KConstraint strict lhs rhs) =
  KConstraint strict (canonicalLevel universes lhs) (canonicalLevel universes rhs)

canonicalConstraintBlock :: Map Int UniverseRef -> [KConstraint] -> ([KConstraint], Map Int Int)
canonicalConstraintBlock universes constraints =
  (map snd sorted, Map.fromList [(oldIndex, newIndex) | (newIndex, (oldIndex, _)) <- zip [0 ..] sorted])
  where
    sorted =
      sortOn
        (\(oldIndex, constraint) -> (constraint, oldIndex))
        [ (oldIndex, canonicalConstraint universes constraint)
        | (oldIndex, constraint) <- zip [0 ..] constraints
        ]

withLocalScope :: State CanonState a -> State CanonState a
withLocalScope action = do
  state0 <- get
  result <- action
  state1 <- get
  put state1 {canonLocals = canonLocals state0}
  pure result

canonicalBinder :: Map Int UniverseRef -> KBinder -> State CanonState KBinder
canonicalBinder universes binder = do
  ty <- canonicalTerm universes (kbType binder)
  access <- canonicalAccess (kbAccess binder)
  ref <- canonicalLocal (kbRef binder)
  pure
    binder
      { kbRef = ref
      , kbType = ty
      , kbAccess = access
      }

canonicalLocal :: LocalRef -> State CanonState LocalRef
canonicalLocal old = do
  state <- get
  case Map.lookup (lrId old) (canonLocals state) of
    Just ref -> pure ref
    Nothing -> do
      let ref = LocalRef "v" (canonNextLocal state)
      put
        state
          { canonNextLocal = canonNextLocal state + 1
          , canonLocals = Map.insert (lrId old) ref (canonLocals state)
          }
      pure ref

canonicalLocalUse :: LocalRef -> State CanonState LocalRef
canonicalLocalUse ref = do
  state <- get
  pure (Map.findWithDefault ref (lrId ref) (canonLocals state))

canonicalAccess :: KAccess -> State CanonState KAccess
canonicalAccess = \case
  KValue -> pure KValue
  KBorrow Nothing -> pure (KBorrow Nothing)
  KBorrow (Just (KRGlobal ref)) -> pure (KBorrow (Just (KRGlobal ref)))
  KBorrow (Just (KRLocal ref)) -> KBorrow . Just . KRLocal <$> canonicalLocalUse ref

canonicalTerm :: Map Int UniverseRef -> KTerm -> State CanonState KTerm
canonicalTerm universes = \case
  KTLocal ref levels -> KTLocal <$> canonicalLocalUse ref <*> mapM (canonicalLevelM universes) levels
  KTGlobal ref levels -> KTGlobal ref <$> mapM (canonicalLevelM universes) levels
  KTType level -> KTType <$> canonicalLevelM universes level
  KTPi binder body -> withLocalScope $ do
    binder' <- canonicalBinder universes binder
    KTPi binder' <$> canonicalTerm universes body
  KTSigma binder body -> withLocalScope $ do
    binder' <- canonicalBinder universes binder
    KTSigma binder' <$> canonicalTerm universes body
  KTLambda binder body -> withLocalScope $ do
    binder' <- canonicalBinder universes binder
    KTLambda binder' <$> canonicalTerm universes body
  KTApply fun args -> KTApply <$> canonicalTerm universes fun <*> mapM canonicalArgument args
  KTBlock items result -> withLocalScope $ KTBlock <$> mapM canonicalBlockItem items <*> canonicalTerm universes result
  KTLetRec definitions result -> withLocalScope $ do
    refs <- mapM (canonicalLocal . kldRef) definitions
    let sharedUniverses = case definitions of
          first : _ -> freshCanonicalUniverses universes (length (kldUniverses first))
          [] -> []
    definitions' <- forM (zip refs definitions) $ \(ref, definition) -> do
      let localMap = Map.fromList [(urId old, new) | (old, new) <- zip (kldUniverses definition) sharedUniverses]
          scope = Map.union localMap universes
      KLocalDef ref (kldMode definition) sharedUniverses
        <$> canonicalTerm scope (kldType definition)
        <*> canonicalTerm scope (kldBody definition)
    KTLetRec definitions' <$> canonicalTerm universes result
  KTCase scrutinee resultType alternatives ->
    KTCase <$> canonicalTerm universes scrutinee <*> canonicalTerm universes resultType <*> mapM canonicalCaseAlt alternatives
  KTConstruct ref levels args -> KTConstruct ref <$> mapM (canonicalLevelM universes) levels <*> mapM canonicalArgument args
  KTProject ref term -> KTProject ref <$> canonicalTerm universes term
  KTLift from to evidence term -> do
    from' <- canonicalLevelM universes from
    to' <- canonicalLevelM universes to
    evidence' <- canonicalEvidence universes evidence
    term' <- canonicalTerm universes term
    pure $
      if sameKLevel from' to'
        then term'
        else KTLift from' to' evidence' term'
  KTSchemaLift family from to certificate roles targetArguments term -> do
    from' <- mapM (canonicalLevelM universes) from
    to' <- mapM (canonicalLevelM universes) to
    roles' <- mapM canonicalSchemaRole roles
    targetArguments' <- mapM canonicalArgument targetArguments
    term' <- canonicalTerm universes term
    pure $
      if sameKLevels from' to'
        then term'
        else
          KTSchemaLift family from' to' certificate roles'
            targetArguments' term'
  KTAscribe value ty -> KTAscribe <$> canonicalTerm universes value <*> canonicalTerm universes ty
  KTLiteral literal -> pure (KTLiteral literal)
  KTRecordType fields -> withLocalScope $
    KTRecordType <$> mapM (\(field, binder) -> (field,) <$> canonicalBinder universes binder) fields
  KTRecordValue fields ->
    KTRecordValue <$> mapM (\(name, value) -> (name,) <$> canonicalTerm universes value) fields
  KTIf condition thenBranch elseBranch ->
    KTIf <$> canonicalTerm universes condition <*> canonicalTerm universes thenBranch <*> canonicalTerm universes elseBranch
  KTGeneric tag fields -> KTGeneric tag <$> mapM (\(name, value) -> (name,) <$> canonicalValue universes value) fields
  where
    canonicalArgument (KArgument explicitness term) = KArgument explicitness <$> canonicalTerm universes term
    canonicalSchemaRole = \case
      KSchemaInvariant -> pure KSchemaInvariant
      KSchemaIrrelevant -> pure KSchemaIrrelevant
      KSchemaCovariant evidence -> KSchemaCovariant <$> canonicalEvidence universes evidence
    canonicalBlockItem = \case
      KBLet binder rhs -> do
        rhs' <- canonicalTerm universes rhs
        binder' <- canonicalBinder universes binder
        pure (KBLet binder' rhs')
    canonicalCaseAlt = \case
      KCaseDefault body -> withLocalScope $ KCaseDefault <$> canonicalTerm universes body
      KCaseConstructor ref levels bindings body -> withLocalScope $ do
        levels' <- mapM (canonicalLevelM universes) levels
        bindings' <- mapM canonicalCaseBinding bindings
        KCaseConstructor ref levels bindings' <$> canonicalTerm universes body
      KCasePattern pattern' guard' body ->
        withLocalScope $ KCasePattern <$> canonicalPattern universes pattern'
          <*> traverse (canonicalTerm universes) guard'
          <*> canonicalTerm universes body
    canonicalCaseBinding = \case
      KCasePayload binder ->
        KCasePayload <$> canonicalBinder universes binder
      KCaseBridge bridge -> do
        proof' <- canonicalTerm universes (kcbProof bridge)
        binder' <- canonicalBinder universes (kcbBinder bridge)
        pure (KCaseBridge (KConstructorBridge binder' proof'))

canonicalEvidence :: Map Int UniverseRef -> KEvidence -> State CanonState KEvidence
canonicalEvidence universes = \case
  KELocal ref -> KELocal <$> canonicalLocalUse ref
  KEGlobal ref levels -> KEGlobal ref <$> mapM (canonicalLevelM universes) levels
  KECertificate ref levels -> KECertificate ref <$> mapM (canonicalLevelM universes) levels

canonicalLevelProof :: Map Int Int -> [KConstraint] -> KConstraint -> KLevelProof -> KLevelProof
canonicalLevelProof assumptionIndices constraints theorem proof =
  KLPArithmetic (minimizeDependencies remapped)
  where
    remapped =
      sort . nub $
        [ Map.findWithDefault index index assumptionIndices
        | index <- proofDependencyIndices proof
        ]
    minimizeDependencies dependencies =
      foldl removeIfRedundant dependencies dependencies
    removeIfRedundant current dependency =
      let candidate = filter (/= dependency) current
          selected = mapMaybe lookupConstraint candidate
       in if length selected == length candidate
            && constraintProved (constraintAssumptions selected) theorem
            then candidate
            else current
    lookupConstraint index
      | index < 0 = Nothing
      | otherwise = listToMaybe (drop index constraints)

proofDependencyIndices :: KLevelProof -> [Int]
proofDependencyIndices = \case
  KLPAssumption index -> [index]
  KLPClosed -> []
  KLPArithmetic dependencies -> dependencies
  KLPMaxLeast left right -> proofDependencyIndices left ++ proofDependencyIndices right
  KLPZero _ -> []
  KLPRefl _ -> []
  KLPTrans left right -> proofDependencyIndices left ++ proofDependencyIndices right
  KLPSuccMono child -> proofDependencyIndices child
  KLPMaxLeft _ _ -> []
  KLPMaxRight _ _ -> []
  KLPAddMonoLeft _ child -> proofDependencyIndices child
  KLPAddMonoRight _ child -> proofDependencyIndices child

canonicalLevel :: Map Int UniverseRef -> KLevel -> KLevel
canonicalLevel universes = canonicalizeLevelConstructors . go
  where
    go = \case
      KLUniverse ref -> KLUniverse (Map.findWithDefault ref (urId ref) universes)
      KLSucc level -> KLSucc (go level)
      KLMax lhs rhs -> KLMax (go lhs) (go rhs)
      KLAdd lhs rhs -> KLAdd (go lhs) (go rhs)
      KLTerm term -> KLTerm (evalState (canonicalTerm universes term) (CanonState 0 Map.empty))
      level -> level

canonicalLevelM :: Map Int UniverseRef -> KLevel -> State CanonState KLevel
canonicalLevelM universes level = canonicalizeLevelConstructors <$> go level
  where
    go = \case
      KLUniverse ref -> pure (KLUniverse (Map.findWithDefault ref (urId ref) universes))
      KLSucc child -> KLSucc <$> go child
      KLMax lhs rhs -> KLMax <$> go lhs <*> go rhs
      KLAdd lhs rhs -> KLAdd <$> go lhs <*> go rhs
      KLTerm term -> KLTerm <$> canonicalTerm universes term
      child -> pure child

canonicalizeLevelConstructors :: KLevel -> KLevel
canonicalizeLevelConstructors level =
  case toLevel level of
    Nothing -> level
    Just solverLevel ->
      case levelToText (normalizeLevel solverLevel) of
        Left _ -> level
        Right canonical -> canonical

canonicalValue :: Map Int UniverseRef -> KValueNode -> State CanonState KValueNode
canonicalValue universes = \case
  KVTerm term -> KVTerm <$> canonicalTerm universes term
  KVLevel level -> KVLevel <$> canonicalLevelM universes level
  KVQuantity (KQTerm term) -> KVQuantity . KQTerm <$> canonicalTerm universes term
  KVAccess access -> KVAccess <$> canonicalAccess access
  KVGlobal ref levels -> KVGlobal ref <$> mapM (canonicalLevelM universes) levels
  KVLocal ref levels -> KVLocal <$> canonicalLocalUse ref <*> mapM (canonicalLevelM universes) levels
  KVBinder binder -> KVBinder <$> canonicalBinder universes binder
  KVPattern pattern' -> KVPattern <$> canonicalPattern universes pattern'
  KVList values -> KVList <$> mapM (canonicalValue universes) values
  value -> pure value

canonicalPattern :: Map Int UniverseRef -> KPattern -> State CanonState KPattern
canonicalPattern universes (KPattern slot exposed node') = do
  slot' <- canonicalBinder universes slot
  node'' <- case node' of
    KPNWild -> pure KPNWild
    KPNLiteral literal -> pure (KPNLiteral literal)
    KPNConstructor constructor levels existentials bridges fields -> do
      levels' <- mapM (canonicalLevelM universes) levels
      existentials' <- mapM (canonicalBinder universes) existentials
      bridges' <- mapM canonicalBridge bridges
      fields' <- mapM (canonicalPattern universes) fields
      pure (KPNConstructor constructor levels' existentials' bridges' fields')
    KPNTuple fields -> KPNTuple <$> mapM (canonicalPattern universes) fields
    KPNRecord fields rest ->
      KPNRecord
        <$> mapM (\(field, selected, pattern') -> (field, selected,) <$> canonicalPattern universes pattern') fields
        <*> traverse (canonicalPattern universes) rest
    KPNInject tag payload -> KPNInject tag <$> canonicalPattern universes payload
    KPNInjectRest excluded -> pure (KPNInjectRest excluded)
    KPNOr alternatives permutations -> KPNOr <$> mapM (canonicalPattern universes) alternatives <*> pure permutations
    KPNAs payload -> KPNAs <$> canonicalPattern universes payload
  pure (KPattern slot' exposed node'')
  where
    canonicalBridge bridge = do
      proof' <- canonicalTerm universes (kcbProof bridge)
      binder' <- canonicalBinder universes (kcbBinder bridge)
      pure (KConstructorBridge binder' proof')

-- Canonical printer ----------------------------------------------------------

printCanonicalKCoreText :: KCoreFile -> Text
printCanonicalKCoreText file0 =
  let KCoreFile version modules = canonicalizeKCoreFile file0
   in
  "kcore " <> tshow version <> ";\n\n"
    <> T.intercalate "\n" (map printModule modules)

printModule :: KModule -> Text
printModule KModule {..} =
  "module " <> renderStable kmRef <> metadata <> " {\n"
    <> T.concat (map ((<> "\n") . indent 2 . printDecl) kmDecls)
    <> "}\n"
  where
    metadata
      | null kmMetadata = ""
      | otherwise =
          " [\n"
            <> T.intercalate ",\n" ["  " <> key <> " = " <> quoteText value | (key, value) <- sortOn fst kmMetadata]
            <> "\n]"

printDecl :: KDecl -> Text
printDecl = \case
  KDAxiom ref mode universes ty ->
    "axiom " <> printObservationMode mode <> " " <> renderStable ref <> printUniverses universes <> " :\n"
      <> indent 2 (printTerm ty) <> ";"
  KDInterface ref universes ty ->
    "interface " <> renderStable ref <> printUniverses universes <> " :\n"
      <> indent 2 (printTerm ty) <> ";"
  KDAssociatedNormalization KAssociatedNormalization {..} ->
    "associated-normalization "
      <> renderStable kanDictionary
      <> printUniverses kanUniverses
      <> " "
      <> renderFieldRef kanField
      <> (if null kanBinders then "" else " " <> T.intercalate " " (map printBinder kanBinders))
      <> " =\n"
      <> indent 2 (printTerm kanValue)
      <> ";"
  KDDef ref mode universes ty body ->
    "def " <> printObservationMode mode <> " " <> renderStable ref <> printUniverses universes <> " :\n"
      <> indent 2 (printTerm ty) <> "\n{\n"
      <> "  body =\n" <> indent 4 (printTerm body) <> ";\n}"
  KDData ref universes binders result certificate constructors ->
    "data " <> renderStable ref <> printNominalUniverses universes
      <> (if null binders then "" else " " <> T.intercalate " " (map printBinder binders))
      <> " : " <> printTerm result
      <> "\ncertificate " <> renderStable certificate
      <> " {\n"
      <> T.concat
        [ "  constructor " <> renderStable ctor <> printUniverses ctorUniverses <> " : " <> printTerm ty
            <> printConstructorFields fields <> ";\n"
        | KCtorDecl ctor ctorUniverses fields ty <- constructors
        ]
      <> "}"
  KDSchemaCertificate KSchemaCertificate {..} ->
    "schema-certificate " <> renderStable kscRef <> " for " <> renderStable kscFamily
      <> " [checkerVersion = " <> tshow kscCheckerVersion
      <> ", typeLevelAlgebraVersion = " <> tshow (tlsvAlgebra kscSemanticVersions)
      <> ", levelConstructorNormalizerVersion = " <> tshow (tlsvConstructorNormalizer kscSemanticVersions)
      <> ", levelRigidEntailmentVersion = " <> tshow (tlsvRigidEntailment kscSemanticVersions)
      <> ", levelPrincipalInferenceVersion = " <> tshow (tlsvPrincipalInference kscSemanticVersions)
      <> ", levelCertificateVersion = " <> tshow (tlsvCertificate kscSemanticVersions)
      <> ", signatureHash = " <> (if kscSignatureHash == "local" then "local" else quoteText kscSignatureHash)
      <> ", saturationArity = " <> tshow kscSaturationArity <> "] {\n"
      <> "  roles = [" <> T.intercalate ", " (map printUniverseVariance kscRoles) <> "];\n"
      <> "  clauseKinds = [" <> T.intercalate ", " (map printNominalClauseKind kscClauseKinds) <> "];\n"
      <> "  monotoneWitnesses = ["
      <> ( if null kscMonotoneWitnesses
             then ""
             else "\n" <> T.intercalate ",\n" (map (indent 4 . printMonotoneWitness) kscMonotoneWitnesses) <> "\n  "
         )
      <> "];\n}"
  KDTermProbe term -> "term-node " <> printTerm term
  KDLevelCertificate ref universes constraints constraint proof ->
    "level-certificate " <> renderStable ref <> printUniverses universes <> " : " <> printConstraint constraint
      <> printConstraints constraints <> " {\n"
      <> indent 2 (printLevelProof proof) <> "\n}"
  KDRepresentationCertificate KRepresentationCertificate {..} ->
    "representation-certificate " <> renderStable krcRef
      <> printUniverses krcUniverses
      <> (if null krcBinders then "" else " " <> T.intercalate " " (map printBinder krcBinders))
      <> " [checkerVersion = " <> tshow krcCheckerVersion
      <> ", certificateVersion = " <> tshow krcCertificateVersion
      <> ", kind = " <> printRepresentationCertificateKind krcKind
      <> "] for " <> printTerm krcTarget
      <> printConstraints krcConstraints
      <> "\n" <> printNamedValues krcPayload
  KDExtension owner version -> "extension " <> owner <> " " <> tshow version <> ";"
  KDGeneric tag fields -> "decl-node " <> quoteText tag <> " " <> printNamedValues fields

printConstructorFields :: [(StableRef, Int)] -> Text
printConstructorFields [] = ""
printConstructorFields fields =
  " fields { "
    <> T.concat [renderFieldRef field <> " = " <> tshow index <> "; " | (field, index) <- fields]
    <> "}"

renderFieldRef :: StableRef -> Text
renderFieldRef field = "@field:" <> srName field <> "#" <> srId field

printUniverses :: [UniverseRef] -> Text
printUniverses [] = ""
printUniverses refs = ".{" <> T.intercalate ", " (map renderUniverse refs) <> "}"

printNominalUniverses :: [(UniverseRef, UniverseVariance)] -> Text
printNominalUniverses [] = ""
printNominalUniverses refs =
  ".{" <> T.intercalate ", " [printUniverseVariance role <> " " <> renderUniverse ref | (ref, role) <- refs] <> "}"

printUniverseVariance :: UniverseVariance -> Text
printUniverseVariance = \case
  Invariant -> "invariant"
  Covariant -> "covariant"
  Irrelevant -> "irrelevant"

printNominalClauseKind :: NominalClauseKind -> Text
printNominalClauseKind = \case
  ClauseSortDeclaration -> "sort_declaration"
  ClausePointConstructor -> "point_constructor"
  ClausePathConstructor -> "path_constructor"
  ClauseHigherBoundary -> "higher_boundary"
  ClauseQuotientEquation -> "quotient_equation"
  ClauseRecursiveOperation -> "recursive_operation"
  ClauseRecursiveEquation -> "recursive_equation"
  ClauseGeneratedProjection -> "generated_projection"
  ClauseEliminator -> "eliminator"
  ClauseComputationRule -> "computation_rule"
  ClauseTruncationRule -> "truncation_rule"
  ClauseExtension -> "extension_clause"

printRepresentationCertificateKind :: KRepresentationCertificateKind -> Text
printRepresentationCertificateKind = \case
  KRepresentationOrdinal -> "ordinal"
  KRepresentationExactNatural -> "exact-natural"
  KRepresentationRefinement -> "refinement"

printConstraints :: [KConstraint] -> Text
printConstraints [] = ""
printConstraints constraints =
  "\nwhere {\n"
    <> T.concat
      [ "  " <> printLevel lhs <> (if strict then " < " else " <= ") <> printLevel rhs <> ";\n"
      | KConstraint strict lhs rhs <- constraints
      ]
    <> "}"

printTerm :: KTerm -> Text
printTerm = \case
  KTLocal ref levels -> renderLocal ref <> printUniverseInstantiation levels
  KTGlobal ref [] -> renderStable ref
  KTGlobal ref levels -> renderStable ref <> ".{" <> T.intercalate ", " (map printLevel levels) <> "}"
  KTType level -> "Type " <> printLevel level
  KTPi binder codomain -> "(" <> printBinder binder <> " -> " <> printTerm codomain <> ")"
  KTSigma binder body -> "sigma " <> printBinder binder <> " { " <> printTerm body <> " }"
  KTLambda binder body -> "lambda " <> printBinder binder <> " { " <> printTerm body <> " }"
  KTApply f arguments -> "apply " <> printTerm f <> printArguments arguments
  KTBlock items result ->
    "block {\n"
      <> T.concat (map ((<> "\n") . indent 2 . printBlockItem) items)
      <> indent 2 (printTerm result) <> "\n}"
  KTLetRec definitions result ->
    "letrec {\n"
      <> T.concat (map ((<> "\n") . indent 2 . printLocalDef) definitions)
      <> "} in " <> printTerm result
  KTCase scrutinee resultType alternatives ->
    "case " <> printTerm scrutinee <> " : " <> printTerm resultType <> " {\n"
      <> T.concat (map ((<> "\n") . indent 2 . printCaseAlt) alternatives)
      <> "}"
  KTConstruct ref levels arguments -> "construct " <> renderStable ref <> printUniverseInstantiation levels <> printArguments arguments
  KTProject ref term -> "project " <> renderFieldRef ref <> " " <> printTerm term
  KTLift from to evidence term ->
    "lift [" <> printLevel from <> " <= " <> printLevel to <> " by " <> printEvidence evidence <> "] " <> printTerm term
  KTSchemaLift family from to certificate roles targetArguments term ->
    "schema-lift [family = " <> renderStable family
      <> ", from = " <> printUniverseInstantiation from
      <> ", to = " <> printUniverseInstantiation to
      <> ", certificate = " <> renderStable certificate
      <> ", roles = [" <> T.intercalate ", " (map printSchemaRoleEvidence roles) <> "]"
      <> ", targetArgs = " <> printArguments targetArguments
      <> "] " <> printTerm term
  KTAscribe value ty -> "ascribe " <> printTerm value <> " : " <> printTerm ty
  KTLiteral literal ->
    "term-node \"impl.kappa.core.literal\" " <> printNamedValues (literalNodeFields literal)
  KTRecordType fields ->
    "term-node \"impl.kappa.core.record-type\" "
      <> printNamedValues
        [ ("names", KVList [KVText (srName field) | (field, _) <- fields])
        , ( "fields"
          , KVList [KVTerm (KTPi binder (KTType (KLFinite 0))) | (_, binder) <- fields]
          )
        ]
  KTRecordValue fields ->
    "term-node \"impl.kappa.core.record-value\" "
      <> printNamedValues
        [ ("names", KVList [KVText name | (name, _) <- fields])
        , ("values", KVList [KVTerm value | (_, value) <- fields])
        ]
  KTIf condition thenBranch elseBranch ->
    "term-node \"impl.kappa.core.if\" "
      <> printNamedValues
        [ ("condition", KVTerm condition)
        , ("then", KVTerm thenBranch)
        , ("else", KVTerm elseBranch)
        ]
  KTGeneric tag fields -> "term-node " <> quoteText tag <> " " <> printNamedValues fields

literalNodeFields :: Literal -> [(Text, KValueNode)]
literalNodeFields = \case
  LitInt value -> scalar "int" (KVInteger value)
  LitDouble value -> scalar "double" (KVText (T.pack (show value)))
  LitStr value -> scalar "string" (KVText value)
  LitScalar value -> scalar "scalar" (KVText (T.singleton value))
  LitByte value -> scalar "byte" (KVInteger (toInteger value))
  LitBytes value -> scalar "bytes" (KVList [KVInteger (toInteger byte) | byte <- BS.unpack value])
  LitGrapheme value -> scalar "grapheme" (KVText value)
  where
    scalar kind value = [("kind", KVText kind), ("value", value)]

printBlockItem :: KBlockItem -> Text
printBlockItem = \case
  KBLet binder rhs -> "let " <> printBinder binder <> " = " <> printTerm rhs <> ";"

printLocalDef :: KLocalDef -> Text
printLocalDef KLocalDef {..} =
  "def " <> printObservationMode kldMode <> " " <> renderLocal kldRef <> printUniverses kldUniverses <> " : " <> printTerm kldType
    <> " { body = " <> printTerm kldBody <> "; }"

printCaseAlt :: KCaseAlt -> Text
printCaseAlt = \case
  KCaseDefault body -> "default { " <> printTerm body <> " }"
  KCaseConstructor ref levels bindings body ->
    "case " <> renderStable ref <> printUniverseInstantiation levels
      <> (if null bindings then "" else " " <> T.intercalate " " (map printCaseBinding bindings))
      <> " { " <> printTerm body <> " }"
  KCasePattern pattern' guard' body ->
    "pattern " <> printPattern pattern'
      <> maybe "" ((" when " <>) . printTerm) guard'
      <> " { " <> printTerm body <> " }"
  where
    printCaseBinding = \case
      KCasePayload binder -> printBinder binder
      KCaseBridge bridge ->
        "bridge " <> printBinder (kcbBinder bridge)
          <> " { " <> printTerm (kcbProof bridge) <> " }"

printBinder :: KBinder -> Text
printBinder KBinder {..} =
  "(" <> mode <> " " <> formation <> " " <> quantity <> " " <> explicitness <> " " <> access <> origin <> " "
    <> renderLocal kbRef <> " : " <> printTerm kbType <> ")"
  where
    mode = printObservationMode kbMode
    formation = case kbFormation of
      FormationOrdinary -> "ordinary"
      FormationParametric -> "parametric"
    quantity = case kbQuantity of
      KQ0 -> "0"; KQ1 -> "1"; KQOmega -> "omega"; KQAffine -> "affine"; KQRelevant -> "relevant"
      KQTerm term -> "quantity-term(" <> printTerm term <> ")"
    explicitness = case kbExplicitness of KExplicit -> "explicit"; KImplicit -> "implicit"
    access = case kbAccess of
      KValue -> "value"
      KBorrow Nothing -> "borrow"
      KBorrow (Just ref) -> "borrow[" <> printRef ref <> "]"
    origin = case kbOrigin of
      BinderSourceWritten -> ""
      BinderGenerated -> " generated"

printObservationMode :: ObservationMode -> Text
printObservationMode = \case
  Ordinary -> "ordinary"
  Parametric -> "parametric"

printArguments :: [KArgument] -> Text
printArguments args =
  "(" <> T.intercalate ", " [printExplicitness ic <> " " <> printTerm term | KArgument ic term <- args] <> ")"

printExplicitness :: KExplicitness -> Text
printExplicitness = \case KExplicit -> "explicit"; KImplicit -> "implicit"

printQuantity :: KQuantity -> Text
printQuantity = \case
  KQ0 -> "0"
  KQ1 -> "1"
  KQOmega -> "omega"
  KQAffine -> "affine"
  KQRelevant -> "relevant"
  KQTerm term -> "quantity-term(" <> printTerm term <> ")"

printEvidence :: KEvidence -> Text
printEvidence = \case
  KELocal ref -> renderLocal ref
  KEGlobal ref levels -> renderStable ref <> printUniverseInstantiation levels
  KECertificate ref levels -> "certificate(" <> renderStable ref <> printUniverseInstantiation levels <> ")"

printSchemaRoleEvidence :: KSchemaRoleEvidence -> Text
printSchemaRoleEvidence = \case
  KSchemaInvariant -> "invariant"
  KSchemaIrrelevant -> "irrelevant"
  KSchemaCovariant evidence -> "covariant " <> printEvidence evidence

printRef :: KRef -> Text
printRef = \case KRLocal ref -> renderLocal ref; KRGlobal ref -> renderStable ref

printMonotoneWitness :: KMonotoneWitness -> Text
printMonotoneWitness KMonotoneWitness {..} =
  "{\n"
    <> "  parameter = " <> tshow kmwParameter <> ";\n"
    <> "  operator = " <> printTerm kmwOperator <> ";\n"
    <> "  goal = " <> printTerm kmwGoal <> ";\n"
    <> "  evidence = " <> printTerm kmwEvidence <> ";\n"
    <> "  dependencies = [" <> T.intercalate ", " (map printRef kmwDependencies) <> "];\n"
    <> "}"

printLevel :: KLevel -> Text
printLevel = \case
  KLFinite n -> tshow n
  KLGlobal ref | ref == stableRefForGlobal prelTypeLevelOmega -> "omega"
  KLGlobal ref -> renderStable ref
  KLUniverse ref -> renderUniverse ref
  KLSucc level -> "succ(" <> printLevel level <> ")"
  KLMax lhs rhs -> "max(" <> printLevel lhs <> ", " <> printLevel rhs <> ")"
  KLAdd lhs rhs -> "add(" <> printLevel lhs <> ", " <> printLevel rhs <> ")"
  KLTerm term -> "level-term(" <> printTerm term <> ")"

printUniverseInstantiation :: [KLevel] -> Text
printUniverseInstantiation [] = ""
printUniverseInstantiation levels = ".{" <> T.intercalate ", " (map printLevel levels) <> "}"

printConstraint :: KConstraint -> Text
printConstraint (KConstraint strict lhs rhs) =
  printLevel lhs <> (if strict then " < " else " <= ") <> printLevel rhs

printLevelProof :: KLevelProof -> Text
printLevelProof = \case
  KLPAssumption index -> "assumption(" <> tshow index <> ");"
  KLPClosed -> "closed;"
  KLPArithmetic dependencies -> "arithmetic [" <> T.intercalate ", " (map tshow dependencies) <> "];"
  KLPMaxLeast left right ->
    "max-least {\n" <> indent 2 (printLevelProof left) <> "\n" <> indent 2 (printLevelProof right) <> "\n}"
  KLPZero level -> "zero-left " <> printLevel level <> ";"
  KLPRefl level -> "refl " <> printLevel level <> ";"
  KLPTrans lhs rhs -> "trans {\n" <> indent 2 (printLevelProof lhs) <> "\n" <> indent 2 (printLevelProof rhs) <> "\n}"
  KLPSuccMono proof -> "succ-mono {\n" <> indent 2 (printLevelProof proof) <> "\n}"
  KLPMaxLeft lhs rhs -> "max-left " <> printLevel lhs <> " " <> printLevel rhs <> ";"
  KLPMaxRight lhs rhs -> "max-right " <> printLevel lhs <> " " <> printLevel rhs <> ";"
  KLPAddMonoLeft level proof -> "add-mono-left " <> printLevel level <> " {\n" <> indent 2 (printLevelProof proof) <> "\n}"
  KLPAddMonoRight level proof -> "add-mono-right " <> printLevel level <> " {\n" <> indent 2 (printLevelProof proof) <> "\n}"

printNamedValues :: [(Text, KValueNode)] -> Text
printNamedValues fields =
  "{ " <> T.concat [name <> " = " <> printValue value <> "; " | (name, value) <- sortOn fst fields] <> "}"

printValue :: KValueNode -> Text
printValue = \case
  KVTerm term -> "term-value(" <> printTerm term <> ")"
  KVLevel level -> "level-value(" <> printLevel level <> ")"
  KVQuantity quantity -> "quantity-value(" <> printQuantity quantity <> ")"
  KVObservationMode mode -> case mode of Ordinary -> "ordinary"; Parametric -> "parametric"
  KVExplicitness explicitness -> printExplicitness explicitness
  KVAccess access -> case access of
    KValue -> "value"
    KBorrow Nothing -> "borrow"
    KBorrow (Just ref) -> "borrow[" <> printRef ref <> "]"
  KVGlobal ref levels -> "global-ref-value(" <> renderStable ref <> printUniverseInstantiation levels <> ")"
  KVLocal ref levels -> "local-ref-value(" <> renderLocal ref <> printUniverseInstantiation levels <> ")"
  KVBinder binder -> "binder-value(" <> printBinder binder <> ")"
  KVPattern pattern' -> "pattern-value(" <> printPattern pattern' <> ")"
  KVText value -> "string-value(" <> quoteText value <> ")"
  KVInteger value -> "integer-value(" <> tshow value <> ")"
  KVList values -> "[" <> T.intercalate ", " (map printValue values) <> "]"

printPattern :: KPattern -> Text
printPattern (KPattern slot exposed patternNode) =
  case patternNode of
    KPNWild -> node "wild" []
    KPNLiteral literal -> node "literal" [("value", KVTerm (KTLiteral literal))]
    KPNConstructor constructor levels existentials bridges fields ->
      node "constructor"
        [ ("constructor", KVGlobal constructor levels)
        , ("existentials", KVList (map KVBinder existentials))
        , ( "bridges"
          , KVList
              [ KVList [KVBinder (kcbBinder bridge), KVTerm (kcbProof bridge)]
              | bridge <- bridges
              ]
          )
        , ("fields", KVList (map KVPattern fields))
        ]
    KPNTuple fields -> node "tuple" [("fields", KVList (map KVPattern fields))]
    KPNRecord fields rest ->
      node "record"
        [ ("names", KVList [KVText (srName field) | (field, _, _) <- fields])
        , ("selected", KVList [KVInteger (if selected then 1 else 0) | (_, selected, _) <- fields])
        , ("fields", KVList [KVPattern pattern' | (_, _, pattern') <- fields])
        , ("rest", KVList (maybe [] (pure . KVPattern) rest))
        ]
    KPNInject tag payload -> node "inject" [("tag", KVText tag), ("payload", KVPattern payload)]
    KPNInjectRest excluded ->
      node "inject-rest"
        [("excluded", KVList (map KVText excluded))]
    KPNOr alternatives permutations ->
      node "or"
        [ ("alternatives", KVList (map KVPattern alternatives))
        , ("permutations", KVList [KVList (map (KVInteger . toInteger) permutation) | permutation <- permutations])
        ]
    KPNAs payload -> node "as" [("payload", KVPattern payload)]
  where
    node tag fields =
      "pattern-node " <> quoteText tag <> " "
        <> printNamedValues (("slot", KVBinder slot) : ("exposed", KVInteger (if exposed then 1 else 0)) : fields)

renderStable :: StableRef -> Text
renderStable StableRef {..} = "@" <> srName <> "#" <> srId

renderLocal :: LocalRef -> Text
renderLocal LocalRef {..} = "%" <> sanitizeName lrName <> "#" <> tshow lrId

renderUniverse :: UniverseRef -> Text
renderUniverse UniverseRef {..} = "^" <> sanitizeName urName <> "#" <> tshow urId

sanitizeName :: Text -> Text
sanitizeName name
  | T.null name = "_"
  | otherwise = T.map (\c -> if isAlphaNum c || c `elem` ("_.-" :: String) then c else '_') name

quoteText :: Text -> Text
quoteText value = "\"" <> T.concatMap escape value <> "\""
  where
    escape = \case
      '\n' -> "\\n"; '\r' -> "\\r"; '\t' -> "\\t"; '"' -> "\\\""; '\\' -> "\\\\"
      c -> T.singleton c

indent :: Int -> Text -> Text
indent width = T.intercalate "\n" . map (T.replicate width " " <>) . T.lines

tshow :: Show a => a -> Text
tshow = T.pack . show

-- A stable semantic fingerprint over canonical schema text. Stable references
-- retain lossless authoritative identities; this digest is only an indexed
-- lookup/check hint for round trips and caches.
semanticHashKCoreText :: KCoreFile -> Text
semanticHashKCoreText =
  sha256Hex
    . ("KAPPA:v1:KCoreText:" <>)
    . eraseStableRefPresentation
    . printCanonicalKCoreText
    . semanticNormalizeLiftEvidence

-- Proof-object allocation identity is not part of a lift's semantics. Collapse
-- adjacent compatible lifts to their composite theorem and replace selected
-- evidence with one hash-only witness. Verification runs before this function;
-- the witness is deliberately never accepted as serialized input.
semanticNormalizeLiftEvidence :: KCoreFile -> KCoreFile
semanticNormalizeLiftEvidence (KCoreFile version modules) =
  KCoreFile version (map module' modules)
  where
    proofIrrelevant = KECertificate (StableRef "certificate.semantic" "proof-irrelevant") []
    module' module0 = module0 {kmDecls = map decl (kmDecls module0)}
    decl = \case
      KDDef ref mode universes ty body ->
        KDDef ref mode universes (term ty) (term body)
      KDAxiom ref mode universes ty ->
        KDAxiom ref mode universes (term ty)
      KDInterface ref universes ty ->
        KDInterface ref universes (term ty)
      KDSchemaCertificate certificate ->
        KDSchemaCertificate
          certificate
            { kscMonotoneWitnesses =
                [ let operator' = term (kmwOperator witness)
                      goal' = term (kmwGoal witness)
                      semanticDependencies =
                        sort . nub $
                          map KRGlobal (termStableRefs goal')
                            ++ map KRLocal (termLocalRefs goal')
                   in witness
                        { kmwOperator = operator'
                        , kmwGoal = goal'
                        , kmwEvidence = proofIrrelevantTerm
                        , kmwDependencies = semanticDependencies
                        }
                | witness <- kscMonotoneWitnesses certificate
                ]
            }
      KDData ref universes parameters result certificate constructors ->
        KDData ref universes (map binder parameters) (term result) certificate
          [ KCtorDecl ctor ctorUniverses fields (term ty)
          | KCtorDecl ctor ctorUniverses fields ty <- constructors
          ]
      KDTermProbe value -> KDTermProbe (term value)
      KDLevelCertificate ref universes constraints theorem proof ->
        KDLevelCertificate ref universes (map constraint constraints) (constraint theorem) (levelProof proof)
      KDRepresentationCertificate certificate ->
        KDRepresentationCertificate
          certificate
            { krcBinders = map binder (krcBinders certificate)
            , krcTarget = term (krcTarget certificate)
            , krcConstraints = map constraint (krcConstraints certificate)
            , krcPayload =
                [ (name, value node)
                | (name, node) <- krcPayload certificate
                ]
            }
      KDGeneric tag fields -> KDGeneric tag [(name, value node) | (name, node) <- fields]
      declaration -> declaration
    proofIrrelevantTerm = KTGlobal (StableRef "evidence.semantic" "proof-irrelevant") []
    term = \case
      KTLocal ref levels -> KTLocal ref (map level levels)
      KTGlobal ref levels -> KTGlobal ref (map level levels)
      KTType universe -> KTType (level universe)
      KTPi parameter body -> KTPi (binder parameter) (term body)
      KTSigma parameter body -> KTSigma (binder parameter) (term body)
      KTLambda parameter body -> KTLambda (binder parameter) (term body)
      KTApply function arguments -> KTApply (term function) (map argument arguments)
      KTBlock items result -> KTBlock (map blockItem items) (term result)
      KTLetRec definitions result -> KTLetRec (map localDef definitions) (term result)
      KTCase scrutinee result alternatives -> KTCase (term scrutinee) (term result) (map alternative alternatives)
      KTConstruct ctor levels arguments -> KTConstruct ctor (map level levels) (map argument arguments)
      KTProject field record -> KTProject field (term record)
      KTLift from to _ inner ->
        let from' = level from
            to' = level to
            inner' = term inner
         in if sameKLevel from' to'
              then inner'
              else case inner' of
                KTLift innerFrom middle _ payload
                  | sameKLevel middle from' ->
                      KTLift innerFrom to' proofIrrelevant payload
                _ -> KTLift from' to' proofIrrelevant inner'
      KTSchemaLift family from to certificate roles arguments inner ->
        let from' = map level from
            to' = map level to
            roles' = map semanticSchemaRole roles
            arguments' = map argument arguments
            inner' = term inner
         in if sameKLevels from' to'
              then inner'
              else case inner' of
                KTSchemaLift innerFamily innerFrom middle innerCertificate innerRoles _ payload
                  | family == innerFamily
                  , certificate == innerCertificate
                  , sameKLevels middle from'
                  , sameSchemaRoleShapes innerRoles roles' ->
                      KTSchemaLift family innerFrom to' certificate roles' arguments' payload
                _ ->
                  KTSchemaLift family from' to' certificate roles' arguments' inner'
      KTAscribe inner ty -> KTAscribe (term inner) (term ty)
      KTLiteral literal -> KTLiteral literal
      KTRecordType fields -> KTRecordType [(field, binder parameter) | (field, parameter) <- fields]
      KTRecordValue fields -> KTRecordValue [(name, term inner) | (name, inner) <- fields]
      KTIf condition yes no -> KTIf (term condition) (term yes) (term no)
      KTGeneric tag fields -> KTGeneric tag [(name, value node) | (name, node) <- fields]
    binder parameter = parameter {kbType = term (kbType parameter)}
    argument (KArgument explicitness inner) = KArgument explicitness (term inner)
    blockItem (KBLet parameter rhs) = KBLet (binder parameter) (term rhs)
    localDef definition =
      definition
        { kldType = term (kldType definition)
        , kldBody = term (kldBody definition)
        }
    alternative = \case
      KCaseDefault body -> KCaseDefault (term body)
      KCaseConstructor ctor levels bindings body ->
        KCaseConstructor ctor (map level levels)
          (map (mapKCaseBinding binder term) bindings) (term body)
      KCasePattern pattern' guard' body ->
        KCasePattern (mapKPattern binder level term pattern') (fmap term guard') (term body)
    level = \case
      KLSucc child -> KLSucc (level child)
      KLMax left right -> KLMax (level left) (level right)
      KLAdd left right -> KLAdd (level left) (level right)
      KLTerm inner -> KLTerm (term inner)
      universe -> universe
    constraint (KConstraint strict lower upper) = KConstraint strict (level lower) (level upper)
    evidence = \case
      KELocal ref -> KELocal ref
      KEGlobal ref levels -> KEGlobal ref (map level levels)
      KECertificate ref levels -> KECertificate ref (map level levels)
    schemaRole = \case
      KSchemaInvariant -> KSchemaInvariant
      KSchemaCovariant selected -> KSchemaCovariant (evidence selected)
      KSchemaIrrelevant -> KSchemaIrrelevant
    semanticSchemaRole = \case
      KSchemaInvariant -> KSchemaInvariant
      KSchemaCovariant _ -> KSchemaCovariant proofIrrelevant
      KSchemaIrrelevant -> KSchemaIrrelevant
    levelProof = \case
      KLPAssumption index -> KLPAssumption index
      KLPClosed -> KLPClosed
      KLPArithmetic dependencies -> KLPArithmetic dependencies
      KLPMaxLeast left right -> KLPMaxLeast (levelProof left) (levelProof right)
      KLPZero universe -> KLPZero (level universe)
      KLPRefl universe -> KLPRefl (level universe)
      KLPTrans left right -> KLPTrans (levelProof left) (levelProof right)
      KLPSuccMono child -> KLPSuccMono (levelProof child)
      KLPMaxLeft left right -> KLPMaxLeft (level left) (level right)
      KLPMaxRight left right -> KLPMaxRight (level left) (level right)
      KLPAddMonoLeft fixed child -> KLPAddMonoLeft (level fixed) (levelProof child)
      KLPAddMonoRight fixed child -> KLPAddMonoRight (level fixed) (levelProof child)
    value = \case
      KVTerm inner -> KVTerm (term inner)
      KVLevel universe -> KVLevel (level universe)
      KVQuantity (KQTerm inner) -> KVQuantity (KQTerm (term inner))
      KVGlobal ref levels -> KVGlobal ref (map level levels)
      KVLocal ref levels -> KVLocal ref (map level levels)
      KVBinder parameter -> KVBinder (binder parameter)
      KVPattern pattern' -> KVPattern (mapKPattern binder level term pattern')
      KVList nodes -> KVList (map value nodes)
      node -> node

-- | Count independently verified arithmetic proof nodes in a KCore artifact.
-- A 'KCoreFile' is only returned after certificate replay succeeds, so this
-- query is structural and never infers proof validity from rendered text.
kcoreArithmeticCertificateCount :: KCoreFile -> Int
kcoreArithmeticCertificateCount (KCoreFile _ modules) =
  sum
    [ sum (map declarationCount declarations)
    | KModule {kmDecls = declarations} <- modules
    ]
  where
    declarationCount = \case
      KDDef _ _ _ ty body -> termCount ty + termCount body
      KDAxiom _ _ _ ty -> termCount ty
      KDInterface _ _ ty -> termCount ty
      KDAssociatedNormalization normalization ->
        sum (map (binderCount) (kanBinders normalization))
          + termCount (kanValue normalization)
      KDData _ _ parameters result _ constructors ->
        sum (map (termCount . kbType) parameters)
          + termCount result
          + sum [termCount ty | KCtorDecl _ _ _ ty <- constructors]
      KDSchemaCertificate certificate ->
        sum
          [ termCount (kmwOperator witness)
              + termCount (kmwGoal witness)
              + termCount (kmwEvidence witness)
          | witness <- kscMonotoneWitnesses certificate
          ]
      KDTermProbe term -> termCount term
      KDLevelCertificate _ _ constraints theorem _ ->
        sum (map constraintCount constraints) + constraintCount theorem
      KDRepresentationCertificate certificate ->
        sum (map (binderCount) (krcBinders certificate))
          + termCount (krcTarget certificate)
          + sum (map constraintCount (krcConstraints certificate))
          + sum (map (valueCount . snd) (krcPayload certificate))
      KDGeneric _ fields -> sum (map (valueCount . snd) fields)
      KDExtension {} -> 0

    constraintCount (KConstraint _ lower upper) =
      levelCount lower + levelCount upper

    termCount = \case
      KTLocal _ levels -> sum (map levelCount levels)
      KTGlobal _ levels -> sum (map levelCount levels)
      KTType level -> levelCount level
      KTPi binder body -> binderCount binder + termCount body
      KTSigma binder body -> binderCount binder + termCount body
      KTLambda binder body -> binderCount binder + termCount body
      KTApply function arguments ->
        termCount function + sum (map (termCount . argumentTerm) arguments)
      KTBlock items result ->
        sum [binderCount binder + termCount rhs | KBLet binder rhs <- items]
          + termCount result
      KTLetRec definitions result ->
        sum [termCount (kldType definition) + termCount (kldBody definition) | definition <- definitions]
          + termCount result
      KTCase scrutinee result alternatives ->
        termCount scrutinee + termCount result + sum (map alternativeCount alternatives)
      KTConstruct _ levels arguments ->
        sum (map levelCount levels) + sum (map (termCount . argumentTerm) arguments)
      KTProject _ record -> termCount record
      KTLift lower upper _ term ->
        levelCount lower + levelCount upper + termCount term
      KTSchemaLift _ source target _ _ arguments term ->
        sum (map levelCount (source ++ target))
          + sum (map (termCount . argumentTerm) arguments)
          + termCount term
      KTAscribe term ty -> termCount term + termCount ty
      KTLiteral _ -> 0
      KTRecordType fields -> sum [binderCount binder | (_, binder) <- fields]
      KTRecordValue fields -> sum [termCount term | (_, term) <- fields]
      KTIf condition yes no ->
        termCount condition + termCount yes + termCount no
      KTGeneric tag fields ->
        (if tag == "impl.kappa.core.arithmetic-proof" then 1 else 0)
          + sum (map (valueCount . snd) fields)

    alternativeCount = \case
      KCaseConstructor _ levels bindings body ->
        sum (map levelCount levels)
          + sum
            [ binderCount (caseBindingBinder binding)
                + case binding of
                    KCaseBridge bridge -> termCount (kcbProof bridge)
                    KCasePayload {} -> 0
            | binding <- bindings
            ]
          + termCount body
      KCaseDefault body -> termCount body
      KCasePattern pattern' guard' body ->
        patternCount pattern' + maybe 0 termCount guard' + termCount body

    patternCount (KPattern slot _ node) =
      binderCount slot + case node of
        KPNWild -> 0
        KPNLiteral _ -> 0
        KPNConstructor _ levels binders bridges fields ->
          sum (map levelCount levels)
            + sum (map binderCount binders)
            + sum
              [ binderCount (kcbBinder bridge) + termCount (kcbProof bridge)
              | bridge <- bridges
              ]
            + sum (map patternCount fields)
        KPNTuple fields -> sum (map patternCount fields)
        KPNRecord fields rest ->
          sum [patternCount pattern' | (_, _, pattern') <- fields]
            + maybe 0 patternCount rest
        KPNInject _ payload -> patternCount payload
        KPNInjectRest _ -> 0
        KPNOr alternatives _ -> sum (map patternCount alternatives)
        KPNAs payload -> patternCount payload

    binderCount = termCount . kbType

    levelCount = \case
      KLSucc level -> levelCount level
      KLMax left right -> levelCount left + levelCount right
      KLAdd left right -> levelCount left + levelCount right
      KLTerm term -> termCount term
      _ -> 0

    valueCount = \case
      KVTerm term -> termCount term
      KVLevel level -> levelCount level
      KVQuantity (KQTerm term) -> termCount term
      KVGlobal _ levels -> sum (map levelCount levels)
      KVLocal _ levels -> sum (map levelCount levels)
      KVBinder binder -> binderCount binder
      KVPattern pattern' -> patternCount pattern'
      KVList values -> sum (map valueCount values)
      _ -> 0

kcoreRepresentationCertificateCount :: KCoreFile -> Int
kcoreRepresentationCertificateCount (KCoreFile _ modules) =
  length
    [ ()
    | KModule {kmDecls = declarations} <- modules
    , KDRepresentationCertificate {} <- declarations
    ]

kcoreHasValidSchemaCertificate :: KCoreFile -> Text -> Bool
kcoreHasValidSchemaCertificate (KCoreFile _ modules) requestedFamily =
  case verifySchemaCertificates (Map.keysSet families) families certificates of
    Left _ -> False
    Right () ->
      any
        (\certificate -> renderStable (kscFamily certificate) == requestedFamily)
        (Map.elems certificates)
  where
    declarations = concatMap kmDecls modules
    certificates =
      Map.fromList [(kscRef certificate, certificate) | KDSchemaCertificate certificate <- declarations]
    families =
      Map.fromList
        [ (ref, KNominalFamily universes binders result certificate constructors)
        | KDData ref universes binders result certificate constructors <- declarations
        ]

-- | Return the canonical assumption dependency set of a verified level
-- certificate.  Parsing has already replayed the proof, so this query never
-- attempts to infer dependencies from the stated theorem.
kcoreLevelCertificateDependencies :: KCoreFile -> Text -> Maybe [Int]
kcoreLevelCertificateDependencies file requested =
  listToMaybe
    [ proofDependencyIndices proof
    | KModule {kmDecls = declarations} <- modules
    , KDLevelCertificate ref _ _ _ proof <- declarations
    , renderStable ref == requested || srName ref == requested
    ]
  where
    KCoreFile _ modules = canonicalizeKCoreFile file

-- | Query a verified interchange artifact by its declared family reference.
-- The short-name fallback is tooling-only presentation lookup; certificate
-- verification itself always uses the full stable reference identity.
kcoreNominalRoles :: KCoreFile -> Text -> Maybe [UniverseVariance]
kcoreNominalRoles (KCoreFile _ modules) requested =
  listToMaybe
    [ roles
    | KModule {kmDecls = declarations} <- modules
    , KDData ref universes _ _ _ _ <- declarations
    , let roles = map snd universes
    , renderStable ref == requested || stableLeaf ref == requested
    ]
  where
    stableLeaf ref = case reverse (T.splitOn "." (srName ref)) of
      leaf : _ -> leaf
      [] -> srName ref

-- Canonical text retains human-readable reference names, but those names are
-- not semantic identity. Strip only reference-name tokens outside string
-- literals before hashing; the authoritative text after '#' remains.
eraseStableRefPresentation :: Text -> Text
eraseStableRefPresentation = T.pack . go False False . T.unpack
  where
    go _ _ [] = []
    go inString escaped (char : rest)
      | inString =
          char : go (if escaped then True else char /= '"') (not escaped && char == '\\') rest
      | char == '"' = char : go True False rest
      | char == '@' = '@' : dropName rest
      | otherwise = char : go False False rest
    dropName [] = []
    dropName ('#' : rest) = '#' : go False False rest
    dropName (_ : rest) = dropName rest

-- | Reconstruct the abstract dictionary constructor carried by a nominal
-- record family. The record interface and family declaration are converted
-- independently, so align their binder identities structurally before using
-- the record fields as constructor payloads.
nominalDictionaryConstructor
  :: StableRef
  -> StableRef
  -> [UniverseRef]
  -> [KBinder]
  -> KTerm
  -> Either KCoreTextError KCtorDecl
nominalDictionaryConstructor familyRef constructorRef universes parameters interface = do
  recordInterface <- alignParameters parameters interface
  recordFields <- case recordInterface of
    KTRecordType fields -> pure fields
    _ ->
      Left
        ( invalid
            ( "nominal record dictionary does not elaborate to a record telescope for "
                <> renderStable familyRef
            )
        )
  let payload = map snd recordFields
      familyResult =
        applyKArguments
          (KTGlobal familyRef (map KLUniverse universes))
          [ KArgument
              (kbExplicitness parameter)
              (KTLocal (kbRef parameter) [])
          | parameter <- parameters
          ]
      dictionaryFields = zip (map fst recordFields) [0 ..]
  pure
    ( KCtorDecl
        constructorRef
        []
        dictionaryFields
        (foldr KTPi familyResult payload)
    )
  where
    alignParameters [] body = pure body
    alignParameters (expected : rest) (KTLambda actual body) = do
      let alignedActual = actual {kbRef = kbRef expected}
      unless (alignedActual == expected) $
        Left
          ( invalid
              ( "nominal record dictionary parameter disagrees with family telescope for "
                  <> renderStable familyRef
              )
          )
      alignParameters
        rest
        (substituteLocal (kbRef actual) (KTLocal (kbRef expected) []) body)
    alignParameters _ _ =
      Left
        ( invalid
            ( "nominal record dictionary does not saturate the family telescope for "
                <> renderStable familyRef
            )
        )

    applyKArguments function [] = function
    applyKArguments function arguments = KTApply function arguments

-- | Derive the portable associated-normalization surface from checked KCore
-- dictionary bodies. This pass grants no authority: every emitted equation is
-- replayed by 'verifyAssociatedNormalizations'. Its only job is to preserve
-- the exact static fields that an opaque imported dictionary is allowed to
-- expose without making ordinary method bodies transparent.
deriveAssociatedNormalizations
  :: VerifyContext
  -> [(StableRef, [UniverseRef], KTerm)]
  -> [KAssociatedNormalization]
deriveAssociatedNormalizations context =
  concatMap derive
  where
    derive (dictionary, universes, body) = do
      (declarationUniverses, dictionaryType) <-
        maybeToList (Map.lookup dictionary (vcGlobalTypes context))
      guardList (length declarationUniverses == length universes)
      let (typeBinders, resultType) = splitPiTelescope dictionaryType
      (bodyBinders, fields) <- maybeToList (dictionaryBody body)
      guardList (length typeBinders == length bodyBinders)
      (familyRef, _, _) <- maybeToList (nominalApplication resultType)
      family <- maybeToList (Map.lookup familyRef (vcNominalFamilies context))
      certificate <-
        maybeToList
          (Map.lookup (knfCertificate family) (vcSchemaCertificates context))
      guardList
        (ClauseGeneratedProjection `elem` kscClauseKinds certificate)
      KCtorDecl _ _ fieldPositions constructorType <-
        case knfConstructors family of
          [constructor] -> [constructor]
          _ -> []
      let (payload, _) = splitPiTelescope constructorType
          payloadByField =
            Map.fromList
              [ (field, binder)
              | (field, index) <- fieldPositions
              , Just binder <- [atMay payload index]
              ]
      (fieldName, value) <- fields
      let field = stableFieldRef fieldName
      fieldBinder <- maybeToList (Map.lookup field payloadByField)
      guardList (kAssociatedStaticMemberType context (kbType fieldBinder))
      pure
        KAssociatedNormalization
          { kanDictionary = dictionary
          , kanField = field
          , kanUniverses = universes
          , kanBinders = bodyBinders
          , kanValue = value
          }

    dictionaryBody = go []
      where
        go binders (KTLambda binder body) = go (binders ++ [binder]) body
        go binders (KTLift _ _ _ body) = go binders body
        go binders (KTSchemaLift _ _ _ _ _ _ body) = go binders body
        go binders (KTAscribe body _) = go binders body
        go binders (KTRecordValue fields) = Just (binders, fields)
        go binders generic@(KTGeneric tag fields)
          | tag `Set.member` decodedBuiltinTermTags =
              case decodeBuiltinTermNode tag fields of
                Right decoded
                  | decoded /= generic -> go binders decoded
                _ -> Nothing
        go _ _ = Nothing

    nominalApplication = go []
      where
        go arguments (KTApply function more) =
          go (more ++ arguments) function
        go arguments (KTGlobal ref levels) =
          Just (ref, levels, arguments)
        go _ _ = Nothing

    atMay values index
      | index < 0 = Nothing
      | otherwise = listToMaybe (drop index values)

    guardList True = [()]
    guardList False = []

-- KCore -> KCoreText ---------------------------------------------------------

kcoreMonotoneWitnesses
  :: [KBinder]
  -> NominalCumulativitySummary
  -> Either KCoreTextError [KMonotoneWitness]
kcoreMonotoneWitnesses binders summary =
  mapM convert (nscMonotoneWitnesses (ncsClosure summary))
  where
    env = map kbRef binders
    convert witness = do
      operator <- neutralLevelTermToText env (nmwOperator witness)
      goal <- neutralLevelTermToText env (nmwGoal witness)
      evidence <- neutralLevelTermToText env (nmwEvidence witness)
      dependencies <- sort . nub <$> mapM dependency (nmwDependencies witness)
      pure
        KMonotoneWitness
          { kmwParameter = nmwParameter witness
          , kmwOperator = operator
          , kmwGoal = goal
          , kmwEvidence = evidence
          , kmwDependencies = dependencies
          }
    dependency = \case
      NominalLocalDependency level ->
        KRLocal
          <$> maybe
            (Left (invalid ("monotonicity evidence local " <> tshow level <> " is outside the family telescope")))
            pure
            (localAtLevel env level)
      NominalGlobalDependency owner name ->
        pure (KRGlobal (stableRefForGlobal (GName (ModuleName owner) name)))
      NominalConstructorDependency owner name ->
        pure (KRGlobal (stableRefForConstructor (GName (ModuleName owner) name)))
      NominalFieldDependency field -> pure (KRGlobal (stableFieldRef field))

renderKCoreModule
  :: ModuleName
  -> EvalCtx
  -> Map GName GlobalDef
  -> Map GName Term
  -> Map GName KCoreDataInfo
  -> Map GName KCoreConstructorInfo
  -> Either KCoreTextError Text
renderKCoreModule moduleName ec globals bodies dataInfos constructorInfos = do
  closedCertificateDeclarations <- mapM renderCertificate (Map.toAscList certificateRelations)
  renderedOwners <- mapM renderOwnedGlobal ours
  let scopedCertificateDeclarations = concatMap fst renderedOwners
      ownedDeclarations = map snd renderedOwners
      preliminaryDeclarations =
        KDExtension "impl.kappa" 1
          : closedCertificateDeclarations ++ scopedCertificateDeclarations ++ ownedDeclarations
      preliminaryModule =
        KModule moduleRef metadata preliminaryDeclarations
      localTypes =
        Map.fromList (moduleDeclarationTypes preliminaryModule)
      localModes =
        Map.fromList (moduleDeclarationModes preliminaryModule)
      localBodyMap =
        Map.fromList (moduleDeclarationBodies preliminaryModule)
      localRecordInterfaces =
        Map.fromList (moduleRecordInterfaces preliminaryModule)
      localSchemaCertificates =
        Map.fromList
          [ (kscRef certificate, certificate)
          | KDSchemaCertificate certificate <- preliminaryDeclarations
          ]
      localNominalFamilies =
        Map.fromList
          [ (ref, KNominalFamily universes binders result certificate constructors)
          | KDData ref universes binders result certificate constructors <-
              preliminaryDeclarations
          ]
      localBodies =
        [ (ref, universes, body)
        | KDDef ref _ universes _ body <- preliminaryDeclarations
        , not (isUnavailableBody body)
        ]
      localConstructorTypes =
        Map.fromList (moduleConstructorTypes preliminaryModule)
      localLevelCertificates =
        Map.fromList
          [ (ref, (universes, constraints, theorem, proof))
          | KDLevelCertificate ref universes constraints theorem proof <-
              preliminaryDeclarations
          ]
      localContext =
        VerifyContext
          (Map.map (length . fst) localTypes)
          localTypes
          localModes
          localBodyMap
          localRecordInterfaces
          Map.empty
          localConstructorTypes
          (nominalConstructorFields localNominalFamilies)
          localLevelCertificates
          localSchemaCertificates
          localNominalFamilies
          (Set.singleton "impl.kappa")
          []
      associatedNormalizations =
        deriveAssociatedNormalizations
          localContext
          localBodies
      declarations =
        preliminaryDeclarations
          ++ map KDAssociatedNormalization associatedNormalizations
  pure (printCanonicalKCoreText (KCoreFile 1 [KModule moduleRef metadata declarations]))
  where
    moduleText = case moduleName of ModuleName parts -> T.intercalate "." parts
    moduleRef = stableRefForText moduleText
    metadata =
      [ ("languageVersion", "kappa-v1")
      , ("compilerInterfaceVersion", "1")
      , ("sourceModuleIdentity", moduleText)
      , ("typeLevelAlgebraVersion", "1")
      , ("levelConstructorNormalizerVersion", "1")
      , ("levelRigidEntailmentVersion", "1")
      , ("levelPrincipalInferenceVersion", "1")
      , ("levelCertificateVersion", "1")
      ]
    ours =
      [ (g, gd)
      | (g@(GName owner _), gd) <- Map.toList globals
      , owner == moduleName
      , Map.notMember g constructorInfos || Map.member g dataInfos
      ]
    conversionContext = CoreConversionContext (Just ec) globals constructorInfos
    certificateRelations =
      Map.fromList
        [ ( LiftCertificateKey (fst relation) (snd relation) []
          , LiftCertificateUse
              (stableLevelCertificateRef certificateName)
              []
          )
        | relation <- Set.toAscList closedLiftRelations
        , let certificateName =
                "certificate.generated." <> moduleText <> "."
                  <> stableHex (T.pack (show relation))
        ]
    closedLiftRelations =
      Set.fromList
        [ relation
        | term <-
            concat [maybeToList (Map.lookup g bodies) | (g, _) <- ours]
              ++ [globalCoreType ec gd | (_, gd) <- ours]
              ++ [ kcciType info
                 | (GName owner _, info) <- Map.toList constructorInfos
                 , owner == moduleName
                 ]
        , relation <- foldTerm closedLift (const []) term
        , Right constraint <- [uncurry coreLevelConstraint relation]
        , closedConstraint constraint
        , constraintProved emptyAssumptions constraint
        ]
    closedLift = \case
      CUniverseLift lower upper _ _ ->
        [(normalizeLevel lower, normalizeLevel upper)]
      CSchemaLift _ source target roles evidence _ _ _ _ ->
        [ (normalizeLevel lower, normalizeLevel upper)
        | (role, roleEvidence, lower, upper) <- zip4 roles evidence source target
        , role == Covariant
        , SchemaCovariantEvidence _ <- [roleEvidence]
        ]
      _ -> []
    coreLevelConstraint lower upper =
      KConstraint False <$> levelToText lower <*> levelToText upper
    renderCertificate (LiftCertificateKey lower upper _, LiftCertificateUse ref _) =
      KDLevelCertificate ref [] [] <$> coreLevelConstraint lower upper <*> pure KLPClosed
    renderOwnedGlobal entry@(g, _)=
      withGlobalContext g $
        case Map.lookup g dataInfos of
          Just info -> renderData entry info
          Nothing -> case gdNominalSummary (snd entry) of
            Just summary -> renderNominalRecord entry summary
            Nothing -> renderGlobal entry
    withGlobalContext global action =
      case action of
        Left err ->
          Left err {kcteMessage = "while emitting " <> gKey global <> ": " <> kcteMessage err}
        Right value -> Right value
    renderData (g, gd) KCoreDataInfo {..} = do
      let telescope = gdUniverses gd
          universes = [UniverseRef "u" i | i <- [0 .. dutParameterCount telescope - 1]]
          dataTypeCore = globalCoreType ec gd
          ownerConstraints = declarationUniverseConstraints (dutParameterCount telescope) dataTypeCore
      (dataCertificates, dataCertificateUses) <-
        renderScopedCertificates g telescope ownerConstraints [dataTypeCore]
      let certificateUses = Map.union dataCertificateUses certificateRelations
      dataType <- coreToTextWithEvidenceIn conversionContext certificateUses dataTypeCore
      let (allParameters, result) = splitPiTelescope dataType
          parameters = allParameters
      renderedConstructors <- mapM renderConstructor kcdiConstructors
      let constructorCertificates = concatMap fst renderedConstructors
          constructors = map snd renderedConstructors
      (schemaDeclarations, roleUniverses, schemaCertificate) <-
        case gdNominalSummary gd of
          Nothing ->
            Left
              ( invalid
                  ("cannot emit an uncertified nominal declaration for " <> gKey g)
              )
          Just summary -> do
            unless (verifyNominalCumulativitySummary summary) $
              Left (invalid ("cannot emit an invalid nominal cumulativity summary for " <> gKey g))
            unless (ncsFamilyIdentity summary == gKey g) $
              Left (invalid ("cannot emit a nominal cumulativity summary for another family as " <> gKey g))
            unless (length universes == length (ncsRoles summary)) $
              Left (invalid ("nominal cumulativity role arity disagrees with the universe telescope for " <> gKey g))
            monotoneWitnesses <- kcoreMonotoneWitnesses parameters summary
            let certificateName = unSchemaActionCertificateId (ncsCertificateId summary)
                certificateRef = stableSchemaCertificateRef certificateName
                familyForCertificate =
                  KNominalFamily
                    (zip universes (ncsRoles summary))
                    parameters
                    result
                    certificateRef
                    constructors
                certificate =
                  KSchemaCertificate
                    { kscRef = certificateRef
                    , kscFamily = stableRefForGlobal g
                    , kscCheckerVersion = toInteger (ncsCheckerVersion summary)
                    , kscSemanticVersions = ncsSemanticVersions summary
                    , kscSignatureHash =
                        kCoreNominalSignatureHash (stableRefForGlobal g) familyForCertificate
                    , kscSaturationArity = ncsSaturationArity summary
                    , kscRoles = ncsRoles summary
                    , kscClauseKinds = ncsClauseKinds summary
                    , kscMonotoneWitnesses = monotoneWitnesses
                    }
            pure
              ( [KDSchemaCertificate certificate]
              , zip universes (ncsRoles summary)
              , certificateRef
              )
      pure
        ( dataCertificates ++ constructorCertificates ++ schemaDeclarations
        , KDData (stableRefForGlobal g) roleUniverses parameters result schemaCertificate constructors
        )
    -- Traits elaborate to nominal record families rather than ordinary data,
    -- but their dictionary value contains the complete checked record
    -- telescope. Serialize that telescope as one abstract dictionary
    -- constructor so role/certificate replay and generated projections remain
    -- source-free and independently typecheckable.
    renderNominalRecord (g, gd) summary = do
      unless (verifyNominalCumulativitySummary summary) $
        Left (invalid ("cannot emit an invalid nominal cumulativity summary for " <> gKey g))
      unless (ncsFamilyIdentity summary == gKey g) $
        Left (invalid ("cannot emit a nominal cumulativity summary for another family as " <> gKey g))
      let telescope = gdUniverses gd
          universes = [UniverseRef "u" i | i <- [0 .. dutParameterCount telescope - 1]]
          familyTypeCore = globalCoreType ec gd
          ownerConstraints = declarationUniverseConstraints (dutParameterCount telescope) familyTypeCore
      valueCore <- maybe
        (Left (invalid ("nominal record interface has no checked dictionary signature for " <> gKey g)))
        (pure . quote ec 0)
        (gdValue gd)
      (certificates, certificateUses0) <-
        renderScopedCertificates g telescope ownerConstraints [familyTypeCore, valueCore]
      let certificateUses = Map.union certificateUses0 certificateRelations
      familyType <- coreToTextWithEvidenceIn conversionContext certificateUses familyTypeCore
      dictionaryType <- coreToTextAgainstWithEvidenceIn conversionContext certificateUses familyTypeCore valueCore
      let (allParameters, result) = splitPiTelescope familyType
          parameters = allParameters
      unless (length universes == length (ncsRoles summary)) $
        Left (invalid ("nominal record role arity disagrees with its universe telescope for " <> gKey g))
      dictionaryConstructor <-
        nominalDictionaryConstructor
          (stableRefForGlobal g)
          (stableRefForConstructor g)
          universes
          parameters
          dictionaryType
      monotoneWitnesses <- kcoreMonotoneWitnesses parameters summary
      let certificateName = unSchemaActionCertificateId (ncsCertificateId summary)
          certificateRef = stableSchemaCertificateRef certificateName
          familyForCertificate =
            KNominalFamily
              (zip universes (ncsRoles summary))
              parameters
              result
              certificateRef
              [dictionaryConstructor]
          certificate =
            KSchemaCertificate
              { kscRef = certificateRef
              , kscFamily = stableRefForGlobal g
              , kscCheckerVersion = toInteger (ncsCheckerVersion summary)
              , kscSemanticVersions = ncsSemanticVersions summary
              , kscSignatureHash =
                  kCoreNominalSignatureHash (stableRefForGlobal g) familyForCertificate
              , kscSaturationArity = ncsSaturationArity summary
              , kscRoles = ncsRoles summary
              , kscClauseKinds = ncsClauseKinds summary
                    , kscMonotoneWitnesses = monotoneWitnesses
                    }
      pure
        ( certificates ++ [KDSchemaCertificate certificate]
        , KDData (stableRefForGlobal g) (zip universes (ncsRoles summary))
            parameters result certificateRef [dictionaryConstructor]
        )
    renderConstructor constructor =
      case Map.lookup constructor constructorInfos of
        Nothing -> Left (invalid ("constructor interface is unavailable for " <> gKey constructor))
        Just KCoreConstructorInfo {..} -> do
          let telescope = kcciUniverses
              universes = [UniverseRef "u" i | i <- [0 .. dutParameterCount telescope - 1]]
              ownerConstraints = declarationUniverseConstraints (dutParameterCount telescope) kcciType
          (certificates, scopedCertificateUses) <-
            renderScopedCertificates constructor telescope ownerConstraints [kcciType]
          let certificateUses = Map.union scopedCertificateUses certificateRelations
          converted <- coreToTextWithEvidenceIn conversionContext certificateUses kcciType
          familyParameterCount <-
            maybe
              (Left (invalid ("constructor family interface is unavailable for " <> gKey kcciData)))
              pure
              (familyCoreParameterCount ec globals kcciData)
          let (allBinders, result) = splitPiTelescope converted
              payloadBinders = drop familyParameterCount allBinders
              fieldOffset = length payloadBinders - length kcciSourceFields
          when (fieldOffset < 0) $
            Left (invalid ("constructor " <> gKey constructor <> " source fields exceed its checked payload telescope"))
          pure
            ( certificates
            , KCtorDecl (stableRefForConstructor constructor) universes
                [ (stableFieldRef field, index)
                | (index, (_, Just field)) <- zip [fieldOffset ..] kcciSourceFields
                ]
                (foldr KTPi result payloadBinders)
            )
    renderGlobal (g, gd) = do
      let telescope = gdUniverses gd
          universes = [UniverseRef "u" i | i <- [0 .. dutParameterCount telescope - 1]]
          tyCore = globalCoreType ec gd
          ownerConstraints = declarationUniverseConstraints (dutParameterCount telescope) tyCore
          valueCore = quote ec 0 <$> gdValue gd
          bodyCore =
            if gdReducible gd
              then Map.lookup g bodies <|> gdCoreBody gd <|> valueCore
              else Nothing
          semanticCore = bodyCore <|> valueCore
      (certificates, scopedCertificateUses) <-
        renderScopedCertificates
          g
          telescope
          ownerConstraints
          (tyCore : maybeToList semanticCore)
      let certificateUses = Map.union scopedCertificateUses certificateRelations
      ty <- coreToTextWithEvidenceIn conversionContext certificateUses tyCore
      recordInterface <- case semanticCore of
        Nothing -> pure []
        Just value -> do
          rendered <-
            coreToTextAgainstWithEvidenceIn
              conversionContext
              certificateUses
              tyCore
              value
          pure
            [ KDInterface (stableRefForGlobal g) universes rendered
            | ktermHasRecordInterface rendered
            ]
      declaration <- case bodyCore of
        Just body ->
          KDDef (stableRefForGlobal g) (gdObservationMode gd) universes ty
            <$> coreToTextAgainstWithEvidenceIn conversionContext certificateUses tyCore body
        Nothing
          | Just _ <- gdValue gd ->
              pure
                ( KDDef
                    (stableRefForGlobal g)
                    (gdObservationMode gd)
                    universes
                    ty
                    (KTGeneric "impl.kappa.core.body-unavailable" [])
                )
          | otherwise -> pure (KDAxiom (stableRefForGlobal g) (gdObservationMode gd) universes ty)
      pure (certificates ++ recordInterface, declaration)

    renderScopedCertificates =
      renderScopedLevelCertificates moduleText certificateRelations

data LiftCertificateKey = LiftCertificateKey
  !Level
  !Level
  ![(Level, Level)]
  deriving stock (Eq, Ord, Show)

data LiftCertificateUse = LiftCertificateUse !StableRef ![Level]

type LiftCertificateUses = Map LiftCertificateKey LiftCertificateUse

liftCertificateKey :: Level -> Level -> UniverseEvidence -> LiftCertificateKey
liftCertificateKey lower upper evidence =
  LiftCertificateKey
    (normalizeLevel lower)
    (normalizeLevel upper)
    (universeEvidenceDependencies evidence)

universeEvidenceDependencies :: UniverseEvidence -> [(Level, Level)]
universeEvidenceDependencies (UniverseEvidence steps) =
  nub . sort $
    [ (normalizeLevel lower, normalizeLevel upper)
    | step <- steps
    , (lower, upper) <- uesAssumptions step
    ]

-- | Replay the checker-owned evidence attached to cumulative Core lifts and
-- materialize every non-local obligation as a KCoreText certificate.  Both
-- module emission and imported-environment construction use this path: an
-- imported signature is typed metadata, but its lift evidence is not exempt
-- from interchange verification.
renderScopedLevelCertificates
  :: Text
  -> LiftCertificateUses
  -> GName
  -> DeclarationUniverseTelescope
  -> [UniverseConstraint]
  -> [Term]
  -> Either KCoreTextError ([KDecl], LiftCertificateUses)
renderScopedLevelCertificates moduleText closedCertificates owner telescope _ownerConstraints terms = do
  rendered <- mapM renderOpenCertificate (Map.toAscList openLifts)
  pure (map fst rendered, Map.fromList (map snd rendered))
  where
    declarationParameterCount = dutParameterCount telescope
    openLifts =
      Map.fromListWith min
        [ (key, evidence)
        | term <- terms
        , (relation, evidence) <- foldTerm collectLift (const []) term
        , let key = uncurry liftCertificateKey relation evidence
        , key `Map.notMember` closedCertificates
        , relation `notElem` universeEvidenceDependencies evidence
        ]
    collectLift = \case
      CUniverseLift lower upper evidence _ ->
        [((normalizeLevel lower, normalizeLevel upper), evidence)]
      CSchemaLift _ source target roles evidence _ _ _ _ ->
        [ ((normalizeLevel lower, normalizeLevel upper), proof)
        | (role, roleEvidence, lower, upper) <- zip4 roles evidence source target
        , role == Covariant
        , SchemaCovariantEvidence proof <- [roleEvidence]
        ]
      _ -> []
    renderOpenCertificate (key@(LiftCertificateKey lower upper dependencies), evidence) = do
      validateUniverseEvidence (lower, upper) evidence
      let localAtoms =
            nub . sort . concatMap localLevelAtoms $
              [lower, upper] ++ concatMap (\(lhs, rhs) -> [lhs, rhs]) dependencies
          atomParameters =
            Map.fromList
              (zip localAtoms [declarationParameterCount ..])
          abstract = abstractLocalLevelAtoms atomParameters
          abstractedDependencies =
            [(abstract lhs, abstract rhs) | (lhs, rhs) <- dependencies]
          abstractedLower = abstract lower
          abstractedUpper = abstract upper
          universes =
            [ UniverseRef "u" index
            | index <- [0 .. declarationParameterCount + length localAtoms - 1]
            ]
          universeArguments =
            [LParam index | index <- [0 .. declarationParameterCount - 1]]
              ++ localAtoms
          assumptions =
            foldr (uncurry insertAssumption) emptyAssumptions abstractedDependencies
      unless (assumptionsConsistent assumptions) $
        Left (invalid "a cumulative lift certificate has inconsistent recorded dependencies")
      unless (proveLevelLeq assumptions abstractedLower abstractedUpper == Proved) $
        Left
          ( invalid
              ( "recorded cumulative-lift dependencies do not prove "
                  <> renderLevel lower <> " <= " <> renderLevel upper
              )
          )
      renderedConstraints <-
        mapM
          (\(lhs, rhs) -> KConstraint False <$> levelToText lhs <*> levelToText rhs)
          abstractedDependencies
      theorem <-
        KConstraint False
          <$> levelToText abstractedLower
          <*> levelToText abstractedUpper
      let proof = KLPArithmetic [0 .. length renderedConstraints - 1]
      let identitySeed =
            gKey owner <> ":" <> T.pack (show renderedConstraints)
              <> ":" <> T.pack (show theorem) <> ":" <> T.pack (show proof)
          suffix = stableHex identitySeed
          certificateName = "certificate.generated." <> moduleText <> "." <> suffix
          ref = stableLevelCertificateRef certificateName
          declaration =
            KDLevelCertificate ref universes renderedConstraints theorem proof
      pure (declaration, (key, LiftCertificateUse ref universeArguments))

validateUniverseEvidence
  :: (Level, Level)
  -> UniverseEvidence
  -> Either KCoreTextError ()
validateUniverseEvidence relation (UniverseEvidence steps0) = case steps0 of
  [] -> Left (invalid "a cumulative lift has no replayable evidence steps")
  steps@(firstStep : _)
    | any (uncurry (/=) . normalizeEndpointPair) (zip steps (drop 1 steps)) ->
        Left (invalid "a cumulative lift has a malformed evidence chain")
    | overallEndpoints /= relation ->
        Left (invalid "a cumulative lift evidence chain proves different endpoints")
    | otherwise -> pure ()
    where
      overallEndpoints =
        ( normalizeLevel (uesLower firstStep)
        , normalizeLevel (uesUpper (last steps))
        )
      normalizeEndpointPair (leftStep, rightStep) =
        (normalizeLevel (uesUpper leftStep), normalizeLevel (uesLower rightStep))

localLevelAtoms :: Level -> [Level]
localLevelAtoms = \case
  level@LVar {} -> [level]
  level@LField {} -> [level]
  level@LProjection {} -> [level]
  level@LNeutral {}
    | not (null (levelVars level) && null (levelFields level)) -> [level]
  LSucc level -> localLevelAtoms level
  LAdd lhs rhs -> localLevelAtoms lhs ++ localLevelAtoms rhs
  LMax lhs rhs -> localLevelAtoms lhs ++ localLevelAtoms rhs
  _ -> []

abstractLocalLevelAtoms :: Map Level Int -> Level -> Level
abstractLocalLevelAtoms parameters = normalizeLevel . go
  where
    go level
      | Just parameter <- Map.lookup level parameters = LParam parameter
    go (LNeutral atom) = LNeutral (mapNeutralLevelAtomLevels go atom)
    go (LSucc level) = LSucc (go level)
    go (LAdd lhs rhs) = LAdd (go lhs) (go rhs)
    go (LMax lhs rhs) = LMax (go lhs) (go rhs)
    go level = level

coreToTextWithEvidenceIn :: CoreConversionContext -> LiftCertificateUses -> Term -> Either KCoreTextError KTerm
coreToTextWithEvidenceIn context certificates =
  coreToTextWithExpected context certificates Nothing

coreToTextAgainstWithEvidenceIn
  :: CoreConversionContext
  -> LiftCertificateUses
  -> Term
  -> Term
  -> Either KCoreTextError KTerm
coreToTextAgainstWithEvidenceIn context certificates expected =
  coreToTextWithExpected context certificates (Just expected)

arithmeticReplaySemantics :: ArithmeticDomain -> Maybe ArithmeticSemantics
arithmeticReplaySemantics = \case
  ArithmeticNatural -> Just ArithmeticNaturalSemantics
  ArithmeticInteger -> Just ArithmeticIntegerSemantics
  ArithmeticTypeLevel -> Nothing
  ArithmeticProviderLaw -> Nothing

coreToTextWithExpected
  :: CoreConversionContext
  -> LiftCertificateUses
  -> Maybe Term
  -> Term
  -> Either KCoreTextError KTerm
coreToTextWithExpected conversionContext certificates expected term =
  evalStateT
    (go [] expected term)
    CoreConversionState
      { ccsNextLocal = 0
      , ccsGlobalTerms = Map.empty
      }
  where
    initialUniverse =
      1 + maximum
        ( -1
            : levelParamsOfTerm term
              ++ maybe [] levelParamsOfTerm expected
        )
    go :: [RenderedLocal] -> Maybe Term -> Term -> CoreConversionM KTerm
    go env expectedHere = \case
      CVar index -> case drop index env of
        local : _ ->
          pure
            ( KTLocal
                (renderedLocalRef local)
                [KLUniverse universe | universe <- renderedLocalUniverses local]
            )
        [] -> conversionError ("Core local index " <> tshow index <> " is out of scope")
      CLocal index levels -> case drop index env of
        local : _ -> KTLocal (renderedLocalRef local) <$> mapM (convertLevel env) levels
        [] -> conversionError ("Core local declaration index " <> tshow index <> " is out of scope")
      CGlobal g levels -> do
        scopedGlobals <- gets ccsGlobalTerms
        case (levels, Map.lookup g scopedGlobals) of
          ([], Just replacement) -> pure replacement
          _ ->
            KTGlobal
              (stableRefForGlobal (fromMaybe g (canonicalTrustedIntPrimitive g)))
              <$> mapM (convertLevel env) levels
      CLamM mode ic quantity name body -> do
        let expectedPi = stripClassifierWrappers <$> expectedHere
        (formation, assumption, origin, domainTerm, expectedBody) <- case expectedPi of
          Just (CPiEvidenceM _ formed _ _ _ _ bound binderOrigin domain codomain) ->
            pure (formed, bound, binderOrigin, domain, Just codomain)
          _ -> conversionError ("lambda emission requires its checked Pi type; expected " <> maybe "<none>" (T.pack . show) expectedHere)
        domain0 <- go env Nothing domainTerm
        domain' <- canonicalBoundType env assumption domain0
        ref <- freshLocal name
        let local = RenderedLocal ref assumption (Just domainTerm) []
        body' <- go (local : env) expectedBody body
        pure (KTLambda (KBinder mode formation (quantityToText quantity) (icitToText ic) KValue origin ref domain') body')
      CPiEvidenceM mode formation ic quantity borrowed name assumption origin domain codomain -> do
        domain0 <- go env Nothing domain
        domain' <- canonicalBoundType env assumption domain0
        ref <- freshLocal name
        let local = RenderedLocal ref assumption (Just domain) []
        codomain' <- go (local : env) Nothing codomain
        pure (KTPi (KBinder mode formation (quantityToText quantity) (icitToText ic) (if borrowed then KBorrow Nothing else KValue) origin ref domain') codomain')
      application@CApp {} -> do
        let (headTerm, arguments) = collectApplication application
        case betaReduceApplication (length env) headTerm arguments of
          Just reduced -> go env expectedHere reduced
          Nothing -> do
            head' <- go env Nothing headTerm
            arguments' <-
              case inferCoreType conversionContext env headTerm of
                Just signature -> convertApplicationArguments env signature arguments
                Nothing ->
                  mapM
                    (\(ic, argument) ->
                       KArgument (icitToText ic) <$> go env Nothing argument)
                    arguments
            pure (KTApply head' arguments')
      CSort level -> KTType <$> convertLevel env level
      CLevel level -> levelAsTerm <$> convertLevel env level
      CUniverseLift from to evidence inner -> do
        let from' = normalizeLevel from
            to' = normalizeLevel to
        proof <- renderLiftEvidence env from' to' evidence
        KTLift
          <$> convertLevel env from'
          <*> convertLevel env to'
          <*> pure proof
          <*> go env (Just (CSort from')) inner
      CSchemaLift family source target roles roleEvidence certificate _sourceArguments targetArguments inner -> do
        unless (length source == length target && length source == length roles && length roles == length roleEvidence) $
          conversionError "schema lift has inconsistent universe-role vector arities"
        source' <- mapM (convertLevel env . normalizeLevel) source
        target' <- mapM (convertLevel env . normalizeLevel) target
        renderedRoles <- forM (zip4 roles roleEvidence source target) $ \case
          (Invariant, SchemaInvariantEvidence, _, _) -> pure KSchemaInvariant
          (Irrelevant, SchemaIrrelevantEvidence, _, _) -> pure KSchemaIrrelevant
          (Covariant, SchemaCovariantEvidence evidence, lower, upper) ->
            KSchemaCovariant <$> renderLiftEvidence env (normalizeLevel lower) (normalizeLevel upper) evidence
          _ -> conversionError "schema lift role evidence disagrees with its role vector"
        argumentIcit <- familyArgumentIcit env family target targetArguments
        arguments' <- zipWithM (\icit argument -> KArgument (icitToText icit) <$> go env Nothing argument) argumentIcit targetArguments
        let certificateName = unSchemaActionCertificateId certificate
            certificateRef = stableSchemaCertificateRef certificateName
        KTSchemaLift (stableRefForGlobal family) source' target' certificateRef renderedRoles arguments'
          <$> go env Nothing inner
      CArithmeticProof certificate -> do
        -- Preserve the exact proposition authenticated by proof search.
        -- 'acReplayGoal' is a separate normalized representation for the
        -- independent arithmetic kernel; replacing the checked goal with an
        -- enclosing, more-reduced expected type would collapse that trust
        -- boundary and can erase the selected operation/evidence identities.
        goal <- go env Nothing (acGoal certificate)
        replayGoal <- go env Nothing (acReplayGoal certificate)
        convertedProviders <-
          forM (acProviders certificate) $ \(ArithmeticProviderEvidence descriptor trait evidence) -> do
            evidence' <- go env Nothing evidence
            let traitRef = stableRefForGlobal trait
                encoded = case descriptor of
                  Nothing ->
                    KVList
                      [ KVText (srName traitRef)
                      , KVText (srId traitRef)
                      , KVTerm evidence'
                      ]
                  Just provider ->
                    let providerRef = stableRefForText (anpIdentity provider)
                        lawRef = stableRefForGlobal (anpLawIdentity provider)
                        theoryName = case anpTheory provider of
                          ArithmeticMonoid -> "Monoid"
                          ArithmeticCommutativeMonoid -> "CommutativeMonoid"
                     in KVList
                          [ KVText "normalization"
                          , KVText (srName providerRef)
                          , KVText (srId providerRef)
                          , KVText theoryName
                          , KVText (srName traitRef)
                          , KVText (srId traitRef)
                          , KVText (srName lawRef)
                          , KVText (srId lawRef)
                          , KVInteger (anpNormalFormVersion provider)
                          , KVInteger (anpProviderVersion provider)
                          , KVInteger (anpCheckerVersion provider)
                          , KVTerm evidence'
                          ]
            pure (traitRef, evidence', descriptor, encoded)
        let providers =
              map snd
                . nubBy ((==) `on` fst)
                . sortOn fst
                $ [ (portableArithmeticProvider trait evidence descriptor, entry)
                  | entry@(trait, evidence, descriptor, _) <- convertedProviders
                  ]
        variableEntries <-
          forM (acVariables certificate) $ \(ArithmeticVariable kind variable) -> do
            variable' <- go env Nothing variable
            variableId <-
              case stripArithmeticTermWrappers variable' of
                KTLocal ref [] -> pure (lrId ref)
                _ -> conversionError "arithmetic certificate variable entry is not a monomorphic local"
            pure (variableId, kind, variable')
        let canonicalVariableEntries = sortOn (\(identity, _, _) -> identity) variableEntries
            variableIdentities = [identity | (identity, _, _) <- canonicalVariableEntries]
            variableNodes =
              [ KVList
                  [ KVText $ case kind of
                      ArithmeticVariableNatural -> "Natural"
                      ArithmeticVariableInteger -> "Integer"
                  , KVTerm variable
                  ]
              | (_, kind, variable) <- canonicalVariableEntries
              ]
        unless
          ( length variableIdentities
              == Set.size (Set.fromList variableIdentities)
          ) $
          conversionError "arithmetic certificate variable identities are not unique"
        let encodeAssumptionSource = \case
              ArithmeticAssumptionProof proposition evidence -> do
                proposition' <- go env Nothing proposition
                evidence' <- go env (Just proposition) evidence
                pure
                  ( KVList
                      [ KVText "proof"
                      , KVTerm proposition'
                      , KVTerm evidence'
                      ]
                  )
              ArithmeticAssumptionConversion proposition -> do
                proposition' <- go env Nothing proposition
                pure
                  ( KVList
                      [ KVText "conversion"
                      , KVTerm proposition'
                      ]
                  )
              ArithmeticAssumptionBranch truth condition -> do
                condition' <- go env Nothing condition
                pure
                  ( KVList
                      [ KVText "branch"
                      , KVInteger (if truth then 1 else 0)
                      , KVTerm condition'
                      ]
                  )
        (assumptionNodes, replayNode) <-
          case acDomain certificate of
            ArithmeticTypeLevel -> do
              unless (null variableIdentities) $
                conversionError "TypeLevel certificates cannot declare value-arithmetic variables"
              assumptions' <-
                fmap sort . forM (acAssumptions certificate) $ \(ArithmeticAssumption truth proposition replayProposition source) -> do
                  proposition' <- go env Nothing proposition
                  replayProposition' <- go env Nothing replayProposition
                  source' <- encodeAssumptionSource source
                  constraint <- maybe
                    (conversionError "TypeLevel certificate assumption is outside the authenticated comparison fragment")
                    pure
                    ( typeLevelAssumptionConstraint
                        [(trait, evidence) | (trait, evidence, _, _) <- providers]
                        truth
                        replayProposition'
                    )
                  pure
                    ( (if truth then 1 else 0, proposition', replayProposition')
                    , constraint
                    , KVList
                        [ KVInteger (if truth then 1 else 0)
                        , KVTerm proposition'
                        , KVTerm replayProposition'
                        , source'
                        ]
                    )
              replay <- maybe
                (conversionError "TypeLevel certificate goal is not derivable from its recorded assumptions")
                pure
                ( deriveTypeLevelReplay
                    [(trait, evidence) | (trait, evidence, _, _) <- providers]
                    [constraint | (_, constraint, _) <- assumptions']
                    replayGoal
                )
              pure ([encoded | (_, _, encoded) <- assumptions'], replay)
            ArithmeticProviderLaw -> do
              unless (null variableIdentities) $
                conversionError "provider-law certificates cannot declare value-arithmetic variables"
              (providerRef, _descriptor) <- case providers of
                [(_, _, Just descriptor, _)] ->
                  pure (stableRefForText (anpIdentity descriptor), descriptor)
                _ ->
                  conversionError
                    "provider-law certificate must select exactly one normalization-provider artifact"
              (assumptionNode, proof) <- case acAssumptions certificate of
                [ArithmeticAssumption True proposition replayProposition source] -> do
                  proposition' <- go env Nothing proposition
                  replayProposition' <- go env Nothing replayProposition
                  unless (replayProposition' == goal) $
                    conversionError
                      "provider-law replay has a different result proposition"
                  source' <- encodeAssumptionSource source
                  proof' <- case source of
                    ArithmeticAssumptionProof sourceProposition evidence -> do
                      sourceProposition' <- go env Nothing sourceProposition
                      unless (sourceProposition' == proposition') $
                        conversionError
                          "provider-law source proof has a different checked proposition"
                      go env (Just sourceProposition) evidence
                    ArithmeticAssumptionConversion {} ->
                      conversionError "provider-law certificate cannot use conversion evidence"
                    ArithmeticAssumptionBranch {} ->
                      conversionError "provider-law certificate cannot use branch evidence"
                  pure
                    ( KVList [KVInteger 1, KVTerm proposition', KVTerm replayProposition', source']
                    , proof'
                    )
                _ ->
                  conversionError
                    "provider-law certificate must contain exactly one checked law proof"
              pure
                ( [assumptionNode]
                , KVList
                    [ KVText "provider-law"
                    , KVText (srName providerRef)
                    , KVText (srId providerRef)
                    , KVTerm proof
                    ]
                )
            domain -> do
              assumptions' <-
                fmap sort . forM (acAssumptions certificate) $ \(ArithmeticAssumption truth proposition replayProposition source) -> do
                  proposition' <- go env Nothing proposition
                  replayProposition' <- go env Nothing replayProposition
                  source' <- encodeAssumptionSource source
                  formula <- maybe
                    ( conversionError
                        ( "arithmetic certificate assumption is outside the authenticated fragment: "
                            <> printTerm replayProposition'
                        )
                    )
                    pure
                    (arithmeticFormulaFromKTerm domain replayProposition')
                  pure
                    ( (if truth then 1 else 0, proposition', replayProposition')
                    , (truth, formula)
                    , KVList
                        [ KVInteger (if truth then 1 else 0)
                        , KVTerm proposition'
                        , KVTerm replayProposition'
                        , source'
                        ]
                    )
              goalFormula <- maybe
                ( conversionError
                    ( "arithmetic certificate goal is outside the authenticated fragment: "
                        <> printTerm replayGoal
                    )
                )
                pure
                (arithmeticFormulaFromKTerm domain replayGoal)
              let variableContext =
                    Map.fromList (zip variableIdentities [0 ..])
                  canonicalNaturalSet =
                    Set.fromList
                      [ index
                      | (index, (_, kind, _)) <- zip [0 ..] canonicalVariableEntries
                      , kind == ArithmeticVariableNatural
                      ]
              canonicalGoal <- maybe
                (conversionError "arithmetic certificate goal refers to a variable outside its recorded context")
                pure
                (reindexArithmeticFormula variableContext goalFormula)
              canonicalAssumptions <- maybe
                (conversionError "arithmetic certificate assumption refers to a variable outside its recorded context")
                pure
                ( traverse
                    (\(truth, formula) ->
                      (truth,) <$> reindexArithmeticFormula variableContext formula)
                    [formula | (_, formula, _) <- assumptions']
                )
              replay <- maybe
                ( conversionError
                    ( "arithmetic certificate goal is not derivable from its recorded assumptions"
                        <> "; goal="
                        <> T.pack (show canonicalGoal)
                        <> "; assumptions="
                        <> T.pack (show canonicalAssumptions)
                        <> "; natural-variables="
                        <> T.pack (show canonicalNaturalSet)
                    )
                )
                pure
                ( do
                    semantics <- arithmeticReplaySemantics domain
                    deriveArithmeticFormulaReplayWithAssumptions
                      semantics
                      canonicalNaturalSet
                      canonicalAssumptions
                      True
                      canonicalGoal
                )
              pure
                ( [encoded | (_, _, encoded) <- assumptions']
                , encodeArithmeticFormulaReplay replay
                )
        let domainName = case acDomain certificate of
              ArithmeticNatural -> "Natural"
              ArithmeticInteger -> "Integer"
              ArithmeticTypeLevel -> "TypeLevel"
              ArithmeticProviderLaw -> "ProviderLaw"
        pure
          ( KTGeneric
              "impl.kappa.core.arithmetic-proof"
              [ ("result-type", KVTerm goal)
              , ("replay-goal", KVTerm replayGoal)
              , ("version", KVInteger (acVersion certificate))
              , ("domain", KVText domainName)
              , ("providers", KVList [encoded | (_, _, _, encoded) <- providers])
              , ("variables", KVList variableNodes)
              , ("assumptions", KVList assumptionNodes)
              , ("replay", replayNode)
              ]
          )

      CLit literal -> pure (KTLiteral literal)
      CCtorI constructor levels annotation arguments ->
        case Map.lookup constructor (cccConstructors conversionContext) of
          Just info -> do
            unless (length levels == dutParameterCount (kcciUniverses info)) $
              conversionError
                ( "constructor " <> gKey constructor <> " carries " <> tshow (length levels)
                    <> " declaration-universe arguments but its interface requires "
                    <> tshow (dutParameterCount (kcciUniverses info))
                )
            levelArguments <- mapM (convertLevel env) levels
            parameterCount <- constructorParameterCount info
            convertedArguments <-
              convertConstructorArguments env constructor parameterCount
                (specializeCoreUniverses levels (kcciType info)) arguments
            pure (KTConstruct (stableRefForConstructor constructor) levelArguments convertedArguments)
          Nothing
            | constructor == prelEffPure || constructor == prelEffOp -> do
                unless (null levels) $
                  conversionError "effect-tree intrinsics cannot carry declaration-universe arguments"
                resultCore <-
                  maybe (conversionError "effect-tree constructor emission requires its checked result type") pure expectedHere
                constructorType <- case annotation of
                  Just checked -> pure checked
                  Nothing
                    | constructor == prelEffPure
                    , [argument] <- arguments -> do
                        argumentType <-
                          maybe (conversionError "__EffPure payload type is unavailable at the typed checkpoint") pure
                            (inferCoreType conversionContext env (caTerm argument))
                        pure
                          ( CPiEvidenceM Ordinary FormationOrdinary Expl Q1 False "__value" Nothing BinderSourceWritten
                              argumentType (shiftTerm 1 0 resultCore)
                          )
                  Nothing -> conversionError "__EffOp is missing its checked intrinsic telescope"
                convertedArguments <- convertConstructorArguments env constructor 0 constructorType arguments
                resultType <- go env Nothing resultCore
                constructorType' <- go env Nothing constructorType
                pure
                  ( KTGeneric
                      intrinsicEffectTreeTag
                      [ ("result-type", KVTerm resultType)
                      , ("constructor", KVGlobal (stableRefForConstructor constructor) [])
                      , ("constructor-type", KVTerm constructorType')
                      , ("arguments", KVList [KVTerm term | KArgument _ term <- convertedArguments])
                      ]
                  )
            | otherwise -> conversionError ("constructor interface is unavailable for " <> gKey constructor)
      CMatch scrutinee scrutineeAnnotation alternatives -> do
        resultCore <- maybe (conversionError "case emission requires its checked result type") pure expectedHere
        scrutineeType <-
          maybe
            (conversionError "case scrutinee type is unavailable at the typed checkpoint")
            pure
            (scrutineeAnnotation <|> inferCoreType conversionContext env scrutinee)
        scrutinee' <- go env Nothing scrutinee
        scrutineeType' <- go env Nothing scrutineeType
        resultType <- go env Nothing resultCore
        alternatives' <- mapM (goCaseAlt env scrutineeType scrutineeType' resultCore) alternatives
        pure (KTCase scrutinee' resultType alternatives')
      CRecordTQ fields -> KTRecordType <$> goRecordFields env fields
      CRecordV fields -> do
        expectedCore <- maybe (conversionError "record value emission requires its checked record type") pure expectedHere
        recordFields <-
          maybe
            (conversionError ("record value expected type has no structural record interface: " <> T.pack (show expectedCore)))
            pure
            (coreRecordFieldsFor conversionContext env expectedCore)
        KTRecordValue <$> goRecordValues env recordFields fields
      CProj record field -> KTProject (stableFieldRef field) <$> go env Nothing record
      CProjAt record field _ -> KTProject (stableFieldRef field) <$> go env Nothing record
      CLetM mode quantity name ty rhs body -> do
        ty' <- go env Nothing ty
        ref <- freshLocal name
        rhs' <- go env (Just ty) rhs
        let local = RenderedLocal ref Nothing (Just ty) []
        body' <- go (local : env) expectedHere body
        let binder = KBinder mode FormationOrdinary (quantityToText quantity) KExplicit KValue BinderSourceWritten ref ty'
        pure (KTBlock [KBLet binder rhs'] body')
      CLetRecM mode quantity name ty rhs body -> do
        ty' <- go env Nothing ty
        ref <- freshLocal name
        let local = RenderedLocal ref Nothing (Just ty) []
            env' = local : env
            definition = KLocalDef ref mode [] ty'
        rhs' <- go env' (Just ty) rhs
        body' <- go env' expectedHere body
        pure (KTLetRec [definition rhs'] body')
      CLetPolyM mode _quantity name telescope ty rhs body -> do
        ref <- freshLocal name
        localUniverses <- localUniversesFor ref (dutParameterCount telescope)
        let scope = localUniverseScope localUniverses
            tyScoped = scope ty
            rhsScoped = scope rhs
            definition = KLocalDef ref mode localUniverses
            local = RenderedLocal ref Nothing (Just ty) []
        ty' <- go env Nothing tyScoped
        rhs' <- go env (Just tyScoped) rhsScoped
        body' <- go (local : env) expectedHere body
        pure (KTLetRec [definition ty' rhs'] body')
      CLetRecPolyM mode _quantity name telescope ty rhs body -> do
        ref <- freshLocal name
        localUniverses <- localUniversesFor ref (dutParameterCount telescope)
        let scope = localUniverseScope localUniverses
            tyScoped = scope ty
            rhsScoped = scope rhs
            activeLocal = RenderedLocal ref Nothing (Just ty) localUniverses
            bodyLocal = activeLocal {renderedLocalUniverses = []}
            definition = KLocalDef ref mode localUniverses
        ty' <- go env Nothing tyScoped
        rhs' <- go (activeLocal : env) (Just tyScoped) rhsScoped
        body' <- go (bodyLocal : env) expectedHere body
        pure (KTLetRec [definition ty' rhs'] body')
      CLetRecGroupM telescope definitions body -> do
        firstDefinition <- case definitions of
          first : _ -> pure first
          [] -> conversionError "a local recursive SCC must contain at least one definition"
        firstRef <- freshLocal (clrdName firstDefinition)
        restRefs <- mapM (freshLocal . clrdName) (drop 1 definitions)
        let refs = firstRef : restRefs
        localUniverses <- localUniversesFor firstRef (dutParameterCount telescope)
        let scope = localUniverseScope localUniverses
            activeLocals =
              [ RenderedLocal ref Nothing (Just (clrdType definition)) localUniverses
              | (ref, definition) <- zip refs definitions
              ]
            bodyLocals = map (\local -> local {renderedLocalUniverses = []}) activeLocals
            recursiveEnv = reverse activeLocals ++ env
            bodyEnv = reverse bodyLocals ++ env
        renderedDefinitions <- forM (zip refs definitions) $ \(ref, definition) -> do
          let tyScoped = scope (clrdType definition)
              rhsScoped = scope (clrdRhs definition)
          ty' <- go env Nothing tyScoped
          rhs' <- go recursiveEnv (Just tyScoped) rhsScoped
          pure (KLocalDef ref (clrdMode definition) localUniverses ty' rhs')
        body' <- go bodyEnv expectedHere body
        pure (KTLetRec renderedDefinitions body')
      CVariantT members ->
        do
          evalContext <- maybe (conversionError "variant type emission requires the finalized evaluation context") pure (cccEvalContext conversionContext)
          let depth = length env
              rigidEnvironment = [VRigid (depth - 1 - index) [] | index <- [0 .. depth - 1]]
              tags = [semanticTypeTag evalContext depth (eval evalContext rigidEnvironment member) | member <- members]
          members' <- mapM (go env Nothing) members
          pure
            ( KTGeneric "impl.kappa.core.variant-type"
                [ ("tags", KVList (map KVText tags))
                , ("members", KVList (map KVTerm members'))
                ]
            )
      CInject tag value ->
        typedGeneric env expectedHere "impl.kappa.core.inject"
          [("tag", pure (KVText tag)), ("value", KVTerm <$> go env Nothing value)]
      CSealE labels value ->
        typedGeneric env expectedHere "impl.kappa.core.seal"
          [("labels", pure (KVList (map KVText labels))), ("value", KVTerm <$> go env Nothing value)]
      CSigT labels value ->
        KTGeneric "impl.kappa.core.signature-type"
          <$> sequence
            [ pure ("labels", KVList (map KVText labels))
            , ("value",) . KVTerm <$> go env expectedHere value
            ]
      CThunkE value suspensionType ->
        typedGeneric env (suspensionType <|> expectedHere) "impl.kappa.core.thunk"
          [("value", KVTerm <$> go env Nothing value)]
      CLazyE value suspensionType ->
        typedGeneric env (suspensionType <|> expectedHere) "impl.kappa.core.lazy"
          [("value", KVTerm <$> go env Nothing value)]
      CForceE value resultType ->
        typedGeneric env (resultType <|> expectedHere) "impl.kappa.core.force"
          [("value", KVTerm <$> go env Nothing value)]
      CQuote quoted slots ->
        typedGeneric env expectedHere "impl.kappa.core.quote"
          [ ("syntax", pure (syntaxDataValue (qsExpr quoted)))
          , ("captures", KVList <$> mapM (quoteCaptureValue env) (qsCaptures quoted))
          , ("origin", pure (syntaxDataValue (qsSpan quoted)))
          , ("slots", KVList <$> mapM (fmap KVTerm . goInferred env "syntax quote splice slot") slots)
          ]
      CDo label items -> do
        expectedCore <-
          maybe (conversionError "impl.kappa.core.do emission requires its checked result type") pure expectedHere
        resultCore <-
          maybe (conversionError "impl.kappa.core.do emission requires an applied checked monad result type") pure
            (monadicCoreResult expectedCore)
        encodedItems <- goDoItems expectedCore resultCore env items
        typedGeneric env expectedHere "impl.kappa.core.do"
          [ ("label", pure (maybe (KVList []) (KVList . pure . KVText) label))
          , ("items", pure (KVList (map KVTerm encodedItems)))
          ]
      CIf condition thenBranch elseBranch ->
        KTIf
          <$> go env Nothing condition
          <*> go env expectedHere thenBranch
          <*> go env expectedHere elseBranch
      CMeta meta -> conversionError ("unsolved Core metavariable " <> tshow meta <> " reached KCoreText emission")
      other -> conversionError ("Core form has no KCoreText schema: " <> T.pack (show other))
    goCaseAlt env scrutineeType scrutineeType' resultCore = \case
      CaseAlt CPWild Nothing body -> KCaseDefault <$> go env (Just resultCore) body
      CaseAlt (CPCtorM existentialModes bridges constructor levels patterns) Nothing body
        | all simplePattern patterns -> do
        info <-
          maybe
            (conversionError ("case constructor interface is unavailable for " <> gKey constructor))
            pure
            (Map.lookup constructor (cccConstructors conversionContext))
        unless (length levels == dutParameterCount (kcciUniverses info)) $
          conversionError
            ( "case constructor " <> gKey constructor <> " carries " <> tshow (length levels)
                <> " declaration-universe arguments but its interface requires "
                <> tshow (dutParameterCount (kcciUniverses info))
            )
        specialized <- go env Nothing (specializeCoreUniverses levels (kcciType info))
        parameterCount <- constructorParameterCount info
        let (allBinders, constructorResult) = splitPiTelescope specialized
            (parameters, payload0) = splitAt parameterCount allBinders
        alignment <-
          maybe
            (conversionError ("case constructor " <> gKey constructor <> " result does not determine its data parameters"))
            pure
            ( alignKConstructorResult
                True
                True
                conversionNominalFamily
                (\ref -> lrId ref `Set.member` renderedLocalIds env)
                (==)
                parameters
                Map.empty
                constructorResult
                scrutineeType'
            )
        let payload =
              constructorEliminationPayload
                parameters
                payload0
                alignment
            fieldCount = length (kcciSourceFields info)
            existentialCount = length payload - fieldCount
            (existentialPayload, fieldPayload) = splitAt existentialCount payload
        unless
          ( existentialCount >= 0
              && length existentialPayload == length existentialModes
              && length fieldPayload == fieldCount
          ) $
          conversionError ("case constructor " <> gKey constructor <> " source-field telescope does not align with its checked payload")
        alignedPatterns <- alignConstructorPatterns constructor (kcciSourceFields info) patterns
        (existentialBinders, existentialLocals) <- prepareExistentialBinders existentialPayload existentialModes
        (bridgeBinders, bridgeLocals) <-
          prepareConstructorBridges
            (reverse existentialLocals ++ env)
            (propositionalConstructorBridges bridges)
        unless
          ( constructorBridgesMatchEquations
              (kcaPropositionalEquations alignment)
              bridgeBinders
          ) $
          conversionError
            ("case constructor " <> gKey constructor <> " bridge proofs do not match its unresolved index equations")
        let fieldPayload' = renameExpectedBinders existentialPayload existentialBinders fieldPayload
        (fieldBinders, fieldLocals) <- preparePatternBinders fieldPayload' alignedPatterns
        let bindings =
              map KCasePayload existentialBinders
                ++ map KCaseBridge bridgeBinders
                ++ map KCasePayload fieldBinders
            bodyLocals = existentialLocals ++ bridgeLocals ++ fieldLocals
        body' <- go (reverse bodyLocals ++ env) (Just resultCore) body
        KCaseConstructor (stableRefForConstructor constructor)
          <$> mapM (convertLevel env) levels
          <*> pure bindings
          <*> pure body'
      CaseAlt pattern guard' body -> do
        (pattern', patternLocals) <- preparePortablePattern env scrutineeType scrutineeType' pattern
        let bodyEnv = reverse patternLocals ++ env
        guard'' <- traverse (go bodyEnv Nothing) guard'
        body' <- go bodyEnv (Just resultCore) body
        pure (KCasePattern pattern' guard'' body')
    conversionNominalFamily ref =
      any
        ((== ref) . stableRefForGlobal . kcciData)
        (Map.elems (cccConstructors conversionContext))
    constructorBridgesMatchEquations equations bridges =
      length equations == length bridges
        && and
          ( zipWith
              (constructorBridgeMatchesEquationWith (==))
              equations
              bridges
          )
    simplePattern = \case CPVarM {} -> True; CPWild -> True; _ -> False

    preparePortablePattern envHere expectedCore expectedText pattern' = do
      let expectedBinder =
            KBinder (patternSlotMode Ordinary pattern') FormationOrdinary KQOmega KExplicit KValue BinderSourceWritten
              (LocalRef (patternSlotName "_" pattern') (-1)) expectedText
      preparePatternAt envHere expectedCore expectedBinder pattern'

    preparePatternAt envHere expectedCore expectedBinder pattern' = do
      ref <- freshLocal (patternSlotName (lrName (kbRef expectedBinder)) pattern')
      let slot =
            expectedBinder
              { kbRef = ref
              , kbMode = patternSlotMode (kbMode expectedBinder) pattern'
              }
          slotLocal = RenderedLocal ref Nothing (Just expectedCore) []
          exposed = patternExposesSlot pattern'
          exposedLocals = [slotLocal | exposed]
      case pattern' of
        CPWild -> pure (KPattern slot False KPNWild, [])
        CPVarM {} -> pure (KPattern slot True KPNWild, exposedLocals)
        CPLit literal -> pure (KPattern slot False (KPNLiteral literal), [])
        CPTuple patterns -> do
          coreFields <- case stripClassifierWrappers expectedCore of
            CRecordTQ fields -> pure fields
            _ -> conversionError "tuple pattern scrutinee has no checked record telescope"
          textFields <- case expectedTextHead (kbType slot) of
            KTRecordType fields -> pure fields
            _ -> conversionError "tuple pattern scrutinee KCore type is not a record telescope"
          unless (length patterns == length coreFields && length patterns == length textFields) $
            conversionError "tuple pattern arity does not match its checked record telescope"
          (patterns', locals) <- preparePatternFields envHere coreFields (map snd textFields) patterns
          pure (KPattern slot False (KPNTuple patterns'), locals)
        CPCtorM existentialModes bridges constructor levels patterns -> do
          info <-
            maybe (conversionError ("nested case constructor interface is unavailable for " <> gKey constructor)) pure
              (Map.lookup constructor (cccConstructors conversionContext))
          unless (length levels == dutParameterCount (kcciUniverses info)) $
            conversionError
              ( "nested case constructor " <> gKey constructor <> " carries " <> tshow (length levels)
                  <> " declaration-universe arguments but its interface requires "
                  <> tshow (dutParameterCount (kcciUniverses info))
              )
          parameterCount <- constructorParameterCount info
          let specializedCore = specializeCoreUniverses levels (kcciType info)
              (coreDomains, _) = splitCorePiTelescope specializedCore
              corePayload = drop parameterCount coreDomains
          specialized <- go envHere Nothing specializedCore
          let (allBinders, constructorResult) = splitPiTelescope specialized
              (parameters, payload0) = splitAt parameterCount allBinders
          alignment <-
            maybe (conversionError ("nested constructor " <> gKey constructor <> " result does not determine its data parameters")) pure
              ( alignKConstructorResult
                  True
                  True
                  conversionNominalFamily
                  (\ref -> lrId ref `Set.member` renderedLocalIds envHere)
                  (==)
                  parameters
                  Map.empty
                  constructorResult
                  (kbType slot)
              )
          let payload =
                constructorEliminationPayload
                  parameters
                  payload0
                  alignment
              fieldCount = length (kcciSourceFields info)
              existentialCount = length payload - fieldCount
              coreExistentialCount = length corePayload - fieldCount
              (existentialPayload, fieldPayload) = splitAt existentialCount payload
              (coreExistentials, coreFields) = splitAt coreExistentialCount corePayload
          unless
            ( existentialCount >= 0
                && coreExistentialCount >= 0
                && length existentialPayload == length existentialModes
                && length coreExistentials == length existentialModes
                && length fieldPayload == fieldCount
                && length coreFields == fieldCount
            ) $
            conversionError "nested constructor source-field telescope does not align with its checked payload"
          alignedPatterns <- alignConstructorPatterns constructor (kcciSourceFields info) patterns
          (existentials, existentialLocals) <- prepareExistentialBinders existentialPayload existentialModes
          (bridgeBinders, bridgeLocals) <-
            prepareConstructorBridges
              (reverse existentialLocals ++ envHere)
              (propositionalConstructorBridges bridges)
          unless
            ( constructorBridgesMatchEquations
                (kcaPropositionalEquations alignment)
                bridgeBinders
            ) $
            conversionError
              ("nested constructor " <> gKey constructor <> " bridge proofs do not match its unresolved index equations")
          let fieldPayload' = renameExpectedBinders existentialPayload existentials fieldPayload
              fieldEnv =
                reverse (existentialLocals ++ bridgeLocals) ++ envHere
              coreFieldRecords =
                [ RecordField (lrName (kbRef binder)) (kbMode binder) (kbFormation binder) QW Nothing coreType
                | (binder, coreType) <- zip fieldPayload' coreFields
                ]
          (fields', fieldLocals) <- preparePatternFields fieldEnv coreFieldRecords fieldPayload' alignedPatterns
          levels' <- mapM (convertLevel envHere) levels
          pure
            ( KPattern slot False
                (KPNConstructor
                  (stableRefForConstructor constructor)
                  levels'
                  existentials
                  bridgeBinders
                  fields')
            , existentialLocals ++ bridgeLocals ++ fieldLocals
            )
        CPRecordM selectedFields rest -> do
          coreFields <- case stripClassifierWrappers expectedCore of
            CRecordTQ fields -> pure fields
            _ -> conversionError "record pattern scrutinee has no checked record telescope"
          textFields <- case expectedTextHead (kbType slot) of
            KTRecordType fields -> pure fields
            _ -> conversionError "record pattern scrutinee KCore type is not a record telescope"
          unless (map rfName coreFields == map (srName . fst) textFields) $
            conversionError "record pattern checked Core and KCore telescopes disagree"
          let selectedNames = map fst selectedFields
              patterns = [maybe CPWild id (lookup (rfName field) selectedFields) | field <- coreFields]
          (fields', locals) <- preparePatternFields envHere coreFields (map snd textFields) patterns
          let serializedFields =
                [ (stableFieldRef (rfName field), rfName field `elem` selectedNames, patternValue)
                | (field, patternValue) <- zip coreFields fields'
                ]
              remainingCore = [field | field <- coreFields, rfName field `notElem` selectedNames]
          remainingText <- prepareResidualRecordFields serializedFields
          (rest', restLocals) <- case rest of
            Nothing -> pure (Nothing, [])
            Just (mode, name) -> do
              ref' <- freshLocal (if T.null name then "_rest" else name)
              let restBinder = KBinder mode FormationOrdinary KQOmega KExplicit KValue BinderSourceWritten ref' (KTRecordType remainingText)
                  restPattern = KPattern restBinder (not (T.null name)) KPNWild
                  restLocal = RenderedLocal ref' Nothing (Just (CRecordTQ remainingCore)) []
              pure (Just restPattern, [restLocal | not (T.null name)])
          pure (KPattern slot False (KPNRecord serializedFields rest'), locals ++ restLocals)
        CPInject tag payload -> do
          (memberCore, memberText) <- variantMember envHere expectedCore (kbType slot) tag
          ref' <- freshLocal (patternSlotName "variant" payload)
          let payloadBinder =
                KBinder (patternSlotMode (kbMode slot) payload) FormationOrdinary KQOmega KExplicit KValue BinderSourceWritten ref' memberText
          (payload', locals) <- preparePatternAt envHere memberCore payloadBinder payload
          pure (KPattern slot False (KPNInject tag payload'), locals)
        CPInjectRestM mode excluded ->
          pure (KPattern (slot {kbMode = mode}) True (KPNInjectRest excluded), exposedLocals)
        CPAsM _ _ payload -> do
          let asLocal = slotLocal
          (payload', nestedLocals) <- preparePortablePattern (asLocal : envHere) expectedCore (kbType slot) payload
          pure (KPattern slot True (KPNAs payload'), asLocal : nestedLocals)
        CPOr alternatives permutations -> do
          prepared <- mapM (preparePatternAt envHere expectedCore expectedBinder) alternatives
          case prepared of
            [] -> conversionError "empty Core or-pattern reached KCoreText emission"
            (_, canonicalLocals) : _ -> do
              unless (all ((== length canonicalLocals) . length . snd) prepared) $
                conversionError "or-pattern alternatives disagree on binder arity"
              pure (KPattern slot False (KPNOr (map fst prepared) permutations), canonicalLocals)

    preparePatternFields _ [] [] [] = pure ([], [])
    preparePatternFields envHere (coreField : coreRest) (expectedBinder : expectedRest) (pattern' : patternRest) = do
      (headPattern, headLocals) <- preparePatternAt envHere (rfType coreField) expectedBinder pattern'
      let oldRef = kbRef expectedBinder
          newRef = kbRef (kpSlot headPattern)
          expectedRest' = map (renameBinderLocal oldRef newRef) expectedRest
          structuralLocal = RenderedLocal newRef Nothing (Just (rfType coreField)) []
      (tailPatterns, tailLocals) <-
        preparePatternFields (structuralLocal : envHere) coreRest expectedRest' patternRest
      pure (headPattern : tailPatterns, headLocals ++ tailLocals)
    preparePatternFields _ _ _ _ = conversionError "pattern structural arity disagrees with its checked telescope"

    prepareResidualRecordFields = goResidual []
      where
        goResidual _ [] = pure []
        goResidual renamings ((field, selected, pattern') : rest)
          | selected = goResidual renamings rest
          | otherwise = do
              let structural = kpSlot pattern'
                  renamedType =
                    foldl
                      (\ty (oldRef, newRef) -> renameLocal oldRef newRef ty)
                      (kbType structural)
                      renamings
              ref <- freshLocal (srName field)
              let residualBinder = structural {kbRef = ref, kbType = renamedType}
              remaining <- goResidual (renamings ++ [(kbRef structural, ref)]) rest
              pure ((field, residualBinder) : remaining)

    patternSlotName fallback = \case
      CPVarM _ name -> name
      CPAsM _ name _ -> name
      _ -> fallback
    patternSlotMode fallback = \case
      CPVarM mode _ -> mode
      CPAsM mode _ _ -> mode
      CPInjectRestM mode _ -> mode
      _ -> fallback
    patternExposesSlot = \case
      CPVarM {} -> True
      CPAsM {} -> True
      CPInjectRestM {} -> True
      _ -> False

    alignConstructorPatterns constructor sourceFields explicitPatterns = do
      unless (length explicitPatterns == length [() | (Expl, _) <- sourceFields]) $
        conversionError
          ( "constructor " <> gKey constructor
              <> " explicit pattern arity does not match its checked source-field telescope"
          )
      pure (go sourceFields explicitPatterns)
      where
        go [] [] = []
        go ((Impl, _) : rest) remaining = CPWild : go rest remaining
        go ((Expl, _) : rest) (pattern' : remaining) = pattern' : go rest remaining
        go _ _ = []
    expectedTextHead = id

    renameExpectedBinders expected actual rest =
      foldl
        (\renamed (expectedBinder, actualBinder) -> map (renameBinderLocal (kbRef expectedBinder) (kbRef actualBinder)) renamed)
        rest
        (zip expected actual)

    variantMember envHere expectedCore expectedText tag = do
      coreMembers <- case stripClassifierWrappers expectedCore of
        CVariantT members -> pure members
        _ -> conversionError "variant pattern scrutinee has no checked variant type"
      textMembers <- case expectedTextHead expectedText of
        KTGeneric "impl.kappa.core.variant-type" fields -> case (lookup "tags" fields, lookup "members" fields) of
          (Just (KVList tags), Just (KVList members)) -> do
            tags' <- mapM (\case KVText value -> pure value; _ -> conversionError "variant tag metadata is malformed") tags
            members' <- mapM (\case KVTerm value -> pure value; _ -> conversionError "variant member metadata is malformed") members
            pure (zip tags' members')
          _ -> conversionError "variant KCore type lacks tag/member metadata"
        _ -> conversionError "variant pattern scrutinee KCore type is not a variant type"
      evalContext <- maybe (conversionError "variant pattern emission requires the finalized evaluation context") pure (cccEvalContext conversionContext)
      let depth = length envHere
          rigidEnvironment = [VRigid (depth - 1 - index) [] | index <- [0 .. depth - 1]]
          coreTagged = [(semanticTypeTag evalContext depth (eval evalContext rigidEnvironment member), member) | member <- coreMembers]
      coreMember <- maybe (conversionError "variant pattern tag is absent from checked Core type") pure (lookup tag coreTagged)
      textMember <- maybe (conversionError "variant pattern tag is absent from checked KCore type") pure (lookup tag textMembers)
      pure (coreMember, textMember)

    prepareExistentialBinders [] [] = pure ([], [])
    prepareExistentialBinders (expectedBinder : expectedRest) (mode : modeRest) = do
      let oldRef = kbRef expectedBinder
      ref <- freshLocal (lrName oldRef)
      let binder = expectedBinder {kbRef = ref, kbMode = mode}
          renamedRest = map (renameBinderLocal oldRef ref) expectedRest
          local = RenderedLocal ref Nothing Nothing []
      (restBinders, restLocals) <- prepareExistentialBinders renamedRest modeRest
      pure (binder : restBinders, local : restLocals)
    prepareExistentialBinders _ _ = conversionError "constructor existential pattern binder count mismatch"

    prepareConstructorBridges _ [] = pure ([], [])
    prepareConstructorBridges envHere
      (ConstructorPropositionalBridge bridgeType bridgeProof : rest) = do
      type' <- go envHere Nothing bridgeType
      proof' <- go envHere (Just bridgeType) bridgeProof
      ref <- freshLocal "__bridge"
      let binder =
            KBinder
              Ordinary
              FormationOrdinary
              KQ0
              KImplicit
              KValue
              BinderSourceWritten
              ref
              type'
          local = RenderedLocal ref Nothing (Just bridgeType) []
      (restBridges, restLocals) <-
        prepareConstructorBridges (local : envHere) rest
      pure
        ( KConstructorBridge binder proof' : restBridges
        , local : restLocals
        )
    prepareConstructorBridges _ (ConstructorForcedEquality {} : _) =
      conversionError
        "forced constructor equalities must not be serialized as lexical bridge binders"

    preparePatternBinders [] [] = pure ([], [])
    preparePatternBinders (expectedBinder : expectedRest) (pattern : patternRest) = do
      let oldRef = kbRef expectedBinder
          patternName = case pattern of
            CPVarM _ name -> name
            CPWild -> "_"
            _ -> "_"
          patternMode = case pattern of
            CPVarM mode _ -> mode
            _ -> kbMode expectedBinder
      unless (case pattern of CPVarM {} -> True; CPWild -> True; _ -> False) $
        conversionError ("nested Core constructor pattern has no portable KCoreText schema: " <> T.pack (show pattern))
      ref <- freshLocal patternName
      let binder = expectedBinder {kbRef = ref, kbMode = patternMode}
          renamedRest = map (renameBinderLocal oldRef ref) expectedRest
          bodyLocal = case pattern of
            CPVarM _ _ -> [RenderedLocal ref Nothing Nothing []]
            _ -> []
      (restBinders, restLocals) <- preparePatternBinders renamedRest patternRest
      pure (binder : restBinders, bodyLocal ++ restLocals)
    preparePatternBinders _ _ = conversionError "constructor pattern payload arity mismatch"
    goDoItems _ _ _ [] = pure []
    goDoItems actionCore resultCore env (item : rest) = case item of
      KBind quantity pattern' action _ -> do
        actionType <-
          maybe (conversionError "do bind action type is unavailable at the typed checkpoint") pure
            (inferCoreType conversionContext env action)
        resultCore <- maybe (conversionError "do bind action is not an application of its checked monad carrier") pure (monadicCoreResult actionType)
        resultType <- go env Nothing resultCore
        action' <- go env (Just actionType) action
        (pattern'', locals) <- prepareDoPattern env quantity resultCore resultType pattern'
        let encoded =
              KTGeneric "impl.kappa.core.do.bind"
                [ ("action", KVTerm action')
                , ("quantity", KVQuantity (quantityToText quantity))
                , ("pattern", KVPattern pattern'')
                ]
        rest' <- goDoItems actionCore resultCore (reverse locals ++ env) rest
        pure (encoded : rest')
      KLet quantity pattern' rhs -> do
        rhsCoreType <- maybe (conversionError "do let value type is unavailable at the typed checkpoint") pure (inferCoreType conversionContext env rhs)
        rhsType <- go env Nothing rhsCoreType
        rhs' <- go env (Just rhsCoreType) rhs
        (pattern'', locals) <- prepareDoPattern env quantity rhsCoreType rhsType pattern'
        let encoded =
              KTGeneric "impl.kappa.core.do.let"
                [ ("quantity", KVQuantity (quantityToText quantity))
                , ("pattern", KVPattern pattern'')
                , ("value", KVTerm rhs')
                ]
        rest' <- goDoItems actionCore resultCore (reverse locals ++ env) rest
        pure (encoded : rest')
      KLetQ pattern' rhs elseBranch -> do
        rhsCoreType <- maybe (conversionError "do let? value type is unavailable at the typed checkpoint") pure (inferCoreType conversionContext env rhs)
        rhsType <- go env Nothing rhsCoreType
        rhs' <- go env (Just rhsCoreType) rhs
        (pattern'', locals) <- prepareDoPattern env QW rhsCoreType rhsType pattern'
        (elsePatterns, elseActions) <- case elseBranch of
          Nothing -> pure ([], [])
          Just (elsePattern, elseAction) -> do
            (elsePattern', elseLocals) <- prepareDoPattern env QW rhsCoreType rhsType elsePattern
            elseAction' <- goInferred (reverse elseLocals ++ env) "do let? else action" elseAction
            pure ([KVPattern elsePattern'], [KVTerm elseAction'])
        let encoded =
              KTGeneric "impl.kappa.core.do.letq"
                [ ("pattern", KVPattern pattern'')
                , ("value", KVTerm rhs')
                , ("else-pattern", KVList elsePatterns)
                , ("else-action", KVList elseActions)
                ]
        rest' <- goDoItems actionCore resultCore (reverse locals ++ env) rest
        pure (encoded : rest')
      KVarItem name initial action _ -> do
        actionType <- maybe (conversionError "do var allocation action type is unavailable") pure (inferCoreType conversionContext env action)
        refCoreType <- maybe (conversionError "do var allocation action is not an application of its checked monad carrier") pure (monadicCoreResult actionType)
        refType <- go env Nothing refCoreType
        ref <- freshLocal name
        initial' <- goInferred env "do var initializer" initial
        action' <- go env (Just actionType) action
        let binder = KBinder Ordinary FormationOrdinary KQOmega KExplicit KValue BinderSourceWritten ref refType
            encoded =
              KTGeneric "impl.kappa.core.do.var"
                [("binder", KVBinder binder), ("initial", KVTerm initial'), ("action", KVTerm action')]
            local = RenderedLocal ref Nothing (Just refCoreType) []
        rest' <- goDoItems actionCore resultCore (local : env) rest
        pure (encoded : rest')
      KUsing pattern' acquire release -> do
        acquireType <- maybe (conversionError "do using acquire type is unavailable") pure (inferCoreType conversionContext env acquire)
        resourceCore <- maybe (conversionError "do using acquire is not an application of its checked monad carrier") pure (monadicCoreResult acquireType)
        resourceType <- go env Nothing resourceCore
        (pattern'', locals) <- prepareDoPattern env QW resourceCore resourceType pattern'
        acquire' <- go env (Just acquireType) acquire
        release' <- goInferred env "do using release action" release
        let encoded =
              KTGeneric "impl.kappa.core.do.using"
                [("pattern", KVPattern pattern''), ("acquire", KVTerm acquire'), ("release", KVTerm release')]
        rest' <- goDoItems actionCore resultCore (reverse locals ++ env) rest
        pure (encoded : rest')
      _ -> do
        encoded <- goDoItem actionCore resultCore env item
        (encoded :) <$> goDoItems actionCore resultCore env rest
    goDoItem actionCore resultCore env = \case
      KExpr value -> typedItem "expr" [("value", KVTerm <$> goInferred env "do expression action" value)]
      KReturn value -> typedItem "return" [("value", KVTerm <$> go env (Just resultCore) value)]
      KBreak label -> pure (simpleControl "break" label)
      KContinue label -> pure (simpleControl "continue" label)
      KAssign ref monadic rhs action _ ->
        typedItem
          "assign"
          [ ("ref", KVTerm <$> goInferred env "do assignment reference" ref)
          , ("monadic", pure (KVInteger (if monadic then 1 else 0)))
          , ("rhs", KVTerm <$> goInferred env "do assignment value" rhs)
          , ("action", KVTerm <$> goInferred env "do assignment action" action)
          ]
      KWhile label condition body elseItems -> do
        let (conditionKind, conditionTerm) = case condition of
              KCondPure term -> ("pure", term)
              KCondAction term -> ("action", term)
        condition' <- case condition of
          KCondPure _ -> goInferred env "do while condition" conditionTerm
          KCondAction _ -> do
            conditionType <-
              maybe (conversionError "do while action carrier has no replaceable result argument") pure
                (replaceMonadicCoreResult actionCore (CGlobal prelBool []))
            go env (Just conditionType) conditionTerm
        body' <- goDoItems actionCore resultCore env body
        else' <- traverse (goDoItems actionCore resultCore env) elseItems
        pure
          ( KTGeneric "impl.kappa.core.do.while"
              [ ("label", optionalText label)
              , ("condition-kind", KVText conditionKind)
              , ("condition", KVTerm condition')
              , ("body", itemValues body')
              , ("else", optionalItems else')
              ]
          )
      KFor label pattern' source body elseItems -> do
        sourceType <- maybe (conversionError "do for source type is unavailable") pure (inferCoreType conversionContext env source)
        elementCore <-
          maybe
            (conversionError ("do for source is not the checked List generator form: " <> T.pack (show sourceType)))
            pure
            (listCoreElement sourceType)
        elementType <- go env Nothing elementCore
        (pattern'', locals) <- prepareDoPattern env QW elementCore elementType pattern'
        source' <- go env (Just sourceType) source
        body' <- goDoItems actionCore resultCore (reverse locals ++ env) body
        else' <- traverse (goDoItems actionCore resultCore env) elseItems
        pure
          ( KTGeneric "impl.kappa.core.do.for"
              [ ("label", optionalText label)
              , ("pattern", KVPattern pattern'')
              , ("source", KVTerm source')
              , ("body", itemValues body')
              , ("else", optionalItems else')
              ]
          )
      KIf alternatives elseItems -> do
        conditions <- mapM (goInferred env "do if condition" . fst) alternatives
        bodies <- mapM (goDoItems actionCore resultCore env . snd) alternatives
        else' <- traverse (goDoItems actionCore resultCore env) elseItems
        pure
          ( KTGeneric "impl.kappa.core.do.if"
              [ ("conditions", KVList (map KVTerm conditions))
              , ("bodies", KVList (map itemValues bodies))
              , ("else", optionalItems else')
              ]
          )
      KDefer label action -> do
        action' <- goInferred env "do deferred action" action
        pure
          ( KTGeneric
              "impl.kappa.core.do.defer"
              [ ("label", maybe (KVList []) (KVList . pure . KVText) label)
              , ("action", KVTerm action')
              ]
          )
      KSubDo label nested -> do
        nested' <- goDoItems actionCore resultCore env nested
        pure
          ( KTGeneric
              "impl.kappa.core.do.subdo"
              [ ("label", maybe (KVList []) (KVList . pure . KVText) label)
              , ("items", KVList (map KVTerm nested'))
              ]
          )
      item -> conversionError ("do-kernel item has no portable KCoreText schema: " <> T.pack (show item))
      where
        typedItem tag fields = do
          fields' <- mapM (\(name, action) -> (name,) <$> action) fields
          pure (KTGeneric ("impl.kappa.core.do." <> tag) fields')
        simpleControl tag label =
          KTGeneric
            ("impl.kappa.core.do." <> tag)
            [("label", optionalText label)]
        optionalText = maybe (KVList []) (KVList . pure . KVText)
        itemValues = KVList . map KVTerm
        optionalItems = maybe (KVList []) (KVList . pure . itemValues)
    goInferred env label value = do
      inferred <-
        maybe (conversionError (label <> " type is unavailable at the typed checkpoint")) pure
          (inferCoreType conversionContext env value)
      go env (Just inferred) value
    quoteCaptureValue env capture =
      let index = length env - 1 - qcLevel capture
       in case drop index env of
            local : _
              | index >= 0 ->
                  pure
                    ( KVList
                        [ KVText (qcHyg capture)
                        , KVText (qcOrig capture)
                        , KVLocal
                            (renderedLocalRef local)
                            (map KLUniverse (renderedLocalUniverses local))
                        ]
                    )
            _ -> conversionError "syntax quote capture is outside the serialized local scope"
    prepareDoPattern env quantity coreType textType pattern' = do
      (prepared, locals) <- preparePortablePattern env coreType textType pattern'
      pure (prepared {kpSlot = (kpSlot prepared) {kbQuantity = quantityToText quantity}}, locals)
    listCoreElement type' = case collectApplication (stripClassifierWrappers type') of
      (CGlobal global _, [(_, element)]) | global == gPrel "List" -> Just element
      _ -> Nothing
    convertConstructorArguments env constructor = goArguments
      where
        goArguments remainingParameters signature []
          | remainingParameters > 0 =
              conversionError ("constructor " <> gKey constructor <> " occurrence is missing data-parameter arguments from its checked interface")
          | otherwise =
          case stripClassifierWrappers signature of
            CPiEvidenceM {} ->
              conversionError ("constructor " <> gKey constructor <> " occurrence is missing arguments from its checked interface")
            _ -> pure []
        goArguments remainingParameters signature (argument : rest) =
          case stripClassifierWrappers signature of
            CPiEvidenceM _ _ icit _ _ _ _ _ domain codomain -> do
              unless (caIcit argument == icit) $
                conversionError ("constructor " <> gKey constructor <> " argument icity disagrees with its checked interface")
              let residual = substTopTermAt (length env) (caTerm argument) codomain
              if remainingParameters > 0
                then goArguments (remainingParameters - 1) residual rest
                else do
                  argument' <- KArgument (icitToText icit) <$> go env (Just domain) (caTerm argument)
                  rest' <- goArguments 0 residual rest
                  pure (argument' : rest')
            _ ->
              conversionError
                ( "constructor " <> gKey constructor <> " occurrence has more arguments than its checked interface"
                )
    -- General applications need the same dependent telescope walk as
    -- constructors. In particular, a generated `subst` motive is a lambda
    -- whose binder type is available only from the selected argument domain;
    -- serializing every argument with no expected type loses that checked
    -- formation fact. Each accepted argument is substituted through the
    -- remaining telescope before the next argument is rendered.
    convertApplicationArguments env = goArguments
      where
        goArguments _ [] = pure []
        goArguments signature ((icit, argument) : rest) =
          case stripClassifierWrappers signature of
            CPiEvidenceM _ _ expectedIcit _ _ _ _ _ domain codomain
              | icit == expectedIcit -> do
                  argument' <-
                    KArgument (icitToText icit)
                      <$> go env (Just domain) argument
                  rest' <-
                    goArguments
                      (substTopTermAt (length env) argument codomain)
                      rest
                  pure (argument' : rest')
              | otherwise ->
                  conversionError
                    "application argument icity disagrees with its checked telescope"
            _ ->
              conversionError
                "application occurrence has more arguments than its checked telescope"
    constructorParameterCount info = do
      evalContext <-
        maybe
          (conversionError "constructor parameter recovery requires the finalized evaluation context")
          pure
          (cccEvalContext conversionContext)
      maybe
        (conversionError ("constructor family interface is unavailable for " <> gKey (kcciData info)))
        pure
        (familyCoreParameterCount evalContext (cccGlobals conversionContext) (kcciData info))
    familyArgumentIcit env family levels = goIcit familyType
      where
        familyType = do
          evalContext <- cccEvalContext conversionContext
          definition <- Map.lookup family (cccGlobals conversionContext)
          pure (specializeCoreUniverses levels (globalCoreType evalContext definition))
        goIcit Nothing [] = pure []
        goIcit Nothing _ = conversionError ("schema lift cannot recover the checked family telescope for " <> gKey family)
        goIcit (Just _) [] = pure []
        goIcit (Just signature) (argument : rest) = case stripClassifierWrappers signature of
          CPiM _ icit _ _ _ _ codomain ->
            (icit :) <$> goIcit (Just (substTopTermAt (length env) argument codomain)) rest
          _ -> conversionError ("schema lift ordinary arguments over-saturate " <> gKey family)
    canonicalBoundType env = \case
      Just (lower, upper) -> \_ -> do
        lower' <- convertLevel env lower
        upper' <- convertLevel env upper
        pure
          ( KTApply
              (KTGlobal levelLeStableRef [])
              [ KArgument KExplicit (levelAsTerm lower')
              , KArgument KExplicit (levelAsTerm upper')
              ]
          )
      Nothing -> pure
    renderLiftEvidence env lower upper evidence = do
      let key = liftCertificateKey lower upper evidence
          closedKey = LiftCertificateKey lower upper []
          localAuthorities =
            [ (renderedLocalRef local, assumption)
            | local <- env
            , Just assumption <- [renderedLocalAssumption local]
            ]
          authorizes (assumedLower, assumedUpper) =
            proveLevelLeq
              (insertAssumption assumedLower assumedUpper emptyAssumptions)
              lower
              upper
              == Proved
          localProof = fst <$> find (authorizes . snd) localAuthorities
      case localProof of
        Just ref -> pure (KELocal ref)
        Nothing -> case
            Map.lookup key certificates
              <|> if proveLevelLeq emptyAssumptions lower upper == Proved
                    then Map.lookup closedKey certificates
                    else Nothing of
          Just (LiftCertificateUse ref levels) ->
            KECertificate ref <$> mapM (convertLevel env) levels
          Nothing ->
            conversionError
              ( "cumulative lift " <> renderLevel lower <> " <= " <> renderLevel upper
                  <> " has no scoped proof or verified certificate"
                  <> "; scoped assumptions: "
                  <> T.intercalate ", "
                    [ renderLevel assumedLower <> " <= " <> renderLevel assumedUpper
                    | RenderedLocal {renderedLocalAssumption = Just (assumedLower, assumedUpper)} <- env
                    ]
              )
    convertLevel env level =
      either (lift . Left) pure (levelToTextWithEnv (renderedLocalRefs env) level)
    typedGeneric env expectedHere tag fields = do
      expectedCore <- maybe (conversionError (tag <> " emission requires its checked result type")) pure expectedHere
      resultType <- go env Nothing expectedCore
      fields' <- mapM (\(name, action) -> (name,) <$> action) fields
      pure (KTGeneric tag (("result-type", KVTerm resultType) : fields'))
    goRecordFields envHere = goFields Map.empty Map.empty 0 envHere
      where
        outerDepth = length envHere
        goFields _ _ _ _ [] = pure []
        goFields fieldLocals fieldLevels fieldCount fieldsEnv (RecordField name mode formation quantity assumption ty : rest) = do
          let depth = length fieldsEnv
              scopedType =
                scopeRecordFields outerDepth fieldCount fieldLocals fieldLevels ty
          ty0 <- go fieldsEnv Nothing scopedType
          let scopedAssumption = scopeRecordLevelAssumption fieldLevels assumption
          ty' <- canonicalBoundType fieldsEnv scopedAssumption ty0
          ref <- freshLocal name
          let local = RenderedLocal ref scopedAssumption (Just scopedType) []
              nextLocals = Map.insert name depth fieldLocals
              nextLevels =
                if coreTypeIsTypeLevel scopedType
                  then Map.insert name depth fieldLevels
                  else fieldLevels
          rest' <- goFields nextLocals nextLevels (fieldCount + 1) (local : fieldsEnv) rest
          pure ((stableFieldRef name, KBinder mode formation (quantityToText quantity) KExplicit KValue BinderSourceWritten ref ty') : rest')
    goRecordValues envHere = goValues []
      where
        goValues _ [] remaining
          | null remaining = pure []
          | otherwise =
              conversionError
                "record value contains fields absent from its checked structural interface"
        goValues prior (field : rest) remaining = do
          value <-
            maybe
              ( conversionError
                  ( "record value is missing checked field "
                      <> rfName field
                  )
              )
              pure
              (lookup (rfName field) remaining)
          let remaining' =
                filter ((/= rfName field) . fst) remaining
          converted <-
            withScopedGlobal
              prelThis
              (KTRecordValue prior)
              (go envHere (Just (rfType field)) value)
          let convertedField =
                (kcoreReadableName (rfName field), converted)
          later <-
            goValues
              (prior ++ [convertedField])
              rest
              remaining'
          pure (convertedField : later)
    withScopedGlobal global replacement action = do
      previous <- gets (Map.lookup global . ccsGlobalTerms)
      modify'
        (\state ->
           state
             { ccsGlobalTerms =
                 Map.insert global replacement (ccsGlobalTerms state)
             })
      result <- action
      modify'
        (\state ->
           state
             { ccsGlobalTerms =
                 case previous of
                   Just prior -> Map.insert global prior (ccsGlobalTerms state)
                   Nothing -> Map.delete global (ccsGlobalTerms state)
             })
      pure result
    freshLocal name = do
      state <- get
      let ident = ccsNextLocal state
      put state {ccsNextLocal = ident + 1}
      pure (LocalRef (if T.null name then "_" else name) ident)
    localUniversesFor ref count =
      pure
        [ UniverseRef "v" (initialUniverse + pair (lrId ref) position)
        | position <- [0 .. count - 1]
        ]
    pair left right =
      let diagonal = left + right
       in diagonal * (diagonal + 1) `div` 2 + right
    localUniverseScope universeRefs =
      let count = length universeRefs
          scopeLevel = \case
            LParam parameter
              | parameter < count ->
                  LParam (urId (universeRefs !! parameter))
              | otherwise -> LParam (parameter - count)
            LSucc level -> LSucc (scopeLevel level)
            LAdd left right -> LAdd (scopeLevel left) (scopeLevel right)
            LMax left right -> LMax (scopeLevel left) (scopeLevel right)
            level -> level
       in zonkTermWith (\_ _ -> Nothing) scopeLevel 0
    stripClassifierWrappers = \case
      CUniverseLift _ _ _ inner -> stripClassifierWrappers inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> stripClassifierWrappers inner
      other -> other
    collectApplication = goApplication []
      where
        goApplication arguments (CApp ic fun argument) = goApplication ((ic, argument) : arguments) fun
        goApplication arguments headTerm = (headTerm, arguments)
    betaReduceApplication depth = goBeta False
      where
        goBeta changed (CLamM _ binderIcit _ _ body) ((argumentIcit, argument) : rest)
          | binderIcit == argumentIcit = goBeta True (substTopTermAt depth argument body) rest
        goBeta True headTerm rest = Just (foldl (\function (ic, argument) -> CApp ic function argument) headTerm rest)
        goBeta False _ _ = Nothing

data RenderedLocal = RenderedLocal
  { renderedLocalRef :: !LocalRef
  , renderedLocalAssumption :: !(Maybe (Level, Level))
  , renderedLocalCoreType :: !(Maybe Term)
  , renderedLocalUniverses :: ![UniverseRef]
  }

data CoreConversionState = CoreConversionState
  { ccsNextLocal :: !Int
  , ccsGlobalTerms :: !(Map GName KTerm)
  }

type CoreConversionM = StateT CoreConversionState (Either KCoreTextError)

data CoreConversionContext = CoreConversionContext
  { cccEvalContext :: !(Maybe EvalCtx)
  , cccGlobals :: !(Map GName GlobalDef)
  , cccConstructors :: !(Map GName KCoreConstructorInfo)
  }

coreRecordFieldsFor :: CoreConversionContext -> [RenderedLocal] -> Term -> Maybe [RecordField Term]
coreRecordFieldsFor context env typeTerm =
  case stripTypeWrappers typeTerm of
    CRecordTQ fields -> Just fields
    normalized -> do
      evalContext <- cccEvalContext context
      let depth = length env
          rigidEnvironment = [VRigid (depth - 1 - index) [] | index <- [0 .. depth - 1]]
          typeValue = eval evalContext rigidEnvironment normalized
      fields <- exposeRecordInterface evalContext typeValue
      pure
        [ field {rfType = quote evalContext depth (rfType field)}
        | field <- fields
        ]
  where
    stripTypeWrappers = \case
      CUniverseLift _ _ _ inner -> stripTypeWrappers inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> stripTypeWrappers inner
      other -> other
    exposeRecordInterface evalContext value =
      case force evalContext value of
        VRecordTQ fields -> Just fields
        VGlobI global universes spine -> do
          definition <- Map.lookup global (cccGlobals context)
          body <- gdValue definition
          let specialized = specializeCoreUniverses universes (quote evalContext 0 body)
              interface = evalApp evalContext (eval evalContext [] specialized) spine
          case force evalContext interface of
            VRecordTQ fields -> Just fields
            _ -> Nothing
        _ -> Nothing

specializeCoreUniverses :: [Level] -> Term -> Term
specializeCoreUniverses levels =
  zonkTermWith (\_ _ -> Nothing) (substituteLevelParams levels) 0

splitCorePiTelescope :: Term -> ([Term], Term)
splitCorePiTelescope = go []
  where
    go domains (CPiM _ _ _ _ _ domain codomain) = go (domains ++ [domain]) codomain
    go domains result = (domains, result)


inferCoreType :: CoreConversionContext -> [RenderedLocal] -> Term -> Maybe Term
inferCoreType context env = go
  where
    go = \case
      CVar index -> do
        local <- case drop index env of local : _ -> Just local; [] -> Nothing
        localType <- renderedLocalCoreType local
        pure (shiftTerm (index + 1) 0 localType)
      CLocal index levels -> do
        local <- case drop index env of local : _ -> Just local; [] -> Nothing
        localType <- renderedLocalCoreType local
        let specialized =
              zonkTermWith
                (\_ _ -> Nothing)
                (instantiateLocalLevelParams (length levels) levels)
                0
                localType
        pure (shiftTerm (index + 1) 0 specialized)
      CGlobal global levels -> do
        evalContext <- cccEvalContext context
        definition <- Map.lookup global (cccGlobals context)
        let raw = globalCoreType evalContext definition
        pure (specializeCoreUniverses levels raw)
      application@CApp {} ->
        case betaReduce application of
          Just reduced -> go reduced
          Nothing -> case application of
            CApp _ function argument -> do
              functionType <- strip <$> go function
              case functionType of
                CPiM _ _ _ _ _ _ codomain -> pure (substTopTermAt (length env) argument codomain)
                _ -> Nothing
            _ -> Nothing
      CUniverseLift _ _ _ inner -> go inner
      CSchemaLift family _ target _ _ _ _sourceArguments targetArguments _ -> do
        evalContext <- cccEvalContext context
        definition <- Map.lookup family (cccGlobals context)
        let familyType = specializeCoreUniverses target (globalCoreType evalContext definition)
        fst <$> applyFamilyArguments (CGlobal family target) familyType targetArguments
      CProjM _ record field -> do
        recordType <- go record
        recordField <- find ((== field) . rfName) =<< coreRecordFieldsFor context env recordType
        pure (substGlobal prelThis record (rfType recordField))
      CProjAtM _ record field _ -> do
        recordType <- go record
        recordField <- find ((== field) . rfName) =<< coreRecordFieldsFor context env recordType
        pure (substGlobal prelThis record (rfType recordField))
      CLit literal -> pure $ CGlobal (literalCoreType literal) []
      CCtorI _ _ (Just constructorType) arguments ->
        applyArguments constructorType (map caTerm arguments)
      CIf _ thenBranch _ -> go thenBranch
      CThunkE _ suspensionType -> suspensionType
      CLazyE _ suspensionType -> suspensionType
      CForceE _ resultType -> resultType
      CLetM _ _ _ ty _ body -> inferCoreType context (RenderedLocal (LocalRef "_" (-1)) Nothing (Just ty) [] : env) body
      CLetRecM _ _ _ ty _ body -> inferCoreType context (RenderedLocal (LocalRef "_" (-1)) Nothing (Just ty) [] : env) body
      CLetPolyM _ _ _ _ ty _ body -> inferCoreType context (RenderedLocal (LocalRef "_" (-1)) Nothing (Just ty) [] : env) body
      CLetRecPolyM _ _ _ _ ty _ body -> inferCoreType context (RenderedLocal (LocalRef "_" (-1)) Nothing (Just ty) [] : env) body
      CLetRecGroupM _ definitions body ->
        let locals =
              [RenderedLocal (LocalRef (clrdName definition) (-1 - index)) Nothing (Just (clrdType definition)) []
              | (index, definition) <- zip [0 ..] definitions]
         in inferCoreType context (reverse locals ++ env) body
      _ -> Nothing
    strip = \case
      CUniverseLift _ _ _ inner -> strip inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> strip inner
      other -> other
    applyFamilyArguments term ty [] = Just (term, strip ty)
    applyFamilyArguments term ty (argument : rest) = case strip ty of
      CPiM _ icit _ _ _ _ codomain ->
        applyFamilyArguments
          (CApp icit term argument)
          (substTopTermAt (length env) argument codomain)
          rest
      _ -> Nothing
    applyArguments ty [] = Just (strip ty)
    applyArguments ty (argument : rest) = case strip ty of
      CPiM _ _ _ _ _ _ codomain -> applyArguments (substTopTermAt (length env) argument codomain) rest
      _ -> Nothing
    betaReduce application =
      let (headTerm, arguments) = collect [] application
       in apply False headTerm arguments
      where
        collect arguments (CApp icit function argument) = collect ((icit, argument) : arguments) function
        collect arguments headTerm = (headTerm, arguments)
        apply changed (CLamM _ binderIcit _ _ body) ((argumentIcit, argument) : rest)
          | binderIcit == argumentIcit = apply True (substTopTermAt (length env) argument body) rest
        apply True headTerm rest = Just (foldl (\function (icit, argument) -> CApp icit function argument) headTerm rest)
        apply False _ _ = Nothing
    literalCoreType = \case
      LitInt _ -> prelInt
      LitDouble _ -> prelDouble
      LitStr _ -> prelString
      LitScalar _ -> prelUnicodeScalar
      LitByte _ -> prelByte
      LitBytes _ -> gPrel "Bytes"
      LitGrapheme _ -> prelGrapheme

monadicCoreResult :: Term -> Maybe Term
monadicCoreResult term =
  case collect [] (strip term) of
    (_, []) -> Nothing
    (_, arguments) -> Just (snd (last arguments))
  where
    strip (CUniverseLift _ _ _ inner) = strip inner
    strip (CSchemaLift _ _ _ _ _ _ _ _ inner) = strip inner
    strip other = other
    collect arguments (CApp ic function argument) = collect ((ic, argument) : arguments) function
    collect arguments headTerm = (headTerm, arguments)

replaceMonadicCoreResult :: Term -> Term -> Maybe Term
replaceMonadicCoreResult term result =
  case collect [] (strip term) of
    (_, []) -> Nothing
    (headTerm, arguments) -> case reverse arguments of
      (resultIcit, _) : reversedPrefix ->
        Just
          ( foldl
              (\function (icit, argument) -> CApp icit function argument)
              headTerm
              (reverse reversedPrefix ++ [(resultIcit, result)])
          )
      [] -> Nothing
  where
    strip (CUniverseLift _ _ _ inner) = strip inner
    strip (CSchemaLift _ _ _ _ _ _ _ _ inner) = strip inner
    strip other = other
    collect arguments (CApp ic function argument) = collect ((ic, argument) : arguments) function
    collect arguments headTerm = (headTerm, arguments)

substituteKTermParameters :: [KBinder] -> Map Int KTerm -> KTerm -> KTerm
substituteKTermParameters parameters substitution term =
  foldl substitute renamedParameters freshSubstitutions
  where
    -- Parameter interfaces and the term being specialized may originate in
    -- independently canonicalized KCore scopes. Their numeric local IDs are
    -- therefore not globally unique. Move every binder in the target into a
    -- range disjoint from both the target and replacement terms before
    -- substituting, otherwise a family argument can be captured by a payload
    -- lambda or dependent record field with the same presentation ID.
    replacementIds =
      Set.unions
        [kTermLocalIds replacement | replacement <- Map.elems substitution]
    freshened = freshenKTermBindersAgainst replacementIds term
    usedIds =
      replacementIds
        `Set.union` kTermLocalIds freshened
        `Set.union` Set.fromList (map (lrId . kbRef) parameters)
    firstFresh = maybe 0 (+ 1) (Set.lookupMax usedIds)
    freshParameterRefs =
      Map.fromList
        [ ( lrId (kbRef binder)
          , LocalRef "__parameter" identity
          )
        | (binder, identity) <-
            zip
              [ binder
              | binder <- parameters
              , Map.member (lrId (kbRef binder)) substitution
              ]
              [firstFresh ..]
        ]
    renamedParameters =
      foldl
        (\body binder ->
           case Map.lookup (lrId (kbRef binder)) freshParameterRefs of
             Just fresh -> renameLocal (kbRef binder) fresh body
             Nothing -> body)
        freshened
        parameters
    freshSubstitutions =
      [ (fresh, replacement)
      | (identity, replacement) <- Map.toList substitution
      , Just fresh <- [Map.lookup identity freshParameterRefs]
      ]
    substitute body (ref, replacement) =
      substituteLocal ref replacement body

-- | Alpha-freshen every binder in a term away from the supplied free-local
-- identities and from every identity already present in the term. KCore
-- declarations are canonicalized independently, so a global telescope binder
-- may have the same numeric presentation id as a local at its call site.
-- Freshening before substitution is therefore required for capture avoidance:
-- substituting that local through an earlier Pi must not let a later Pi capture
-- it. 'canonicalTerm' already implements the complete scope-aware alpha walk
-- for Pi/Sigma/lambda, blocks, recursive groups, records, and case patterns.
freshenKTermBindersAgainst :: Set Int -> KTerm -> KTerm
freshenKTermBindersAgainst avoided term =
  evalState
    (canonicalTerm Map.empty term)
    (CanonState freshStart Map.empty)
  where
    allIds = avoided `Set.union` kTermLocalIds term
    freshStart = maybe 0 (+ 1) (Set.lookupMax allIds)

-- | Put a dependent function telescope in a namespace disjoint from all of
-- its caller-owned arguments before applying any of them. Sequential
-- substitution is then simultaneous in the relevant sense: no later
-- declaration binder can capture or rewrite a local introduced by an earlier
-- argument merely because independently canonicalized scopes reused an id.
freshenKPiTelescopeForArguments :: [KArgument] -> KTerm -> KTerm
freshenKPiTelescopeForArguments arguments =
  freshenKTermBindersAgainst
    ( Set.unions
        [ kTermLocalIds argument
        | KArgument _ argument <- arguments
        ]
    )

renderedLocalRefs :: [RenderedLocal] -> [LocalRef]
renderedLocalRefs = map renderedLocalRef

renderedLocalIds :: [RenderedLocal] -> Set Int
renderedLocalIds =
  Set.fromList . map (lrId . renderedLocalRef)

levelToText :: Level -> Either KCoreTextError KLevel
levelToText = levelToTextWithEnv []

levelToTextWithEnv :: [LocalRef] -> Level -> Either KCoreTextError KLevel
levelToTextWithEnv env = \case
  LZero -> pure (KLFinite 0)
  LFinite n -> pure (KLFinite n)
  LOmega -> pure (KLGlobal (stableRefForGlobal prelTypeLevelOmega))
  LSucc level -> KLSucc <$> levelToTextWithEnv env level
  LAdd lhs rhs -> KLAdd <$> levelToTextWithEnv env lhs <*> levelToTextWithEnv env rhs
  LMax lhs rhs -> KLMax <$> levelToTextWithEnv env lhs <*> levelToTextWithEnv env rhs
  LVar ident ->
    case localAtLevel env ident of
      Just ref -> pure (KLTerm (KTLocal ref []))
      Nothing -> Left (invalid ("level local " <> tshow ident <> " is out of scope during KCoreText emission"))
  LParam ident -> pure (KLUniverse (UniverseRef "u" ident))
  LField ident field -> Left (invalid ("record-field level " <> field <> "#" <> tshow ident <> " escaped its telescope"))
  LProjection root path ->
    let index = length env - root - 1
     in case drop index env of
          ref : _ | index >= 0 ->
            pure (KLTerm (foldl (\term field -> KTProject (stableFieldRef field) term) (KTLocal ref []) path))
          _ -> Left (invalid ("level projection root " <> tshow root <> " is out of scope during KCoreText emission"))
  LNeutral atom -> case atom of
    NeutralLevelSymbol identity _ ->
      Left (invalid ("solver-only neutral level symbol " <> identity <> " reached KCoreText emission"))
    NeutralLevelTermAtom digest term -> do
      let rebuiltDigest = neutralLevelTermDigest term
      unless (rebuiltDigest == digest) $
        Left (invalid "neutral level term digest does not match its structural artifact")
      KLTerm <$> neutralLevelTermToText env term
  LMeta ident -> Left (invalid ("unsolved level metavariable " <> tshow ident <> " reached KCoreText emission"))

neutralLevelTermToText :: [LocalRef] -> NeutralLevelTerm -> Either KCoreTextError KTerm
neutralLevelTermToText env = go
  where
    go = \case
      NLTLocal level -> KTLocal <$> local level <*> pure []
      NLTLocalDeclaration level levels ->
        KTLocal <$> local level <*> mapM (levelToTextWithEnv env) levels
      NLTGlobal owner name levels ->
        KTGlobal (stableRefForGlobal (GName (ModuleName owner) name))
          <$> mapM (levelToTextWithEnv env) levels
      NLTConstruct owner name levels arguments ->
        KTConstruct (stableRefForConstructor (GName (ModuleName owner) name))
          <$> mapM (levelToTextWithEnv env) levels
          <*> mapM (\(explicit, argument) -> KArgument (if explicit then KExplicit else KImplicit) <$> go argument) arguments
      NLTApply explicit function argument ->
        KTApply <$> go function <*> ((: []) . KArgument (if explicit then KExplicit else KImplicit) <$> go argument)
      NLTProject field receiver -> KTProject (stableFieldRef field) <$> go receiver
      NLTLevel level -> levelAsTerm <$> levelToTextWithEnv env level
      NLTLiteral literal -> pure (KTLiteral (literalFromArtifact literal))
      NLTRecord fields -> KTRecordValue <$> mapM (\(field, value) -> (field,) <$> go value) fields
      NLTIf condition thenBranch elseBranch -> KTIf <$> go condition <*> go thenBranch <*> go elseBranch
      NLTUnsupported reason ->
        Left (invalid ("neutral level term is not serializable after substitution: " <> reason))

    local level =
      maybe
        (Left (invalid ("neutral level local " <> tshow level <> " is out of scope during KCoreText emission")))
        pure
        (localAtLevel env level)

    literalFromArtifact = \case
      NLLInt value -> LitInt value
      NLLDouble value -> LitDouble value
      NLLString value -> LitStr value
      NLLScalar value -> LitScalar value
      NLLByte value -> LitByte value
      NLLBytes value -> LitBytes (BS.pack value)
      NLLGrapheme value -> LitGrapheme value

conversionError :: Text -> CoreConversionM a
conversionError = lift . Left . invalid

quantityToText :: Q -> KQuantity
quantityToText = \case Q0 -> KQ0; Q1 -> KQ1; QW -> KQOmega; QLe1 -> KQAffine; QGe1 -> KQRelevant

icitToText :: Icit -> KExplicitness
icitToText = \case Expl -> KExplicit; Impl -> KImplicit

stableRefForGlobal :: GName -> StableRef
stableRefForGlobal g =
  StableRef
    (kcoreReadableName (gKey g))
    (canonicalIdentityHex "KCoreGlobal" (gKey g))

-- Static family/type and constructor facets may deliberately share a source
-- spelling (for example @data R = R@), but they are distinct semantic
-- declarations. Keep the readable owner name while tagging both parts of the
-- stable identity; equality is defined by 'srId', not by display metadata.
stableRefForConstructor :: GName -> StableRef
stableRefForConstructor g =
  StableRef
    (kcoreReadableName (gKey g <> ".constructor"))
    (canonicalIdentityHex "KCoreConstructor" (gKey g))

stableRefForText :: Text -> StableRef
stableRefForText name =
  StableRef (kcoreReadableName name) (canonicalIdentityHex "KCoreText" name)

stableFieldRef :: Text -> StableRef
stableFieldRef name =
  let canonical = kcoreReadableName name
   in StableRef canonical (canonicalIdentityHex "KCoreField" canonical)

stableFieldRefFromReadable :: Text -> StableRef
stableFieldRefFromReadable name =
  StableRef name (canonicalIdentityHex "KCoreField" name)

stableLevelCertificateRef :: Text -> StableRef
stableLevelCertificateRef name =
  StableRef
    ("certificate." <> kcoreReadableName certificateName)
    (canonicalIdentityHex "KCoreLevelCertificate" name)
  where
    certificateName = fromMaybe name (T.stripPrefix "certificate." name)

stableSchemaCertificateRef :: Text -> StableRef
stableSchemaCertificateRef name =
  StableRef
    ("schema:" <> kcoreReadableName certificateName)
    (canonicalIdentityHex "KCoreSchemaCertificate" name)
  where
    certificateName = fromMaybe name (T.stripPrefix "schema:" name)

-- KCoreText names are metadata, but they must still inhabit the identifier
-- grammar. Escape every underscore and non-alphanumeric code point so the
-- mapping is injective; dots remain qualified-name separators. Stable IDs are
-- computed from semantic identities independently of this readable spelling.
kcoreReadableName :: Text -> Text
kcoreReadableName = T.intercalate "." . map encodeComponent . T.splitOn "."
  where
    encodeComponent component =
      let encoded = T.concatMap encodeChar component
       in if T.null encoded
            then "_xempty_"
            else case T.uncons encoded of
              Just (first, _) | isDigit first -> "_xstart_" <> encoded
              _ -> encoded
    encodeChar char
      | isAlphaNum char = T.singleton char
      | otherwise = "_x" <> T.pack (showHex (ord char) "") <> "_"

localAtLevel :: [LocalRef] -> Int -> Maybe LocalRef
localAtLevel env level
  | index < 0 = Nothing
  | otherwise = case drop index env of
      ref : _ -> Just ref
      [] -> Nothing
  where
    index = length env - level - 1

stableHex :: Text -> Text
stableHex = sha256Hex . ("KAPPA:v1:KCoreDigest:" <>)
