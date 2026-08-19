{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- | Source-free checked-module state used by the bundled prelude image.
--
-- The artifact contains only persistent semantic interface/implementation
-- facts. Solver metas, diagnostics, source-occurrence tables, caches, and the
-- current module scope are intentionally absent and are reset by the loader.
module Kappa.Check.Artifact
  ( CheckedPreludeArtifact (..)
  , checkedPreludeArtifactVersion
  , snapshotCheckedPrelude
  , restoreCheckedPrelude
  ) where

import Data.Data (Data)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, maybeToList)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Check
import Kappa.Check.Support (setCheckInstances)
import Kappa.Core
import Kappa.CoreOps (levelMetasOfTerm, metaIdsOf, termScopedAt)
import Kappa.Eval
import Kappa.NominalVariance (NominalCumulativitySummary)
import Kappa.Observation (ObservationMode)
import Kappa.Prelude (builtinState)
import Kappa.Source (ModuleName)

checkedPreludeArtifactVersion :: Integer
checkedPreludeArtifactVersion = 8

data CheckedGlobalValueArtifact
  = CheckedNoValue
  | CheckedValueFromBody
  | CheckedClosedValue !Term
  deriving stock (Data)

data CheckedGlobalArtifact = CheckedGlobalArtifact
  { cgaUniverses :: !DeclarationUniverseTelescope
  , cgaObservationMode :: !ObservationMode
  , cgaNominalSummary :: !(Maybe NominalCumulativitySummary)
  , cgaQuotedType :: !Term
  , cgaCoreType :: !(Maybe Term)
  , cgaBody :: !(Maybe Term)
  , cgaRecordInterface :: !(Maybe Term)
  , cgaValue :: !CheckedGlobalValueArtifact
  , cgaReducible :: !Bool
  }
  deriving stock (Data)

data CheckedDataArtifact = CheckedDataArtifact
  { cdaConstructors :: ![GName]
  , cdaParameterCount :: !Int
  , cdaLevel :: !Level
  }
  deriving stock (Data)

data CheckedConstructorArtifact = CheckedConstructorArtifact
  { ccaData :: !GName
  , ccaUniverses :: !DeclarationUniverseTelescope
  , ccaType :: !Term
  , ccaFieldNames :: ![Maybe Text]
  , ccaHasUncheckedDefaults :: !Bool
  , ccaSourceFields :: ![(Icit, Maybe Text)]
  }
  deriving stock (Data)

data CheckedTraitArtifact = CheckedTraitArtifact
  { ctaParameterCount :: !Int
  , ctaMembers :: ![Text]
  , ctaMemberModes :: !(Map Text ObservationMode)
  , ctaAssociatedStaticMembers :: !(Set Text)
  , ctaMemberQuantities :: !(Map Text Q)
  , ctaDefaults :: !(Map Text GName)
  , ctaSupers :: ![(Text, Term)]
  , ctaDerivedMembers :: !(Set Text)
  , ctaDerivedSupers :: !(Set Text)
  , ctaEvidenceIndependentlyUnique :: !Bool
  }
  deriving stock (Data)

data CheckedInstanceArtifact = CheckedInstanceArtifact
  { ciaTrait :: !GName
  , ciaTraitUniverses :: ![Level]
  , ciaUniverses :: !DeclarationUniverseTelescope
  , ciaTelescopeLength :: !Int
  , ciaPremises :: ![Term]
  , ciaHead :: ![Term]
  , ciaDictionary :: !GName
  }
  deriving stock (Data)

data CheckedProjectionArtifact = CheckedProjectionArtifact
  { cpaPlacePositions :: ![Bool]
  , cpaPlaceNames :: ![Text]
  , cpaSelector :: !Bool
  , cpaYields :: ![(Text, [Text])]
  }
  deriving stock (Data)

data CheckedInoutArtifact = CheckedInoutArtifact
  { ciaFormal :: !Text
  , ciaSuccessor :: !Text
  }
  deriving stock (Data)

data CheckedEffectOperationArtifact = CheckedEffectOperationArtifact
  { ceoaName :: !Text
  , ceoaQuantity :: !Q
  , ceoaImplicits :: !Telescope
  , ceoaArguments :: !Telescope
  , ceoaResult :: !Term
  }
  deriving stock (Data)

data CheckedEffectLabelArtifact = CheckedEffectLabelArtifact
  { celaLabel :: !GName
  , celaInterface :: !GName
  , celaParameters :: !Telescope
  , celaFixedArguments :: !(Maybe [Term])
  , celaFixedUniverses :: !(Maybe [Level])
  , celaOperations :: ![CheckedEffectOperationArtifact]
  }
  deriving stock (Data)

data CheckedEffectOperationValueArtifact = CheckedEffectOperationValueArtifact
  { ceovaLabel :: !GName
  , ceovaName :: !Text
  , ceovaQuantity :: !Q
  , ceovaArity :: !Int
  }
  deriving stock (Data)

data CheckedPreludeArtifact = CheckedPreludeArtifact
  { cprVersion :: !Integer
  , cprSourceHash :: !Text
  , cprGlobals :: ![(GName, CheckedGlobalArtifact)]
  , cprDatas :: ![(GName, CheckedDataArtifact)]
  , cprConstructors :: ![(GName, CheckedConstructorArtifact)]
  , cprTraits :: ![(GName, CheckedTraitArtifact)]
  , cprBareTraitMembers :: ![(GName, (GName, Text))]
  , cprTraitMemberOwners :: ![(GName, GName)]
  , cprInstances :: ![CheckedInstanceArtifact]
  , cprInstanceUniverseInterfaces :: ![(GName, [Term])]
  , cprUniverseInterfaceValues :: ![GName]
  , cprFinalizedUniverseInterfaces :: ![GName]
  , cprUniverseInferenceRecords :: ![(Text, UniverseInferenceRecord)]
  , cprModuleExports :: ![(ModuleName, [Text])]
  , cprActivePatterns :: ![(GName, Int)]
  , cprProjections :: ![(GName, CheckedProjectionArtifact)]
  , cprInoutParameters :: ![(GName, [Maybe CheckedInoutArtifact])]
  , cprEffectOperationValues :: ![(GName, CheckedEffectOperationValueArtifact)]
  , cprReceivers :: ![(GName, [Int])]
  , cprOpaqueDatas :: ![GName]
  , cprOpaqueDefinitions :: ![GName]
  , cprRecordOrders :: ![(GName, [Text])]
  , cprReExports :: ![(ModuleName, [(Text, GName)])]
  , cprPositivity :: ![(GName, [Bool])]
  , cprMultiFixOperators :: ![Text]
  , cprFoundationProviders :: ![(GName, Term)]
  , cprImplementationBodies :: ![(GName, Term)]
  , cprLevelOperatorAliases :: ![(GName, Int)]
  , cprModuleEffectLabels :: ![(Text, CheckedEffectLabelArtifact)]
  , cprEffectInterfaces :: ![(GName, CheckedEffectLabelArtifact)]
  , cprMultishotOperations :: ![Text]
  }
  deriving stock (Data)

snapshotCheckedPrelude :: Text -> CheckState -> CheckedPreludeArtifact
snapshotCheckedPrelude sourceHash state =
  CheckedPreludeArtifact
    { cprVersion = checkedPreludeArtifactVersion
    , cprSourceHash = sourceHash
    , cprGlobals = map (fmap snapshotGlobal) (Map.toAscList (csGlobals state))
    , cprDatas = map (fmap snapshotData) (Map.toAscList (csDatas state))
    , cprConstructors = map (fmap snapshotConstructor) (Map.toAscList (csCtors state))
    , cprTraits = map (fmap snapshotTrait) (Map.toAscList (csTraits state))
    , cprBareTraitMembers = Map.toAscList (csBareTraitMembers state)
    , cprTraitMemberOwners = Map.toAscList (csTraitMemberOwners state)
    , cprInstances = map snapshotInstance (csInstances state)
    , cprInstanceUniverseInterfaces = Map.toAscList (csInstanceUniverseInterfaces state)
    , cprUniverseInterfaceValues = Set.toAscList (csUniverseInterfaceValues state)
    , cprFinalizedUniverseInterfaces = Set.toAscList (csFinalizedUniverseInterfaces state)
    , cprUniverseInferenceRecords = Map.toAscList (csUniverseInferenceRecords state)
    , cprModuleExports = Map.toAscList (csModuleExports state)
    , cprActivePatterns = map (fmap snapshotActive) (Map.toAscList (csActive state))
    , cprProjections = map (fmap snapshotProjection) (Map.toAscList (csProjections state))
    , cprInoutParameters = map (fmap (map (fmap snapshotInout))) (Map.toAscList (csInoutParams state))
    , cprEffectOperationValues = map (fmap snapshotEffectOperationValue) (Map.toAscList (csEffectOpValueGlobals state))
    , cprReceivers = Map.toAscList (csReceivers state)
    , cprOpaqueDatas = Map.keys (csOpaqueDatas state)
    , cprOpaqueDefinitions = Map.keys (csOpaqueDefs state)
    , cprRecordOrders = Map.toAscList (csRecordOrders state)
    , cprReExports = map (fmap Map.toAscList) (Map.toAscList (csReExports state))
    , cprPositivity = Map.toAscList (csPositivity state)
    , cprMultiFixOperators = Set.toAscList (csMultiFixOps state)
    , cprFoundationProviders = Map.toAscList (csFoundationProviders state)
    , cprImplementationBodies = Map.toAscList (linkedCoreBodies state)
    , cprLevelOperatorAliases = map (fmap snapshotLevelOperator) (Map.toAscList (csLevelOperatorAliases state))
    , cprModuleEffectLabels = map (fmap snapshotEffectLabel) (Map.toAscList (csModEffLabels state))
    , cprEffectInterfaces = map (fmap snapshotEffectLabel) (Map.toAscList (csEffectInterfaces state))
    , cprMultishotOperations = Set.toAscList (csMultishotOps state)
    }
  where
    context = EvalCtx (Globals (csGlobals state)) (csMetas state) False Map.empty
    snapshotGlobal definition =
      CheckedGlobalArtifact
        { cgaUniverses = gdUniverses definition
        , cgaObservationMode = gdObservationMode definition
        , cgaNominalSummary = gdNominalSummary definition
        , cgaQuotedType = maybe (quote context 0 (gdType definition)) id (gdCoreType definition)
        , cgaCoreType = gdCoreType definition
        , cgaBody = gdCoreBody definition
        , cgaRecordInterface = gdRecordInterface definition
        , cgaValue = snapshotValue definition
        , cgaReducible = gdReducible definition
        }
    snapshotValue definition = case gdValue definition of
      Nothing -> CheckedNoValue
      Just value
        | let term = quote context 0 value
        , finalizedTerm 0 term -> CheckedClosedValue term
        | otherwise -> CheckedValueFromBody
    finalizedTerm depth term =
      termScopedAt depth term
        && null (metaIdsOf term)
        && null (levelMetasOfTerm term)
    snapshotData info = CheckedDataArtifact (diCtors info) (diParamCount info) (diLevel info)
    snapshotConstructor info =
      CheckedConstructorArtifact
        (ciData info)
        (ciUniverses info)
        (ciType info)
        (map fst (ciFields info))
        (any (maybe False (const True) . snd) (ciFields info))
        (ciSourceFields info)
    snapshotTrait info =
      CheckedTraitArtifact
        (tiParamCount info)
        (tiMembers info)
        (tiMemberModes info)
        (tiAssociatedStaticMembers info)
        (tiMemberQs info)
        (tiDefaults info)
        (tiSupers info)
        (tiDerivedMembers info)
        (tiDerivedSupers info)
        (tiEvidenceConstructionMode info == IndependentlyUnique)
    snapshotInstance entry =
      CheckedInstanceArtifact
        (ieTrait entry)
        (ieTraitUniverses entry)
        (ieUniverses entry)
        (ieTeleLen entry)
        (iePremises entry)
        (ieHead entry)
        (ieDict entry)
    snapshotActive info = case apResult info of APOption -> 0; APMatch -> 1; APTotal -> 2
    snapshotProjection info = CheckedProjectionArtifact (pjIsPlace info) (pjPlaceNames info) (pjSelector info) (pjYields info)
    snapshotInout info = CheckedInoutArtifact (iopFormal info) (iopSuccessor info)
    snapshotEffectOperationValue info = CheckedEffectOperationValueArtifact (eoviLabel info) (eoviName info) (eoviQ info) (eoviArity info)
    snapshotLevelOperator = \case
      LevelOperatorZero -> 0
      LevelOperatorOne -> 1
      LevelOperatorSucc -> 2
      LevelOperatorAdd -> 3
      LevelOperatorMax -> 4
      LevelOperatorFromInteger -> 5
      LevelOperatorLt -> 6
      LevelOperatorLe -> 7
    snapshotEffectLabel info =
      CheckedEffectLabelArtifact
        (eliLabel info)
        (eliIface info)
        (eliParams info)
        (fmap (map (quote context 0)) (eliFixedArgs info))
        (eliFixedUniverses info)
        (map snapshotEffectOperation (eliOps info))
    snapshotEffectOperation info =
      CheckedEffectOperationArtifact (eoiName info) (eoiQ info) (eoiImplicits info) (eoiArgs info) (eoiResT info)

restoreCheckedPrelude
  :: Text
  -> CheckedPreludeArtifact
  -> Either Text CheckState
restoreCheckedPrelude expectedSourceHash artifact
  | cprVersion artifact /= checkedPreludeArtifactVersion =
      Left "checked prelude artifact schema version mismatch"
  | cprSourceHash artifact /= expectedSourceHash =
      Left "checked prelude artifact source fingerprint mismatch"
  | any ((`notElem` [0, 1, 2]) . snd) (cprActivePatterns artifact) =
      Left "checked prelude artifact contains an invalid active-pattern result tag"
  | any ((`notElem` [0 .. 7]) . snd) (cprLevelOperatorAliases artifact) =
      Left "checked prelude artifact contains an invalid level-operator tag"
  | any (ccaHasUncheckedDefaults . snd) (cprConstructors artifact) =
      Left "checked prelude artifact contains an unchecked constructor-default source dependency"
  | any hasDuplicateKey keyedSections
      || any hasDuplicateKey moduleKeyedSections
      || any hasDuplicateKey textKeyedSections
      || hasDuplicateKey (map ciaDictionary (cprInstances artifact))
      || any hasDuplicateKey setLikeSections =
      Left "checked prelude artifact contains a duplicate semantic identity"
  | Just global <- valueWithoutBody =
      Left ("checked prelude artifact cannot reconstruct the value of " <> gKey global)
  | Just owner <- firstUnfinalizedTerm =
      Left ("checked prelude artifact contains an open or unresolved Core term at " <> owner)
  | otherwise = Right restored
  where
    finalizedTerm (depth, term) =
      termScopedAt depth term
        && null (metaIdsOf term)
        && null (levelMetasOfTerm term)
    instanceDepths =
      Map.fromList
        [ (ciaDictionary entry, ciaTelescopeLength entry)
        | entry <- cprInstances artifact
        ]
    firstUnfinalizedTerm =
      listToMaybe
        [ owner
        | (owner, depth, term) <- artifactTerms
        , not (finalizedTerm (depth, term))
        ]
    valueWithoutBody =
      listToMaybe
        [ globalName
        | (globalName, global) <- cprGlobals artifact
        , CheckedValueFromBody <- [cgaValue global]
        , Nothing <- [cgaBody global]
        ]
    artifactTerms =
      concat
        [ concat
            [ ("global " <> gKey globalName <> " quoted type", 0, cgaQuotedType global)
                : map ("global " <> gKey globalName <> " Core type", 0,) (maybeToList (cgaCoreType global))
                ++ map ("global " <> gKey globalName <> " body", 0,) (maybeToList (cgaBody global))
                ++ map ("global " <> gKey globalName <> " record interface", 0,) (maybeToList (cgaRecordInterface global))
                ++ [("global " <> gKey globalName <> " value", 0, term) | CheckedClosedValue term <- [cgaValue global]]
            | (globalName, global) <- cprGlobals artifact
            ]
        , [("constructor " <> gKey constructorName <> " type", 0, ccaType constructor) | (constructorName, constructor) <- cprConstructors artifact]
        , concat
            [ [("trait " <> gKey traitName <> " super " <> name, 0, term) | (name, term) <- ctaSupers trait]
            | (traitName, trait) <- cprTraits artifact
            ]
        , concat
            [ [("instance " <> gKey (ciaDictionary entry) <> " term", ciaTelescopeLength entry, term) | term <- ciaPremises entry ++ ciaHead entry]
            | entry <- cprInstances artifact
            ]
        , concat
            [ [("instance interface " <> gKey dictionary, Map.findWithDefault 0 dictionary instanceDepths, term) | term <- terms]
            | (dictionary, terms) <- cprInstanceUniverseInterfaces artifact
            ]
        , [("foundation provider " <> gKey global, 0, term) | (global, term) <- cprFoundationProviders artifact]
        , [("implementation " <> gKey global, 0, term) | (global, term) <- cprImplementationBodies artifact]
        , concatMap effectLabelTerms (cprModuleEffectLabels artifact)
        , concatMap effectLabelTerms (cprEffectInterfaces artifact)
        ]
    effectLabelTerms :: Show owner => (owner, CheckedEffectLabelArtifact) -> [(Text, Int, Term)]
    effectLabelTerms (owner, label) =
      telescopeTerms ("effect " <> renderOwner owner <> " parameter") 0 (celaParameters label)
        ++ [ ("effect " <> renderOwner owner <> " fixed argument", 0, term)
           | term <- maybe [] id (celaFixedArguments label)
           ]
        ++ concatMap
          (operationTerms owner (length (celaParameters label)))
          (celaOperations label)
    operationTerms :: Show owner => owner -> Int -> CheckedEffectOperationArtifact -> [(Text, Int, Term)]
    operationTerms owner parameterDepth operation =
      let implicitDepth = parameterDepth
          argumentDepth = implicitDepth + length (ceoaImplicits operation)
          resultDepth = argumentDepth + length (ceoaArguments operation)
       in telescopeTerms
            ("effect " <> renderOwner owner <> " operation " <> ceoaName operation <> " implicit")
            implicitDepth
            (ceoaImplicits operation)
            ++ telescopeTerms
              ("effect " <> renderOwner owner <> " operation " <> ceoaName operation <> " argument")
              argumentDepth
              (ceoaArguments operation)
            ++ [("effect " <> renderOwner owner <> " operation " <> ceoaName operation <> " result", resultDepth, ceoaResult operation)]
    telescopeTerms owner initialDepth telescope =
      [ (owner, initialDepth + index, teDomain entry)
      | (index, entry) <- zip [0 ..] telescope
      ]
    renderOwner :: Show owner => owner -> Text
    renderOwner = T.pack . show
    keyedSections =
      [ map fst (cprGlobals artifact)
      , map fst (cprDatas artifact)
      , map fst (cprConstructors artifact)
      , map fst (cprTraits artifact)
      , map fst (cprBareTraitMembers artifact)
      , map fst (cprTraitMemberOwners artifact)
      , map fst (cprInstanceUniverseInterfaces artifact)
      , map fst (cprActivePatterns artifact)
      , map fst (cprProjections artifact)
      , map fst (cprInoutParameters artifact)
      , map fst (cprEffectOperationValues artifact)
      , map fst (cprReceivers artifact)
      , map fst (cprRecordOrders artifact)
      , map fst (cprPositivity artifact)
      , map fst (cprLevelOperatorAliases artifact)
      , map fst (cprEffectInterfaces artifact)
      , map fst (cprImplementationBodies artifact)
      , map fst (cprFoundationProviders artifact)
      ]
    moduleKeyedSections =
      [ map fst (cprModuleExports artifact)
      , map fst (cprReExports artifact)
      ]
    textKeyedSections =
      [ map fst (cprUniverseInferenceRecords artifact)
      , map fst (cprModuleEffectLabels artifact)
      ]
    setLikeSections =
      [ cprUniverseInterfaceValues artifact
      , cprFinalizedUniverseInterfaces artifact
      , cprOpaqueDatas artifact
      , cprOpaqueDefinitions artifact
      ]
    hasDuplicateKey keys = length keys /= Set.size (Set.fromList keys)
    encodedGlobals = Map.fromList (cprGlobals artifact)
    globals = Map.mapWithKey restoreGlobal encodedGlobals
    context = EvalCtx (Globals globals) emptyMetas False Map.empty
    primitiveRegistrationBodies =
      Map.mapMaybeWithKey
        (\global definition ->
           CGlob . GName primModule <$> globalPrimitiveIdentity global definition)
        (csGlobals builtinState)
    restoreGlobal global encoded =
      GlobalDefData
        (cgaUniverses encoded)
        []
        (cgaObservationMode encoded)
        (cgaNominalSummary encoded)
        (eval context [] (cgaQuotedType encoded))
        (cgaCoreType encoded)
        (restoreValue encoded)
        (case cgaBody encoded of
           Just body -> Just body
           Nothing -> Map.lookup global primitiveRegistrationBodies)
        (cgaRecordInterface encoded)
        (cgaReducible encoded)
    restoreValue encoded = case cgaValue encoded of
      CheckedNoValue -> Nothing
      CheckedValueFromBody -> eval context [] <$> cgaBody encoded
      CheckedClosedValue term -> Just (eval context [] term)
    restored =
      setCheckInstances restoredInstances $
      builtinState
        { csGlobals = globals
        , csDatas = Map.fromList (map (fmap restoreData) (cprDatas artifact))
        , csCtors = Map.fromList (map (fmap restoreConstructor) (cprConstructors artifact))
        , csTraits = Map.fromList (map (fmap restoreTrait) (cprTraits artifact))
        , csBareTraitMembers = Map.fromList (cprBareTraitMembers artifact)
        , csTraitMemberOwners = Map.fromList (cprTraitMemberOwners artifact)
        , csInstanceUniverseInterfaces = Map.fromList (cprInstanceUniverseInterfaces artifact)
        , csUniverseInterfaceValues = Set.fromList (cprUniverseInterfaceValues artifact)
        , csFinalizedUniverseInterfaces = Set.fromList (cprFinalizedUniverseInterfaces artifact)
        , csUniverseInferenceRecords = Map.fromList (cprUniverseInferenceRecords artifact)
        , csModuleExports = Map.fromList (cprModuleExports artifact)
        , csActive = Map.fromList (map (fmap restoreActive) (cprActivePatterns artifact))
        , csProjections = Map.fromList (map (fmap restoreProjection) (cprProjections artifact))
        , csInoutParams = Map.fromList (map (fmap (map (fmap restoreInout))) (cprInoutParameters artifact))
        , csEffectOpValueGlobals = Map.fromList (map (fmap restoreEffectOperationValue) (cprEffectOperationValues artifact))
        , csReceivers = Map.fromList (cprReceivers artifact)
        , csOpaqueDatas = Map.fromSet (const ()) (Set.fromList (cprOpaqueDatas artifact))
        , csOpaqueDefs = Map.fromSet (const ()) (Set.fromList (cprOpaqueDefinitions artifact))
        , csRecordOrders = Map.fromList (cprRecordOrders artifact)
        , csReExports = Map.fromList (map (fmap Map.fromList) (cprReExports artifact))
        , csPositivity = Map.fromList (cprPositivity artifact)
        , csMultiFixOps = Set.fromList (cprMultiFixOperators artifact)
        , csFoundationProviders = Map.fromList (cprFoundationProviders artifact)
        , csCoreBodies = Map.empty
        , csImportedCoreBodies = Map.fromList (cprImplementationBodies artifact)
        , csLevelOperatorAliases = Map.fromList (map (fmap restoreLevelOperator) (cprLevelOperatorAliases artifact))
        , csModEffLabels = Map.fromList (map (fmap restoreEffectLabel) (cprModuleEffectLabels artifact))
        , csEffectInterfaces = Map.fromList (map (fmap restoreEffectLabel) (cprEffectInterfaces artifact))
        , csMultishotOps = Set.fromList (cprMultishotOperations artifact)
        , csMetas = emptyMetas
        , csSolvedMetas = Set.empty
        , csDiags = []
        , csScopeNameCache = Nothing
        , csAllowUnsafeIntrinsics = False
        , csEmbeddedLoad = False
        }
    restoredInstances = map restoreInstance (cprInstances artifact)
    restoreData encoded =
      DataInfo (cdaConstructors encoded) (cdaParameterCount encoded) (cdaLevel encoded)
    restoreConstructor encoded =
      CtorInfo
        (ccaData encoded)
        (ccaUniverses encoded)
        (ccaType encoded)
        [(field, Nothing) | field <- ccaFieldNames encoded]
        (ccaSourceFields encoded)
    restoreTrait encoded =
      TraitInfo
        (ctaParameterCount encoded)
        (ctaMembers encoded)
        (ctaMemberModes encoded)
        (ctaAssociatedStaticMembers encoded)
        (ctaMemberQuantities encoded)
        (ctaDefaults encoded)
        (ctaSupers encoded)
        (ctaDerivedMembers encoded)
        (ctaDerivedSupers encoded)
        (if ctaEvidenceIndependentlyUnique encoded then IndependentlyUnique else SealedCoherent)
    restoreInstance encoded =
      InstanceEntry
        (ciaTrait encoded)
        (ciaTraitUniverses encoded)
        (ciaUniverses encoded)
        (ciaTelescopeLength encoded)
        (ciaPremises encoded)
        (ciaHead encoded)
        (ciaDictionary encoded)
    restoreActive tag = APInfo $ case tag of 0 -> APOption; 1 -> APMatch; _ -> APTotal
    restoreProjection encoded =
      ProjInfo (cpaPlacePositions encoded) (cpaPlaceNames encoded) (cpaSelector encoded) (cpaYields encoded)
    restoreInout encoded = InoutParamInfo (ciaFormal encoded) (ciaSuccessor encoded)
    restoreEffectOperationValue encoded = EffectOpValueInfo (ceovaLabel encoded) (ceovaName encoded) (ceovaQuantity encoded) (ceovaArity encoded)
    restoreLevelOperator = \case
      0 -> LevelOperatorZero
      1 -> LevelOperatorOne
      2 -> LevelOperatorSucc
      3 -> LevelOperatorAdd
      4 -> LevelOperatorMax
      5 -> LevelOperatorFromInteger
      6 -> LevelOperatorLt
      _ -> LevelOperatorLe
    restoreEffectLabel encoded =
      EffLabelInfo
        (celaLabel encoded)
        (celaInterface encoded)
        (celaParameters encoded)
        (fmap (map (eval context [])) (celaFixedArguments encoded))
        (celaFixedUniverses encoded)
        (map restoreEffectOperation (celaOperations encoded))
    restoreEffectOperation encoded =
      EffOpInfo (ceoaName encoded) (ceoaQuantity encoded) (ceoaImplicits encoded) (ceoaArguments encoded) (ceoaResult encoded)
