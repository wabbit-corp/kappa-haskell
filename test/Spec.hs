{-# LANGUAGE PatternSynonyms #-}

-- | Cabal test-suite driver: runs the Appendix T conformance tree
-- under @tests/conformance@ through the in-process harness, then
-- cross-checks the §3.1.2A diagnostic code registry against every
-- diagnostic code spelled in the implementation sources.
module Main (main) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Control.Applicative ((<|>))
import Data.Either (isLeft)
import Data.List (isInfixOf, isSuffixOf, nub, permutations, sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Monad (forM, unless, when)
import Kappa.Arithmetic
  ( ACmp (..)
  , AExpr (..)
  , AFact (..)
  , AFormula (..)
  , ArithmeticAssumptionCaseReplay (..)
  , ArithmeticFormulaReplay (..)
  , ArithmeticNormalForm (..)
  , ArithmeticReplay (..)
  , ArithmeticSemantics (..)
  , derivePrincipalAffineAssignment
  , derivePrincipalAffineSubstitution
  , deriveArithmeticFormulaReplayWithAssumptions
  , deriveArithmeticReplay
  , negateFact
  , verifyArithmeticReplay
  )
import Kappa.Backend.C (generateC)
import Kappa.Backend.IR
  ( BackendAlt (..)
  , BackendBinder (..)
  , BackendBinderId (..)
  , BackendBody (..)
  , BackendCond (..)
  , BackendCtorLayout (..)
  , BackendItem (..)
  , BackendMeta (..)
  , BackendNodeId (..)
  , BackendParam (..)
  , BackendErasure (..)
  , ErasureProvenance (..)
  , BackendPat (..)
  , BackendTerm (..)
  , BackendIRViolation (..)
  , BackendUse (..)
  , KBackendIR (..)
  , BackendUseId (..)
  , kbackendRepresentationCertificates
  , lowerKBackendIR
  , validateCoreCapabilities
  , validateKBackendIR
  )
import Kappa.Backend.LLVM (generateLL)
import Kappa.Backend.Repr
  ( ArgConv (..)
  , CtorLayout (..)
  , CtorLayoutInfo (..)
  , Rep (..)
  , argConvSelectGlobalForArgs
  , argConvSelectGlobal
  , ctorLayoutOf
  , erasedSpinePositionsForArgs
  , runtimeConstructorField
  , scalarRep
  )
import Kappa.Backend.Verify (VerifyInputs (..), verifyInputs, verifyUnit)
import Kappa.Builtins
  ( gPrel
  , prelDouble
  , prelEqType
  , prelFin
  , prelInt
  , prelLevelLe
  , prelNat
  , prelNatSucc
  , prelNatZero
  , prelUnit
  , primModule
  )
import Kappa.Cardinality (cardLiteral)
import Kappa.Check
  ( CheckState (..)
  , CtorInfo (..)
  , DataInfo (..)
  , InstanceEntry (..)
  , LevelOperatorIdentity (..)
  , TraitInfo (..)
  )
import Kappa.Core
  ( Closure (..)
  , BinderOrigin (..)
  , CaseAlt (..)
  , ConstructorArg (..)
  , CorePat (..)
  , FormationMode (..)
  , GName (..)
  , gnameText
  , Icit (..)
  , KItem (..)
  , Literal (..)
  , ObservationMode (..)
  , Q (..)
  , RecordField (..)
  , SchemaRoleEvidence (..)
  , Term (..)
  , UniverseEvidence (..)
  , UniverseEvidenceStep (..)
  , Value (..)
  , emptyDeclarationUniverseTelescope
  , mapUniverseEvidenceLevels
  , solverUniverseEvidence
  , universeLift
  , validateUniverseLiftEvidence
  , validateUniverseLiftEvidenceUnder
  , pattern CPiM
  , pattern CPiFormedM
  , pattern CGlob
  , pattern VGlobN
  , pattern VPiM
  , pattern VPi
  )
import Kappa.CoreOps
  ( CorePatternDecision (..)
  , foldTerm
  , globalsOfTerm
  , levelMetasOfTerm
  , levelParamsOfTerm
  , mapTermWithDepth
  , matchCorePattern
  , shiftTerm
  , substTerm
  , substTopTermAt
  , termScopedAt
  , weakenTermUnderBinderAt
  , zonkTermWith
  )
import Kappa.CoreText
  ( KCoreTextError (..)
  , KCoreDataInfo (..)
  , KCoreConstructorInfo (..)
  , parseAndVerifyKCoreTextWithEnvironment
  , parseAndVerifyKCoreInterface
  , parseAndVerifyKCoreInterfaceWithInterfaces
  , parseKCoreText
  , printCanonicalKCoreText
  , kcoreRepresentationCertificateCount
  , renderKCoreModule
  , semanticHashKCoreText
  , verifyKCoreTextWithInterfaces
  )
import Kappa.Diagnostic (dCode, isError, jArray, jObject, jStr)
import Kappa.Eval
  ( EvalCtx (..)
  , GlobalDef (..)
  , Globals (..)
  , emptyMetas
  , eval
  , force
  , globalDefWithCoreBody
  , globalDefWithCoreType
  , globalDefWithNominalSummary
  , globalDefWithUniverses
  , quote
  )
import Kappa.Explain (ExplainEntry (..), explainExists, registry)
import Kappa.Inhabitance
  ( CardinalityBound (..)
  , InhabitanceSummary (Contractible, Empty, Finite, Subsingleton, Unknown)
  , addSummaries
  , canonicalizeFinite
  , isEmpty
  , maxCount
  , minCount
  , multiplySummaries
  )
import Kappa.NominalVariance
  ( NominalClauseKind (..)
  , NominalClosureClause (..)
  , NominalCumulativitySummary (..)
  , NominalMonotoneWitness (..)
  , NominalRepresentationAction (..)
  , NominalRoleAction (..)
  , NominalSignatureClosure (..)
  , RoleRequirement (..)
  , SchemaActionCertificateId (..)
  , UniverseVariance (..)
  , makeNominalCumulativitySummary
  , makeNominalSignatureClosure
  , nominalEvidenceDependencies
  , verifyNominalCumulativitySummary
  , withNominalMonotoneWitnesses
  )
import Kappa.Level
  ( ConstraintOrigin (..)
  , DeclarationUniverseTelescope (..)
  , Level (..)
  , NeutralLevelAtom (..)
  , NeutralLevelTerm (..)
  , LevelConstraint (..)
  , LevelAssignmentGraphError (..)
  , LevelAssignmentGraphBudget
  , LevelSolveError (..)
  , LevelSolution (..)
  , PrincipalInferenceOutcome (..)
  , PrincipalNonLeastWitness (..)
  , SolveResult (..)
  , assumptionsConsistent
  , emptyAssumptions
  , finiteLevel
  , emptyLevelAssignmentGraphBudget
  , extendLevelAssignmentGraph
  , extendLevelAssignmentGraphWithBudget
  , inferPrincipalLevelsFor
  , insertAssumption
  , levelAdd
  , levelMax
  , levelMetas
  , mergeLevelAssignments
  , levelSucc
  , normalizeLevel
  , rebuildLevelAssignmentGraphBudget
  , proveLevelLeq
  , solveLevelConstraints
  , solveLevelConstraintsFor
  , substituteLevelMetas
  )
import Kappa.Ownership
  ( BinderId (..)
  , BinderOwn (..)
  , BranchSite (..)
  , OwnershipCtorType (..)
  , OwnInfo (..)
  , UseKind (..)
  , annotateOwnershipWithUniverses
  , argConvBodies
  , crossCheckBodiesWithUniverses
  , renderOwnInfo
  )
import Kappa.Parser (parseExprText)
import Kappa.Pipeline (CompiledUnit (..), compileFiles, compileSourceWithPrelude)
import Kappa.Pretty (renderJudgment, renderTerm)
import Kappa.Representation
  ( BackendProfileRestriction (..)
  , ConstructorFieldPath (..)
  , ExactNaturalRepresentationCertificate (..)
  , OrdinalEncoding (..)
  , OrdinalRepresentationCertificate (..)
  , RefinementRepresentationCertificate (..)
  , RepresentationContext (..)
  , VerifiedRepresentationCertificate (..)
  , exactNaturalRepresentationCertificateIdentity
  , ordinalRepresentationCertificateIdentity
  , refinementRepresentationCertificateIdentity
  , representationTypeIdentity
  , verifiedRepresentationCertificateIdentity
  , verifyRepresentationCertificate
  , verifyExactNaturalRepresentationCertificate
  , verifyOrdinalRepresentationCertificate
  , verifyRefinementRepresentationCertificate
  )
import Kappa.SemanticHash (canonicalIdentityHex, sha256Hex)
import Kappa.Source (ModuleName (..))
import Kappa.Syntax (Expr (EArrow, EForall, ERecordType))
import Kappa.TestHarness
  ( Outcome (..)
  , Summary (..)
  , TestReport (..)
  , runTestFile
  , runTestPath
  , summarize
  )
import Numeric.Natural (Natural)
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , getTemporaryDirectory
  , listDirectory
  , removeDirectoryRecursive
  )
import System.Environment (lookupEnv)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath ((</>))
import System.IO (BufferMode (..), hSetBuffering, stdout)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  regOk0 <- registryComplete
  famOk <- familiesHygienic
  harnessOk <- harnessFaithful
  jsonOk <- jsonEncoderSound
  semanticHashOk <- semanticHashDomain
  closureReadbackOk <- closureReadbackDomain
  usingBinderScopeOk <- usingBinderScopeDomain
  arithmeticReplayOk <- arithmeticReplayDomain
  constructorPatternAlignmentOk <- constructorPatternAlignmentDomain
  representationCertificateOk <- representationCertificateIdentityDomain
  inhabitanceOk <- inhabitanceIntervalDomain
  universeLevelOk <- universeLevelDomain
  universeLiftOk <- universeLiftEvidenceDomain
  universeSchemaOk <- universeSchemaInterfaceDomain
  universePrincipalOk <- universeOccurrenceInstantiationPrincipalDomain
  universeLawSchemaOk <- universeLawSchemasPrincipalDomain
  associatedStaticMemberOk <- associatedStaticMemberUniverseDomain
  universeCapabilityOk <- universeCapabilityBoundary
  schemaLiftBoundaryOk <- schemaLiftBackendCertificateBoundary
  nominalVarianceOk <- nominalVarianceCertificateDomain
  singletonRecordSyntaxOk <- parserSingletonRecordCommaDomain
  quantifierSyntaxOk <- parserQuantifierSyntaxDomain
  expectFragmentOk <- expectFragmentDomain
  kcoreTextOk <- kcoreTextCanonicalDomain
  kcoreInterfaceOk <- kcoreSourceFreeInterfaceDomain
  verifyOk <- verifierCatchesViolations
  reprOk <- reprScalarIdentity
  primConvOk <- primArgConventionS23c
  spineErasureOk <- spineErasureOmittedImplicitS5
  ownOk <- ownershipCrossCheckClean
  s23dOk <- perceusS23dDeadBinderDrops
  s23dDiagOk <- perceusS23dLegacyPathTamperIgnoredS5
  s32Ok <- perceusS32FreeOnZeroEntryGates
  cachePubOk <- globalCachePublicationMarksShared
  backendIrOk <- backendIRPhaseAS5
  backendIrValidateOk <- backendIRValidatorS5
  backendIrConsumerOk <- backendIRConsumerContractS5
  backendIrNoPathOwnOk <- backendIRNoPathOwnershipS5
  ownershipNoRPathOk <- ownershipPhysicalRPathRetiredS5
  backendIrProjectedBorrowedOk <- backendIRProjectedBorrowedCalleeS5
  backendIrPatternErasureOk <- backendIRPatternErasesExistentialsS5
  scalarKindParamOk <- scalarKindDomainParamKeepsWorkers
  scalarDoubleEscapeOk <- llvmDoubleScalarUnboxEscapesWrongTag
  ctorLayoutOk <- ctorLayoutEvidenceFields
  reExportOk <- reExportBoundaryRefinement
  let unitChecks =
        [ ("registryComplete", regOk0)
        , ("familiesHygienic", famOk)
        , ("harnessFaithful", harnessOk)
        , ("jsonEncoderSound", jsonOk)
        , ("semanticHashDomain", semanticHashOk)
        , ("closureReadbackDomain", closureReadbackOk)
        , ("usingBinderScopeDomain", usingBinderScopeOk)
        , ("arithmeticReplayDomain", arithmeticReplayOk)
        , ("constructorPatternAlignmentDomain", constructorPatternAlignmentOk)
        , ("representationCertificateIdentityDomain", representationCertificateOk)
        , ("inhabitanceIntervalDomain", inhabitanceOk)
        , ("universeLevelDomain", universeLevelOk)
        , ("universeLiftEvidenceDomain", universeLiftOk)
        , ("universeSchemaInterfaceDomain", universeSchemaOk)
        , ("universeOccurrenceInstantiationPrincipalDomain", universePrincipalOk)
        , ("universeLawSchemasPrincipalDomain", universeLawSchemaOk)
        , ("associatedStaticMemberUniverseDomain", associatedStaticMemberOk)
        , ("universeCapabilityBoundary", universeCapabilityOk)
        , ("schemaLiftBackendCertificateBoundary", schemaLiftBoundaryOk)
        , ("nominalVarianceCertificateDomain", nominalVarianceOk)
        , ("parserSingletonRecordCommaDomain", singletonRecordSyntaxOk)
        , ("parserQuantifierSyntaxDomain", quantifierSyntaxOk)
        , ("expectFragmentDomain", expectFragmentOk)
        , ("kcoreTextCanonicalDomain", kcoreTextOk)
        , ("kcoreSourceFreeInterfaceDomain", kcoreInterfaceOk)
        , ("verifierCatchesViolations", verifyOk)
        , ("reprScalarIdentity", reprOk)
        , ("primArgConventionS23c", primConvOk)
        , ("spineErasureOmittedImplicitS5", spineErasureOk)
        , ("ownershipCrossCheckClean", ownOk)
        , ("perceusS23dDeadBinderDrops", s23dOk)
        , ("perceusS23dLegacyPathTamperIgnoredS5", s23dDiagOk)
        , ("perceusS32FreeOnZeroEntryGates", s32Ok)
        , ("globalCachePublicationMarksShared", cachePubOk)
        , ("backendIRPhaseAS5", backendIrOk)
        , ("backendIRValidatorS5", backendIrValidateOk)
        , ("backendIRConsumerContractS5", backendIrConsumerOk)
        , ("backendIRNoPathOwnershipS5", backendIrNoPathOwnOk)
        , ("ownershipPhysicalRPathRetiredS5", ownershipNoRPathOk)
        , ("backendIRProjectedBorrowedCalleeS5", backendIrProjectedBorrowedOk)
        , ("backendIRPatternErasesExistentialsS5", backendIrPatternErasureOk)
        , ("scalarKindDomainParamKeepsWorkers", scalarKindParamOk)
        , ("llvmDoubleScalarUnboxEscapesWrongTag", scalarDoubleEscapeOk)
        , ("ctorLayoutEvidenceFields", ctorLayoutOk)
        , ("reExportBoundaryRefinement", reExportOk)
        ]
      regOk = all snd unitChecks
  unless regOk $ do
    putStrLn "unit domains FAILED:"
    mapM_ (putStrLn . ("  " <>) . fst) (filter (not . snd) unitChecks)
  unitOnly <- maybe False (`elem` ["1", "true", "yes"]) <$> lookupEnv "KAPPA_TEST_UNITS_ONLY"
  when unitOnly $ if regOk then exitSuccess else exitFailure
  let root = "tests/conformance"
  exists <- doesDirectoryExist root
  if not exists
    then do
      putStrLn ("missing conformance tree: " <> root)
      exitFailure
    else do
      reports <- runTestPath root
      let s = summarize reports
      putStrLn $
        "total " <> show (length reports)
          <> ": " <> show (sPass s) <> " passed, "
          <> show (sFail s) <> " failed, "
          <> show (sUnsupported s) <> " unsupported, "
          <> show (sHarnessError s) <> " harness errors"
      if sFail s > 0 || sHarnessError s > 0 || not regOk
        then exitFailure
        else pure ()

semanticHashDomain :: IO Bool
semanticHashDomain =
  pure
    ( sha256Hex ""
        == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        && sha256Hex "abc"
          == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        && canonicalIdentityHex "Global" "a"
          /= canonicalIdentityHex "Global" "b"
        && canonicalIdentityHex "Global" "a"
          /= canonicalIdentityHex "Constructor" "a"
    )

-- | §13.2.1: a one-field record type is comma-terminated regardless of
-- field markers. The same marked syntax remains available to Pi binders when
-- followed by an arrow, so the parser must distinguish these grammatically
-- rather than by the marker itself.
parserSingletonRecordCommaDomain :: IO Bool
parserSingletonRecordCommaDomain = do
  let noComma =
        [ "(@x : Type)"
        , "(1 x : Int)"
        , "(& x : Int)"
        ]
      comma =
        [ "(@x : Type,)"
        , "(1 x : Int,)"
        , "(& x : Int,)"
        ]
      arrows =
        [ "(@x : Type) -> Type"
        , "(1 x : Int) -> Int"
        , "(& x : Int) -> Int"
        ]
      parse source = parseExprText "singleton-record-syntax.kp" source
      isNotSingletonRecord = \case
        Right (ERecordType [_] Nothing _) -> False
        _ -> True
      isSingletonRecord = \case
        Right (ERecordType [_] Nothing _) -> True
        _ -> False
      isArrow = \case
        Right EArrow {} -> True
        _ -> False
      notRecords = map (isNotSingletonRecord . parse) noComma
      records = map (isSingletonRecord . parse) comma
      parsedArrows = map (isArrow . parse) arrows
      ok = and notRecords && and records && and parsedArrows
  unless ok $ do
    putStrLn "parserSingletonRecordCommaDomain FAILED:"
    putStrLn ("  no-comma is-not-record results: " ++ show (zip noComma notRecords))
    putStrLn ("  comma results: " ++ show (zip comma records))
    putStrLn ("  arrow results: " ++ show (zip arrows parsedArrows))
  pure ok

-- | §11.3 has two implicit quantity-0 spellings: a bare binder and a
-- parenthesized typed binder. Braces are application syntax, not a third
-- quantifier-binder form, and a malformed quantifier must not backtrack into
-- an ordinary identifier application.
parserQuantifierSyntaxDomain :: IO Bool
parserQuantifierSyntaxDomain = do
  let parse source = parseExprText "quantifier-syntax.kp" source
      isForall = \case
        Right EForall {} -> True
        _ -> False
      bare = isForall (parse "forall a. a -> a")
      typed = isForall (parse "forall (a : Type). a -> a")
      bracesReject = case parse "forall {a : Type}. a -> a" of
        Left _ -> True
        Right _ -> False
      ok = bare && typed && bracesReject
  unless ok $
    putStrLn
      ( "parserQuantifierSyntaxDomain FAILED: "
          <> show (bare, typed, bracesReject)
      )
  pure ok

-- | Spec §9.4: an @expect@ contract is implemented only by a selected
-- companion fragment, never by a declaration in the expectation source file
-- itself. This source-file distinction is independent of module merging.
expectFragmentDomain :: IO Bool
expectFragmentDomain = do
  let expectation =
        T.unlines
          [ "expect term platformValue : Int"
          , "answer : Int"
          , "let answer = platformValue"
          ]
      implementation =
        T.unlines
          [ "platformValue : Int"
          , "let platformValue = 42"
          ]
      sameFile = compileFiles [("main.kp", expectation <> implementation)]
      companion =
        compileFiles
          [ ("main.kp", expectation)
          , ("main.impl.kp", implementation)
          ]
      dataExpectation =
        T.unlines
          [ "expect data F (A : Type) : Type"
          , "expect term foo : forall A. F A"
          , "let use = foo"
          ]
      dataImplementation =
        T.unlines
          [ "data F (A : Type) : Type ="
          , "    MkF"
          , "let foo = MkF"
          ]
      implementationFirstData =
        compileFiles
          [ ("main.impl.kp", dataImplementation)
          , ("main.kp", dataExpectation)
          ]
      errorCodes = map dCode . filter isError . cuDiags
      sameFileCodes = errorCodes sameFile
      companionCodes = errorCodes companion
      dataCodes = errorCodes implementationFirstData
      ok =
        sameFileCodes == ["E_EXPECT_UNSATISFIED"]
          && null companionCodes
          && null dataCodes
  unless ok $ do
    putStrLn "expectFragmentDomain FAILED:"
    putStrLn ("  same-file errors: " ++ show sameFileCodes)
    putStrLn ("  companion-fragment errors: " ++ show companionCodes)
    putStrLn ("  implementation-first data errors: " ++ show dataCodes)
  pure ok

-- | §11.1.2.3A regression: a finalized semantic interface has one stable
-- declaration-universe arity. Every global occurrence in a global or
-- constructor type must carry exactly that many levels, and no provisional
-- level metavariable may escape the module generalization boundary. This is
-- deliberately checked over the embedded prelude as well as user code: a
-- constructor result whose hidden spine diverges from its data family makes
-- nominally identical types fail conversion throughout every downstream
-- module.
universeSchemaInterfaceDomain :: IO Bool
universeSchemaInterfaceDomain = do
  let cu = compileSourceWithPrelude "universe-schema-interface.kp" "module universe_schema_interface\n"
      st = cuState cu
      ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
      expectedArity target =
        dutParameterCount . gdUniverses <$> Map.lookup target (csGlobals st)
          <|> dutParameterCount . ciUniverses <$> Map.lookup target (csCtors st)
      arityMismatches owner term =
        foldTerm
          (\case
             CGlobal target universes ->
               case expectedArity target of
                 Just expected
                   | length universes /= expected ->
                       [(owner, target, length universes, expected)]
                 _ -> []
             _ -> [])
          (const [])
          term
      globalTerms =
        [ (gnameText owner, quote ctx 0 (gdType definition))
        | (owner, definition) <- Map.toList (csGlobals st)
        ]
      ctorTerms =
        [ (gnameText owner, ciType info)
        | (owner, info) <- Map.toList (csCtors st)
        ]
      mismatches =
        concat
          [ arityMismatches owner term
          | (owner, term) <- globalTerms ++ ctorTerms
          ]
      escapedMetas =
        [ (owner, levelMetasOfTerm term)
        | (owner, term) <- globalTerms ++ ctorTerms
        , not (null (levelMetasOfTerm term))
        ]
      retainedLevelAssignments = Map.size (csLevelAssignments st)
      retainedConstraintIndex = Map.size (csLevelConstraintIndex st)
      errors = filter isError (cuDiags cu)
      ok =
        null errors
          && null mismatches
          && null escapedMetas
          && retainedLevelAssignments == 0
          && retainedConstraintIndex == 0
  unless ok $ do
    putStrLn "universeSchemaInterfaceDomain FAILED:"
    unless (null errors) $
      putStrLn ("  compilation errors: " ++ show (length errors))
    mapM_
      (\(owner, target, actual, expected) ->
         putStrLn
           ( "  " ++ T.unpack owner ++ " references " ++ T.unpack (gnameText target)
               ++ " with " ++ show actual ++ " universe arguments; expected " ++ show expected
           ))
      (take 20 mismatches)
    mapM_
      (\(owner, metas) ->
         putStrLn ("  " ++ T.unpack owner ++ " retains level metas " ++ show metas))
      (take 20 escapedMetas)
    when (retainedLevelAssignments /= 0) $
      putStrLn
        ( "  completed module retains "
            ++ show retainedLevelAssignments
            ++ " level assignments"
            ++ " (constraints="
            ++ show (length (csLevelConstraints st))
            ++ ", pendingEvidence="
            ++ show (Map.size (csPendingLevelEvidence st))
            ++ ", pendingProofs="
            ++ show (Map.size (csPendingUniverseProofs st))
            ++ ", provisionalOccurrences="
            ++ show (length (csProvisionalUniverseInstantiations st))
            ++ ", activeOwner="
            ++ show (csActiveUniverseDefinition st)
            ++ ")"
        )
    when (retainedConstraintIndex /= 0) $
      putStrLn
        ( "  completed module retains "
            ++ show retainedConstraintIndex
            ++ " indexed level constraints"
        )
  pure ok

-- | §11.1.2.4A regression: omitted instantiations of a dependency's hidden
-- universe telescope are minimizable elaboration choices. Repeating @List A@
-- in an interface must not turn each fresh List specialization into another
-- parameter of the referencing declaration's schema.
universeOccurrenceInstantiationPrincipalDomain :: IO Bool
universeOccurrenceInstantiationPrincipalDomain = do
  let source =
        T.unlines
          [ "module universe_occurrence_principal"
          , "mapLists : forall (A : Type). List A -> List A -> List A"
          , "let mapLists A xs ys = listAppend xs ys"
          ]
      cu = compileSourceWithPrelude "universe-occurrence-principal.kp" source
      owner = GName (ModuleName ["universe_occurrence_principal"]) "mapLists"
      errors = filter isError (cuDiags cu)
      actual =
        dutParameterCount . gdUniverses
          <$> Map.lookup owner (csGlobals (cuState cu))
      ok = null errors && actual == Just 1
  unless ok $ do
    putStrLn "universeOccurrenceInstantiationPrincipalDomain FAILED:"
    putStrLn ("  errors: " ++ show (map dCode errors))
    putStrLn ("  mapLists schema arity: " ++ show actual ++ "; expected Just 1")
  pure ok

-- | §11.1.2.4A regression: universe arguments introduced while elaborating
-- law-bearing trait members are occurrences of dependency schemas, not new
-- parameters of the trait or member declaration. The carrier level is the
-- sole parameter of a generic algebra trait, while laws and dictionaries for
-- the closed TypeLevel carrier are monomorphic.
universeLawSchemasPrincipalDomain :: IO Bool
universeLawSchemasPrincipalDomain = do
  let cu = compileSourceWithPrelude "universe-law-schemas.kp" "module universe_law_schemas\n"
      globals = csGlobals (cuState cu)
      arity name =
        dutParameterCount . gdUniverses
          <$> Map.lookup (GName (ModuleName ["std", "prelude"]) name) globals
      typeLevelArity name =
        dutParameterCount . gdUniverses
          <$> Map.lookup (GName (ModuleName ["std", "typelevel"]) name) globals
      typeLevelInstanceArities trait =
        [ dutParameterCount (gdUniverses definition)
        | entry <- csInstances (cuState cu)
        , ieTrait entry == gPrel trait
        , let GName owner _ = ieDict entry
        , owner == ModuleName ["std", "typelevel"]
        , Just definition <- [Map.lookup (ieDict entry) globals]
        ]
      checks =
        [ ("AdditiveMonoid", arity "AdditiveMonoid", Just 1)
        , ("AdditiveMonoid.addAssoc", arity "AdditiveMonoid.addAssoc", Just 1)
        , ("typeLevelAddAssoc", typeLevelArity "typeLevelAddAssoc", Just 0)
        , ( "Eq TypeLevel instance"
          , Just (maximum (0 : typeLevelInstanceArities "Eq"))
          , Just 0
          )
        ]
      errors = filter isError (cuDiags cu)
      failures =
        [ (name, actual, expected)
        | (name, actual, expected) <- checks
        , actual /= expected
        ]
      ok = null errors && null failures
  unless ok $ do
    putStrLn "universeLawSchemasPrincipalDomain FAILED:"
    putStrLn ("  errors: " ++ show (map dCode errors))
    mapM_
      (\(name, actual, expected) ->
         putStrLn
           ( "  " ++ T.unpack name ++ " schema arity: " ++ show actual
               ++ "; expected " ++ show expected
           ))
      failures
  pure ok

-- | §11.1.2.3A / §14.2.1 regression: a generated associated-static-member
-- accessor is a semantic component of its owning trait prefix. Its hidden
-- universe occurrence must stay connected to that prefix while any
-- member-local suffix is generalized independently. Otherwise selecting a
-- concrete dictionary leaves @Rangeable.Range Int@ neutral instead of
-- reducing to the dictionary's @NumericRange Int@ field, and repeated
-- conversion attempts amplify the disconnected level constraints.
associatedStaticMemberUniverseDomain :: IO Bool
associatedStaticMemberUniverseDomain = do
  let source =
        T.unlines
          [ "module associated_static_member_universe"
          , "rangeValue : NumericRange Int"
          , "let rangeValue = 1 .. 5"
          , "doubleValue : Double"
          , "let doubleValue = 1 + 2"
          ]
      cu = compileSourceWithPrelude "associated-static-member-universe.kp" source
      state = cuState cu
      preludeName name = GName (ModuleName ["std", "prelude"]) name
      arity name =
        dutParameterCount . gdUniverses
          <$> Map.lookup (preludeName name) (csGlobals state)
      errors = filter isError (cuDiags cu)
      renderedDefinition name =
        case Map.lookup (preludeName name) (csGlobals state) of
          Nothing -> "<missing>"
          Just definition -> renderDefinition definition
      renderDefinition definition =
        "type="
              ++ maybe "<quoted>" (T.unpack . renderTerm) (gdCoreType definition)
              ++ "; body="
              ++ maybe "<missing>" (T.unpack . renderTerm) (gdCoreBody definition)
              ++ "; reducible=" ++ show (gdReducible definition)
      rangeableInstances =
        [ T.unpack (gnameText (ieTrait entry))
            ++ " universes=" ++ show (ieTraitUniverses entry)
            ++ " head=" ++ show (map renderTerm (ieHead entry))
            ++ " dict=" ++ T.unpack (gnameText (ieDict entry))
            ++ " " ++ maybe "<missing definition>" renderDefinition
              (Map.lookup (ieDict entry) (csGlobals state))
        | entry <- csInstances state
        , gnameText (ieTrait entry) == "Rangeable"
        ]
      checks =
        [ ("Rangeable owner arity", arity "Rangeable", Just 1)
        , ("Rangeable.Range accessor arity", arity "Rangeable.Range", Just 1)
        ]
      failures =
        [ (label, actual, expected)
        | (label, actual, expected) <- checks
        , actual /= expected
        ]
      ok = null errors && null failures
  unless ok $ do
    putStrLn "associatedStaticMemberUniverseDomain FAILED:"
    putStrLn ("  errors: " ++ show errors)
    putStrLn ("  Rangeable: " ++ renderedDefinition "Rangeable")
    putStrLn ("  Rangeable.Range: " ++ renderedDefinition "Rangeable.Range")
    putStrLn ("  (..): " ++ renderedDefinition "(..)")
    mapM_ (putStrLn . ("  instance: " ++)) rangeableInstances
    mapM_
      (\(label, actual, expected) ->
         putStrLn
           ( "  " ++ label ++ ": " ++ show actual
               ++ "; expected " ++ show expected
           ))
      failures
  pure ok

-- | §30.2.7 regression: inhabitance is a normalized cardinality interval, not
-- a closed five-constructor enumeration. The richer bounds retain useful
-- partial facts under sums/products, while only exact zero proves unreachable.
-- Exact arithmetic uses 'Natural', so a large finite product cannot overflow a
-- machine 'Int' and be misclassified as 'Empty'.
inhabitanceIntervalDomain :: IO Bool
inhabitanceIntervalDomain = do
  let hasBounds lo hi s = minCount s == lo && maxCount s == hi
      finite n = canonicalizeFinite n
      beyondInt = fromIntegral (maxBound :: Int) + 1 :: Natural
      beyondIntSquared = beyondInt * beyondInt
      checks =
        [ ("Finite 0 canonicalizes to Empty", finite 0 == Empty)
        , ("Finite 1 canonicalizes to Contractible", finite 1 == Contractible)
        , ("Finite n remains exact", finite 7 == Finite 7)
        , ("Subsingleton is [0,1]", hasBounds 0 (FiniteBound 1) Subsingleton)
        , ("Unknown is [0,unbounded]", hasBounds 0 Unbounded Unknown)
        , ("two subsingleton arms retain [0,2]", hasBounds 0 (FiniteBound 2) (addSummaries Subsingleton Subsingleton))
        , ("subsingleton times three retains [0,3]", hasBounds 0 (FiniteBound 3) (multiplySummaries Subsingleton (Finite 3)))
        , ("known singleton plus unknown retains inhabited lower bound", hasBounds 1 Unbounded (addSummaries Contractible Unknown))
        , ("exact zero absorbs an unbounded product", multiplySummaries Empty Unknown == Empty)
        , ("a nonzero range is not empty", not (isEmpty (addSummaries Subsingleton Subsingleton)))
        , ( "exact products do not overflow through Int"
          , hasBounds beyondIntSquared (FiniteBound beyondIntSquared) (multiplySummaries (finite beyondInt) (finite beyondInt))
          )
        ]
      failures = [label | (label, False) <- checks]
      ok = null failures
  unless ok $ do
    putStrLn "inhabitanceIntervalDomain FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
  pure ok

-- | §11.1.1-§11.1.2.2: canonical levels implement commutative natural sum,
-- normalize max AC-idempotently, and use scoped assumptions without treating
-- a consistent equality cycle as a contradiction. Metavariables are reported
-- as blocked until the owning elaboration boundary solves or generalizes them.
universeLevelDomain :: IO Bool
universeLevelDomain = do
  let u = LVar 0
      v = LVar 1
      m = LMeta 0
      m2 = LMeta 1
      one = finiteLevel (1 :: Integer)
      omegaPlusOne = levelAdd LOmega one
      onePlusOmega = levelAdd one LOmega
      cyc = insertAssumption v u (insertAssumption u v emptyAssumptions)
      impossible = insertAssumption (levelSucc u) u emptyAssumptions
      equalityConstrainedImpossible =
        insertAssumption
          (levelSucc u)
          v
          (insertAssumption v u (insertAssumption u v emptyAssumptions))
      ordered = insertAssumption u v emptyAssumptions
      atomicChain = insertAssumption v (LVar 2) ordered
      maxBoundedByAssumptions =
        insertAssumption v (LVar 2) (insertAssumption u (LVar 2) emptyAssumptions)
      maxBoundAssumption = insertAssumption (levelMax u v) (LVar 2) emptyAssumptions
      atomicMaxEntailed =
        insertAssumption
          u
          v
          (insertAssumption v (levelMax v (LVar 2)) emptyAssumptions)
      atomicMaxCountermodel =
        insertAssumption
          v
          u
          (insertAssumption u (levelMax u (LVar 2)) emptyAssumptions)
      disconnectedCompoundAssumption =
        insertAssumption
          (levelSucc (LVar 8))
          (LVar 9)
          (insertAssumption u v emptyAssumptions)
      bounded = insertAssumption (levelSucc u) LOmega emptyAssumptions
      origin = ConstraintOrigin "unit constraint" "universeLevelDomain"
      constraint a b = LevelConstraint 0 a b origin emptyAssumptions
      metaConstraints =
        [ constraint one m
        , constraint (finiteLevel (3 :: Integer)) m
        , constraint m (LMeta 1)
        ]
      metaSolutions = map solveLevelConstraints (permutations metaConstraints)
      solveForward = solveLevelConstraints metaConstraints
      assignedThree = \case
        Right solution ->
          Map.lookup 0 (lsAssignments solution) == Just (finiteLevel (3 :: Integer))
            && Map.lookup 1 (lsAssignments solution) == Just (finiteLevel (3 :: Integer))
        Left _ -> False
      occursRejected = case solveLevelConstraints [constraint (levelSucc m) m] of
        Left {} -> True
        Right _ -> False
      reflexiveAccepted = case solveLevelConstraints [constraint m m] of
        Right solution -> null (lsResidual solution)
        Left _ -> False
      recursiveMaxAccepted = case solveLevelConstraints [constraint (levelMax m (finiteLevel (4 :: Integer))) m] of
        Right solution ->
          Map.lookup 0 (lsAssignments solution) == Just (finiteLevel (4 :: Integer))
            && null (lsResidual solution)
        Left _ -> False
      embeddedMaxLeast =
        case solveLevelConstraintsFor (Set.singleton 0)
          [constraint LOmega (levelMax m one)] of
          Right solution ->
            Map.lookup 0 (lsAssignments solution) == Just LOmega
              && null (lsResidual solution)
          Left _ -> False
      embeddedAddLeast =
        case solveLevelConstraintsFor (Set.singleton 0)
          [constraint LOmega (levelAdd m one)] of
          Right solution ->
            Map.lookup 0 (lsAssignments solution) == Just LOmega
              && null (lsResidual solution)
          Left _ -> False
      embeddedFiniteAddLeast =
        case solveLevelConstraintsFor (Set.singleton 0)
          [constraint (finiteLevel (5 :: Integer)) (levelAdd m (finiteLevel (2 :: Integer)))] of
          Right solution ->
            Map.lookup 0 (lsAssignments solution) == Just (finiteLevel (3 :: Integer))
              && null (lsResidual solution)
          Left _ -> False
      embeddedIncomparableRemainsResidual =
        case solveLevelConstraintsFor (Set.fromList [0, 1])
          [constraint LOmega (levelMax m m2)] of
          Right solution ->
            Map.null (lsAssignments solution)
              && not (null (lsResidual solution))
          Left _ -> False
      metaMaxIntroductionAccepted =
        case solveLevelConstraints [constraint m (levelMax m m2)] of
          Right solution ->
            Map.null (lsAssignments solution) && null (lsResidual solution)
          Left _ -> False
      rigidParameterAssigned = case solveLevelConstraints [constraint (LParam 0) m] of
        Right solution ->
          Map.lookup 0 (lsAssignments solution) == Just (LParam 0)
            && null (lsResidual solution)
        Left _ -> False
      solvedAssignmentSurvivesResidual =
        case solveLevelConstraints
          [ constraint (LParam 0) m
          , constraint (LMeta 1) (LParam 1)
          ] of
          Right solution ->
            Map.lookup 0 (lsAssignments solution) == Just (LParam 0)
              && map (\c -> (lcLhs c, lcRhs c)) (lsResidual solution)
                == [(LMeta 1, LParam 1)]
          Left _ -> False
      duplicateResidualsAreCanonical =
        solveLevelConstraints (replicate 64 (constraint m (LParam 1)))
          == solveLevelConstraints [constraint m (LParam 1)]
      mutualMaxCycleCanonical =
        let m0 = LMeta 10
            m1 = LMeta 11
            m2 = LMeta 12
            lower = LParam 0
         in case solveLevelConstraints
              [ constraint (levelMax lower m1) m0
              , constraint (levelMax lower m2) m1
              , constraint (levelMax lower m0) m2
              ] of
              Right solution ->
                all ((== Just lower) . (`Map.lookup` lsAssignments solution)) [10, 11, 12]
                  && null (lsResidual solution)
                  && all (null . levelMetas) (Map.elems (lsAssignments solution))
              Left _ -> False
      successorCycleRejected =
        case solveLevelConstraints
          [ constraint (levelSucc (LMeta 21)) (LMeta 20)
          , constraint (LMeta 20) (LMeta 21)
          ] of
          Left LevelMetaOccurs {} -> True
          _ -> False
      neutralU = LNeutral (NeutralLevelSymbol "test:u" [])
      neutralV = LNeutral (NeutralLevelSymbol "test:v" [])
      neutralW = LNeutral (NeutralLevelSymbol "test:w" [])
      neutralP = LNeutral (NeutralLevelSymbol "test:p" [])
      naturalDistributionLeft = levelAdd neutralU (levelMax neutralV neutralW)
      naturalDistributionRight =
        levelMax (levelAdd neutralU neutralV) (levelAdd neutralU neutralW)
      additiveCancellationPrincipal =
        inferPrincipalLevelsFor
          (Set.singleton 30)
          [constraint (levelAdd neutralP one) (levelAdd (LMeta 30) one)]
          == SolvedPrincipal (Map.singleton 30 neutralP)
      successorCancellationPrincipal =
        inferPrincipalLevelsFor
          (Set.singleton 31)
          [constraint (levelSucc neutralP) (levelSucc (LMeta 31))]
          == SolvedPrincipal (Map.singleton 31 neutralP)
      principalAssignmentsComposeWithoutRevision =
        mergeLevelAssignments
          (Map.fromList [(40, LMeta 41)])
          (Map.fromList [(41, LZero)])
          == Right (Map.fromList [(40, LZero), (41, LZero)])
      principalAssignmentsRejectRevision =
        case
          mergeLevelAssignments
            (Map.singleton 42 neutralP)
            (Map.singleton 42 (levelMax neutralP neutralV))
        of
          Left (42, old, new) ->
            old == neutralP && new == levelMax neutralP neutralV
          _ -> False
      incrementalAssignmentGraphTracksTransitiveDependents =
        case
          extendLevelAssignmentGraph
            Map.empty
            Map.empty
            (Map.fromList [(40, LMeta 41), (50, neutralP)])
        of
          Right (initial, initialDependents, initialAffected) ->
            initialAffected == Set.fromList [40, 50]
              && case
                extendLevelAssignmentGraph
                  initial
                  initialDependents
                  (Map.singleton 41 LZero)
              of
                Right (combined, dependents, affected) ->
                  substituteLevelMetas combined (LMeta 40) == LZero
                    && substituteLevelMetas combined (LMeta 41) == LZero
                    && substituteLevelMetas combined (LMeta 50) == neutralP
                    && affected == Set.fromList [40, 41]
                    && Map.findWithDefault Set.empty 41 dependents == Set.singleton 40
                Left _ -> False
          Left _ -> False
      incrementalAssignmentGraphRefinesFlexibleAlias =
        case
          extendLevelAssignmentGraph
            Map.empty
            Map.empty
            (Map.singleton 40 (LMeta 41))
        of
          Right (initial, initialDependents, _) ->
            case
              extendLevelAssignmentGraph
                initial
                initialDependents
                (Map.singleton 40 LZero)
            of
              Right (combined, dependents, affected) ->
                Map.lookup 40 combined == Just (LMeta 41)
                  && Map.lookup 41 combined == Just LZero
                  && substituteLevelMetas combined (LMeta 40) == LZero
                  && affected == Set.fromList [40, 41]
                  && Map.findWithDefault Set.empty 41 dependents == Set.singleton 40
              Left _ -> False
          Left _ -> False
      incrementalAssignmentBudgetMatchesFullRebuild =
        case
          extendLevelAssignmentGraphWithBudget
            Map.empty
            Map.empty
            emptyLevelAssignmentGraphBudget
            (Map.fromList
              [ (70, levelAdd (LMeta 71) (LMeta 72))
              , (73, levelSucc (LMeta 70))
              , (74, neutralP)
              ])
        of
          Right (initial, initialDependents, initialBudget, _) ->
            case
              extendLevelAssignmentGraphWithBudget
                initial
                initialDependents
                initialBudget
                (Map.fromList [(71, LZero), (72, levelSucc LZero)])
            of
              Right (combined, _, incrementalBudget, affected) ->
                rebuildLevelAssignmentGraphBudget combined
                  == Right incrementalBudget
                  && affected == Set.fromList [70, 71, 72, 73]
              Left _ -> False
          Left _ -> False
      exactAssignmentGraphUpdateIsANoOp =
        case
          extendLevelAssignmentGraphWithBudget
            Map.empty
            Map.empty
            emptyLevelAssignmentGraphBudget
            (Map.fromList [(75, neutralP), (76, levelSucc neutralP)])
        of
          Right (initial, initialDependents, initialBudget, _) ->
            extendLevelAssignmentGraphWithBudget
              initial
              initialDependents
              initialBudget
              (Map.fromList [(75, neutralP), (76, levelSucc neutralP)])
              == Right
                ( initial
                , initialDependents
                , initialBudget
                , Set.empty
                )
          Left _ -> False
      noPointwiseLeastClass =
        case inferPrincipalLevelsFor
          (Set.fromList [32, 33])
          [constraint LOmega (levelMax (LMeta 32) (LMeta 33))] of
          NoPointwiseLeastSolution witness ->
            pnlwLeft witness /= pnlwRight witness
              && Map.keysSet (pnlwLeft witness) == Set.fromList [32, 33]
              && Map.keysSet (pnlwRight witness) == Set.fromList [32, 33]
          _ -> False
      maxSplitWitnessChecksCompleteSystem =
        inferPrincipalLevelsFor
          (Set.fromList [35, 36])
          [ constraint LOmega (levelMax (LMeta 35) (LMeta 36))
          , constraint (LMeta 35) LZero
          ]
          == SolvedPrincipal (Map.fromList [(35, LZero), (36, LOmega)])
      rigidMaxArmHasSymbolicPrincipal =
        inferPrincipalLevelsFor
          (Set.singleton 37)
          [constraint neutralP (levelMax (LMeta 37) neutralV)]
          == SolvedPrincipal (Map.singleton 37 neutralP)
      unconstrainedMetaHasCheckedZeroPrincipal =
        inferPrincipalLevelsFor (Set.singleton 38) []
          == SolvedPrincipal (Map.singleton 38 LZero)
      upperOnlyMetaHasCheckedZeroPrincipal =
        inferPrincipalLevelsFor
          (Set.singleton 39)
          [constraint (LMeta 39) neutralP]
          == SolvedPrincipal (Map.singleton 39 LZero)
      selectedInferencePreservesUnselectedProofObligations =
        inferPrincipalLevelsFor
          (Set.singleton 43)
          [ constraint neutralP (LMeta 43)
          , constraint (LMeta 44) neutralV
          ]
          == SolvedPrincipal (Map.singleton 43 neutralP)
      selectedChainSolvedTogether =
        inferPrincipalLevelsFor
          (Set.fromList [45, 46])
          [constraint (LMeta 45) (LMeta 46)]
          == SolvedPrincipal (Map.fromList [(45, LZero), (46, LZero)])
      selectedEqualitySccSolvedTogether =
        inferPrincipalLevelsFor
          (Set.fromList [47, 48])
          [ constraint (LMeta 47) (LMeta 48)
          , constraint (LMeta 48) (LMeta 47)
          ]
          == SolvedPrincipal (Map.fromList [(47, LZero), (48, LZero)])
      selectedDependencyRetainsUnselectedMeta =
        inferPrincipalLevelsFor
          (Set.singleton 49)
          [constraint (LMeta 50) (LMeta 49)]
          == SolvedPrincipal (Map.singleton 49 (LMeta 50))
      selectedEqualityLeavesRigidProofObligation =
        let constraints =
              [ constraint (LMeta 51) (LMeta 52)
              , constraint (LMeta 52) (LMeta 51)
              , constraint (LMeta 53) (LMeta 52)
              ]
            assignment = Map.singleton 52 (LMeta 51)
            substituted =
              [ ( substituteLevelMetas assignment (lcLhs item)
                , substituteLevelMetas assignment (lcRhs item)
                )
              | item <- constraints
              ]
         in inferPrincipalLevelsFor (Set.singleton 52) constraints
              == SolvedPrincipal assignment
              && (LMeta 53, LMeta 51) `elem` substituted
      solvedMetasRewriteConstraintAssumptions =
        let constrained lower upper assumptions =
              LevelConstraint 0 lower upper origin assumptions
            authenticated =
              insertAssumption (LMeta 54) (LMeta 55) emptyAssumptions
         in case
              solveLevelConstraintsFor
                (Set.fromList [54, 55])
                [ constraint (LParam 0) (LMeta 54)
                , constraint (LParam 1) (LMeta 55)
                , constrained (LMeta 54) (LParam 1) authenticated
                ]
            of
              Right solution ->
                Map.lookup 54 (lsAssignments solution) == Just (LParam 0)
                  && Map.lookup 55 (lsAssignments solution) == Just (LParam 1)
                  && null (lsResidual solution)
              Left _ -> False
      selectedMetaInAssumptionCannotHideUnsatisfiableBody =
        let assumptions = insertAssumption (LMeta 56) LZero emptyAssumptions
            impossibleUnderSelectedAssumption =
              LevelConstraint 0 one LZero origin assumptions
         in inferPrincipalLevelsFor (Set.singleton 56) [impossibleUnderSelectedAssumption]
              == Unsatisfiable
      explosiveAssignmentGraphFailsClosed =
        let depth = 24
            targets = Set.fromList [60 .. 60 + depth]
            chain =
              [ constraint
                  (levelAdd (LMeta (meta + 1)) (LMeta (meta + 1)))
                  (LMeta meta)
              | meta <- [60 .. 60 + depth - 1]
              ]
                ++ [constraint neutralP (LMeta (60 + depth))]
         in case solveLevelConstraintsFor targets chain of
              Left LevelResourceLimit {} -> True
              _ -> False
      contradictoryAssumptionsDominateTrivialQueries =
        proveLevelLeq impossible LZero LZero == ContradictoryAssumptions
      resourceLimitDominatesBlockedMetavariables =
        let crowded =
              foldr
                (\index ->
                  insertAssumption
                    (LNeutral
                      (NeutralLevelSymbol
                        (T.pack ("resource:" ++ show index))
                        (replicate 100 LZero)))
                    (LMeta 999))
                emptyAssumptions
                [1 :: Int .. 1000]
         in proveLevelLeq crowded (LMeta 1000) (LMeta 1001)
              == IndeterminateResourceLimit
      incrementalAssignmentGraphFailsBeforeExpansion =
        let extendOne (Right (assignments, dependents, budget, _)) meta =
              extendLevelAssignmentGraphWithBudget
                assignments
                dependents
                budget
                (Map.singleton meta (levelAdd (LMeta (meta + 1)) (LMeta (meta + 1))))
            extendOne failure _ = failure
         in case
              foldl
                extendOne
                (Right
                  ( Map.empty
                  , Map.empty
                  , emptyLevelAssignmentGraphBudget
                  , Set.empty
                  ))
                [100 .. 130]
            of
              Left (LevelAssignmentGraphResourceLimit _) -> True
              _ -> False
      outsidePortableClass =
        inferPrincipalLevelsFor
          (Set.singleton 34)
          [ constraint
              (LNeutral (NeutralLevelSymbol "test:f" [neutralP]))
              (levelMax (levelAdd (LMeta 34) neutralV) neutralW)
          ]
          == OutsidePortableInferenceFragment
      hugeFinite = finiteLevel (toInteger (maxBound :: Int) + 1)
      rigidPairs =
        [ (LVar 0, LVar 1)
        , (LField 100 "left", LField 101 "right")
        , (LProjection 200 ["level"], LProjection 201 ["nested", "level"])
        , (LParam 0, LParam 1)
        ]
      boundedExpressions a b =
        let atoms = [LZero, LOmega, a, b]
         in nub
              ( map normalizeLevel
                  ( atoms
                      ++ map levelSucc atoms
                      ++ [levelAdd x y | x <- atoms, y <- atoms]
                      ++ [levelMax x y | x <- atoms, y <- atoms]
                  )
              )
      sampleOrdinals :: [(Integer, Integer)]
      sampleOrdinals =
        [ (0, 0)
        , (0, 1)
        , (0, 2)
        , (1, 0)
        , (1, 1)
        , (2, 0)
        -- The open-addition cases can add one omega coefficient. Keep a
        -- strictly larger sample available than every generated expression,
        -- plus one further coefficient for the strict @succ u <= v@ edge.
        -- Without that final point the bounded reference oracle incorrectly
        -- labels @u <= omega + omega@ as entailed: its first countermodel is
        -- @u = 3*omega, v = 4*omega@.
        , (3, 0)
        , (4, 0)
        ]
      exhaustiveFailures =
        [ "solver/reference mismatch for " ++ show (a, b) ++ " under " ++ show edges ++ ": " ++ show lhs ++ " <= " ++ show rhs
        | (a, b) <- rigidPairs
        , let rigidExpressions = boundedExpressions a b
              valuations =
                [ Map.fromList [(a, aValue), (b, bValue)]
                | aValue <- sampleOrdinals
                , bValue <- sampleOrdinals
                ]
              assumptionSets =
                [ []
                , [(a, b)]
                , [(b, a)]
                , [(a, b), (b, a)]
                , [(levelSucc a, b)]
                , [(a, LOmega)]
                , [(LOmega, a)]
                ]
        , edges <- assumptionSets
        , lhs <- rigidExpressions
        , rhs <- rigidExpressions
        , let assumptions = foldr (uncurry insertAssumption) emptyAssumptions edges
              expected =
                all
                  ( \valuation ->
                      not (all (referenceLeq valuation) edges)
                        || referenceLeq valuation (lhs, rhs)
                  )
                  valuations
              actual = proveLevelLeq assumptions lhs rhs == Proved
        , expected /= actual
        ]
      checks =
        [ ("finite successor canonicalizes", normalizeLevel (LSucc (finiteLevel (2 :: Integer))) == finiteLevel (3 :: Integer))
        , ("constructor NF orders atoms before additive forms", normalizeLevel neutralU < normalizeLevel (levelAdd neutralU one))
        , ("constructor NF orders closed forms before atoms", normalizeLevel omegaPlusOne < normalizeLevel neutralU)
        , ("constructor NF orders additive forms before maxima", normalizeLevel (levelAdd neutralU one) < normalizeLevel (levelMax neutralU one))
        , ("constructor NF orders maxima before metas", normalizeLevel (levelMax neutralU one) < LMeta 99)
        , ("one plus omega commutes", onePlusOmega == omegaPlusOne)
        , ("omega plus one remains above omega", proveLevelLeq emptyAssumptions omegaPlusOne LOmega == Disproved)
        , ("finite levels are below omega", proveLevelLeq emptyAssumptions (finiteLevel (100 :: Integer)) LOmega == Proved)
        , ("successor self-containment is disproved", proveLevelLeq emptyAssumptions (levelSucc u) u == Disproved)
        , ("max introduction left", proveLevelLeq emptyAssumptions u (levelMax u v) == Proved)
        , ("zero is the identity of max", levelMax LZero u == u)
        , ("max elimination uses both arms", proveLevelLeq bounded (levelMax u one) LOmega == Proved)
        , ("max elimination recursively uses scoped arm bounds", proveLevelLeq maxBoundedByAssumptions (levelMax u v) (LVar 2) == Proved)
        , ("left-max assumptions expose both atomic arm bounds", proveLevelLeq maxBoundAssumption u (LVar 2) == Proved && proveLevelLeq maxBoundAssumption v (LVar 2) == Proved)
        , ("consistent assumption cycle proves equality", proveLevelLeq cyc u v == Proved && proveLevelLeq cyc v u == Proved)
        , ("consistent equality cycle remains satisfiable", assumptionsConsistent cyc)
        , ("strict self-cycle is unsatisfiable", not (assumptionsConsistent impossible))
        , ("rigid equality canonicalization preserves strict-cycle rejection", not (assumptionsConsistent equalityConstrainedImpossible))
        , ("assumptions close through successor", proveLevelLeq ordered (levelSucc u) (levelSucc v) == Proved)
        , ("atomic rigid assumptions close by graph reachability", proveLevelLeq atomicChain u (LVar 2) == Proved)
        , ("atomic reachability proves a right-side maximum", proveLevelLeq atomicMaxEntailed u (levelMax v (LVar 2)) == Proved)
        , ("atomic right-side maximum has a graph countermodel", proveLevelLeq atomicMaxCountermodel (LVar 2) (levelMax u v) == Disproved)
        , ("disconnected compound assumptions do not enter an atomic zero query", proveLevelLeq disconnectedCompoundAssumption u LZero == Disproved)
        , ("open natural addition preserves omega", proveLevelLeq emptyAssumptions LOmega (levelAdd u LOmega) == Proved)
        , ("open natural coefficient can exceed omega", proveLevelLeq emptyAssumptions (levelAdd u LOmega) LOmega == Disproved)
        , ("adding one is successor", levelAdd one u == levelSucc u)
        , ("open natural addition commutes", levelAdd u v == levelAdd v u)
        , ("open natural addition associates", levelAdd (levelAdd u v) one == levelAdd u (levelAdd v one))
        , ("scoped field identities do not alias by label", proveLevelLeq emptyAssumptions (LField 0 "k") (LField 1 "k") == Disproved)
        , ("unresolved level meta blocks", proveLevelLeq emptyAssumptions m LOmega == Blocked [0])
        , ("level-meta lower bounds choose the least solution", assignedThree solveForward)
        , ("level-meta solving is order independent", all (== solveForward) metaSolutions)
        , ("level-meta occurs checks reject self containment", occursRejected)
        , ("reflexive level-meta constraints are tautologies", reflexiveAccepted)
        , ("recursive max lower bounds have a principal solution", recursiveMaxAccepted)
        , ("embedded max constraints choose their unique least solution", embeddedMaxLeast)
        , ("embedded natural-add constraints choose their unique least solution", embeddedAddLeast)
        , ("embedded finite additions subtract the closed offset", embeddedFiniteAddLeast)
        , ("incomparable embedded minima remain residual", embeddedIncomparableRemainsResidual)
        , ("max introduction discharges without assigning level metas", metaMaxIntroductionAccepted)
        , ("hidden declaration parameters are valid principal lower bounds", rigidParameterAssigned)
        , ("principal assignments survive unrelated residual constraints", solvedAssignmentSurvivesResidual)
        , ("duplicate universe judgments do not duplicate residual obligations", duplicateResidualsAreCanonical)
        , ("mutual max lower-bound cycles have a closed principal solution", mutualMaxCycleCanonical)
        , ("successor-bearing mutual cycles fail the occurs check", successorCycleRejected)
        , ("rigid neutral natural addition distributes over max", proveLevelLeq emptyAssumptions naturalDistributionLeft naturalDistributionRight == Proved && proveLevelLeq emptyAssumptions naturalDistributionRight naturalDistributionLeft == Proved)
        , ("rigid neutral max is dominated by successor", proveLevelLeq emptyAssumptions (levelMax neutralU (levelSucc neutralU)) (levelSucc neutralU) == Proved)
        , ("principal inference cancels common natural-add terms", additiveCancellationPrincipal)
        , ("principal inference cancels successor contexts", successorCancellationPrincipal)
        , ("principal assignments compose through later substitutions", principalAssignmentsComposeWithoutRevision)
        , ("principal assignments cannot be revised by a later join", principalAssignmentsRejectRevision)
        , ("incremental assignment graph tracks transitive dependents", incrementalAssignmentGraphTracksTransitiveDependents)
        , ("incremental assignment graph refines a flexible alias without revision", incrementalAssignmentGraphRefinesFlexibleAlias)
        , ("incremental assignment budget matches a full rebuild", incrementalAssignmentBudgetMatchesFullRebuild)
        , ("exact assignment graph updates are constant-state no-ops", exactAssignmentGraphUpdateIsANoOp)
        , ("principal inference detects incomparable max minima", noPointwiseLeastClass)
        , ("max-split certificates satisfy the complete constraint system", maxSplitWitnessChecksCompleteSystem)
        , ("single-meta max inference retains a rigid symbolic lower bound", rigidMaxArmHasSymbolicPrincipal)
        , ("unconstrained selected meta has checked zero principal", unconstrainedMetaHasCheckedZeroPrincipal)
        , ("upper-only selected meta has checked zero principal", upperOnlyMetaHasCheckedZeroPrincipal)
        , ("selected inference preserves unrelated rigid proof obligations", selectedInferencePreservesUnselectedProofObligations)
        , ("selected-meta chains are solved as one principal system", selectedChainSolvedTogether)
        , ("selected-meta equality SCCs have the pointwise-zero principal solution", selectedEqualitySccSolvedTogether)
        , ("selected inference retains an unselected meta dependency", selectedDependencyRetainsUnselectedMeta)
        , ("selected equality preserves the resulting rigid proof obligation", selectedEqualityLeavesRigidProofObligation)
        , ("solving metas rewrites authenticated constraint assumptions", solvedMetasRewriteConstraintAssumptions)
        , ("selected metas in assumptions participate in full satisfiability recheck", selectedMetaInAssumptionCannotHideUnsatisfiableBody)
        , ("selected-meta assignment DAGs fail closed before exponential materialization", explosiveAssignmentGraphFailsClosed)
        , ("contradictory assumptions dominate trivially true queries", contradictoryAssumptionsDominateTrivialQueries)
        , ("resource limits dominate blocked metavariables", resourceLimitDominatesBlockedMetavariables)
        , ("incremental assignment graphs fail before exponential materialization", incrementalAssignmentGraphFailsBeforeExpansion)
        , ("principal inference classifies opaque meta contexts outside the portable fragment", outsidePortableClass)
        , ("large finite levels remain exact", proveLevelLeq emptyAssumptions hugeFinite LOmega == Proved && hugeFinite /= LZero)
        , ("renderer keeps Type0 implicit", renderTerm (CSort LZero) == "Type")
        , ("renderer prints higher finite universes explicitly", renderTerm (CSort one) == "Type 1")
        , ("verbose renderer classifies Type0 in Type1", renderJudgment (CSort LZero) (CSort one) == "Type : Type 1")
        , ("verbose renderer never prints Type : Type", renderJudgment (CSort LZero) (CSort one) /= "Type : Type")
        ]
      failures = [label | (label, False) <- checks] ++ exhaustiveFailures
      ok = null failures
  unless ok $ do
    putStrLn "universeLevelDomain FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
  pure ok
  where
    referenceLeq valuation (lhs, rhs) = referenceLevel valuation lhs <= referenceLevel valuation rhs

    referenceLevel valuation = \case
      LZero -> (0, 0)
      LFinite n -> (0, n)
      LOmega -> (1, 0)
      LSucc a -> let (c, n) = referenceLevel valuation a in (c, n + 1)
      LAdd a b ->
        let (ac, an) = referenceLevel valuation a
            (bc, bn) = referenceLevel valuation b
         in (ac + bc, an + bn)
      LMax a b -> max (referenceLevel valuation a) (referenceLevel valuation b)
      rigid@LVar {} -> Map.findWithDefault (0, 0) rigid valuation
      rigid@LField {} -> Map.findWithDefault (0, 0) rigid valuation
      rigid@LProjection {} -> Map.findWithDefault (0, 0) rigid valuation
      rigid@LParam {} -> Map.findWithDefault (0, 0) rigid valuation
      LMeta ident -> error ("referenceLevel: unexpected level meta " ++ show ident)

-- | §30.2.1A: cumulative subsumption is explicit in KCore and carries a
-- replayable, scope-checked universe certificate.  These are constructor-level
-- properties so a frontend regression cannot hide behind source inference.
universeLiftEvidenceDomain :: IO Bool
universeLiftEvidenceDomain = do
  let u = LParam 0
      v = LParam 1
      w = LParam 2
      uvAssumptions = insertAssumption u v emptyAssumptions
      vwAssumptions = insertAssumption v w emptyAssumptions
      uv = solverUniverseEvidence uvAssumptions u v
      vw = solverUniverseEvidence vwAssumptions v w
      irrelevantAssumptions = insertAssumption u v emptyAssumptions
      assumptionFree = solverUniverseEvidence irrelevantAssumptions LZero w
      neededDependencyRetained = case uv of
        UniverseEvidence [UniverseEvidenceStep {uesAssumptions = dependencies}] ->
          dependencies == [(u, v)]
        _ -> False
      irrelevantDependencyOmitted = case assumptionFree of
        UniverseEvidence [UniverseEvidenceStep {uesAssumptions = dependencies}] ->
          null dependencies
        _ -> False
      specializedUv =
        mapUniverseEvidenceLevels
          (\level -> if level == u then LZero else level)
          uv
      specializedDependencyOmitted = case specializedUv of
        UniverseEvidence [UniverseEvidenceStep {uesAssumptions = dependencies}] ->
          null dependencies
        _ -> False
      payload = CGlob prelUnit
      identity = universeLift (solverUniverseEvidence emptyAssumptions u u) payload == payload
      composed = universeLift vw (universeLift uv payload)
      composedCanonical = case composed of
        CUniverseLift from to (UniverseEvidence steps) inner ->
          from == u
            && to == w
            && inner == payload
            && length steps == 2
        _ -> False
      composedAssumptions = insertAssumption v w uvAssumptions
      composedValid = null (validateUniverseLiftEvidenceUnder composedAssumptions 0 3 composed)
      malformed = CUniverseLift u w (UniverseEvidence []) payload
      malformedRejected = not (null (validateUniverseLiftEvidence 0 3 malformed))
      forgedAssumptions = insertAssumption u v emptyAssumptions
      forged = universeLift (solverUniverseEvidence forgedAssumptions u v) payload
      forgedSelfAuthorizationRejected =
        not (null (validateUniverseLiftEvidence 0 3 forged))
      outOfScopeRejected =
        not
          ( null
              (validateUniverseLiftEvidence 0 1 (universeLift uv payload))
          )
      sourceUnit =
        compileSourceWithPrelude
          "universe-lift-source.kp"
          ( T.unlines
              [ "module universe_lift_source"
              , "Small : Type0"
              , "let Small = Int"
              , "widen : Type1"
              , "let widen = Small"
              ]
          )
      sourceState = cuState sourceUnit
      sourceOwner = GName (ModuleName ["universe_lift_source"]) "widen"
      sourceLifted = case Map.lookup sourceOwner (csCoreBodies sourceState) of
        Just CUniverseLift {} -> True
        _ -> False
      sourceErrorFree = not (any isError (cuDiags sourceUnit))
      sourceLiftEvidenceValid =
        and
          [ null (validateUniverseLiftEvidence 0 universeArity body)
          | (owner, body) <- Map.toList (csCoreBodies sourceState)
          , let universeArity =
                  maybe
                    0
                    (dutParameterCount . gdUniverses)
                    (Map.lookup owner (csGlobals sourceState))
          ]
      syntheticModule = ModuleName ["universe_lift_composed_kcore"]
      syntheticOwner = GName syntheticModule "raise"
      proofType lower upper =
        CApp Expl
          (CApp Expl (CGlobal prelLevelLe []) (CLevel lower))
          (CLevel upper)
      syntheticType =
        CPiEvidenceM Ordinary FormationOrdinary Impl Q0 False "uv" (Just (u, v)) BinderSourceWritten (proofType u v) $
          CPiEvidenceM Ordinary FormationOrdinary Impl Q0 False "vw" (Just (v, w)) BinderSourceWritten (proofType v w) $
            CPiFormedM Ordinary FormationOrdinary Expl QW False "A" (CSort u) (CSort w)
      syntheticBody =
        CLamM Ordinary Impl Q0 "uv" $
          CLamM Ordinary Impl Q0 "vw" $
            CLamM Ordinary Expl QW "A" (universeLift vw (universeLift uv (CVar 0)))
      syntheticTelescope =
        DeclarationUniverseTelescope 3 False
      sourceEval = EvalCtx (Globals (csGlobals sourceState)) (csMetas sourceState) False mempty
      syntheticDefinition =
        globalDefWithCoreBody syntheticBody
          ( globalDefWithCoreType syntheticType
              ( globalDefWithUniverses syntheticTelescope
                  (GlobalDef (eval sourceEval [] syntheticType) Nothing True)
              )
          )
      syntheticGlobals = Map.insert syntheticOwner syntheticDefinition (csGlobals sourceState)
      sourceConstructorInterfaces =
        Map.map
          (\info ->
             KCoreConstructorInfo
               (ciData info)
               (ciUniverses info)
               (ciType info)
               (ciSourceFields info))
          (csCtors sourceState)
      composedKCoreRoundTrip = do
        dump <-
          renderKCoreModule
            syntheticModule
            sourceEval
            syntheticGlobals
            (Map.singleton syntheticOwner syntheticBody)
            (Map.empty :: Map.Map GName KCoreDataInfo)
            sourceConstructorInterfaces
            []
        parsed <-
          parseAndVerifyKCoreTextWithEnvironment
            sourceEval
            (csGlobals sourceState)
            (Map.map (\info -> KCoreDataInfo (diCtors info) (diParamCount info)) (csDatas sourceState))
            sourceConstructorInterfaces
            dump
        let canonical = printCanonicalKCoreText parsed
        reparsed <-
          parseAndVerifyKCoreTextWithEnvironment
            sourceEval
            (csGlobals sourceState)
            (Map.map (\info -> KCoreDataInfo (diCtors info) (diParamCount info)) (csDatas sourceState))
            sourceConstructorInterfaces
            canonical
        pure
          ( "arithmetic [0, 1]" `T.isInfixOf` canonical
              && "certificate(" `T.isInfixOf` canonical
              && printCanonicalKCoreText reparsed == canonical
          , canonical
          )
      runtimeIdentity =
        case
          ( eval (EvalCtx (Globals Map.empty) emptyMetas True Map.empty) [] composed
          , eval (EvalCtx (Globals Map.empty) emptyMetas True Map.empty) [] payload
          ) of
          (VGlobal g us [], VGlobal g' us' []) -> g == g' && us == us'
          _ -> False
      substitutedEvidence =
        substTopTermAt
          0
          (CLevel LOmega)
          ( CUniverseLift
              (LVar 0)
              (levelSucc (LVar 0))
              (solverUniverseEvidence (insertAssumption (LVar 0) (levelSucc (LVar 0)) emptyAssumptions) (LVar 0) (levelSucc (LVar 0)))
              (CSort (LVar 0))
          )
      substitutionTransportsLevelsAndEvidence =
        case substitutedEvidence of
          CUniverseLift from to (UniverseEvidence [UniverseEvidenceStep lower upper assumptions]) (CSort payloadLevel) ->
            from == LOmega
              && to == levelSucc LOmega
              && lower == LOmega
              && upper == levelSucc LOmega
              && null assumptions
              && payloadLevel == LOmega
          _ -> False
      substitutionReindexesInnerLevelIdentities =
        substTopTermAt
          1
          (CVar 0)
          (CPiFormedM Ordinary FormationOrdinary Expl QW False "inner" (CSort (LVar 1)) (CSort (LVar 2)))
          == CPiFormedM Ordinary FormationOrdinary Expl QW False "inner" (CSort (LVar 0)) (CSort (LVar 1))
      assumptionMetadataParticipatesInLevelTraversal =
        let metadataTerm =
              CPiEvidenceM Ordinary FormationOrdinary Impl Q0 False "proof"
                (Just (LMeta 88, LParam 0))
                BinderSourceWritten
                (CGlob prelUnit)
                ( CRecordTQ
                    [ RecordField
                        "fieldProof"
                        Ordinary
                        FormationOrdinary
                        Q0
                        (Just (LMeta 89, LParam 1))
                        (CGlob prelUnit)
                    ]
                )
         in sort (levelMetasOfTerm metadataTerm) == [88, 89]
              && sort (levelParamsOfTerm metadataTerm) == [0, 1]
      weakeningTransportsAssumptionLevelIdentities =
        let memberType =
              CPiEvidenceM Ordinary FormationOrdinary Expl QW False "x" Nothing
                BinderSourceWritten
                (CGlob prelUnit)
                ( CPiEvidenceM Ordinary FormationOrdinary Expl QW False "y" Nothing
                    BinderSourceWritten
                    (CGlob prelUnit)
                    ( CPiEvidenceM Ordinary FormationOrdinary Impl Q0 False "p"
                        (Just (LVar 1, LVar 2))
                        BinderSourceWritten
                        (CGlob prelUnit)
                        (CSort (LMax (LVar 0) (LVar 2)))
                    )
                )
            weakened = weakenTermUnderBinderAt 1 memberType
         in case weakened of
              CPiEvidenceM _ _ _ _ _ _ _ _ _
                (CPiEvidenceM _ _ _ _ _ _ _ _ _
                  (CPiEvidenceM _ _ _ _ _ _ (Just relation) _ _ (CSort resultLevel))) ->
                    relation == (LVar 2, LVar 3)
                      && resultLevel == LMax (LVar 0) (LVar 3)
              _ -> False
      checks =
        [ ("identity lifts normalize away", identity)
        , ("solver evidence retains assumptions required by its judgment", neededDependencyRetained)
        , ("solver evidence omits ambient assumptions irrelevant to its judgment", irrelevantDependencyOmitted)
        , ("evidence substitution removes dependencies made irrelevant by specialization", specializedDependencyOmitted)
        , ("nested lifts compose and retain both evidence dependencies", composedCanonical)
        , ("composed evidence replays at checkpoint", composedValid)
        , ("missing evidence fails closed", malformedRejected)
        , ("lift evidence cannot authorize itself with embedded assumptions", forgedSelfAuthorizationRejected)
        , ("out-of-scope universe evidence fails closed", outOfScopeRejected)
        , ("surface cumulativity elaborates to an explicit KCore lift", sourceLifted)
        , ("generalized source lifts retain replayable solver evidence", sourceErrorFree && sourceLiftEvidenceValid)
        , ("composed Core lifts emit scoped certificates and round trip", either (const False) fst composedKCoreRoundTrip)
        , ("lifts are runtime representation identity", runtimeIdentity)
        , ("term substitution transports embedded levels and lift evidence", substitutionTransportsLevelsAndEvidence)
        , ("term substitution reindexes later level identities", substitutionReindexesInnerLevelIdentities)
        , ("authenticated assumption metadata participates in level traversal", assumptionMetadataParticipatesInLevelTraversal)
        , ("term weakening transports embedded local level identities", weakeningTransportsAssumptionLevelIdentities)
        ]
      failures = [label | (label, False) <- checks]
  unless (null failures) $ do
    putStrLn "universeLiftEvidenceDomain FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
    putStrLn ("  source diagnostics=" ++ show (map dCode (cuDiags sourceUnit)))
    putStrLn ("  source body=" ++ maybe "<missing>" (T.unpack . renderTerm) (Map.lookup sourceOwner (csCoreBodies sourceState)))
    case composedKCoreRoundTrip of
      Left err -> putStrLn ("  composed KCore error=" ++ show err)
      Right (_, canonical) -> TIO.putStrLn canonical
  pure (null failures)

-- | U-G8 artifact boundary: an imported declaration must remain usable after
-- all source/checker state has been discarded. The opaque interface can only
-- be constructed by parsing and verifying its KCoreText artifact, and merging
-- two artifacts with the same semantic owner fails closed.
kcoreSourceFreeInterfaceDomain :: IO Bool
kcoreSourceFreeInterfaceDomain = do
  let metadata owner =
        " [languageVersion = \"kappa-v1\", compilerInterfaceVersion = \"1\", "
          <> "sourceModuleIdentity = \"" <> owner <> "\", "
          <> "typeLevelAlgebraVersion = \"1\", levelConstructorNormalizerVersion = \"1\", "
          <> "levelRigidEntailmentVersion = \"1\", levelPrincipalInferenceVersion = \"1\", "
          <> "levelCertificateVersion = \"1\"]"
      upstream =
        "kcore 1;\nmodule @artifact.up#100" <> metadata "artifact.up" <> " {\n"
          <> "  axiom ordinary @artifact.up.A#101 : Type 0;\n"
          <> "}\n"
      downstream =
        "kcore 1;\nmodule @artifact.down#200" <> metadata "artifact.down" <> " {\n"
          <> "  def ordinary @artifact.down.B#201 : Type 0 { body = @artifact.up.A#101; }\n"
          <> "}\n"
      transitive =
        "kcore 1;\nmodule @artifact.transitive#300" <> metadata "artifact.transitive" <> " {\n"
          <> "  axiom ordinary @artifact.transitive.y#301 : @artifact.down.B#201;\n"
          <> "}\n"
      localNominal =
        "kcore 1;\nmodule @artifact.local-cert#400" <> metadata "artifact.local-cert" <> " {\n"
          <> "  schema-certificate @schema:artifact.local-cert.T#401 for @artifact.local-cert.T#402 "
          <> "[checkerVersion = 1, typeLevelAlgebraVersion = 1, levelConstructorNormalizerVersion = 1, "
          <> "levelRigidEntailmentVersion = 1, levelPrincipalInferenceVersion = 1, "
          <> "levelCertificateVersion = 1, signatureHash = local, saturationArity = 0] {\n"
          <> "    roles = [];\n"
          <> "    clauseKinds = [sort_declaration, point_constructor, eliminator, computation_rule];\n"
          <> "    monotoneWitnesses = [];\n"
          <> "  }\n"
          <> "  data @artifact.local-cert.T#402 : Type 0 certificate @schema:artifact.local-cert.T#401 {\n"
          <> "    constructor @artifact.local-cert.C#403 : @artifact.local-cert.T#402;\n"
          <> "  }\n"
          <> "}\n"
      nominalConsumer =
        "kcore 1;\nmodule @artifact.local-cert-consumer#500" <> metadata "artifact.local-cert-consumer" <> " {\n"
          <> "  axiom ordinary @artifact.local-cert-consumer.x#501 : @artifact.local-cert.T#402;\n"
          <> "}\n"
      result = do
        upstreamInterface <- parseAndVerifyKCoreInterface upstream
        downstreamInterface <-
          parseAndVerifyKCoreInterfaceWithInterfaces [upstreamInterface] downstream
        transitiveFile <- parseKCoreText transitive
        verifyKCoreTextWithInterfaces [downstreamInterface] transitiveFile
        downstreamFile <- parseKCoreText downstream
        case verifyKCoreTextWithInterfaces [upstreamInterface, upstreamInterface] downstreamFile of
          Left _ -> pure ()
          Right () -> Left (KCoreTextError "unit" "duplicate imported identities were accepted")
        localNominalInterface <- parseAndVerifyKCoreInterface localNominal
        nominalConsumerFile <- parseKCoreText nominalConsumer
        case verifyKCoreTextWithInterfaces [localNominalInterface] nominalConsumerFile of
          Left KCoreTextError {kcteCode = "E_KCORE_SCHEMA_CERTIFICATE_INVALID"} -> pure ()
          Left err ->
            Left
              ( KCoreTextError
                  "unit"
                  ("imported local schema certificate failed with the wrong diagnostic: " <> kcteCode err)
              )
          Right () -> Left (KCoreTextError "unit" "an imported local schema certificate was trusted")
  case result of
    Right () -> pure True
    Left err -> do
      putStrLn ("kcoreSourceFreeInterfaceDomain FAILED: " <> show err)
      pure False

-- | §30.2.0A: KCoreText is an untrusted, canonical typed checkpoint, not a
-- presentation dump. These pins cover identity completeness, universe-spine
-- arity, extension ownership, deterministic dependency ordering, and local
-- alpha-normalization independently of the design-bundle fixtures.
kcoreTextCanonicalDomain :: IO Bool
kcoreTextCanonicalDomain = do
  let envUnit = compileSourceWithPrelude "kcore-environment.kp" "module kcore_environment\n"
      envState = cuState envUnit
      envEval = EvalCtx (Globals (csGlobals envState)) (csMetas envState) False mempty
      envConstructorInterfaces =
        Map.map
          (\info ->
             KCoreConstructorInfo
               (ciData info)
               (ciUniverses info)
               (ciType info)
               (ciSourceFields info))
          (csCtors envState)
      envDataInterfaces =
        Map.map
          (\info -> KCoreDataInfo (diCtors info) (diParamCount info))
          (csDatas envState)
      parseVerified =
        parseAndVerifyKCoreTextWithEnvironment
          envEval
          (csGlobals envState)
          envDataInterfaces
          envConstructorInterfaces
      semanticVersionMetadata =
        ", typeLevelAlgebraVersion = \"1\""
          <> ", levelConstructorNormalizerVersion = \"1\""
          <> ", levelRigidEntailmentVersion = \"1\""
          <> ", levelPrincipalInferenceVersion = \"1\""
          <> ", levelCertificateVersion = \"1\""
      header identity extensions =
        "kcore 1;\nmodule @" <> identity <> "#1 ["
          <> "languageVersion = \"kappa-v1\", "
          <> "compilerInterfaceVersion = \"1\", "
          <> "sourceModuleIdentity = \"" <> identity <> "\""
          <> semanticVersionMetadata
          <> extensions <> "] {\n"
      footer = "}\n"
      kcoreTypeIdentity =
        canonicalIdentityHex
          "KCoreTypeNF"
          (T.intercalate "\n" ["", "", "", "Type 0"])
      malformedOrdinalRepresentationCertificate =
        header "test.representation-certificate" ""
          <> "representation-certificate @certificate.test.representation#100 "
          <> "[checkerVersion = 1, certificateVersion = 1, kind = ordinal] "
          <> "for Type 0 { "
          <> "typeIdentity = string-value(\"" <> kcoreTypeIdentity <> "\"); "
          <> "sourceEvidenceIdentity = []; "
          <> "cardinalityExpression = term-value(Type 0); "
          <> "rankTerm = term-value(Type 0); "
          <> "unrankTerm = term-value(Type 0); "
          <> "unrankRankProof = term-value(Type 0); "
          <> "rankUnrankProof = term-value(Type 0); "
          <> "constructorEncoding = string-value(\"invalid\"); "
          <> "eliminatorSimulation = string-value(\"invalid\"); "
          <> "erasureView = []; "
          <> "profileRestrictions = []; "
          <> "}\n"
          <> footer
      representationCertificateParses =
        case parseKCoreText malformedOrdinalRepresentationCertificate of
          Right parsed ->
            kcoreRepresentationCertificateCount parsed == 1
              && case parseKCoreText (printCanonicalKCoreText parsed) of
                   Right reparsed ->
                     printCanonicalKCoreText reparsed
                       == printCanonicalKCoreText parsed
                   Left _ -> False
          Left _ -> False
      nominalCertificate identity familyId certificateId =
        "schema-certificate @schema:" <> identity <> ".T#" <> certificateId
          <> " for @" <> identity <> ".T#" <> familyId
          <> " [checkerVersion = 1, typeLevelAlgebraVersion = 1, levelConstructorNormalizerVersion = 1"
          <> ", levelRigidEntailmentVersion = 1, levelPrincipalInferenceVersion = 1"
          <> ", levelCertificateVersion = 1, signatureHash = local, saturationArity = 0] {\n"
          <> "  roles = [];\n"
          <> "  clauseKinds = [sort_declaration, point_constructor, eliminator, computation_rule];\n"
          <> "  monotoneWitnesses = [];\n"
          <> "}\n"
      constructorCollision =
        header "test.collision" ""
          <> nominalCertificate "test.collision" "2" "4"
          <> "data @test.collision.T#2 : Type 0 certificate @schema:test.collision.T#4 {\n"
          <> "  constructor @test.collision.C#1 : Type 0;\n}\n"
          <> footer
      missingNominalCertificate =
        header "test.missing-nominal-certificate" ""
          <> "data @test.missing-nominal-certificate.T#2 : Type 0 { }\n"
          <> footer
      missingNominalRole =
        header "test.missing-nominal-role" ""
          <> "data @test.missing-nominal-role.T#2 .{^u#0} : Type ^u#0 "
          <> "certificate @test.missing-nominal-role.certificate#3 { }\n"
          <> footer
      wrongLanguageVersion =
        T.replace
          "languageVersion = \"kappa-v1\""
          "languageVersion = \"kappa-v0\""
          unordered
      wrongCompilerInterfaceVersion =
        T.replace
          "compilerInterfaceVersion = \"1\""
          "compilerInterfaceVersion = \"2\""
          unordered
      versionedSchemaCertificate =
        header "test.schema-certificate-version" ""
          <> nominalCertificate "test.schema-certificate-version" "2" "4"
          <> "data @test.schema-certificate-version.T#2 : Type 0 "
          <> "certificate @schema:test.schema-certificate-version.T#4 { }\n"
          <> footer
      wrongSchemaCertificateVersion =
        T.replace
          "levelCertificateVersion = 1, signatureHash"
          "levelCertificateVersion = 2, signatureHash"
          versionedSchemaCertificate
      alternateSourceModuleIdentity =
        T.replace
          "sourceModuleIdentity = \"test.order\""
          "sourceModuleIdentity = \"test.source-package\""
          unordered
      constructorFieldHeader identity fields =
        header identity ""
          <> nominalCertificate identity "2" "4"
          <> "data @" <> identity <> ".T#2 : Type 1 certificate @schema:" <> identity <> ".T#4 {\n"
          <> "  constructor @" <> identity <> ".C#3 : "
          <> "((ordinary ordinary omega explicit value %x#0 : Type 0) -> Type 0) "
          <> "fields { " <> fields <> " };\n}\n"
          <> footer
      forgedConstructorFieldIdentity =
        constructorFieldHeader "test.constructor-field-forged"
          "@field:x#deadbeef = 0;"
      duplicateConstructorFieldPosition =
        constructorFieldHeader "test.constructor-field-duplicate-position"
          "@field:x#4b415050413a76313a4b436f72654669656c640078 = 0; @field:y#4b415050413a76313a4b436f72654669656c640079 = 0;"
      outOfRangeConstructorFieldPosition =
        constructorFieldHeader "test.constructor-field-out-of-range"
          "@field:x#4b415050413a76313a4b436f72654669656c640078 = 1;"
      arityMismatch =
        header "test.arity" ""
          <> "axiom ordinary @test.arity.A#2 .{^u#0} : Type ^u#0;\n"
          <> "def ordinary @test.arity.x#3 : Type 0 { body = @test.arity.A#2; }\n"
          <> footer
      unadvertisedExtension =
        header "test.extension" ""
          <> "decl-node \"example.vendor.node\" { }\n"
          <> footer
      advertisedExtension =
        header "test.extension" ""
          <> "extension example.vendor 1;\n"
          <> "decl-node \"example.vendor.node\" { }\n"
          <> footer
      crossModuleExtensionLeak =
        header "test.extension.owner" ""
          <> "extension example.vendor 1;\n"
          <> footer
          <> "module @test.extension.consumer#2 ["
          <> "languageVersion = \"kappa-v1\", "
          <> "compilerInterfaceVersion = \"1\", "
          <> "sourceModuleIdentity = \"test.extension.consumer\""
          <> semanticVersionMetadata
          <> "] {\n"
          <> "decl-node \"example.vendor.node\" { }\n"
          <> footer
      missingSemanticVersion =
        "kcore 1;\nmodule @test.missing-semantic-version#1 ["
          <> "languageVersion = \"kappa-v1\", "
          <> "compilerInterfaceVersion = \"1\", "
          <> "sourceModuleIdentity = \"test.missing-semantic-version\", "
          <> "typeLevelAlgebraVersion = \"1\", "
          <> "levelConstructorNormalizerVersion = \"1\", "
          <> "levelRigidEntailmentVersion = \"1\", "
          <> "levelPrincipalInferenceVersion = \"1\"] {\n"
          <> footer
      unsupportedAdvertisedExtension =
        header "test.unsupported-extension" ""
          <> "extension unregistered.vendor 1;\n"
          <> "decl-node \"unregistered.vendor.node\" { }\n"
          <> footer
      builtinExtensionBypass =
        header "test.builtin-extension-bypass" ""
          <> "def ordinary @test.builtin-extension-bypass.bad#2 : Type 1 { body = "
          <> "term-node \"impl.kappa.core.record-type\" { "
          <> "names = [string-value(\"x\")]; "
          <> "fields = [term-value(((ordinary ordinary omega explicit value %x#0 : Type 0) -> Type 0))]; }; }\n"
          <> footer
      forgedAscription =
        header "test.forged-ascription" ""
          <> "def ordinary @test.forged-ascription.bad#2 : Type 1 { body = "
          <> "apply ascribe Type 0 : ((ordinary ordinary omega explicit value %x#0 : Type 0) -> Type 1) "
          <> "(explicit Type 0); }\n"
          <> footer
      forgedTypedGenericResult =
        header "test.forged-generic-result" ""
          <> "extension impl.kappa 1;\n"
          <> "def ordinary @test.forged-generic-result.bad#2 : Type 1 { body = "
          <> "term-node \"impl.kappa.core.thunk\" { "
          <> "result-type = term-value(Type 1); value = term-value(Type 0); }; }\n"
          <> footer
      inconsistentConstraints =
        header "test.inconsistent-constraints" ""
          <> "axiom ordinary @test.inconsistent-constraints.A#2 .{^u#0} : Type ^u#0 "
          <> "where { succ(^u#0) <= ^u#0; };\n"
          <> footer
      obsoleteConstraintEvidence =
        header "test.obsolete-constraint-evidence" ""
          <> "def ordinary @test.obsolete-constraint-evidence.bad#2 : Type 0 { body = "
          <> "lift [0 <= 0 by constraint(0)] Type 0; }\n"
          <> footer
      localUniverseAlphaA =
        header "test.local-universe-alpha" ""
          <> "def ordinary @test.local-universe-alpha.value#2 : Type 1 { body = "
          <> "letrec { def ordinary %poly#7 .{^inner#12} : Type succ(^inner#12) "
          <> "{ body = Type ^inner#12; } } in Type 0; }\n"
          <> footer
      localUniverseAlphaB =
        header "test.local-universe-alpha" ""
          <> "def ordinary @test.local-universe-alpha.value#2 : Type 1 { body = "
          <> "letrec { def ordinary %renamed#33 .{^level#91} : Type succ(^level#91) "
          <> "{ body = Type ^level#91; } } in Type 0; }\n"
          <> footer
      disjointLocalReuseA =
        header "test.disjoint-local-alpha" ""
          <> "extension example.vendor 1;\n"
          <> "decl-node \"example.vendor.node\" { "
          <> "left = term-value(lambda (ordinary ordinary omega explicit value %x#7 : Type 0) { %x#7 }); "
          <> "right = term-value(lambda (ordinary ordinary omega explicit value %x#7 : Type 0) { %x#7 }); }\n"
          <> footer
      disjointLocalReuseB =
        header "test.disjoint-local-alpha" ""
          <> "extension example.vendor 1;\n"
          <> "decl-node \"example.vendor.node\" { "
          <> "left = term-value(lambda (ordinary ordinary omega explicit value %left#41 : Type 0) { %left#41 }); "
          <> "right = term-value(lambda (ordinary ordinary omega explicit value %right#70 : Type 0) { %right#70 }); }\n"
          <> footer
      dependencyOrderInput =
        header "test.dependency-order" ""
          <> "def ordinary @test.dependency-order.user#10 : Type 0 { body = @test.dependency-order.dependency#20; }\n"
          <> "axiom ordinary @test.dependency-order.dependency#20 : Type 0;\n"
          <> footer
      cycleOrderInput =
        header "test.cycle-order" ""
          <> "def ordinary @test.cycle-order.right#20 : Type 0 { body = @test.cycle-order.left#10; }\n"
          <> "def ordinary @test.cycle-order.left#10 : Type 0 { body = @test.cycle-order.right#20; }\n"
          <> footer
      structured =
        header "test.structured" ""
          <> "extension example.vendor 1;\n"
          <> "axiom ordinary @test.structured.level#2 : @std.typelevel.TypeLevel#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e547970654c6576656c;\n"
          <> "axiom ordinary @test.structured.F#3 : Type level-term(@test.structured.level#2);\n"
          <> "def ordinary @test.structured.value#4 : Type 1 { body = block {\n"
          <> "  let (ordinary ordinary omega explicit value %x#9 : Type 1) = Type 0;\n"
          <> "  letrec { def ordinary %again#8 : Type 1 { body = Type 0; } } in\n"
          <> "  case %x#9 : Type 1 { default { %x#9 } }\n"
          <> "}; }\n"
          <> "decl-node \"example.vendor.node\" { mode = ordinary; quantity = quantity-value(affine); explicitness = implicit; access = borrow; level = level-value(succ(0)); values = [string-value(\"x\"), integer-value(7)]; }\n"
          <> footer
      invalidLevelTerm =
        header "test.badlevel" ""
          <> "axiom ordinary @test.badlevel.notLevel#2 : Type 0;\n"
          <> "axiom ordinary @test.badlevel.F#3 : Type level-term(@test.badlevel.notLevel#2);\n"
          <> footer
      nonTotalLevelTerm =
        header "test.nontotal-level" ""
          <> "axiom ordinary @test.nontotal-level.F#2 : Type level-term("
          <> "letrec { def ordinary %loop#0 : @std.typelevel.TypeLevel#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e547970654c6576656c "
          <> "{ body = %loop#0; } } in %loop#0);\n"
          <> footer
      unavailableIdentity =
        header "test.unavailable" ""
          <> "axiom ordinary @test.unavailable.bad#2 : @missing.external.Type#deadbeef;\n"
          <> footer
      unrelatedLiftEvidence =
        header "test.badevidence" ""
          <> "axiom ordinary @test.badevidence.notProof#2 .{^u#0, ^v#1} : Type 0;\n"
          <> "def ordinary @test.badevidence.raise#3 .{^u#0, ^v#1} : "
          <> "((ordinary ordinary omega explicit value %A#0 : Type ^u#0) -> Type ^v#1) "
          <> "{ body = "
          <> "lambda (ordinary ordinary omega explicit value %A#0 : Type ^u#0) { "
          <> "lift [^u#0 <= ^v#1 by @test.badevidence.notProof#2] %A#0 }; }\n"
          <> footer
      forgedParametricLocalEvidence =
        header "test.forged-parametric-local-evidence" ""
          <> "def ordinary @test.forged-parametric-local-evidence.raise#2 .{^u#0, ^v#1} : "
          <> "((parametric ordinary 0 implicit value %fake#0 : "
          <> "apply @std.typelevel.LevelLe#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e4c6576656c4c65 "
          <> "(explicit term-node \"impl.kappa.level-value\" { level = level-value(^u#0); }, "
          <> "explicit term-node \"impl.kappa.level-value\" { level = level-value(^v#1); })) -> "
          <> "((ordinary ordinary omega explicit value %A#1 : Type ^u#0) -> Type ^v#1)) "
          <> "{ body = lambda (parametric ordinary 0 implicit value %fake#0 : "
          <> "apply @std.typelevel.LevelLe#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e4c6576656c4c65 "
          <> "(explicit term-node \"impl.kappa.level-value\" { level = level-value(^u#0); }, "
          <> "explicit term-node \"impl.kappa.level-value\" { level = level-value(^v#1); })) { "
          <> "lambda (ordinary ordinary omega explicit value %A#1 : Type ^u#0) { "
          <> "lift [^u#0 <= ^v#1 by %fake#0] %A#1 } }; }\n"
          <> footer
      proofBinderOriginModule generatedMarker =
        header "test.proof-binder-origin" ""
          <> "extension impl.kappa 1;\n"
          <> "axiom ordinary @test.proof-binder-origin.raise#2 .{^u#0, ^v#1} : "
          <> "((ordinary ordinary 0 implicit value" <> generatedMarker <> " %proof#0 : "
          <> "apply @std.typelevel.LevelLe#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e4c6576656c4c65 "
          <> "(explicit term-node \"impl.kappa.level-value\" { level = level-value(^u#0); }, "
          <> "explicit term-node \"impl.kappa.level-value\" { level = level-value(^v#1); })) -> Type 0);\n"
          <> footer
      sourceProofBinder = proofBinderOriginModule ""
      generatedProofBinder = proofBinderOriginModule " generated"
      forgedGeneratedOrdinaryBinder =
        header "test.forged-generated-ordinary-binder" ""
          <> "axiom ordinary @test.forged-generated-ordinary-binder.bad#2 : "
          <> "((ordinary ordinary omega explicit value generated %value#0 : Type 0) -> Type 0);\n"
          <> footer
      composedCertificate =
        header "test.composed-certificate" ""
          <> "extension impl.kappa 1;\n"
          <> "level-certificate @certificate.test.composed#100 .{^u#0, ^v#1, ^w#2} : ^u#0 <= ^w#2 "
          <> "where { ^u#0 <= ^v#1; ^v#1 <= ^w#2; } { "
          <> "trans { assumption(0); assumption(1); } }\n"
          <> "def ordinary @test.composed-certificate.raise#2 .{^u#0, ^v#1, ^w#2} : "
          <> "((ordinary ordinary 0 implicit value %uv#0 : "
          <> "apply @std.typelevel.LevelLe#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e4c6576656c4c65 "
          <> "(explicit term-node \"impl.kappa.level-value\" { level = level-value(^u#0); }, "
          <> "explicit term-node \"impl.kappa.level-value\" { level = level-value(^v#1); })) -> "
          <> "((ordinary ordinary 0 implicit value %vw#1 : "
          <> "apply @std.typelevel.LevelLe#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e4c6576656c4c65 "
          <> "(explicit term-node \"impl.kappa.level-value\" { level = level-value(^v#1); }, "
          <> "explicit term-node \"impl.kappa.level-value\" { level = level-value(^w#2); })) -> "
          <> "((ordinary ordinary omega explicit value %A#2 : Type ^u#0) -> Type ^w#2))) "
          <> "{ body = "
          <> "lambda (ordinary ordinary 0 implicit value %uv#0 : "
          <> "apply @std.typelevel.LevelLe#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e4c6576656c4c65 "
          <> "(explicit term-node \"impl.kappa.level-value\" { level = level-value(^u#0); }, "
          <> "explicit term-node \"impl.kappa.level-value\" { level = level-value(^v#1); })) { "
          <> "lambda (ordinary ordinary 0 implicit value %vw#1 : "
          <> "apply @std.typelevel.LevelLe#4b415050413a76313a4b436f7265476c6f62616c007374642e747970656c6576656c2e4c6576656c4c65 "
          <> "(explicit term-node \"impl.kappa.level-value\" { level = level-value(^v#1); }, "
          <> "explicit term-node \"impl.kappa.level-value\" { level = level-value(^w#2); })) { "
          <> "lambda (ordinary ordinary omega explicit value %A#2 : Type ^u#0) { "
          <> "lift [^u#0 <= ^w#2 by certificate(@certificate.test.composed#100.{^u#0, ^v#1, ^w#2})] %A#2 } } }; }\n"
          <> footer
      badCertificateAssumption =
        header "test.bad-certificate-assumption" ""
          <> "level-certificate @certificate.test.bad-assumption#100 .{^u#0, ^v#1} : ^u#0 <= ^v#1 "
          <> "where { ^u#0 <= ^v#1; } { assumption(1); }\n"
          <> footer
      redundantCertificateProof =
        header "test.canonical-certificate" ""
          <> "level-certificate @certificate.test.canonical#100 .{^u#0, ^v#1} : ^u#0 <= ^v#1 "
          <> "where { ^u#0 <= ^v#1; } { trans { refl ^u#0; assumption(0); } }\n"
          <> footer
      directCertificateProof =
        header "test.canonical-certificate" ""
          <> "level-certificate @certificate.test.canonical#100 .{^u#0, ^v#1} : ^u#0 <= ^v#1 "
          <> "where { ^u#0 <= ^v#1; } { assumption(0); }\n"
          <> footer
      parametricGlobalPromotion =
        header "test.parametric-global-promotion" ""
          <> "axiom parametric @test.parametric-global-promotion.hidden#2 : Type 0;\n"
          <> "def ordinary @test.parametric-global-promotion.bad#3 : Type 0 { "
          <> "body = @test.parametric-global-promotion.hidden#2; }\n"
          <> footer
      dependentParametricApplication =
        header "test.dependent-parametric-application" ""
          <> "axiom ordinary @test.dependent-parametric-application.typeIdentity#2 : "
          <> "((parametric parametric 0 explicit value %T#0 : Type 0) -> Type 0);\n"
          <> "def ordinary @test.dependent-parametric-application.bad#3 : "
          <> "((parametric parametric 0 explicit value %A#1 : Type 0) -> Type 0) { body = "
          <> "lambda (parametric parametric 0 explicit value %A#1 : Type 0) { "
          <> "apply @test.dependent-parametric-application.typeIdentity#2 (explicit %A#1) }; }\n"
          <> footer
      constantParametricApplication =
        header "test.constant-parametric-application" ""
          <> "axiom ordinary @test.constant-parametric-application.constant#2 : "
          <> "((parametric parametric 0 explicit value %T#0 : Type 0) -> @std.prelude.Int#4b415050413a76313a4b436f7265476c6f62616c007374642e7072656c7564652e496e74);\n"
          <> "def ordinary @test.constant-parametric-application.ok#3 : "
          <> "((parametric parametric 0 explicit value %A#1 : Type 0) -> @std.prelude.Int#4b415050413a76313a4b436f7265476c6f62616c007374642e7072656c7564652e496e74) { body = "
          <> "lambda (parametric parametric 0 explicit value %A#1 : Type 0) { "
          <> "apply @test.constant-parametric-application.constant#2 (explicit %A#1) }; }\n"
          <> footer
      captureAvoidingDependentApplication =
        header "test.capture-avoiding-dependent-application" ""
          <> "axiom ordinary @test.capture-avoiding-dependent-application.select#2 : "
          <> "((parametric parametric 0 explicit value %A#0 : Type 0) -> "
          <> "((ordinary ordinary omega implicit value %proof#1 : %A#0) -> "
          <> "((ordinary ordinary omega explicit value %value#2 : %A#0) -> %A#0)));\n"
          <> "def ordinary @test.capture-avoiding-dependent-application.use#3 : "
          <> "((parametric parametric 0 explicit value %A#2 : Type 0) -> "
          <> "((ordinary ordinary omega implicit value %proof#3 : %A#2) -> "
          <> "((ordinary ordinary omega explicit value %value#4 : %A#2) -> %A#2))) { body = "
          <> "lambda (parametric parametric 0 explicit value %A#2 : Type 0) { "
          <> "lambda (ordinary ordinary omega implicit value %proof#3 : %A#2) { "
          <> "lambda (ordinary ordinary omega explicit value %value#4 : %A#2) { "
          <> "apply @test.capture-avoiding-dependent-application.select#2 "
          <> "(explicit %A#2, implicit %proof#3, explicit %value#4) } } }; }\n"
          <> footer
      unordered =
        header "test.order" ""
          <> "axiom ordinary @test.order.z#20 : Type 0;\n"
          <> "def ordinary @test.order.id#10 .{^u#0} : "
          <> "((parametric parametric 0 explicit value %A#9 : Type ^u#0) -> "
          <> "((ordinary ordinary omega explicit value %x#5 : %A#9) -> %A#9)) { "
          <> "body = lambda (parametric parametric 0 explicit value %A#9 : Type ^u#0) { "
          <> "lambda (ordinary ordinary omega explicit value %x#5 : %A#9) { %x#5 } }; }\n"
          <> footer
      alphaRenamed =
        header "test.order" ""
          <> "axiom ordinary @test.order.z#20 : Type 0;\n"
          <> "def ordinary @test.order.id#10 .{^different#41} : "
          <> "((parametric parametric 0 explicit value %Carrier#70 : Type ^different#41) -> "
          <> "((ordinary ordinary omega explicit value %value#61 : %Carrier#70) -> %Carrier#70)) { "
          <> "body = lambda (parametric parametric 0 explicit value %Carrier#70 : Type ^different#41) { "
          <> "lambda (ordinary ordinary omega explicit value %value#61 : %Carrier#70) { %value#61 } }; }\n"
          <> footer
      rejectedWith code source = case parseVerified source of
        Left err -> kcteCode err == code
        Right _ -> False
      parses source = either (const False) (const True) (parseKCoreText source)
      canonical = printCanonicalKCoreText <$> parseVerified unordered
      canonicalStable = do
        first <- canonical
        parsed <- parseVerified first
        pure (printCanonicalKCoreText parsed == first)
      canonicalOrdered = case canonical of
        Right text ->
          let (_, afterId) = T.breakOn "@test.order.id#10" text
           in not (T.null afterId) && "@test.order.z#20" `T.isInfixOf` afterId
        Left _ -> False
      structuredStable = do
        first <- parseVerified structured
        let canonicalText = printCanonicalKCoreText first
        second <- parseVerified canonicalText
        pure (printCanonicalKCoreText second == canonicalText)
      negativeIntegerStable = do
        first <-
          parseVerified
            (T.replace "integer-value(7)" "integer-value(-7)" structured)
        let canonicalText = printCanonicalKCoreText first
        second <- parseVerified canonicalText
        pure (printCanonicalKCoreText second == canonicalText)
      canonicalLocals = case canonical of
        Right text ->
          "%v#0" `T.isInfixOf` text
            && "%v#1" `T.isInfixOf` text
            && not ("%A#9" `T.isInfixOf` text)
            && not ("%x#5" `T.isInfixOf` text)
        Left _ -> False
      alphaStable = do
        original <- parseVerified unordered
        renamed <- parseVerified alphaRenamed
        pure
          ( printCanonicalKCoreText original == printCanonicalKCoreText renamed
              && semanticHashKCoreText original == semanticHashKCoreText renamed
          )
      localUniverseAlphaStable = do
        first <- parseVerified localUniverseAlphaA
        second <- parseVerified localUniverseAlphaB
        pure
          ( printCanonicalKCoreText first == printCanonicalKCoreText second
              && semanticHashKCoreText first == semanticHashKCoreText second
          )
      disjointLocalAlphaStable = do
        first <- parseVerified disjointLocalReuseA
        second <- parseVerified disjointLocalReuseB
        pure
          ( printCanonicalKCoreText first == printCanonicalKCoreText second
              && semanticHashKCoreText first == semanticHashKCoreText second
          )
      declarationAppearsBefore firstRef secondRef source = case printCanonicalKCoreText <$> parseVerified source of
        Right text ->
          let (_, fromFirst) = T.breakOn firstRef text
           in not (T.null fromFirst) && secondRef `T.isInfixOf` fromFirst
        Left _ -> False
      certificateProofCanonical = do
        redundant <- parseVerified redundantCertificateProof
        direct <- parseVerified directCertificateProof
        pure
          ( printCanonicalKCoreText redundant == printCanonicalKCoreText direct
              && semanticHashKCoreText redundant == semanticHashKCoreText direct
          )
      proofBinderOriginIsSemantic = do
        sourceWritten <- parseVerified sourceProofBinder
        generated <- parseVerified generatedProofBinder
        pure
          ( printCanonicalKCoreText sourceWritten /= printCanonicalKCoreText generated
              && semanticHashKCoreText sourceWritten /= semanticHashKCoreText generated
              && " value generated %v#0" `T.isInfixOf` printCanonicalKCoreText generated
          )
      checks =
        [ ("constructor identities participate in stable-id validation", rejectedWith "E_KCORE_TEXT_INVALID" constructorCollision)
        , ("every KCore nominal declaration selects a certificate", not (parses missingNominalCertificate))
        , ("every KCore nominal universe binder records its effective role", not (parses missingNominalRole))
        , ("all semantic-version pins are mandatory", rejectedWith "E_KCORE_TEXT_INVALID" missingSemanticVersion)
        , ("language version metadata is checked, not merely present", rejectedWith "E_KCORE_TEXT_UNSUPPORTED_VERSION" wrongLanguageVersion)
        , ("compiler-interface version metadata is checked, not merely present", rejectedWith "E_KCORE_TEXT_UNSUPPORTED_VERSION" wrongCompilerInterfaceVersion)
        , ("schema certificates pin all semantic-layer versions", rejectedWith "E_KCORE_SCHEMA_CERTIFICATE_INVALID" wrongSchemaCertificateVersion)
        , ( "source-module metadata is opaque provenance and remains semantic"
          , case (parseVerified unordered, parseVerified alternateSourceModuleIdentity) of
              (Right original, Right alternate) ->
                semanticHashKCoreText original /= semanticHashKCoreText alternate
              _ -> False
          )
        , ("constructor field identities are authenticated", parses forgedConstructorFieldIdentity && rejectedWith "E_KCORE_TEXT_INVALID" forgedConstructorFieldIdentity)
        , ("constructor field payload positions are unique", parses duplicateConstructorFieldPosition && rejectedWith "E_KCORE_TEXT_INVALID" duplicateConstructorFieldPosition)
        , ("constructor field payload positions are in range", parses outOfRangeConstructorFieldPosition && rejectedWith "E_KCORE_TEXT_INVALID" outOfRangeConstructorFieldPosition)
        , ("declared global universe instantiation arity is exact", rejectedWith "E_KCORE_TEXT_INVALID" arityMismatch)
        , ("generic tags require an advertised owning extension", rejectedWith "E_KCORE_TEXT_INVALID" unadvertisedExtension)
        , ("advertised generic extension is accepted", either (const False) (const True) (parseVerified advertisedExtension))
        , ("extension ownership is module-local", rejectedWith "E_KCORE_TEXT_INVALID" crossModuleExtensionLeak)
        , ("an extension declaration cannot register an unsupported verifier", parses unsupportedAdvertisedExtension && rejectedWith "E_KCORE_TEXT_INVALID" unsupportedAdvertisedExtension)
        , ("parsed implementation nodes cannot bypass extension ownership", rejectedWith "E_KCORE_TEXT_INVALID" builtinExtensionBypass)
        , ("nested ascriptions cannot manufacture a function type", parses forgedAscription && rejectedWith "E_KCORE_TEXT_INVALID" forgedAscription)
        , ("typed generic nodes cannot forge their result type", parses forgedTypedGenericResult && rejectedWith "E_KCORE_TEXT_INVALID" forgedTypedGenericResult)
        , ("declaration constraint blocks are rejected outside certificates", not (parses inconsistentConstraints))
        , ("constraint-index lift evidence is rejected", not (parses obsoleteConstraintEvidence))
        , ("standard block/case/generic nodes and typed level-term round trip", either (const False) id structuredStable)
        , ("signed integer payloads round trip canonically", either (const False) id negativeIntegerStable)
        , ("level-term rejects a producer not typed by the TypeLevel semantic identity", rejectedWith "E_KCORE_TEXT_INVALID" invalidLevelTerm)
        , ("level-term independently rejects an unproved recursive producer", rejectedWith "E_KCORE_TEXT_INVALID" nonTotalLevelTerm)
        , ("unavailable external semantic identities reject", rejectedWith "E_KCORE_TEXT_INVALID" unavailableIdentity)
        , ("lift evidence must prove the asserted level relation", rejectedWith "E_KCORE_TEXT_INVALID" unrelatedLiftEvidence)
        , ("parametric proof binders cannot authorize level relations", rejectedWith "E_KCORE_TEXT_INVALID" forgedParametricLocalEvidence)
        , ("source-written and generated declaration proof binders have distinct semantic identity", either (const False) id proofBinderOriginIsSemantic)
        , ("only authenticated declaration constraints may carry generated binder provenance", rejectedWith "E_KCORE_TEXT_INVALID" forgedGeneratedOrdinaryBinder)
        , ("composed lift certificates replay scoped assumptions", either (const False) (const True) (parseVerified composedCertificate))
        , ("certificate assumptions are checked against their own normalized block", rejectedWith "E_KCORE_LEVEL_CERTIFICATE_INVALID" badCertificateAssumption)
        , ("semantically neutral certificate proof nodes canonicalize away", either (const False) id certificateProofCanonical)
        , ("representation-certificate declarations parse and round trip", representationCertificateParses)
        , ("representation-certificate law terms are independently checked", rejectedWith "E_KCORE_REPRESENTATION_CERTIFICATE_INVALID" malformedOrdinalRepresentationCertificate)
        , ("parametric global facets cannot enter ordinary positions", rejectedWith "E_PARAMETRIC_TYPE_PROMOTION" parametricGlobalPromotion)
        , ("dependent parametric application preserves its argument dependency", rejectedWith "E_PARAMETRIC_TYPE_PROMOTION" dependentParametricApplication)
        , ("constant parametric application remains ordinary", either (const False) (const True) (parseVerified constantParametricApplication))
        , ("dependent application substitution avoids independently canonicalized binder ids", either (const False) (const True) (parseVerified captureAvoidingDependentApplication))
        , ("canonical declarations use dependency/identity order", canonicalOrdered)
        , ("canonical local binders are numbered in preorder", canonicalLocals)
        , ("canonical text and semantic hashes are alpha-invariant", either (const False) id alphaStable)
        , ("local universe telescopes are alpha-invariant", either (const False) id localUniverseAlphaStable)
        , ("disjoint lexical binders canonicalize by occurrence", either (const False) id disjointLocalAlphaStable)
        , ("canonical SCC order places dependencies before users", declarationAppearsBefore "@test.dependency-order.dependency#20" "@test.dependency-order.user#10" dependencyOrderInput)
        , ("canonical recursive SCC members use stable identity order", declarationAppearsBefore "@test.cycle-order.left#10" "@test.cycle-order.right#20" cycleOrderInput)
        , ("canonical parse-print is byte stable", either (const False) id canonicalStable)
        ]
      failures = [label | (label, False) <- checks]
  unless (null failures) $ do
    putStrLn "kcoreTextCanonicalDomain FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
    case parseVerified composedCertificate of
      Left err -> putStrLn ("  composed certificate error=" ++ show err)
      Right _ -> pure ()
    case parseKCoreText malformedOrdinalRepresentationCertificate of
      Left err -> putStrLn ("  representation certificate parse error=" ++ show err)
      Right parsed -> case parseKCoreText (printCanonicalKCoreText parsed) of
        Left err -> putStrLn ("  representation certificate canonical parse error=" ++ show err)
        Right _ -> pure ()
    case (parseVerified sourceProofBinder, parseVerified generatedProofBinder) of
      (Left err, _) -> putStrLn ("  source proof binder error=" ++ show err)
      (_, Left err) -> putStrLn ("  generated proof binder error=" ++ show err)
      (Right sourceWritten, Right generated) -> do
        putStrLn ("  source proof binder hash=" ++ show (semanticHashKCoreText sourceWritten))
        putStrLn ("  generated proof binder hash=" ++ show (semanticHashKCoreText generated))
        TIO.putStrLn (printCanonicalKCoreText generated)
    case canonical of
      Left err -> putStrLn ("  canonical input rejected: " ++ T.unpack (kcteMessage err))
      Right text -> TIO.putStrLn text
  pure (null failures)

-- | §30.2.2.9: erased binders retain typed justification, while malformed
-- structural observation modes fail closed before either emitter sees them.
universeCapabilityBoundary :: IO Bool
universeCapabilityBoundary = do
  let src =
        T.unlines
          [ "module universe_capability"
          , "param : (parametric 0 A : Type0) -> Unit"
          , "let param A = ()"
          , "ordinary : (ordinary 0 A : Type0) -> Unit"
          , "let ordinary A = ()"
          , "proof : (@0 p : True) -> Unit"
          , "let proof @p = ()"
          ]
      st = cuState (compileSourceWithPrelude "universe-capability-boundary.kp" src)
      ir = lowerKBackendIR st
      erasures = concatMap bbErasures (Map.elems (kbirBodies ir))
      hasParam = any (\e -> case beProvenance e of ErasedParametricTypeWitness LZero -> True; _ -> False) erasures
      hasOrdinary = any ((== ErasedOrdinaryTypeCode) . beProvenance) erasures
      hasEvidence = any ((== ErasedProofOrTraitEvidence) . beProvenance) erasures
      owner = GName (ModuleName [T.pack "universe_capability"]) (T.pack "param")
      malformed =
        st
          { csCoreBodies =
              Map.singleton owner
                (CLamM Ordinary Expl Q0 "A" (CCtor prelUnit Nothing []))
          }
      malformedCodes = map bivCode (validateKBackendIR (lowerKBackendIR malformed))
      checkpointCodes = map bivCode (validateCoreCapabilities malformed)
      unresolvedObservation =
        st
          { csCoreBodies =
              Map.singleton owner
                (CLamM Parametric Expl Q0 "A" (CMeta (csNextMeta st + 1)))
          }
      unresolvedObservationCodes = map bivCode (validateCoreCapabilities unresolvedObservation)
      escapedLevel =
        st
          { csCoreBodies = Map.singleton owner (CSort (LVar 0))
          }
      escapedLevelCodes = map bivCode (validateCoreCapabilities escapedLevel)
      hiddenDoLevel =
        st {csCoreBodies = Map.singleton owner (CDo Nothing [KExpr (CSort (LMeta 77))])}
      hiddenDoCodes = map bivCode (validateCoreCapabilities hiddenDoLevel)
      modeLevel =
        st
          { csCoreBodies = Map.singleton owner (CSort (LMeta 78))
          , csGlobals = Map.adjust (\def -> def {gdType = VSort (LMeta 79)}) owner (csGlobals st)
          }
      modeLevelCodes = map bivCode (validateCoreCapabilities modeLevel)
      annotationLevelMetas =
        ( levelMetasOfTerm (CCtor prelUnit (Just (CSort (LMeta 80))) [])
        , levelMetasOfTerm (CMatch (CGlob prelUnit) (Just (CSort (LMeta 81))) [])
        )
      generatedOwner = GName (ModuleName [T.pack "universe_capability"]) (T.pack "generatedBad")
      mismatchedGeneratedMode =
        st
          { csGlobals =
              Map.insert generatedOwner
                (GlobalDef
                  (VPiEvidenceM Ordinary FormationOrdinary Expl Q0 False "A" Nothing
                    BinderSourceWritten
                    (VSort LZero) (Closure [] (CSort LZero)))
                  Nothing False)
                (csGlobals st)
          , csCoreBodies =
              Map.singleton generatedOwner
                (CLamM Parametric Expl Q0 "A" (CApp Expl (CGlob (gPrel "List")) (CVar 0)))
          }
      mismatchedGeneratedModeCodes = map bivCode (validateCoreCapabilities mismatchedGeneratedMode)
      patternOwner = GName (ModuleName [T.pack "universe_capability"]) (T.pack "patternBad")
      patternType =
        VPiEvidenceM Ordinary FormationOrdinary Expl QW False "s" Nothing
          BinderSourceWritten
          (VRecordTQ [RecordField "A" Parametric FormationParametric Q0 Nothing (VSort LZero)])
          (Closure [] (CSort LZero))
      mismatchedPatternMode =
        st
          { csGlobals =
              Map.insert patternOwner (GlobalDef patternType Nothing False) (csGlobals st)
          , csCoreBodies =
              Map.singleton patternOwner
                (CLamM Ordinary Expl QW "s"
                  (CMatch (CVar 0) Nothing
                    [CaseAlt
                      (CPRecordM [("A", CPVarM Ordinary "A")] Nothing)
                      Nothing
                      (CVar 0)]))
          }
      mismatchedPatternModeCodes = map bivCode (validateCoreCapabilities mismatchedPatternMode)
      returnOwner = GName (ModuleName [T.pack "universe_capability"]) (T.pack "returnBad")
      mismatchedReturnMode =
        st
          { csGlobals =
              Map.insert returnOwner
                (GlobalDef
                  (VPiEvidenceM Parametric FormationParametric Expl Q0 False "A" Nothing BinderSourceWritten (VSort LZero)
                    (Closure [] (CApp Expl (CGlob (gPrel "UIO")) (CSort LZero))))
                  Nothing False)
                (csGlobals st)
          , csCoreBodies =
              Map.singleton returnOwner
                (CLamM Parametric Expl Q0 "A" (CDo Nothing [KReturn (CVar 0)]))
          }
      mismatchedReturnModeViolations = validateCoreCapabilities mismatchedReturnMode
      mismatchedReturnModeCodes = map bivCode mismatchedReturnModeViolations
      libSrc =
        T.unlines
          [ "module lib"
          , "type Sig : Type = (0 A : Type, value : A)"
          , "type Keep (0 T : Type) : Type = T"
          , "plus : TypeLevel -> TypeLevel -> TypeLevel"
          , "let plus = (+)"
          , "copy : Sig -> Sig"
          , "let copy s = (0 A = s.A, value = s.value)"
          ]
      appSrc =
        T.unlines
          [ "module app"
          , "import lib"
          , "use : lib.Sig -> lib.Sig"
          , "let use x = lib.copy x"
          , "asInt : lib.Keep Int"
          , "let asInt = 1"
          , "type ViaImportedAlias : Typeω ="
          , "    (u : TypeLevel) -> (v : TypeLevel) ->"
          , "    (@0 bound : lib.plus u v < ω) -> Type(lib.plus u v)"
          ]
      roundTrip = compileFiles [("lib.kp", libSrc), ("app.kp", appSrc)]
      roundTripState = cuState roundTrip
      keepName = GName (ModuleName [T.pack "lib"]) (T.pack "Keep")
      plusName = GName (ModuleName [T.pack "lib"]) (T.pack "plus")
      viaAliasName = GName (ModuleName [T.pack "app"]) (T.pack "ViaImportedAlias")
      keepMode = gdObservationMode <$> Map.lookup keepName (csGlobals roundTripState)
      plusIdentity = Map.lookup plusName (csLevelOperatorAliases roundTripState)
      viaAliasNormalized =
        maybe False
          (Set.notMember plusName . globalsOfTerm)
          (Map.lookup viaAliasName (csGlobals roundTripState) >>= gdCoreType)
      roundTripErrors = filter isError (cuDiags roundTrip)
      aliasCacheIndependentArtifact =
        roundTripState
          { csLevelOperatorAliases = Map.delete plusName (csLevelOperatorAliases roundTripState)
          }
      aliasCacheIndependentCodes = map bivCode (validateCoreCapabilities aliasCacheIndependentArtifact)
      malformedArtifact =
        roundTripState
          { csGlobals =
              Map.adjust
                (\def -> def {gdType = VSort (LVar 0)})
                keepName
                (csGlobals roundTripState)
          }
      malformedArtifactCodes = map bivCode (validateCoreCapabilities malformedArtifact)
      missingUniverseSpine =
        st
          { csCoreBodies = Map.singleton owner (CGlobal prelEqType [])
          }
      missingUniverseSpineCodes = map bivCode (validateCoreCapabilities missingUniverseSpine)
      lateConstraintSource =
        T.unlines
          [ "module late_constraint_spine"
          , "type Id A = A"
          , "useF :"
          , "    (F : (A : Type) -> Type) ->"
          , "    (A : Type) ->"
          , "    F A -> F A"
          , "let useF F A x = x"
          , "idInt : Id Int -> Id Int"
          , "let idInt x = useF Id Int x"
          ]
      lateConstraintUnit = compileSourceWithPrelude "late-constraint-spine.kp" lateConstraintSource
      lateConstraintErrors = filter isError (cuDiags lateConstraintUnit)
      lateConstraintCodes = map bivCode (validateCoreCapabilities (cuState lateConstraintUnit))
      checks =
        [ ("parametric witness erasure is distinguished", hasParam)
        , ("ordinary type-code erasure is distinguished", hasOrdinary)
        , ("proof/trait evidence erasure is distinguished", hasEvidence)
        , ("malformed witness-to-runtime Core fails closed", T.pack "E_PARAMETRIC_TYPE_PROMOTION" `elem` malformedCodes)
        , ("malformed witness-to-runtime Core fails at typed checkpoint", T.pack "E_PARAMETRIC_TYPE_PROMOTION" `elem` checkpointCodes)
        , ("observation analysis failures reject even in parametric results", T.pack "E_BACKENDIR_OBSERVATION_ANALYSIS" `elem` unresolvedObservationCodes)
        , ("escaped level identity fails at typed checkpoint", T.pack "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" `elem` escapedLevelCodes)
        , ("do-kernel levels are checked before erasure", T.pack "E_UNSOLVED_METAVARIABLE" `elem` hiddenDoCodes)
        , ("Core and interface mode-bearing levels are checked", length (filter (== T.pack "E_UNSOLVED_METAVARIABLE") modeLevelCodes) >= 2)
        , ("typed constructor and match annotations participate in level closure", annotationLevelMetas == ([80], [81]))
        , ("generated Core cannot mislabel observation modes", T.pack "E_PARAMETRIC_TYPE_PROMOTION" `elem` mismatchedGeneratedModeCodes)
        , ("generated Core cannot mislabel record-pattern binders", T.pack "E_PARAMETRIC_TYPE_PROMOTION" `elem` mismatchedPatternModeCodes)
        , ("generated do return cannot promote a parametric witness", T.pack "E_PARAMETRIC_TYPE_PROMOTION" `elem` mismatchedReturnModeCodes)
        , ("two-module witness artifact round trip typechecks", null roundTripErrors)
        , ("two-module alias retains parametric observation mode", keepMode == Just Parametric)
        , ("two-module TypeLevel alias retains semantic identity", plusIdentity == Just LevelOperatorAdd)
        , ("finalized level proofs normalize imported operator aliases to certified constructors",
            viaAliasNormalized
              && T.pack "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" `notElem` aliasCacheIndependentCodes)
        , ("malformed imported type artifact fails closed", T.pack "E_UNSOLVED_METAVARIABLE" `elem` malformedArtifactCodes)
        , ("generalized globals require an exact hidden-universe spine", T.pack "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE" `elem` missingUniverseSpineCodes)
        , ("late generated constraint binders repair earlier call spines", null lateConstraintErrors && null lateConstraintCodes)
        ]
      failures = [label | (label, False) <- checks]
  unless (null failures) $ do
    putStrLn "universeCapabilityBoundary FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
    putStrLn ("  erasures=" ++ show erasures)
    putStrLn ("  malformedCodes=" ++ show malformedCodes)
    putStrLn ("  roundTripErrors=" ++ show roundTripErrors)
    putStrLn ("  lateConstraintErrors=" ++ show lateConstraintErrors)
    putStrLn ("  lateConstraintCodes=" ++ show lateConstraintCodes)
  pure (null failures)

-- | §30.2.1B/§31.2: schema lifts may disappear at the runtime boundary only
-- after the finalized typed-Core checkpoint independently replays their
-- nominal summary and evidence. A selected certificate identity is a lookup
-- key, not authority by itself.
schemaLiftBackendCertificateBoundary :: IO Bool
schemaLiftBackendCertificateBoundary = do
  let source =
        T.unlines
          [ "module schema_lift_boundary"
          , "data Phantom.{irrelevant u} (ordinary 0 A : Type0) : Type0 = Phantom"
          , "up : Phantom.{0} Int -> Phantom.{3} Int"
          , "let up x = x"
          ]
      state = cuState (compileSourceWithPrelude "schema-lift-boundary.kp" source)
      family = GName (ModuleName ["schema_lift_boundary"]) "Phantom"
      owner = GName (ModuleName ["schema_lift_boundary"]) "up"
      rewriteLift transform =
        Map.adjust
          (mapTermWithDepth (\_ term -> case term of
            CSchemaLift family' sourceLevels targetLevels roles evidence certificate sourceArguments targetArguments inner
              | family' == family ->
                  Just (transform sourceLevels targetLevels roles evidence certificate sourceArguments targetArguments inner)
            _ -> Nothing) 0)
          owner
      forgedCertificate =
        state
          { csCoreBodies =
              rewriteLift
                (\sourceLevels targetLevels roles evidence _ sourceArguments targetArguments inner ->
                  CSchemaLift family sourceLevels targetLevels roles evidence
                    (SchemaActionCertificateId "schema:forged") sourceArguments targetArguments inner)
                (csCoreBodies state)
          }
      mismatchedRoleEvidence =
        state
          { csCoreBodies =
              rewriteLift
                (\sourceLevels targetLevels _ _ certificate sourceArguments targetArguments inner ->
                  CSchemaLift family sourceLevels targetLevels [Covariant]
                    [SchemaInvariantEvidence] certificate sourceArguments targetArguments inner)
                (csCoreBodies state)
          }
      mismatchedSourceSpine =
        state
          { csCoreBodies =
              rewriteLift
                (\sourceLevels targetLevels roles evidence certificate sourceArguments targetArguments inner ->
                  CSchemaLift family sourceLevels targetLevels roles evidence certificate
                    (CSort LZero : sourceArguments) targetArguments inner)
                (csCoreBodies state)
          }
      mismatchedSourceArgument =
        state
          { csCoreBodies =
              rewriteLift
                (\sourceLevels targetLevels roles evidence certificate sourceArguments targetArguments inner ->
                  CSchemaLift family sourceLevels targetLevels roles evidence certificate
                    (case sourceArguments of
                       _ : rest -> CGlob prelUnit : rest
                       [] -> [])
                    targetArguments inner)
                (csCoreBodies state)
          }
      transplantedSummary = do
        definition <- Map.lookup family (csGlobals state)
        summary <- gdNominalSummary definition
        pure $
          makeNominalCumulativitySummary
            "schema_lift_boundary.OtherFamily"
            (ncsRoles summary)
            (ncsExplicitRoles summary)
            (ncsClosure summary)
            (ncsExtensionGate summary)
      transplantedFamilySummary =
        case transplantedSummary of
          Nothing -> state
          Just summary ->
            state
              { csGlobals =
                  Map.adjust (globalDefWithNominalSummary summary) family (csGlobals state)
              }
      missingSummary =
        state
          { csGlobals =
              Map.adjust (\definition -> definition {gdNominalSummary = Nothing}) family
                (csGlobals state)
          }
      cleanCodes = map bivCode (validateCoreCapabilities state)
      forgedCodes = map bivCode (validateCoreCapabilities forgedCertificate)
      roleCodes = map bivCode (validateCoreCapabilities mismatchedRoleEvidence)
      sourceSpineCodes = map bivCode (validateCoreCapabilities mismatchedSourceSpine)
      sourceArgumentCodes = map bivCode (validateCoreCapabilities mismatchedSourceArgument)
      transplantedCodes = map bivCode (validateCoreCapabilities transplantedFamilySummary)
      missingCodes = map bivCode (validateCoreCapabilities missingSummary)
      checks =
        [ ("verified schema lift crosses the backend boundary", "E_KCORE_SCHEMA_CERTIFICATE_INVALID" `notElem` cleanCodes && "E_UNIVERSE_SCHEMA_LIFT_INVALID" `notElem` cleanCodes)
        , ("forged schema certificate is rejected", "E_KCORE_SCHEMA_CERTIFICATE_INVALID" `elem` forgedCodes)
        , ("role/evidence mismatch is rejected", "E_UNIVERSE_SCHEMA_LIFT_INVALID" `elem` roleCodes)
        , ("source application mismatch is rejected", "E_UNIVERSE_SCHEMA_LIFT_INVALID" `elem` sourceSpineCodes)
        , ("same-arity source family argument forgery is rejected", "E_UNIVERSE_SCHEMA_LIFT_INVALID" `elem` sourceArgumentCodes)
        , ("valid summary for another family is rejected", "E_KCORE_SCHEMA_CERTIFICATE_INVALID" `elem` transplantedCodes)
        , ("missing nominal summary is rejected", "E_KCORE_SCHEMA_CERTIFICATE_INVALID" `elem` missingCodes)
        ]
      failures = [label | (label, False) <- checks]
  unless (null failures) $ do
    putStrLn "schemaLiftBackendCertificateBoundary FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
    putStrLn ("  clean=" ++ show cleanCodes)
    putStrLn ("  forged=" ++ show forgedCodes)
    putStrLn ("  role=" ++ show roleCodes)
    putStrLn ("  sourceSpine=" ++ show sourceSpineCodes)
    putStrLn ("  sourceArgument=" ++ show sourceArgumentCodes)
    putStrLn ("  transplanted=" ++ show transplantedCodes)
    putStrLn ("  missing=" ++ show missingCodes)
  pure (null failures)

-- | §10.4.3/§30.2.1B: certificate identity is derived from the
-- normalized nominal signature, never diagnostic prose, while trait roles are
-- replayed from their dictionary fields just like ordinary-data actions.
nominalVarianceCertificateDomain :: IO Bool
nominalVarianceCertificateDomain = do
  let summaryWith _reason =
        makeNominalCumulativitySummary
          "certificate_domain.Family"
          [Covariant]
          [False]
          ( makeNominalSignatureClosure 1 [] 0
              [ NominalClosureClause ClauseSortDeclaration "family" [] "sort" [] NominalPreserveRepresentation
              , NominalClosureClause ClausePointConstructor "constructor" [] "result" [NominalCovariantUse 0] NominalPreserveRepresentation
              , NominalClosureClause ClauseEliminator "eliminator" [] "eliminator" [NominalCovariantUse 0] NominalPreserveRepresentation
              , NominalClosureClause ClauseComputationRule "computation" [] "computation" [NominalCovariantUse 0] NominalPreserveRepresentation
              ]
          )
          Nothing
      firstSummary = summaryWith "source field oldName stores a type code"
      renamedSummary = summaryWith "source field newName stores a type code"
      forgedRepresentation =
        firstSummary
          { ncsClosure =
              (ncsClosure firstSummary)
                { nscClauses = case nscClauses (ncsClosure firstSummary) of
                    clause : rest -> clause {nccRepresentationAction = NominalTransformRepresentation} : rest
                    [] -> []
                }
          }
      traitSource =
        T.unlines
          [ "module trait_role_probe"
          , "trait CarriesCode.{u} ="
          , "    code : Type u"
          ]
      traitState = cuState (compileSourceWithPrelude "trait_role_probe.kp" traitSource)
      traitFamily = GName (ModuleName ["trait_role_probe"]) "CarriesCode"
      traitRoles = do
        definition <- Map.lookup traitFamily (csGlobals traitState)
        summary <- gdNominalSummary definition
        pure (ncsRoles summary)
      witnessSummary mode fieldName = do
        let source =
              T.unlines
                [ "module closure_probe"
                , "data Witness.{u} : Type0 ="
                , "    Witness (" <> mode <> " 0 " <> fieldName <> " : Type u)"
                ]
            state = cuState (compileSourceWithPrelude "closure_probe.kp" source)
            family = GName (ModuleName ["closure_probe"]) "Witness"
        definition <- Map.lookup family (csGlobals state)
        gdNominalSummary definition
      ordinarySummary = witnessSummary "ordinary" "A"
      parametricSummary = witnessSummary "parametric" "A"
      renamedOrdinarySummary = witnessSummary "ordinary" "Renamed"
      monotoneSummary proofName =
        let operator = NLTGlobal ["certificate_domain"] "bump" []
            goal = NLTApply True (NLTGlobal ["std", "typelevel"] "Monotone" []) operator
            evidence = NLTGlobal ["certificate_domain"] proofName []
            witness =
              NominalMonotoneWitness
                { nmwParameter = 0
                , nmwOperator = operator
                , nmwGoal = goal
                , nmwEvidence = evidence
                , nmwDependencies = nominalEvidenceDependencies [goal, evidence]
                }
            closure =
              withNominalMonotoneWitnesses [witness]
                ( makeNominalSignatureClosure 1 [] 0
                    [ NominalClosureClause ClauseSortDeclaration "family" [] "sort" [] NominalPreserveRepresentation
                    , NominalClosureClause ClausePointConstructor "constructor" [] "result" [NominalCovariantUse 0] NominalPreserveRepresentation
                    , NominalClosureClause ClauseEliminator "eliminator" [] "eliminator" [NominalCovariantUse 0] NominalPreserveRepresentation
                    , NominalClosureClause ClauseComputationRule "computation" [] "computation" [NominalCovariantUse 0] NominalPreserveRepresentation
                    ]
                )
         in makeNominalCumulativitySummary
              "certificate_domain.MonotoneFamily" [Covariant] [False] closure Nothing
      leftMonotoneSummary = monotoneSummary "leftProof"
      rightMonotoneSummary = monotoneSummary "rightProof"
      checks =
        [ ("generated summaries independently verify", verifyNominalCumulativitySummary firstSummary && verifyNominalCumulativitySummary renamedSummary)
        , ("representation identity is replayed from clause actions", not (verifyNominalCumulativitySummary forgedRepresentation))
        , ("diagnostic/source names do not change certificate identity", ncsClosureHash firstSummary == ncsClosureHash renamedSummary && ncsCertificateId firstSummary == ncsCertificateId renamedSummary)
        , ("trait dictionary fields constrain nominal variance", traitRoles == Just [Covariant])
        , ("binder observation mode changes the normalized nominal closure", (ncsClosureHash <$> ordinarySummary) /= (ncsClosureHash <$> parametricSummary))
        , ("alpha-only constructor binder renaming preserves closure identity", (ncsClosureHash <$> ordinarySummary) == (ncsClosureHash <$> renamedOrdinarySummary))
        , ("alpha-only constructor binder renaming preserves the exported summary", ordinarySummary == renamedOrdinarySummary)
        , ( "selected monotonicity proof identity is audit-only"
          , verifyNominalCumulativitySummary leftMonotoneSummary
              && verifyNominalCumulativitySummary rightMonotoneSummary
              && ncsClosureHash leftMonotoneSummary == ncsClosureHash rightMonotoneSummary
              && ncsCertificateId leftMonotoneSummary == ncsCertificateId rightMonotoneSummary
          )
        ]
      failures = [label | (label, False) <- checks]
  unless (null failures) $ do
    putStrLn "nominalVarianceCertificateDomain FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
    putStrLn ("  firstSummary=" ++ show firstSummary)
    putStrLn ("  renamedSummary=" ++ show renamedSummary)
    putStrLn ("  traitRoles=" ++ show traitRoles)
    putStrLn ("  ordinarySummary=" ++ show ordinarySummary)
    putStrLn ("  parametricSummary=" ++ show parametricSummary)
    putStrLn ("  renamedOrdinarySummary=" ++ show renamedOrdinarySummary)
  pure (null failures)

-- | §1.2 regression pin: 'scalarRep' must classify a primitive by its
-- declaration-symbol IDENTITY (the module-qualified 'GName'), not by surface
-- spelling — §1.2 "every resolved reference … MUST NOT target a spelling
-- string". The real prelude @Double@/@Int@ unbox; a user type that merely
-- SPELLS @Double@ in another module stays boxed. (The spelling-string key this
-- replaced would have mis-unboxed the user type; an even earlier 'gKey' key
-- dropped the workers entirely.) The native perf suite only exercises the real
-- prelude types, so this is the only place the name-collision case is pinned.
reprScalarIdentity :: IO Bool
reprScalarIdentity = do
  let realDouble = scalarRep (VGlobN prelDouble [])
      realInt = scalarRep (VGlobN prelInt [])
      userDouble = scalarRep (VGlobN (GName (ModuleName [T.pack "myapp"]) (T.pack "Double")) [])
      boxedHead = scalarRep (VGlobN prelUnit [])
      ok =
        realDouble == RepDouble
          && realInt == RepInt
          && userDouble == RepBoxed
          && boxedHead == RepBoxed
  unless ok $
    putStrLn
      ( "reprScalarIdentity FAILED: realDouble=" ++ show realDouble
          ++ " realInt=" ++ show realInt
          ++ " userDouble=" ++ show userDouble
          ++ " (a user type spelling 'Double' must NOT unbox)"
      )
  pure ok

-- | §15.8.2/§15.8.4: value arithmetic produces deterministic replay data,
-- not a checker-owned Boolean assertion. Mutation and underconstraint must
-- fail when the same pure kernel replays the artifact.
-- | Zero-binder suspension closures retain the lexical levels captured in
-- their environment when read back under a deeper context. Treating the
-- closure body as already rebased retargets its de Bruijn indices.
closureReadbackDomain :: IO Bool
closureReadbackDomain = do
  let ctx = EvalCtx (Globals Map.empty) emptyMetas False Map.empty
      captured = eval ctx [VRigid 0 []] (CThunkE (CVar 0) Nothing)
      actual = quote ctx 3 captured
      expected = CThunkE (CVar 2) Nothing
      ok = actual == expected
  unless ok $ do
    putStrLn "closureReadbackDomain FAILED:"
    putStrLn ("  expected " ++ show expected)
    putStrLn ("  actual   " ++ show actual)
  pure ok

-- | §18.8.5: @using pat <- acquire@ binds @pat@ for every following
-- do-kernel item. All depth-aware Core operations must agree on that
-- sequential scope; otherwise valid resource uses become free variables or
-- are captured by shifting, substitution, or metavariable zonking.
usingBinderScopeDomain :: IO Bool
usingBinderScopeDomain = do
  let unit = CCtor prelUnit Nothing []
      pattern' = CPVarM Ordinary (T.pack "resource")
      closed =
        CDo Nothing
          [ KUsing pattern' unit unit
          , KReturn (CVar 0)
          ]
      unresolved =
        CDo Nothing
          [ KUsing pattern' unit unit
          , KReturn (CMeta 7)
          ]
      zonked =
        zonkTermWith
          (\depth meta ->
            if meta == 7
              then Just (CVar (depth - 1))
              else Nothing)
          id
          0
          unresolved
      checks =
        [ ("scope", termScopedAt 0 closed)
        , ("shift", shiftTerm 1 0 closed == closed)
        , ("substitution", substTerm 0 (CLit (LitInt 99)) closed == closed)
        , ("zonk", zonked == closed && termScopedAt 0 zonked)
        ]
      ok = all snd checks
  unless ok $ do
    putStrLn "usingBinderScopeDomain FAILED:"
    mapM_ (putStrLn . ("  " <>) . fst) (filter (not . snd) checks)
    putStrLn ("  zonked=" ++ show zonked)
  pure ok

-- | A checked constructor pattern enumerates explicit source fields. Hidden
-- telescope arguments can follow an explicit field, so matching by a suffix
-- would bind the field to evidence rather than to its source value.
constructorPatternAlignmentDomain :: IO Bool
constructorPatternAlignmentDomain = do
  let constructor = GName (ModuleName [T.pack "test"]) (T.pack "Mk")
      value = CLit (LitInt 5)
      evidence = CCtor prelUnit Nothing []
      scrutinee =
        CCtorI
          constructor
          []
          Nothing
          [ ConstructorArg Impl False (Just (T.pack "a")) (CGlobal prelNat [])
          , ConstructorArg Expl True (Just (T.pack "value")) value
          , ConstructorArg Impl False (Just (T.pack "proof")) evidence
          ]
      pattern' =
        CPCtorM
          []
          []
          constructor
          []
          [CPVarM Ordinary (T.pack "value")]
      actual = matchCorePattern pattern' scrutinee
      expected = CorePatternMatched [value]
      ok = actual == expected
  unless ok $ do
    putStrLn "constructorPatternAlignmentDomain FAILED:"
    putStrLn ("  expected " ++ show expected)
    putStrLn ("  actual   " ++ show actual)
  pure ok

arithmeticReplayDomain :: IO Bool
arithmeticReplayDomain = do
  let n = AVar 0
      m = AVar 1
      naturalVariables = Set.fromList [0, 1]
      polynomialGoal =
        AFact
          ACmpEq
          (AAdd (AMul (AConst 2) n) (AConst 3))
          (AAdd (AAdd n n) (AConst 3))
      boundedAssumption = AFact ACmpLe (AAdd n (AConst 1)) m
      strictGoal = AFact ACmpLt n m
      equalityAssumption =
        AFact ACmpEq
          (AAdd m (AConst 1))
          (AAdd n (AConst 1))
      cancellationGoal = AFact ACmpEq m n
      affineConsequence =
        AFact ACmpLt n (AConst 10)
      affinePremise =
        AFact ACmpLt n (AConst 5)
      naturalAffineUpperBound =
        AFact
          ACmpLe
          n
          (AAdd (AMul (AConst 3) n) (AConst 4))
      successorBoundPremise =
        AFact ACmpLe (AAdd n (AConst 1)) m
      successorBoundConsequence =
        AFact ACmpLt n m
      exactDivisionGoal =
        AFact ACmpEq
          (ADiv (AAdd (AMul (AConst 4) n) (AConst 6)) (AConst 2))
          (AAdd (AMul (AConst 2) n) (AConst 3))
      exactModuloGoal =
        AFact ACmpEq
          (AMod (AAdd (AMul (AConst 4) n) (AConst 6)) (AConst 2))
          (AConst 0)
      shiftedModuloPremise =
        AFact ACmpEq (AMod n (AConst 3)) (AConst 1)
      shiftedModuloGoal =
        AFact ACmpEq (AMod (AAdd n (AConst 2)) (AConst 3)) (AConst 0)
      idempotentMaximumGoal =
        AFact ACmpEq (AMax n n) n
      uncheckedNaturalSubtraction =
        AFact ACmpEq (ASub n (AConst 1)) (ASub n (AConst 1))
      checkedNaturalSubtractionPremise =
        AFact ACmpLe (AConst 1) n
      zeroDivisor =
        AFact ACmpEq (ADiv n (AConst 0)) (ADiv n (AConst 0))
      nonzeroNatural = AFact ACmpNe n (AConst 0)
      naturalPositiveFromNonzero = AFact ACmpLe (AConst 1) n
      negativeIntegerDivisor =
        AFact ACmpEq
          (ADiv (AConst 6) (AConst (-2)))
          (AConst (-3))
      principalMeta = AVar 7
      principalAssignable = Set.singleton 7
      principalAddGoal =
        AFact ACmpEq (AAdd principalMeta (AConst 1)) (AConst 4)
      principalScaleGoal =
        AFact ACmpEq (AMul (AConst 2) principalMeta) (AConst 6)
      principalRigidExpressionGoal =
        AFact
          ACmpEq
          (AAdd principalMeta (AConst 1))
          (AAdd (AAdd n (AConst 1)) (AVar 1))
      branchRefinedIndex =
        AFact ACmpEq m (AAdd n (AConst 1))
      principalBranchRefinedGoal =
        AFact
          ACmpEq
          (AAdd principalMeta (AConst 1))
          (AAdd m (AVar 2))
      underconstrainedPrincipalGoal =
        AFact ACmpEq (AAdd principalMeta n) (AConst 4)
      nonPrincipalZeroGoal =
        AFact ACmpEq (AMul principalMeta (AConst 0)) (AConst 0)
      pointThree = AFact ACmpEq n (AConst 3)
      pointSeven = AFact ACmpEq n (AConst 7)
      conditionalPoint =
        AFact
          ACmpEq
          (AIf (AAtom pointThree) (AConst 3) (AConst 7))
          n
      nestedConditionalPoint =
        AFact
          ACmpEq
          ( AIf
              ( AAtom
                  ( AFact
                      ACmpEq
                      (AIf (AAtom pointThree) (AConst 0) (AConst 1))
                      (AConst 0)
                  )
              )
              (AConst 3)
              (AConst 7)
          )
          n
      scatteredPoints =
        AOr (AAtom pointThree) (AAtom pointSeven)
      notThree =
        ANot (AAtom pointThree)
      forcesSeven =
        AAtom (AFact ACmpEq (AConst 7) n)
      scatteredPointReplay =
        deriveArithmeticFormulaReplayWithAssumptions
          ArithmeticNaturalSemantics
          naturalVariables
          [(True, scatteredPoints), (True, notThree)]
          True
          forcesSeven
      underconstrainedScatteredPoint =
        deriveArithmeticFormulaReplayWithAssumptions
          ArithmeticNaturalSemantics
          naturalVariables
          [(True, scatteredPoints)]
          True
          forcesSeven
      impossibleAssumptionReplay =
        deriveArithmeticFormulaReplayWithAssumptions
          ArithmeticNaturalSemantics
          naturalVariables
          [(True, ATruth False)]
          True
          forcesSeven
      polynomialReplay =
        deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [] polynomialGoal
      strictReplay =
        deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [boundedAssumption] strictGoal
      mutated = do
        replay <- polynomialReplay
        pure replay {arNormalForm = NormalLowerBound 0}
      distinctMonomials =
        let x = AVar 0
            y = AVar 1
         in arNormalForm
              <$> deriveArithmeticReplay
                ArithmeticNaturalSemantics
                (Set.fromList [0, 1])
                []
                (AFact ACmpEq (AAdd (AMul x y) (AConst 1)) (AAdd (AConst 1) (AMul y x)))
      checks =
        [ ("polynomial equality has replay evidence", maybe False (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables []) polynomialReplay)
        , ("lexical bound entails strict inequality", maybe False (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [boundedAssumption]) strictReplay)
        , ("mutated normal form rejects", maybe True (not . verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables []) mutated)
        , ( "polynomial replay preserves monomial boundaries"
          , case distinctMonomials of
              Just (NormalPolynomial monomials) ->
                any (\(variables, _) -> variables == [(0, 1), (1, 1)]) monomials
              _ -> False
          )
        , ("underconstrained order remains unknown", deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [] strictGoal == Nothing)
        , ( "equality assumptions support cancellation"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [equalityAssumption])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [equalityAssumption] cancellationGoal)
          )
        , ( "affine assumptions support strict consequences"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [affinePremise])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [affinePremise] affineConsequence)
          )
        , ( "admitted branch facts specialize conditional arithmetic"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [pointThree])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [pointThree] conditionalPoint)
          )
        , ( "admitted branch facts specialize nested conditional arithmetic"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [pointThree])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [pointThree] nestedConditionalPoint)
          )
        , ( "Nat non-negativity proves affine upper bounds"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [] naturalAffineUpperBound)
          )
        , ( "successor upper bounds entail strict Nat bounds"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [successorBoundPremise])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [successorBoundPremise] successorBoundConsequence)
          )
        , ( "exact affine division normalizes"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [] exactDivisionGoal)
          )
        , ( "literal modular congruence normalizes"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [] exactModuloGoal)
          )
        , ( "modular assumptions transport residues"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [shiftedModuloPremise])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [shiftedModuloPremise] shiftedModuloGoal)
          )
        , ( "piecewise idempotence normalizes"
          , maybe False
              (verifyArithmeticReplay ArithmeticNaturalSemantics naturalVariables [])
              (deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [] idempotentMaximumGoal)
          )
        , ( "unchecked natural subtraction is not proof evidence"
          , deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [] uncheckedNaturalSubtraction == Nothing
          )
        , ( "natural subtraction accepts an independently proved domain"
          , isJust
              ( deriveArithmeticReplay
                  ArithmeticNaturalSemantics
                  naturalVariables
                  [checkedNaturalSubtractionPremise]
                  uncheckedNaturalSubtraction
              )
          )
        , ( "zero divisors fail closed"
          , deriveArithmeticReplay ArithmeticNaturalSemantics naturalVariables [] zeroDivisor == Nothing
          )
        , ( "equality negation is represented as disequality"
          , negateFact (AFact ACmpEq n (AConst 0))
              == Just nonzeroNatural
          )
        , ( "Nat nonzero entails positivity"
          , isJust
              ( deriveArithmeticReplay
                  ArithmeticNaturalSemantics
                  naturalVariables
                  [nonzeroNatural]
                  naturalPositiveFromNonzero
              )
          )
        , ( "Integer division accepts a negative nonzero divisor"
          , isJust
              ( deriveArithmeticReplay
                  ArithmeticIntegerSemantics
                  Set.empty
                  []
                  negativeIntegerDivisor
              )
          )
        , ( "integer subtraction remains total"
          , isJust
              ( deriveArithmeticReplay
                  ArithmeticIntegerSemantics
                  Set.empty
                  []
                  uncheckedNaturalSubtraction
              )
          )
        , ( "affine Nat meta has a unique principal assignment"
          , derivePrincipalAffineAssignment
              ArithmeticNaturalSemantics
              (Set.insert 7 naturalVariables)
              principalAssignable
              []
              principalAddGoal
              == Just (7, 3)
          )
        , ( "literal-scaled Nat meta has a unique principal assignment"
          , derivePrincipalAffineAssignment
              ArithmeticNaturalSemantics
              (Set.insert 7 naturalVariables)
              principalAssignable
              []
              principalScaleGoal
              == Just (7, 3)
          )
        , ( "affine Nat meta has a principal expression over rigid variables"
          , derivePrincipalAffineSubstitution
              ArithmeticNaturalSemantics
              (Set.fromList [0, 1, 7])
              principalAssignable
              []
              principalRigidExpressionGoal
              == Just (7, AAdd (AVar 0) (AVar 1))
          )
        , ( "branch-refined Nat indices determine a principal expression"
          , derivePrincipalAffineSubstitution
              ArithmeticNaturalSemantics
              (Set.fromList [0, 1, 2, 7])
              principalAssignable
              [branchRefinedIndex]
              principalBranchRefinedGoal
              == Just (7, AAdd (AVar 0) (AVar 2))
          )
        , ( "an equation retaining a rigid variable is not principal"
          , derivePrincipalAffineAssignment
              ArithmeticNaturalSemantics
              (Set.insert 7 naturalVariables)
              principalAssignable
              []
              underconstrainedPrincipalGoal
              == Nothing
          )
        , ( "a zero coefficient does not determine a meta"
          , derivePrincipalAffineAssignment
              ArithmeticNaturalSemantics
              (Set.insert 7 naturalVariables)
              principalAssignable
              []
              nonPrincipalZeroGoal
              == Nothing
          )
        , ( "disjunctive assumptions prove a consequence by checked cases"
          , case scatteredPointReplay of
              Just (ReplayAssumptionCases cases) ->
                any isContradiction cases
                  && any isGoal cases
              _ -> False
          )
        , ( "a disjunction alone does not select one branch"
          , underconstrainedScatteredPoint == Nothing
          )
        , ( "a constant contradictory assumption retains explicit replay"
          , impossibleAssumptionReplay
              == Just
                ( ReplayAssumptionCases
                    [ReplayAssumptionImpossible 0]
                )
          )
        ]
      failures = [label | (label, False) <- checks]
  unless (null failures) $ do
    putStrLn "arithmeticReplayDomain FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
  pure (null failures)
  where
    isContradiction (ReplayAssumptionContradiction _ _) = True
    isContradiction _ = False
    isGoal (ReplayAssumptionGoal _) = True
    isGoal _ = False

representationCertificateIdentityDomain :: IO Bool
representationCertificateIdentityDomain = do
  let context = RepresentationContext [] []
      naturalType = CGlob prelNat
      exactCertificate =
        ExactNaturalRepresentationCertificate
          { enrcContext = context
          , enrcRepresentedType = naturalType
          , enrcTypeIdentity = representationTypeIdentity context naturalType
          , enrcEvidenceIdentity = "checked-exact-natural-evidence"
          , enrcZeroConstructor = prelNatZero
          , enrcSuccessorConstructor = prelNatSucc
          , enrcRecursiveField = ConstructorFieldPath prelNatSucc 0
          , enrcErasedFields = []
          , enrcProfileRestrictions =
              [ExcludeDynamicBoundary, ExcludeForeignBoundary]
          , enrcCertificateVersion = 1
          , enrcCheckerVersion = 1
          }
      finiteType = CApp Expl (CGlob prelFin) (CLit (LitInt 5))
      ordinalCertificate =
        OrdinalRepresentationCertificate
          { orcContext = context
          , orcRepresentedType = finiteType
          , orcTypeIdentity = representationTypeIdentity context finiteType
          , orcSourceEvidenceIdentity = Nothing
          , orcCardinalityExpression = cardLiteral 5
          , orcEncoding = OrdinalFin (cardLiteral 5)
          , orcErasedFields = []
          , orcProfileRestrictions = [ExcludeExportedAbi]
          , orcCertificateVersion = 1
          , orcCheckerVersion = 1
          }
      wrapper = GName (ModuleName ["test", "representation"]) "Wrapper"
      wrapperCtor = GName (ModuleName ["test", "representation"]) "MkWrapper"
      wrapperType = CGlob wrapper
      refinementCertificate =
        RefinementRepresentationCertificate
          { rrcContext = context
          , rrcRepresentedType = wrapperType
          , rrcTypeIdentity = representationTypeIdentity context wrapperType
          , rrcRefinementEvidenceIdentity = "checked-refinement-evidence"
          , rrcBaseType = naturalType
          , rrcBaseTypeIdentity = representationTypeIdentity context naturalType
          , rrcConstructor = wrapperCtor
          , rrcRetainedBaseField = ConstructorFieldPath wrapperCtor 0
          , rrcErasedEvidenceFields = [ConstructorFieldPath wrapperCtor 1]
          , rrcProfileRestrictions = [InternalValuesOnly]
          , rrcCertificateVersion = 1
          , rrcCheckerVersion = 1
          }
      mutationsChange identity original mutations =
        all ((/= identity original) . identity) mutations
      mutationsReject verify mutations =
        all (isLeft . verify) mutations
      checks =
        [ ("exact-natural certificate verifies", verifyExactNaturalRepresentationCertificate exactCertificate == Right ())
        , ("ordinal certificate verifies", verifyOrdinalRepresentationCertificate ordinalCertificate == Right ())
        , ("refinement certificate verifies", verifyRefinementRepresentationCertificate refinementCertificate == Right ())
        , ( "exact-natural decisive fields affect identity"
          , mutationsChange
              exactNaturalRepresentationCertificateIdentity
              exactCertificate
              [ exactCertificate {enrcEvidenceIdentity = "other-evidence"}
              , exactCertificate {enrcRecursiveField = ConstructorFieldPath prelNatSucc 1}
              , exactCertificate {enrcProfileRestrictions = [ExcludeDynamicBoundary]}
              ]
          )
        , ( "exact-natural decisive mutations reject"
          , mutationsReject
              verifyExactNaturalRepresentationCertificate
              [ exactCertificate {enrcEvidenceIdentity = ""}
              , exactCertificate {enrcRecursiveField = ConstructorFieldPath prelNatSucc (-1)}
              , exactCertificate
                  { enrcProfileRestrictions =
                      [ExcludeDynamicBoundary, ExcludeDynamicBoundary]
                  }
              ]
          )
        , ( "ordinal decisive fields affect identity"
          , mutationsChange
              ordinalRepresentationCertificateIdentity
              ordinalCertificate
              [ ordinalCertificate {orcCardinalityExpression = cardLiteral 6}
              , ordinalCertificate {orcEncoding = OrdinalFin (cardLiteral 6)}
              , ordinalCertificate {orcSourceEvidenceIdentity = Just "other-evidence"}
              ]
          )
        , ( "ordinal decisive mutations reject"
          , mutationsReject
              verifyOrdinalRepresentationCertificate
              [ ordinalCertificate {orcCardinalityExpression = cardLiteral 6}
              , ordinalCertificate {orcEncoding = OrdinalFin (cardLiteral 6)}
              , ordinalCertificate {orcSourceEvidenceIdentity = Just ""}
              ]
          )
        , ( "refinement decisive fields affect identity"
          , mutationsChange
              refinementRepresentationCertificateIdentity
              refinementCertificate
              [ refinementCertificate {rrcBaseTypeIdentity = "wrong-base"}
              , refinementCertificate {rrcRetainedBaseField = ConstructorFieldPath wrapperCtor 1}
              , refinementCertificate {rrcProfileRestrictions = [ExcludeDynamicBoundary]}
              ]
          )
        , ( "refinement decisive mutations reject"
          , mutationsReject
              verifyRefinementRepresentationCertificate
              [ refinementCertificate {rrcBaseTypeIdentity = "wrong-base"}
              , refinementCertificate
                  { rrcRetainedBaseField = ConstructorFieldPath wrapperCtor (-1)
                  }
              , refinementCertificate
                  { rrcProfileRestrictions =
                      [ExcludeDynamicBoundary, ExcludeDynamicBoundary]
                  }
              ]
          )
        ]
      failures = [label | (label, False) <- checks]
  unless (null failures) $ do
    putStrLn "representationCertificateIdentityDomain FAILED:"
    mapM_ (putStrLn . ("  " ++)) failures
  pure (null failures)

-- | Perceus S2.3c/S3.1 regression: primitive call conventions are not the source
-- arrows' blanket @QW@, and the ownership override arity check must skip the
-- same implicit/Q0/kind-domain params as runtime argument lowering. The shared
-- Repr accessor must classify audited runtime-cell publishers as owned at the
-- published value positions and confirmed read-only positions as borrowed, while
-- leaving result-transfer primitives on the conservative telescope fallback until
-- result ownership is modeled.
primArgConventionS23c :: IO Bool
primArgConventionS23c = do
  let cu =
        compileSourceWithPrelude "prim-conventions.kp" $
          T.unlines
            [ "module main"
            , "x : Int"
            , "let x = 0"
            ]
      st = cuState cu
      ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
      conv name = argConvSelectGlobal ctx (gPrel (T.pack name))
      convDirect name = argConvSelectGlobal ctx (GName primModule (T.pack name))
      fakePrimG = GName (ModuleName [T.pack "test"]) (T.pack "fakeWriteRefWithKindParam")
      fakePrimTy =
        CPiFormedM Ordinary FormationOrdinary Expl Q1 False (T.pack "a") (CSort LZero) $
          CPiFormedM Ordinary FormationOrdinary Expl QW False (T.pack "r") (CGlob prelInt) $
            CPiFormedM Ordinary FormationOrdinary Expl QW False (T.pack "v") (CGlob prelInt) $
              CGlob prelUnit
      fakePrimCtx =
        let gd =
              GlobalDef
                (eval ctx [] fakePrimTy)
                (Just (VPrim (T.pack "__ioWriteRef") []))
                False
            Globals globals = ecGlobals ctx
         in ctx {ecGlobals = Globals (Map.insert fakePrimG gd globals)}
      b = ArgBorrowed
      o = ArgOwned
      s = ArgShared
      exact =
        [ ("__ioNewRef", [o])
        , ("__ioReadRef", [b])
        , ("__ioWriteRef", [b, o])
        , ("__newArray", [b, o])
        , ("__arrayRead", [b, b])
        , ("__arrayWrite", [b, b, o])
        , ("__arrayLen", [b])
        , ("newTVar", [o])
        , ("readTVar", [b])
        , ("writeTVar", [b, o])
        , ("__newAtomicRef", [o])
        , ("__atomicLoad", [b, b])
        , ("__atomicStore", [b, b, o])
        , ("__atomicExchange", [b, b, o])
        , ("__atomicCompareExchange", [b, b, b, b, o])
        , ("__atomicFetchAdd", [b, b, b])
        , ("__atomicFetchSub", [b, b, b])
        , ("__atomicFetchAnd", [b, b, b])
        , ("__atomicFetchOr", [b, b, b])
        , ("__atomicFetchXor", [b, b, b])
        , ("newFiberRef", [o])
        , ("getFiberRef", [b])
        , ("setFiberRef", [b, o])
        , ("modifyFiberRef", [b, s])
        , ("locallyFiberRef", [b, o, s])
        , ("completePromise", [b, o])
        , ("awaitPromiseExit", [b])
        , ("pollPromise", [b])
        , ("isDonePromise", [b])
        ]
      fallback =
        [ ("__transport", [s])
        , ("ioPure", [s])
        , ("unsafeConsume", [o])
        ]
      failedExact = [(name, conv name, want) | (name, want) <- exact, conv name /= Just want]
      failedFallback = [(name, conv name, want) | (name, want) <- fallback, conv name /= Just want]
      failedDirect =
        [ (name, convDirect name, want)
        | (name, want) <- exact ++ fallback
        , convDirect name /= Just want
        ]
      fakeKindDomainOk = argConvSelectGlobal fakePrimCtx fakePrimG == Just [b, o]
      ok = null failedExact && null failedFallback && null failedDirect && fakeKindDomainOk
  unless ok $ do
    putStrLn "primArgConventionS23c FAILED:"
    mapM_
      (\(name, got, want) -> putStrLn ("  " <> name <> ": got " <> show got <> ", want " <> show (Just want)))
      (failedExact ++ failedFallback ++ failedDirect)
    unless fakeKindDomainOk $
      putStrLn
        ( "  fakeWriteRefWithKindParam: got "
            <> show (argConvSelectGlobal fakePrimCtx fakePrimG)
            <> ", want "
            <> show (Just [b, o])
            <> " (explicit non-Q0 kind-domain params must be skipped before primitive override arity checks)"
        )
  pure ok

-- | S5.A regression: KCore can omit erased implicit binders from a global
-- application spine.  KBackendIR erasure/convention lowering must align facts
-- to the supplied arguments by icity/telescope, not raw index, otherwise
-- primitives such as __effBind erase their first explicit runtime operands and
-- public IO ref operations lose the selected primitive convention.
spineErasureOmittedImplicitS5 :: IO Bool
spineErasureOmittedImplicitS5 = do
  let cu =
        compileSourceWithPrelude "s5a-spine-erasure.kp" $
          T.unlines
            [ "module main"
            , "main : UIO Unit"
            , "let main = printlnString \"ok\""
            ]
      st = cuState cu
      globals = csGlobals st
      ctx = EvalCtx (Globals globals) (csMetas st) False (csFacts st)
      effBind = erasedSpinePositionsForArgs globals ctx (gPrel (T.pack "__effBind")) [Expl, Expl]
      handleEff = erasedSpinePositionsForArgs globals ctx (gPrel (T.pack "__handleEff")) [Expl, Expl, Expl, Expl, Expl]
      runPure = erasedSpinePositionsForArgs globals ctx (gPrel (T.pack "runPure")) [Expl]
      writeRefConv = argConvSelectGlobalForArgs ctx (gPrel (T.pack "__ioWriteRef")) [Expl, Expl]
      readRefConv = argConvSelectGlobalForArgs ctx (gPrel (T.pack "__ioReadRef")) [Expl]
      directWriteRefConv = argConvSelectGlobalForArgs ctx (GName primModule (T.pack "__ioWriteRef")) [Expl, Expl]
      directReadRefConv = argConvSelectGlobalForArgs ctx (GName primModule (T.pack "__ioReadRef")) [Expl]
      ok =
        effBind == [False, False]
          && handleEff == replicate 5 False
          && runPure == [False]
          && writeRefConv == Just [Just ArgBorrowed, Just ArgOwned]
          && readRefConv == Just [Just ArgBorrowed]
          && directWriteRefConv == Just [Just ArgBorrowed, Just ArgOwned]
          && directReadRefConv == Just [Just ArgBorrowed]
  unless ok $ do
    putStrLn "spineErasureOmittedImplicitS5 FAILED:"
    putStrLn ("  __effBind [Expl,Expl] erased=" <> show effBind <> ", want [False,False]")
    putStrLn ("  __handleEff 5xExpl erased=" <> show handleEff <> ", want all False")
    putStrLn ("  runPure [Expl] erased=" <> show runPure <> ", want [False]")
    putStrLn ("  __ioWriteRef conv=" <> show writeRefConv <> ", want borrowed/owned")
    putStrLn ("  __ioReadRef conv=" <> show readRefConv <> ", want borrowed")
    putStrLn ("  #prim.__ioWriteRef conv=" <> show directWriteRefConv <> ", want borrowed/owned")
    putStrLn ("  #prim.__ioReadRef conv=" <> show directReadRefConv <> ", want borrowed")
  pure ok

replaceGlobInSimpleApp :: GName -> GName -> Term -> Term
replaceGlobInSimpleApp from to = go
  where
    go t = case t of
      CGlob g | g == from -> CGlob to
      CApp ic f a -> CApp ic (go f) (go a)
      CLamM mode ic q n body -> CLamM mode ic q n (go body)
      other -> other

-- | Perceus RC Stage S1.2 gate: the ownership last-use analysis
-- ("Kappa.Ownership") must be consistent with the declared quantities already
-- on the Core binder nodes, across the whole WELL-TYPED corpus.
--
-- 'crossCheckBodies' asserts, for every binder: a linear (@1@) binder has
-- at least one consuming 'LastUse' and no consuming 'NonLast'; a borrowed
-- (@&@) binder has no consuming use. A non-empty result means the last-use
-- analysis is WRONG (it drifted from the quantities the checker validated),
-- and this gate fails the build — the analysis must be fixed, not the check
-- weakened.
--
-- The corpus is the full implicit prelude + std library (hundreds of well-typed
-- globals exercising linear @let@s, borrowed params, and match arms) plus a few
-- crafted fixtures (a linear let, a borrowed param, a one-arm match). It is run
-- here, over WELL-TYPED code only, rather than as a crash inside
-- 'annotateOwnership' on every compilation — the conformance tree intentionally
-- contains quantity-violating programs whose Core legitimately breaks "linear ⇒
-- one last use", which is not an analysis bug.
ownershipCrossCheckClean :: IO Bool
ownershipCrossCheckClean = do
  let fixtures =
        [ -- a linear let: the binder must be consumed exactly once
          T.unlines
            [ "module main"
            , "consume : (1 x : Int) -> Int"
            , "let consume x = x"
            , "linUse : Int -> Int"
            , "let linUse n ="
            , "    let 1 y = n"
            , "    consume y"
            ]
        , -- a borrowed parameter: its uses are non-consuming
          T.unlines
            [ "module main"
            , "peek : (& x : Int) -> Int"
            , "let peek x = addInt x x"
            ]
        , -- a binder used in one match arm only (dropped on the other)
          T.unlines
            [ "module main"
            , "pick : Option Int -> Int"
            , "let pick o ="
            , "    match o"
            , "    case Some v -> v"
            , "    case None -> 0"
            ]
        , -- S1.4 §3a (corrected whole-program-static model): EVERY provably
          -- single-use ω parameter is refined to [1,1] — exported and private
          -- alike — because the analysis sees all uses (no separate compilation
          -- yet). A binder used TWICE stays unrefined. The cross-check asserts
          -- the tighten-only invariant boRefined <= boDeclQ, so a wrong
          -- refinement (a widen) fails here.
          T.unlines
            [ "module main"
            , "share : (ω x : Int) -> Int"
            , "let share (ω x : Int) = x"
            , "private dup1 : (ω y : Int) -> Int"
            , "let dup1 (ω y : Int) = y"
            , "private useTwice : (ω z : Int) -> Int"
            , "let useTwice (ω z : Int) = addInt z z"
            ]
        ]
      -- compile each fixture WITH the implicit prelude+std, so the cross-check
      -- sees the whole well-typed corpus plus the fixture's own definitions.
      check src =
        let cu = compileSourceWithPrelude "fixture.kp" src
            st = cuState cu
            ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
            ctorTypes = Map.map (\ci -> OwnershipCtorType (ciUniverses ci) (ciType ci)) (csCtors st)
            -- S1.1 last-use + S1.4 §3a refinement tighten-only invariant.
            xc =
              crossCheckBodiesWithUniverses
                ctx
                ctorTypes
                (csCoreBodies st)
                (csOwnership st)
            -- S1.5 owned/borrowed call-site classification: every global-headed
            -- call site must classify each of its arguments.
            ac = argConvBodies ctx (csCoreBodies st)
         in xc ++ ac
      mismatches = concatMap check fixtures
      consumeVsReadSrc =
        T.unlines
          [ "module main"
          , "ignore : (0 x : Int) -> Int -> Int"
          , "let ignore x y = y"
          , "peek : (& x : Int) -> Int"
          , "let peek x = x"
          , "pass : Int -> Int"
          , "let pass y = peek y"
          , "type PeekInt = (& x : Int) -> Int"
          , "aliasPeek : PeekInt"
          , "let aliasPeek x = x"
          , "aliasPass : Int -> Int"
          , "let aliasPass y = aliasPeek y"
          , "type IgnoreInt = (0 x : Int) -> Int"
          , "localAlias : PeekInt -> Int -> Int"
          , "let localAlias f y = f y"
          , "localAliasIgnore : IgnoreInt -> Int -> Int"
          , "let localAliasIgnore f y = f y"
          , "localAnnotated : Int -> Int"
          , "let localAnnotated y ="
          , "  let h : PeekInt -> Int = \\f -> f y"
          , "  h aliasPeek"
          , "choosePeek : Bool -> Int -> Int -> Int"
          , "let choosePeek c a b = peek (if c then a else b)"
          , "erasedOnly : Int -> Int"
          , "let erasedOnly n = ignore n 1"
          , "apply : ((1 x : Int) -> Int) -> (1 y : Int) -> Int"
          , "let apply f y = f y"
          , "localIgnore : ((0 x : Int) -> Int) -> Int -> Int"
          , "let localIgnore f y = f y"
          , "data Wrap : Type ="
          , "    MkWrap ((& x : Int) -> Int)"
          , "useWrap : Wrap -> Int -> Int"
          , "let useWrap w y ="
          , "  match w"
          , "  case MkWrap f -> f y"
          , "data WrapAlias : Type ="
          , "    MkWrapAlias PeekInt"
          , "useWrapAlias : WrapAlias -> Int -> Int"
          , "let useWrapAlias w y ="
          , "  match w"
          , "  case MkWrapAlias f -> f y"
          , "data BoxF (ft : Type) : Type ="
          , "    MkBoxF ft"
          , "useParamCtor : BoxF PeekInt -> Int -> Int"
          , "let useParamCtor b y ="
          , "  match b"
          , "  case MkBoxF f -> f y + y"
          , "type RecAlias = (f : PeekInt,)"
          , "useRecordAlias : RecAlias -> Int -> Int"
          , "let useRecordAlias r y ="
          , "  match r"
          , "  case (f = f) -> f y"
          , "useProjectedCallee : RecAlias -> Int -> Int"
          , "let useProjectedCallee r y = r.f y + y"
          , "type TupleAlias = (PeekInt, Int)"
          , "useTupleAlias : TupleAlias -> Int -> Int"
          , "let useTupleAlias p y ="
          , "  match p"
          , "  case (f, _) -> f y"
          , "useVariant : (| PeekInt |) -> Int -> Int"
          , "let useVariant v y ="
          , "  match v"
          , "  case (| f : PeekInt |) -> f y + y"
          , "foo : (ω a : Type) -> Int"
          , "let foo a = 0"
          , "typeOnly : (ω a : Type) -> Int"
          , "let typeOnly a = foo a"
          , "type K = Type"
          , "fooK : (ω a : K) -> Int"
          , "let fooK a = 0"
          , "typeOnlyAlias : (ω a : K) -> Int"
          , "let typeOnlyAlias a = fooK a"
          , "projOnly : (r : (v : Int,)) -> Int"
          , "let projOnly r = r.v"
          , "type Box = (v : Int,)"
          , "peekBox : (& x : Box) -> Int"
          , "let peekBox x = x.v"
          , "useBorrowTwice : Box -> Int"
          , "let useBorrowTwice y = peekBox y + y.v"
          , "primReadRefBorrow : Ref Int -> UIO Int"
          , "let primReadRefBorrow r = __ioReadRef r"
          , "primWriteRefTransfer : Ref Int -> Int -> UIO Unit"
          , "let primWriteRefTransfer r v = __ioWriteRef r v"
          , "tvarReadBorrow : TVar Int -> STM Int"
          , "let tvarReadBorrow r = readTVar r"
          , "tvarWriteTransfer : TVar Int -> Int -> STM Unit"
          , "let tvarWriteTransfer r v = writeTVar r v"
          , "fiberGetBorrow : FiberRef Int -> UIO Int"
          , "let fiberGetBorrow r = getFiberRef r"
          , "fiberSetTransfer : FiberRef Int -> Int -> UIO Unit"
          , "let fiberSetTransfer r v = setFiberRef r v"
          ]
      focused =
        let cu = compileSourceWithPrelude "consume-vs-read.kp" consumeVsReadSrc
            st = cuState cu
            ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
            ctorTypes = Map.map (\ci -> OwnershipCtorType (ciUniverses ci) (ciType ci)) (csCtors st)
            mainMod = ModuleName [T.pack "main"]
            passG = GName mainMod (T.pack "pass")
            aliasPassG = GName mainMod (T.pack "aliasPass")
            localAliasG = GName mainMod (T.pack "localAlias")
            localAliasIgnoreG = GName mainMod (T.pack "localAliasIgnore")
            localAnnotatedG = GName mainMod (T.pack "localAnnotated")
            choosePeekG = GName mainMod (T.pack "choosePeek")
            erasedG = GName mainMod (T.pack "erasedOnly")
            applyG = GName mainMod (T.pack "apply")
            localIgnoreG = GName mainMod (T.pack "localIgnore")
            useWrapG = GName mainMod (T.pack "useWrap")
            useWrapAliasG = GName mainMod (T.pack "useWrapAlias")
            useParamCtorG = GName mainMod (T.pack "useParamCtor")
            useRecordAliasG = GName mainMod (T.pack "useRecordAlias")
            useProjectedCalleeG = GName mainMod (T.pack "useProjectedCallee")
            useTupleAliasG = GName mainMod (T.pack "useTupleAlias")
            useVariantG = GName mainMod (T.pack "useVariant")
            typeOnlyG = GName mainMod (T.pack "typeOnly")
            typeOnlyAliasG = GName mainMod (T.pack "typeOnlyAlias")
            projOnlyG = GName mainMod (T.pack "projOnly")
            useBorrowTwiceG = GName mainMod (T.pack "useBorrowTwice")
            primReadRefBorrowG = GName mainMod (T.pack "primReadRefBorrow")
            primWriteRefTransferG = GName mainMod (T.pack "primWriteRefTransfer")
            tvarReadBorrowG = GName mainMod (T.pack "tvarReadBorrow")
            tvarWriteTransferG = GName mainMod (T.pack "tvarWriteTransfer")
            fiberGetBorrowG = GName mainMod (T.pack "fiberGetBorrow")
            fiberSetTransferG = GName mainMod (T.pack "fiberSetTransfer")
            paramBid g = BinderId g 0
            refinedOf g =
              case Map.lookup g (csOwnership st) of
                Nothing -> Left ("no OwnInfo for " <> show g)
                Just oi ->
                  case Map.lookup (paramBid g) (oiBinders oi) of
                    Nothing -> Left ("no parameter binder for " <> show g)
                    Just bo -> Right (boRefined bo)
            passDump =
              case Map.lookup passG (csOwnership st) of
                Nothing -> T.empty
                Just oi -> renderOwnInfo passG oi
            dumpOf g =
              case Map.lookup g (csOwnership st) of
                Nothing -> T.empty
                Just oi -> renderOwnInfo g oi
            forcedLinear =
              Map.adjust
                ( \oi ->
                    oi
                      { oiBinders =
                          Map.adjust
                            (\bo -> bo {boDeclQ = Q1})
                            (paramBid passG)
                            (oiBinders oi)
                      }
                )
                passG
                (csOwnership st)
            forcedBodies = Map.filterWithKey (\g _ -> g == passG) (csCoreBodies st)
            forcedMsgs = crossCheckBodiesWithUniverses ctx ctorTypes forcedBodies forcedLinear
            missingMsgs = crossCheckBodiesWithUniverses ctx ctorTypes forcedBodies Map.empty
            driftUses =
              Map.adjust
                (\oi -> oi {oiUses = Map.empty})
                passG
                (csOwnership st)
            driftBinderUses =
              Map.adjust
                (\oi -> oi {oiBinderUses = Map.empty})
                passG
                (csOwnership st)
            driftBinders =
              Map.adjust
                (\oi -> oi {oiBinders = Map.empty})
                passG
                (csOwnership st)
            driftUsesMsgs = crossCheckBodiesWithUniverses ctx ctorTypes forcedBodies driftUses
            driftBinderUsesMsgs = crossCheckBodiesWithUniverses ctx ctorTypes forcedBodies driftBinderUses
            driftBindersMsgs = crossCheckBodiesWithUniverses ctx ctorTypes forcedBodies driftBinders
            focusedXc = crossCheckBodiesWithUniverses ctx ctorTypes (csCoreBodies st) (csOwnership st)
            directPrimReadBody =
              replaceGlobInSimpleApp
                (gPrel (T.pack "__ioReadRef"))
                (GName primModule (T.pack "__ioReadRef"))
                <$> Map.lookup primReadRefBorrowG (csCoreBodies st)
            directPrimReadOwn =
              maybe
                Map.empty
                (\body -> annotateOwnershipWithUniverses ctx ctorTypes (Map.singleton primReadRefBorrowG body))
                directPrimReadBody
            directPrimReadDump =
              case Map.lookup primReadRefBorrowG directPrimReadOwn of
                Nothing -> T.empty
                Just oi -> renderOwnInfo primReadRefBorrowG oi
            checks =
              [ ( "borrowed call arg records LastUse consumes=False"
                , T.pack "LastUse consumes=False" `T.isInfixOf` passDump
                )
              , ( "borrowed call arg still counts as runtime use"
                , refinedOf passG == Right (Just (1, Just 1))
                )
              , ( "alias-wrapped borrowed call arg records non-consuming use"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf aliasPassG
                    && refinedOf aliasPassG == Right (Just (1, Just 1))
                )
              , ( "alias-wrapped local borrowed callee records read argument"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf localAliasG
                )
              , ( "alias-wrapped local Q0 callee records runtime read"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf localAliasIgnoreG
                )
              , ( "typed local lambda RHS uses annotated borrowed callee parameter"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf localAnnotatedG
                )
              , ( "branch-computed borrowed arg preserves read context"
                , T.count (T.pack "LastUse consumes=False") (dumpOf choosePeekG) >= 2
                )
              , ( "Q0 erased arg does not count as runtime use"
                , refinedOf erasedG == Right (Just (0, Just 0))
                )
              , ( "higher-order local linear call cross-checks"
                , null focusedXc
                )
              , ( "higher-order local linear call records consuming uses"
                , T.count (T.pack "LastUse consumes=True") (dumpOf applyG) >= 2
                )
              , ( "local Q0 first-class call records runtime read, not erasure"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf localIgnoreG
                )
              , ( "pattern-bound borrowed callee records read argument"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf useWrapG
                )
              , ( "alias-wrapped constructor callee records read argument"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf useWrapAliasG
                )
              , ( "parameterized constructor field instantiates borrowed callee type"
                , T.pack "NonLast consumes=False" `T.isInfixOf` dumpOf useParamCtorG
                )
              , ( "alias-wrapped record callee records read argument"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf useRecordAliasG
                )
              , ( "projected record callee records read argument"
                , T.pack "NonLast consumes=False" `T.isInfixOf` dumpOf useProjectedCalleeG
                )
              , ( "alias-wrapped tuple callee records read argument"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf useTupleAliasG
                )
              , ( "variant payload callee records read argument"
                , T.pack "NonLast consumes=False" `T.isInfixOf` dumpOf useVariantG
                )
              , ( "kind-domain non-Q0 arg does not count as runtime use"
                , refinedOf typeOnlyG == Right (Just (0, Just 0))
                    && not (T.pack "\n  use " `T.isInfixOf` dumpOf typeOnlyG)
                )
              , ( "alias-wrapped kind-domain arg does not count as runtime use"
                , refinedOf typeOnlyAliasG == Right (Just (0, Just 0))
                    && not (T.pack "\n  use " `T.isInfixOf` dumpOf typeOnlyAliasG)
                )
              , ( "projection-only read records non-consuming LastUse"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf projOnlyG
                )
              , ( "projection-only read still counts as runtime use"
                , refinedOf projOnlyG == Right (Just (1, Just 1))
                )
              , ( "read-only NonLast does not consume"
                , T.pack "NonLast consumes=False" `T.isInfixOf` dumpOf useBorrowTwiceG
                )
              , ( "primitive IORef read arg records non-consuming use"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf primReadRefBorrowG
                )
              , ( "direct primModule IORef read arg records non-consuming use"
                , T.pack "LastUse consumes=False" `T.isInfixOf` directPrimReadDump
                )
              , ( "primitive IORef write borrows ref and transfers value"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf primWriteRefTransferG
                    && T.pack "LastUse consumes=True" `T.isInfixOf` dumpOf primWriteRefTransferG
                )
              , ( "primitive TVar read arg records non-consuming use"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf tvarReadBorrowG
                )
              , ( "primitive TVar write borrows ref and transfers value"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf tvarWriteTransferG
                    && T.pack "LastUse consumes=True" `T.isInfixOf` dumpOf tvarWriteTransferG
                )
              , ( "primitive FiberRef get arg records non-consuming use"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf fiberGetBorrowG
                )
              , ( "primitive FiberRef set borrows ref and transfers value"
                , T.pack "LastUse consumes=False" `T.isInfixOf` dumpOf fiberSetTransferG
                    && T.pack "LastUse consumes=True" `T.isInfixOf` dumpOf fiberSetTransferG
                )
              , ( "linear cross-check rejects read-only LastUse"
                , not (null forcedMsgs)
                )
              , ( "cross-check rejects missing OwnInfo entry"
                , not (null missingMsgs)
                )
              , ( "cross-check rejects stored oiUses drift"
                , not (null driftUsesMsgs)
                )
              , ( "cross-check rejects stored oiBinderUses drift"
                , not (null driftBinderUsesMsgs)
                )
              , ( "cross-check rejects stored oiBinders drift"
                , not (null driftBindersMsgs)
                )
              ]
            failed = [name | (name, ok) <- checks, not ok]
         in (null failed, failed, passDump, forcedMsgs, focusedXc, refinedOf passG, refinedOf erasedG, refinedOf typeOnlyG, refinedOf projOnlyG)
      ( focusedOK
        , focusedFailed
        , focusedPassDump
        , focusedForcedMsgs
        , focusedXcOut
        , focusedPassRefined
        , focusedErasedRefined
        , focusedTypeRefined
        , focusedProjRefined
        ) = focused
  unless (null mismatches) $ do
    putStrLn ("ownershipCrossCheckClean FAILED: " <> show (length mismatches) <> " mismatch(es)")
    mapM_ (putStrLn . ("  " <>)) (take 20 mismatches)
  unless focusedOK $ do
    putStrLn "ownershipCrossCheckClean focused consume/read regressions FAILED:"
    mapM_ (putStrLn . ("  " <>)) focusedFailed
    putStrLn ("  passRefined=" <> show focusedPassRefined)
    putStrLn ("  erasedRefined=" <> show focusedErasedRefined)
    putStrLn ("  typeOnlyRefined=" <> show focusedTypeRefined)
    putStrLn ("  projOnlyRefined=" <> show focusedProjRefined)
    putStrLn ("  focusedMsgs=" <> show focusedXcOut)
    putStrLn ("  forcedMsgs=" <> show focusedForcedMsgs)
    putStrLn ("  passDump=" <> T.unpack focusedPassDump)
  pure (null mismatches && focusedOK)

-- | Perceus S2.3d regression: when a locally-owned droppable binder is consumed
-- on one branch and omitted on a sibling branch, RC-on C codegen must drop the
-- existing flat local on the omitting branch. This pins the codegen behavior,
-- not just the ownership metadata: constructor let-locals whose Core reaches
-- codegen as eta-constructor applications are droppable, including after a
-- guarded arm's non-consuming guard succeeds. Incoming params are deliberately
-- not treated as owned at this stage because caller-side ownership transfer is
-- not yet normalized.
perceusS23dDeadBinderDrops :: IO Bool
perceusS23dDeadBinderDrops = do
  let src =
        T.unlines
          [ "module main"
          , "data Box : Type ="
          , "    MkBox (value : Int)"
          , "data Holder : Type ="
          , "    Holder (box : Box)"
          , "type RHolder : Type = (box : Box,)"
          , "consumeBox : Box -> Int"
          , "let consumeBox b ="
          , "    match b"
          , "    case MkBox n -> n"
          , "peekBox : (& b : Box) -> Bool"
          , "let peekBox b = b.value == 4"
          , "peekHolder : (& h : Holder) -> Int"
          , "let peekHolder h = h.box.value"
          , "peekRHolder : (& h : RHolder) -> Int"
          , "let peekRHolder h = h.box.value"
          , "alwaysFalseConsume : Box -> Bool"
          , "let alwaysFalseConsume b ="
          , "    match b"
          , "    case MkBox n -> False"
          , "branchIf : Bool -> Box -> Int"
          , "let branchIf c x ="
          , "    if c"
          , "    then consumeBox x"
          , "    else 0"
          , "branchMatch : Option Int -> Box -> Int"
          , "let branchMatch o x ="
          , "    match o"
          , "    case Some n -> consumeBox x"
          , "    case None -> 0"
          , "branchLetIf : Bool -> Int"
          , "let branchLetIf c ="
          , "    let x = MkBox 3"
          , "    if c"
          , "    then consumeBox x"
          , "    else 0"
          , "branchGuardLet : Option Int -> Int"
          , "let branchGuardLet o ="
          , "    let x = MkBox 4"
          , "    match o"
          , "    case Some n if peekBox x -> n"
          , "    case Some n -> consumeBox x"
          , "    case None -> consumeBox x"
          , "branchAliasParam : Bool -> Box -> Int"
          , "let branchAliasParam c x ="
          , "    let y = x"
          , "    if c"
          , "    then consumeBox y"
          , "    else 0"
          , "branchBorrowedAlias : Bool -> Int"
          , "let branchBorrowedAlias c ="
          , "    let h = Holder (MkBox 6)"
          , "    let y = h.box"
          , "    if c"
          , "    then consumeBox y"
          , "    else peekHolder h"
          , "branchBorrowedRecordAlias : Bool -> Int"
          , "let branchBorrowedRecordAlias c ="
          , "    let h : RHolder = (box = MkBox 9,)"
          , "    let y = h.box"
          , "    if c"
          , "    then consumeBox y"
          , "    else peekRHolder h"
          , "branchBorrowedNestedAlias : Bool -> Int"
          , "let branchBorrowedNestedAlias c ="
          , "    let h : RHolder = (box = MkBox 12,)"
          , "    let y = let z = 0 in h.box"
          , "    if c"
          , "    then consumeBox y"
          , "    else peekRHolder h"
          , "branchNestedClosure : Bool -> Int"
          , "let branchNestedClosure c ="
          , "    (\\n -> let x = MkBox 11 in if c then consumeBox x else 0) 0"
          , "branchGuardConsumeFallthrough : Option Int -> Box -> Int"
          , "let branchGuardConsumeFallthrough o x ="
          , "    match o"
          , "    case Some n if alwaysFalseConsume x -> n"
          , "    case Some n -> consumeBox x"
          , "    case None -> 0"
          , "branchGuardConsumeLocalFallthrough : Option Int -> Int"
          , "let branchGuardConsumeLocalFallthrough o ="
          , "    let x = MkBox 13"
          , "    match o"
          , "    case Some n if alwaysFalseConsume x -> n"
          , "    case Some n -> 0"
          , "    case None -> 0"
          , "borrowedProjectionFalse : Int"
          , "let borrowedProjectionFalse ="
          , "    let h = Holder (MkBox 5)"
          , "    branchIf False h.box"
          , "main : UIO Unit"
          , "let main = printInt (branchIf True (MkBox 1) + branchIf False (MkBox 10) + branchMatch (Some 2) (MkBox 2) + branchMatch None (MkBox 20) + branchLetIf True + branchLetIf False + branchGuardLet (Some 10) + branchGuardLet None + branchAliasParam True (MkBox 7) + branchAliasParam False (MkBox 70) + branchBorrowedAlias True + branchBorrowedAlias False + branchBorrowedRecordAlias True + branchBorrowedRecordAlias False + branchBorrowedNestedAlias True + branchBorrowedNestedAlias False + branchNestedClosure True + branchNestedClosure False + branchGuardConsumeFallthrough (Some 8) (MkBox 8) + branchGuardConsumeLocalFallthrough (Some 13) + branchGuardConsumeLocalFallthrough None + borrowedProjectionFalse)"
          ]
      cu = compileSourceWithPrelude "perceus-s23d.kp" src
      st = cuState cu
      mainG = GName (ModuleName [T.pack "main"]) (T.pack "main")
      worker signature csrc =
        case T.breakOn marker csrc of
          (_, "") -> Nothing
          (_, rest) -> Just (takeBalancedWorkerFunction rest)
        where
          marker = "static KValue *" <> signature <> " {"
      takeBalancedWorkerFunction txt =
        T.unlines (go 0 [] (T.lines txt))
        where
          go _ acc [] = reverse acc
          go depth acc (line : rest) =
            let depth' = depth + T.count "{" line - T.count "}" line
                acc' = line : acc
             in if not (null acc) && depth' <= 0
                  then reverse acc'
                  else go depth' acc' rest
      prefixedLineBefore needle stop body =
        let ls = T.lines body
            beforeStop = takeWhile (not . T.isInfixOf stop) ls
         in any (T.isPrefixOf needle . T.strip) beforeStop
      sliceFromUntil start stop body =
        T.unlines $
          takeWhile (not . T.isInfixOf stop) $
            dropWhile (not . T.isInfixOf start) (T.lines body)
      afterMarker marker body =
        T.unlines $
          drop 1 $
            dropWhile (not . T.isInfixOf marker) (T.lines body)
      noDropBefore needle body =
        not (prefixedLineBefore "kdrop(let_" needle body)
      firstLetAssignedBy rhs body =
        case
          [ name
          | line <- T.lines body
          , let s = T.strip line
          , rhs `T.isInfixOf` s
          , Just name <- [letLocalName s]
          ] of
          name : _ -> Just name
          [] -> Nothing
      letLocalName s =
        case T.stripPrefix "KValue *" s of
          Just rest
            | "let_" `T.isPrefixOf` rest ->
                Just (T.takeWhile (/= ' ') rest)
          _ -> Nothing
      noOwnerDropBefore rhs needle fullBody branchBody =
        case firstLetAssignedBy rhs fullBody of
          Nothing -> False
          Just owner -> not (prefixedLineBefore ("kdrop(" <> owner <> ");") needle branchBody)
      dropLetBeforeReturn body =
        let ls = T.lines body
         in any
              ( \ls' -> case ls' of
                  a : b : _ -> "kdrop(let_" `T.isPrefixOf` T.strip a && "return " `T.isPrefixOf` T.strip b
                  _ -> False
              )
              (tailsText ls)
      tailsText [] = []
      tailsText xs@(_ : rest) = xs : tailsText rest
      report label body = do
        putStrLn ("  " <> label <> " worker:")
        putStrLn (T.unpack body)
  case generateC True True st mainG Set.empty Map.empty of
    Left (errs, mLog) -> do
      putStrLn ("perceusS23dDeadBinderDrops FAILED: generateC rejected: " <> show errs)
      putStrLn ("  rcLog=" <> show mLog)
      putStrLn
        ( "  Eq member quantities="
            <> show (tiMemberQs <$> Map.lookup (gPrel "Eq") (csTraits st))
        )
      putStrLn
        ( "  Eq.eqSound type="
            <> maybe "<missing>" (T.unpack . maybe "<unquoted>" renderTerm . gdCoreType)
              (Map.lookup (gPrel "Eq.eqSound") (csGlobals st))
        )
      pure False
    Right (csrc, _) -> do
      let requiredWorkers :: [(String, T.Text)]
          requiredWorkers =
            [ ("branchIf", "kw_main_2e_branchIf(KValue *p0, KValue *p1)")
            , ("branchMatch", "kw_main_2e_branchMatch(KValue *p0, KValue *p1)")
            , ("branchLetIf", "kw_main_2e_branchLetIf(KValue *p0)")
            , ("branchGuardLet", "kw_main_2e_branchGuardLet(KValue *p0)")
            , ("branchAliasParam", "kw_main_2e_branchAliasParam(KValue *p0, KValue *p1)")
            , ("branchBorrowedAlias", "kw_main_2e_branchBorrowedAlias(KValue *p0)")
            , ("branchBorrowedRecordAlias", "kw_main_2e_branchBorrowedRecordAlias(KValue *p0)")
            , ("branchBorrowedNestedAlias", "kw_main_2e_branchBorrowedNestedAlias(KValue *p0)")
            , ("branchGuardConsumeFallthrough", "kw_main_2e_branchGuardConsumeFallthrough(KValue *p0, KValue *p1)")
            , ("branchGuardConsumeLocalFallthrough", "kw_main_2e_branchGuardConsumeLocalFallthrough(KValue *p0)")
            ]
          extracted = [(label, worker sig csrc) | (label, sig) <- requiredWorkers]
          missing = [label | (label, Nothing) <- extracted]
          lookupWorker label =
            case [body | (label', Just body) <- extracted, label' == label] of
              body : _ -> body
              [] -> ""
          ifWorker = lookupWorker "branchIf"
          matchWorker = lookupWorker "branchMatch"
          letWorker = lookupWorker "branchLetIf"
          guardWorker = lookupWorker "branchGuardLet"
          aliasWorker = lookupWorker "branchAliasParam"
          borrowedWorker = lookupWorker "branchBorrowedAlias"
          borrowedRecordWorker = lookupWorker "branchBorrowedRecordAlias"
          borrowedNestedWorker = lookupWorker "branchBorrowedNestedAlias"
          guardConsumeWorker = lookupWorker "branchGuardConsumeFallthrough"
          guardConsumeLocalWorker = lookupWorker "branchGuardConsumeLocalFallthrough"
          guardSuccess = sliceFromUntil "kw_main_2e_peekBox(let_" "matched_" guardWorker
          borrowedElse = afterMarker "} else {" borrowedWorker
          borrowedRecordThen = sliceFromUntil "if (kas_bool" "} else {" borrowedRecordWorker
          borrowedRecordElse = afterMarker "} else {" borrowedRecordWorker
          borrowedNestedThen = sliceFromUntil "if (kas_bool" "} else {" borrowedNestedWorker
          borrowedNestedElse = afterMarker "} else {" borrowedNestedWorker
          dupedCtorField fn =
            "kdup(kctor_arg" `T.isInfixOf` fn
              || any
                ( \line ->
                    "kdup(scrut_" `T.isInfixOf` line
                      && "->as.ctor.args[" `T.isInfixOf` line
                )
                (T.lines fn)
          nestedClosureOk =
            any
              ( \fn ->
                  "consumeBox" `T.isInfixOf` fn
                    && "kctor(" `T.isInfixOf` fn
                    && dropLetBeforeReturn fn
              )
              (nestedClosureFunctions csrc)
          paramsOk =
            null missing
              && not ("kdrop(p1);" `T.isInfixOf` ifWorker)
              && not ("kdrop(p1);" `T.isInfixOf` matchWorker)
              && not ("kdrop(scrut_" `T.isInfixOf` matchWorker)
          letOk =
            not (prefixedLineBefore "kdrop(let_" "} else {" letWorker)
              && "} else {" `T.isInfixOf` letWorker
              && dropLetBeforeReturn (snd (T.breakOn "} else {" letWorker))
          guardOk =
            "if (kas_bool(" `T.isInfixOf` guardWorker
              && "kw_main_2e_peekBox(let_" `T.isInfixOf` guardWorker
              && dropLetBeforeReturn guardSuccess
          aliasOk =
            "consumeBox" `T.isInfixOf` aliasWorker
              && not ("kdrop(let_" `T.isInfixOf` aliasWorker)
          borrowedAliasOk =
            dupedCtorField borrowedWorker
              && "consumeBox" `T.isInfixOf` borrowedWorker
              && "peekHolder" `T.isInfixOf` borrowedWorker
              && noOwnerDropBefore " = kctor(" "peekHolder" borrowedWorker borrowedElse
          borrowedRecordAliasOk =
            "consumeBox" `T.isInfixOf` borrowedRecordWorker
              && "peekRHolder" `T.isInfixOf` borrowedRecordWorker
              && "kdup(krec_at" `T.isInfixOf` borrowedRecordWorker
              && noDropBefore "consumeBox" borrowedRecordThen
              && noOwnerDropBefore " = krec(" "peekRHolder" borrowedRecordWorker borrowedRecordElse
          borrowedNestedAliasOk =
            "consumeBox" `T.isInfixOf` borrowedNestedWorker
              && "peekRHolder" `T.isInfixOf` borrowedNestedWorker
              && "if (kas_bool(p0))" `T.isInfixOf` borrowedNestedWorker
              && "kdup(krec_at" `T.isInfixOf` borrowedNestedWorker
              && noDropBefore "consumeBox" borrowedNestedThen
              && noOwnerDropBefore " = krec(" "peekRHolder" borrowedNestedWorker borrowedNestedElse
          guardConsumeOk =
            "kw_main_2e_alwaysFalseConsume(kdup(p1))" `T.isInfixOf` guardConsumeWorker
          guardConsumeLocalOk =
            "alwaysFalseConsume" `T.isInfixOf` guardConsumeLocalWorker
              && ( "alwaysFalseConsume(kdup(let_" `T.isInfixOf` guardConsumeLocalWorker
                     || not ("kdrop(let_" `T.isInfixOf` guardConsumeLocalWorker)
                 )
          ok = paramsOk && letOk && guardOk && aliasOk && borrowedAliasOk && borrowedRecordAliasOk && borrowedNestedAliasOk && nestedClosureOk && guardConsumeOk && guardConsumeLocalOk
      unless ok $ do
        putStrLn "perceusS23dDeadBinderDrops FAILED:"
        putStrLn ("  missingWorkers=" <> show missing)
        putStrLn ("  paramsOk=" <> show paramsOk <> " letOk=" <> show letOk <> " guardOk=" <> show guardOk <> " aliasOk=" <> show aliasOk <> " borrowedAliasOk=" <> show borrowedAliasOk <> " borrowedRecordAliasOk=" <> show borrowedRecordAliasOk <> " borrowedNestedAliasOk=" <> show borrowedNestedAliasOk <> " nestedClosureOk=" <> show nestedClosureOk <> " guardConsumeOk=" <> show guardConsumeOk <> " guardConsumeLocalOk=" <> show guardConsumeLocalOk)
        unless paramsOk (report "branchIf" ifWorker >> report "branchMatch" matchWorker)
        unless letOk (report "branchLetIf" letWorker)
        unless guardOk (report "branchGuardLet" guardWorker)
        unless aliasOk (report "branchAliasParam" aliasWorker)
        unless borrowedAliasOk (report "branchBorrowedAlias" borrowedWorker)
        unless borrowedRecordAliasOk (report "branchBorrowedRecordAlias" borrowedRecordWorker)
        unless borrowedNestedAliasOk (report "branchBorrowedNestedAlias" borrowedNestedWorker)
        unless nestedClosureOk (putStrLn "  nested closure functions:" >> mapM_ (putStrLn . T.unpack) (nestedClosureFunctions csrc))
        unless guardConsumeOk (report "branchGuardConsumeFallthrough" guardConsumeWorker)
        unless guardConsumeLocalOk (report "branchGuardConsumeLocalFallthrough" guardConsumeLocalWorker)
      pure ok
  where
    nestedClosureFunctions csrc =
      let starts = T.breakOnAll "static KValue *kfn_" csrc
       in [takeBalancedFunction rest | (_, rest) <- starts]

    takeBalancedFunction txt =
      T.unlines (go 0 [] (T.lines txt))
      where
        go _ acc [] = reverse acc
        go depth acc (line : rest) =
          let depth' = depth + T.count "{" line - T.count "}" line
              acc' = line : acc
           in if not (null acc) && depth' <= 0
                then reverse acc'
                else go depth' acc' rest

-- | S5.A regression for the former S2.3d path-drift diagnostic: branch-drop
-- metadata is now produced on KBackendIR node identities, so tampering with the
-- legacy path-keyed 'csOwnership' table must not affect native codegen. This is
-- the structural replacement for the old "branch drop path miss" failure mode.
perceusS23dLegacyPathTamperIgnoredS5 :: IO Bool
perceusS23dLegacyPathTamperIgnoredS5 = do
  let src =
        T.unlines
          [ "module main"
          , "data Box : Type ="
          , "    MkBox Int"
          , "consumeBox : Box -> Int"
          , "let consumeBox b ="
          , "    match b"
          , "    case MkBox n -> n"
          , "branchLetIf : Bool -> Int"
          , "let branchLetIf c ="
          , "    let x = MkBox 3"
          , "    if c"
          , "    then consumeBox x"
          , "    else 0"
          , "main : UIO Unit"
          , "let main = printInt (branchLetIf False)"
          ]
      cu = compileSourceWithPrelude "perceus-s23d-branch-drop-miss.kp" src
      st = cuState cu
      mainG = GName (ModuleName [T.pack "main"]) (T.pack "main")
      branchG = GName (ModuleName [T.pack "main"]) (T.pack "branchLetIf")
  case Map.lookup branchG (csOwnership st) of
    Nothing -> do
      putStrLn "perceusS23dBranchDropMissFails FAILED: no ownership table for branchLetIf"
      pure False
    Just own ->
      case Map.lookupMin (oiBranchDropSites own) of
        Nothing -> do
          putStrLn "perceusS23dBranchDropMissFails FAILED: no branch drop site in source program"
          pure False
        Just (site@(BranchSite siteId), bids) -> do
          let fakeBid = BinderId branchG (siteId + 9999)
              fakeOwn = BinderOwn QW Nothing False True
              own' =
                own
                  { oiBinders = Map.insert fakeBid fakeOwn (oiBinders own)
                  , oiBranchDropSites = Map.singleton site [fakeBid]
                  }
              st' = st {csOwnership = Map.insert branchG own' (csOwnership st)}
              staleSite = BranchSite (siteId + 8888)
              ownStaleBranchSite = own {oiBranchDropSites = Map.singleton staleSite bids}
              stStaleBranchSite = st {csOwnership = Map.insert branchG ownStaleBranchSite (csOwnership st)}
              expectAccepted label stCase =
                case generateC True True stCase mainG Set.empty Map.empty of
                  Right (csrc, _) ->
                    if "kdrop(let_" `T.isInfixOf` csrc
                      then pure True
                      else do
                        putStrLn ("perceusS23dLegacyPathTamperIgnoredS5 FAILED: " <> label <> " generated no node-local branch drop")
                        pure False
                  Left (errs, mFindings) -> do
                    putStrLn ("perceusS23dLegacyPathTamperIgnoredS5 FAILED: " <> label <> " was rejected")
                    putStrLn ("  errs=" <> show errs)
                    putStrLn ("  findings=" <> show mFindings)
                    pure False
          unresolvedOk <-
            expectAccepted
              "unresolved branch drop site"
              st'
          staleBranchSiteOk <-
            expectAccepted
              "stale branch drop site"
              stStaleBranchSite
          pure (unresolvedOk && staleBranchSiteOk)

-- | Perceus S3.2 generated-code entry gate: before runtime free-on-zero is
-- enabled, the C backend must own escaping projections and attach proven
-- scope/match drops to every tail exit. Otherwise recursive freeing can turn a
-- borrowed field return into a use-after-free or let a tail return bypass the
-- last drop.
perceusS32FreeOnZeroEntryGates :: IO Bool
perceusS32FreeOnZeroEntryGates = do
  let src =
        T.unlines
          [ "module main"
          , "data Box : Type ="
          , "    MkBox Int"
          , "data BigBox : Type ="
          , "    MkBigBox String Int"
          , "type Pair : Type = (left : Box, right : Box)"
          , "consumeBox : Box -> Int"
          , "let consumeBox b ="
          , "    match b"
          , "    case MkBox n -> n"
          , "inlineEtaCtorMatch : Int -> Int"
          , "let inlineEtaCtorMatch n ="
          , "    match MkBigBox (showInt n) n"
          , "    case MkBigBox s m -> m"
          , "returnRecordProjection : Bool -> Box"
          , "let returnRecordProjection c ="
          , "    let p : Pair = (left = MkBox 1, right = MkBox 2)"
          , "    if c"
          , "    then p.left"
          , "    else p.right"
          , "returnNestedProjection : Bool -> Box"
          , "let returnNestedProjection c ="
          , "    let p : Pair = (left = MkBox 7, right = MkBox 8)"
          , "    let y = let z = 0 in if c then p.left else p.right"
          , "    y"
          , "consumeRecordProjection : Bool -> Int"
          , "let consumeRecordProjection c ="
          , "    let p : Pair = (left = MkBox 3, right = MkBox 4)"
          , "    if c"
          , "    then consumeBox p.left"
          , "    else consumeBox p.right"
          , "returnMatchedField : Bool -> Box"
          , "let returnMatchedField c ="
          , "    let o = if c then Some (MkBox 5) else Some (MkBox 6)"
          , "    match o"
          , "    case Some b -> b"
          , "    case None -> MkBox 0"
          , "main : UIO Unit"
          , "let main = printInt (inlineEtaCtorMatch 9 + consumeBox (returnRecordProjection True) + consumeBox (returnNestedProjection False) + consumeRecordProjection False + consumeBox (returnMatchedField True))"
          ]
      cu = compileSourceWithPrelude "perceus-s32-entry-gates.kp" src
      st = cuState cu
      mainG = GName (ModuleName [T.pack "main"]) (T.pack "main")
      worker signature csrc =
        case T.breakOn marker csrc of
          (_, "") -> Nothing
          (_, rest) -> Just (takeBalancedWorkerFunction rest)
        where
          marker = "static KValue *" <> signature <> " {"
      takeBalancedWorkerFunction txt =
        T.unlines (go 0 [] (T.lines txt))
        where
          go _ acc [] = reverse acc
          go depth acc (line : rest) =
            let depth' = depth + T.count "{" line - T.count "}" line
                acc' = line : acc
             in if not (null acc) && depth' <= 0
                  then reverse acc'
                  else go depth' acc' rest
      dropBeforeReturn body =
        any
          ( \ls -> case ls of
              a : b : _ -> "kdrop(" `T.isPrefixOf` T.strip a && "return " `T.isPrefixOf` T.strip b
              _ -> False
          )
          (tailsText (T.lines body))
      tailsText [] = []
      tailsText xs@(_ : rest) = xs : tailsText rest
      report label body = do
        putStrLn ("  " <> label <> " worker:")
        putStrLn (T.unpack body)
  case generateC True True st mainG Set.empty Map.empty of
    Left (errs, mLog) -> do
      putStrLn ("perceusS32FreeOnZeroEntryGates FAILED: generateC rejected: " <> show errs)
      putStrLn ("  rcLog=" <> show mLog)
      pure False
    Right (csrc, _) -> do
      let requiredWorkers :: [(String, T.Text)]
          requiredWorkers =
            [ ("returnRecordProjection", "kw_main_2e_returnRecordProjection(KValue *p0)")
            , ("returnNestedProjection", "kw_main_2e_returnNestedProjection(KValue *p0)")
            , ("consumeRecordProjection", "kw_main_2e_consumeRecordProjection(KValue *p0)")
            , ("inlineEtaCtorMatch", "kw_main_2e_inlineEtaCtorMatch(KValue *p0)")
            , ("returnMatchedField", "kw_main_2e_returnMatchedField(KValue *p0)")
            ]
          extracted = [(label, worker sig csrc) | (label, sig) <- requiredWorkers]
          missing = [label | (label, Nothing) <- extracted]
          lookupWorker label =
            case [body | (label', Just body) <- extracted, label' == label] of
              body : _ -> body
              [] -> ""
          returnProjWorker = lookupWorker "returnRecordProjection"
          returnNestedWorker = lookupWorker "returnNestedProjection"
          consumeProjWorker = lookupWorker "consumeRecordProjection"
          inlineEtaWorker = lookupWorker "inlineEtaCtorMatch"
          returnMatchWorker = lookupWorker "returnMatchedField"
          dupedCtorField fn =
            "kdup(kctor_arg" `T.isInfixOf` fn
              || any
                ( \line ->
                    "kdup(scrut_" `T.isInfixOf` line
                      && "->as.ctor.args[" `T.isInfixOf` line
                )
                (T.lines fn)
          projectionOwnsOk =
            "kdup(krec_at(let_" `T.isInfixOf` returnProjWorker
              && "kdup(krec_at(let_" `T.isInfixOf` returnNestedWorker
              && "kdup(krec_at(let_" `T.isInfixOf` consumeProjWorker
          tailDropsOk =
            dropBeforeReturn returnProjWorker
              && dropBeforeReturn returnNestedWorker
              && dropBeforeReturn consumeProjWorker
              && dropBeforeReturn returnMatchWorker
          matchFieldsOk =
            dupedCtorField returnMatchWorker
              && "kdrop(scrut_" `T.isInfixOf` returnMatchWorker
          inlineEtaMatchDropsOk =
            "kdrop(scrut_" `T.isInfixOf` inlineEtaWorker
          ok = null missing && projectionOwnsOk && tailDropsOk && matchFieldsOk
            && inlineEtaMatchDropsOk
      unless ok $ do
        putStrLn "perceusS32FreeOnZeroEntryGates FAILED:"
        putStrLn ("  missingWorkers=" <> show missing)
        putStrLn ("  projectionOwnsOk=" <> show projectionOwnsOk <> " tailDropsOk=" <> show tailDropsOk <> " matchFieldsOk=" <> show matchFieldsOk <> " inlineEtaMatchDropsOk=" <> show inlineEtaMatchDropsOk)
        report "returnRecordProjection" returnProjWorker
        report "returnNestedProjection" returnNestedWorker
        report "consumeRecordProjection" consumeProjWorker
        report "inlineEtaCtorMatch" inlineEtaWorker
        report "returnMatchedField" returnMatchWorker
      pure ok

-- | Perceus S3.1/S3.4 regression: arity-0/global caches are process-wide
-- publication cells.  The C backend, which emits ownership maintenance and can
-- free on zero, must mark the freshly-built value graph shared before writing
-- the static cache.  LLVM currently emits no matching ownership maintenance, so
  -- its generated binaries must explicitly disable runtime counting/freeing
  -- effects; publication marking still emits because the shared bit is
  -- synchronization metadata for process-wide caches.
globalCachePublicationMarksShared :: IO Bool
globalCachePublicationMarksShared = do
  let src =
        T.unlines
          [ "module main"
          , "let cached = \"cache-payload\""
          , "let ident (x : String) = x"
          , "main : UIO Unit"
          , "let main = printlnString (ident cached)"
          ]
      cu = compileSourceWithPrelude "s31-cache-publication.kp" src
      st = cuState cu
      mainG = GName (ModuleName [T.pack "main"]) (T.pack "main")
      checkC csrc =
        let accessors = cacheAccessorBodies csrc
         in "#include <stdatomic.h>" `T.isInfixOf` csrc
              && length accessors >= 2
              && all cacheAccessorReturnsCountedOwner accessors
      checkLL llsrc =
        "declare void @krc_set_enabled(i32)" `T.isInfixOf` llsrc
          && "call void @krc_set_enabled(i32 0)" `T.isInfixOf` llsrc
          && "krc_mark_shared_recursive" `T.isInfixOf` llsrc
          && "load atomic ptr, ptr @" `T.isInfixOf` llsrc
          && " acquire, align 8" `T.isInfixOf` llsrc
          && " release, align 8" `T.isInfixOf` llsrc
  cOk <-
    case generateC True True st mainG Set.empty Map.empty of
      Left (errs, mLog) -> do
        putStrLn ("globalCachePublicationMarksShared FAILED: generateC rejected: " <> show errs)
        putStrLn ("  rcLog=" <> show mLog)
        pure False
      Right (csrc, _) -> do
        unless (checkC csrc) $ do
          putStrLn "globalCachePublicationMarksShared FAILED: C cache accessor did not publish and return distinct counted owners"
          putStrLn (T.unpack csrc)
        pure (checkC csrc)
  llOk <-
    case generateLL True True st mainG Set.empty Map.empty of
      Left (errs, mLog) -> do
        putStrLn ("globalCachePublicationMarksShared FAILED: generateLL rejected: " <> show errs)
        putStrLn ("  rcLog=" <> show mLog)
        pure False
      Right (llsrc, _) -> do
        unless (checkLL llsrc) $ do
          putStrLn "globalCachePublicationMarksShared FAILED: LLVM cache publication did not mark shared while keeping runtime RC disabled"
          putStrLn (T.unpack llsrc)
        pure (checkLL llsrc)
  pure (cOk && llOk)

-- | Scalar worker regression: explicit kind-domain binders are runtime-erased.
-- A source function with type `(a : Type) -> Int -> Int` still has two leading
-- Core lambdas, but the worker ABI has one runtime `Int` slot. Both backends
-- must use the shared representation-table mask to drop the static binder
-- instead of disabling the proven `kwi_` worker.
scalarKindDomainParamKeepsWorkers :: IO Bool
scalarKindDomainParamKeepsWorkers = do
  let src =
        T.unlines
          [ "module main"
          , "let addOne (a : Type) (x : Int) = addInt x 1"
          , "main : UIO Unit"
          , "let main = printlnString (showInt (addOne Int 41))"
          ]
      cu = compileSourceWithPrelude "s31-scalar-kind-param.kp" src
      st = cuState cu
      mainG = GName (ModuleName [T.pack "main"]) (T.pack "main")
      worker = "kwi_main_2e_addOne"
      argsAfter needle line =
        let mark = needle <> "("
         in case T.breakOn mark line of
              (_, rest) | T.null rest -> Nothing
              (_, rest) ->
                let after = T.drop (T.length mark) rest
                    (inside, suffix) = T.breakOn ")" after
                 in if T.null suffix then Nothing else Just (map T.strip (T.splitOn "," inside))
      cCallShape csrc =
        any
          ( \line ->
              " = " `T.isInfixOf` line
                && case argsAfter worker line of
                  Just [a, b] ->
                    "lu_" `T.isPrefixOf` a
                      && "&kovf_" `T.isPrefixOf` b
                      && not ("la_" `T.isInfixOf` line)
                  _ -> False
          )
          (T.lines csrc)
      llCallShape llsrc =
        any
          ( \line ->
              ("call i64 @" <> worker <> "(") `T.isInfixOf` line
                && case argsAfter ("@" <> worker) line of
                  Just [a, b] ->
                    "i64 %" `T.isPrefixOf` a
                      && "ptr %" `T.isPrefixOf` b
                  _ -> False
          )
          (T.lines llsrc)
      cHasWorker csrc =
        ("static int64_t " <> worker <> "(int64_t p0, int *kovf)") `T.isInfixOf` csrc
          && cCallShape csrc
      llHasWorker llsrc =
        ("define internal i64 @" <> worker <> "(i64 %p0, ptr %kovf)") `T.isInfixOf` llsrc
          && llCallShape llsrc
  cOk <-
    case generateC False True st mainG Set.empty Map.empty of
      Left (errs, mLog) -> do
        putStrLn ("scalarKindDomainParamKeepsWorkers FAILED: generateC rejected: " <> show errs)
        putStrLn ("  rcLog=" <> show mLog)
        pure False
      Right (csrc, _) -> do
        unless (cHasWorker csrc) $ do
          putStrLn "scalarKindDomainParamKeepsWorkers FAILED: C omitted kwi_ worker"
          putStrLn (T.unpack csrc)
        pure (cHasWorker csrc)
  llOk <-
    case generateLL False True st mainG Set.empty Map.empty of
      Left (errs, mLog) -> do
        putStrLn ("scalarKindDomainParamKeepsWorkers FAILED: generateLL rejected: " <> show errs)
        putStrLn ("  rcLog=" <> show mLog)
        pure False
      Right (llsrc, _) -> do
        unless (llHasWorker llsrc) $ do
          putStrLn "scalarKindDomainParamKeepsWorkers FAILED: LLVM omitted kwi_ worker"
          putStrLn (T.unpack llsrc)
        pure (llHasWorker llsrc)
  pure (cOk && llOk)

llvmDoubleScalarUnboxEscapesWrongTag :: IO Bool
llvmDoubleScalarUnboxEscapesWrongTag = do
  let src =
        T.unlines
          [ "module main"
          , "let addHalf (x : Double) = addDouble x 0.5"
          , "main : UIO Unit"
          , "let main = printlnString (showDouble (addHalf 1.5))"
          ]
      cu = compileSourceWithPrelude "s31-double-scalar-escape.kp" src
      st = cuState cu
      mainG = GName (ModuleName [T.pack "main"]) (T.pack "main")
      helper =
        T.unlines
          [ "define internal double @kunbox_dbl_ll(ptr %v, ptr %ovf) {"
          , "entry:"
          , "  %d = call double @kunbox_dbl_runtime(ptr %v, ptr %ovf)"
          , "  ret double %d"
          , "}"
          ]
      checkLL llsrc =
        "declare double @kunbox_dbl_runtime(ptr, ptr)" `T.isInfixOf` llsrc
          && helper `T.isInfixOf` llsrc
          && not ("call double @kas_dbl(ptr %v)" `T.isInfixOf` llsrc)
          && doubleUnboxFallbackBranches llsrc
  case generateLL False True st mainG Set.empty Map.empty of
    Left (errs, mLog) -> do
      putStrLn ("llvmDoubleScalarUnboxEscapesWrongTag FAILED: generateLL rejected: " <> show errs)
      putStrLn ("  rcLog=" <> show mLog)
      pure False
    Right (llsrc, _) -> do
      unless (checkLL llsrc) $ do
        putStrLn "llvmDoubleScalarUnboxEscapesWrongTag FAILED: LLVM Double helper can still abort instead of escaping"
        putStrLn (T.unpack llsrc)
      pure (checkLL llsrc)

doubleUnboxFallbackBranches :: T.Text -> Bool
doubleUnboxFallbackBranches llsrc =
  let ls = T.lines llsrc
      windows = [take 8 (drop i ls) | (i, l) <- zip [0 :: Int ..] ls, "call double @kunbox_dbl_ll" `T.isInfixOf` l]
      okPreFallback w =
        any ("load i32, ptr" `T.isInfixOf`) w
          && any ("icmp ne i32" `T.isInfixOf`) w
          && any (\l -> "br i1" `T.isInfixOf` l && "label %kwboxed_" `T.isInfixOf` l) w
      boxedBlocks = [take 8 (drop i ls) | (i, l) <- zip [0 :: Int ..] ls, T.isPrefixOf "  kwboxed_" l]
      okBoxedBlock w =
        any ("call ptr @kapp(" `T.isInfixOf`) w
          && any ("call ptr @ktrampoline(" `T.isInfixOf`) w
   in any okPreFallback windows && any okBoxedBlock boxedBlocks

balancedFunctionBody :: T.Text -> T.Text
balancedFunctionBody txt = T.unlines (go (0 :: Int) [] (T.lines txt))
  where
    go _ acc [] = reverse acc
    go depth acc (l : ls) =
      let depth' = depth + T.count "{" l - T.count "}" l
          acc' = l : acc
       in if not (null acc) && depth' <= 0 then reverse acc' else go depth' acc' ls

cacheAccessorBodies :: T.Text -> [T.Text]
cacheAccessorBodies csrc =
  [ body
  | (_, start) <- T.breakOnAll "static KValue *" csrc
  , let body = balancedFunctionBody start
  , "static _Atomic(KValue *) cache = NULL;" `T.isInfixOf` body
  ]

cacheAccessorReturnsCountedOwner :: T.Text -> Bool
cacheAccessorReturnsCountedOwner body =
  "atomic_load_explicit(&cache, memory_order_acquire)" `T.isInfixOf` body
    && "if (cached) return kdup(cached);" `T.isInfixOf` body
    && "atomic_compare_exchange_strong_explicit(&cache, &expected, fresh" `T.isInfixOf` body
    && "return kdup(fresh);" `T.isInfixOf` body
    && "kdrop(fresh);" `T.isInfixOf` body
    && "return kdup(expected);" `T.isInfixOf` body
    && not ("return cached;" `T.isInfixOf` body)
    && not ("atomic_store_explicit(&cache, fresh" `T.isInfixOf` body)
    && allStoresMarkedImmediatelyBefore
      "if (atomic_compare_exchange_strong_explicit(&cache, &expected, fresh,"
      "krc_mark_shared_recursive(fresh);"
      body

allStoresMarkedImmediatelyBefore :: T.Text -> T.Text -> T.Text -> Bool
allStoresMarkedImmediatelyBefore storeNeedle markNeedle src =
  let ls = T.lines src
      storeIdxs = [i | (i, l) <- zip [0 :: Int ..] ls, storeNeedle `T.isInfixOf` l]
      prevNonEmpty i =
        case dropWhile T.null (reverse (take i (map T.strip ls))) of
          p : _ -> p
          [] -> T.empty
   in not (null storeIdxs) && all (\i -> markNeedle `T.isInfixOf` prevNonEmpty i) storeIdxs

-- | S5.A regression: KBackendIR must be a separate runtime tree, not an
-- annotated Core.Term wrapper. Erased positions are structurally absent, and
-- representation/ownership facts live on the nodes that need them.
backendIRPhaseAS5 :: IO Bool
backendIRPhaseAS5 = do
  let src =
        T.unlines
          [ "module main"
          , "data Box (a : Type) : Type = MkBox (value : a)"
          , "let idBox (a : Type) (b : Box a) ="
          , "    match b"
          , "    case MkBox x -> MkBox x"
          , "let useIdBox (a : Type) (b : Box a) = idBox a b"
          , "type R = (a : Type, b : Int)"
          , "type TypeOnly = (a : Type,)"
          , "type TupleErased = (a : Type, b : Int)"
          , "type RuntimeProofRec = (proof : (=) 1 1, value : Int)"
          , "type ErasedProofRec = (prop : IsProp ((=) \"x\" \"x\"), value : Int)"
          , "data GhostBox : Type = MkGhostBox (0 ghost : Int) (value : Int)"
          , "data ErasedTail : Type = MkErasedTail (a : Int) (b : Int) (c : Type)"
          , "data RepresentedFields : Type = MkRepresentedFields (n : Nat) (i : Fin 5)"
          , "foo : R"
          , "let foo = (a = Int, b = 5)"
          , "let useRecord = foo.b"
          , "sourceType : TypeOnly"
          , "let sourceType = (a = Int,)"
          , "fooComputed : R"
          , "let fooComputed = (a = sourceType.a, b = 6)"
          , "let useRecordComputed = fooComputed.b"
          , "runtimeProofRec : RuntimeProofRec"
          , "let runtimeProofRec = (proof = refl, value = 9)"
          , "erasedProofRec : ErasedProofRec"
          , "let erasedProofRec = (prop = isPropEq, value = 10)"
          , "makeGhost : GhostBox"
          , "let makeGhost = MkGhostBox 99 5"
          , "useErasedTail : ErasedTail -> Int"
          , "let useErasedTail t ="
          , "    match t"
          , "    case MkErasedTail _ b _ -> b"
          , "useTuplePattern : TupleErased -> Int"
          , "let useTuplePattern r ="
          , "    match r"
          , "    case (_, b) -> b"
          , "applyPoly : ((a : Type) -> a -> a) -> Int"
          , "let applyPoly f = f Int 5"
          , "usePolyArg : Int"
          , "let usePolyArg = applyPoly (\\t x -> x)"
          , "localPoly : Int"
          , "let localPoly ="
          , "    let f : (a : Type) -> a -> a = \\a x -> x"
          , "    f Int 7"
          , "main : UIO Unit"
          , "let main = printlnString \"ok\""
          ]
      cu = compileSourceWithPrelude "s5a-backendir.kp" src
      st = cuState cu
      ir = lowerKBackendIR st
      dataInterfaces =
        Map.map
          (\info -> KCoreDataInfo (diCtors info) (diParamCount info))
          (csDatas st)
      constructorInterfaces =
        Map.map
          (\info ->
             KCoreConstructorInfo
               (ciData info)
               (ciUniverses info)
               (ciType info)
               (ciSourceFields info))
          (csCtors st)
      importedGlobals =
        Map.filterWithKey
          (\(GName owner _) _ -> owner /= cuModule cu)
          (csGlobals st)
      importedDataInterfaces =
        Map.filterWithKey
          (\(GName owner _) _ -> owner /= cuModule cu)
          dataInterfaces
      importedConstructorInterfaces =
        Map.filterWithKey
          (\(GName owner _) _ -> owner /= cuModule cu)
          constructorInterfaces
      importedEval =
        EvalCtx
          (Globals importedGlobals)
          (csMetas st)
          False
          mempty
      renderedKCore =
        renderKCoreModule
          (cuModule cu)
          (EvalCtx (Globals (csGlobals st)) (csMetas st) False mempty)
          (csGlobals st)
          (csCoreBodies st)
          dataInterfaces
          constructorInterfaces
          representationCertificates
      m = ModuleName [T.pack "main"]
      idBoxG = GName m (T.pack "idBox")
      useIdBoxG = GName m (T.pack "useIdBox")
      mkBoxG = GName m (T.pack "MkBox")
      mkGhostBoxG = GName m (T.pack "MkGhostBox")
      fooG = GName m (T.pack "foo")
      useRecordG = GName m (T.pack "useRecord")
      fooComputedG = GName m (T.pack "fooComputed")
      useRecordComputedG = GName m (T.pack "useRecordComputed")
      runtimeProofRecG = GName m (T.pack "runtimeProofRec")
      erasedProofRecG = GName m (T.pack "erasedProofRec")
      makeGhostG = GName m (T.pack "makeGhost")
      useErasedTailG = GName m (T.pack "useErasedTail")
      mkErasedTailG = GName m (T.pack "MkErasedTail")
      useTuplePatternG = GName m (T.pack "useTuplePattern")
      usePolyArgG = GName m (T.pack "usePolyArg")
      localPolyG = GName m (T.pack "localPoly")
      backendBodies = kbirBodies ir
      body = Map.lookup idBoxG backendBodies
      callBody = Map.lookup useIdBoxG backendBodies
      recordBody = Map.lookup fooG backendBodies
      recordProjBody = Map.lookup useRecordG backendBodies
      computedRecordBody = Map.lookup fooComputedG backendBodies
      computedRecordProjBody = Map.lookup useRecordComputedG backendBodies
      runtimeProofRecordBody = Map.lookup runtimeProofRecG backendBodies
      erasedProofRecordBody = Map.lookup erasedProofRecG backendBodies
      ghostBody = Map.lookup makeGhostG backendBodies
      erasedTailBody = Map.lookup useErasedTailG backendBodies
      tuplePatternBody = Map.lookup useTuplePatternG backendBodies
      polyArgBody = Map.lookup usePolyArgG backendBodies
      localPolyBody = Map.lookup localPolyG backendBodies
      terms = maybe [] (backendTerms . bbRoot) body
      callTerms = maybe [] (backendTerms . bbRoot) callBody
      recordTerms = maybe [] (backendTerms . bbRoot) recordBody
      recordProjTerms = maybe [] (backendTerms . bbRoot) recordProjBody
      computedRecordTerms = maybe [] (backendTerms . bbRoot) computedRecordBody
      computedRecordProjTerms = maybe [] (backendTerms . bbRoot) computedRecordProjBody
      runtimeProofRecordTerms = maybe [] (backendTerms . bbRoot) runtimeProofRecordBody
      erasedProofRecordTerms = maybe [] (backendTerms . bbRoot) erasedProofRecordBody
      ghostTerms = maybe [] (backendTerms . bbRoot) ghostBody
      erasedTailAlts = maybe [] (backendAlts . bbRoot) erasedTailBody
      tuplePatternAlts = maybe [] (backendAlts . bbRoot) tuplePatternBody
      polyArgTerms = maybe [] (backendTerms . bbRoot) polyArgBody
      localPolyTerms = maybe [] (backendTerms . bbRoot) localPolyBody
      representationCertificates = kbackendRepresentationCertificates ir
      representationCertificateIds =
        map verifiedRepresentationCertificateIdentity representationCertificates
      representationCertificatesAreUnique =
        length representationCertificateIds
          == Set.size (Set.fromList representationCertificateIds)
      hasExactNaturalCertificate =
        any
          (\case VerifiedExactNaturalRepresentation {} -> True; _ -> False)
          representationCertificates
      hasFiniteOrdinalCertificate =
        any
          (\case VerifiedOrdinalRepresentation {} -> True; _ -> False)
          representationCertificates
      representationCertificatesReplay =
        all ((== Right ()) . verifyRepresentationCertificate) representationCertificates
      representationCertificatesSerialized =
        case
            renderedKCore
              >>= parseAndVerifyKCoreTextWithEnvironment
                importedEval
                importedGlobals
                importedDataInterfaces
                importedConstructorInterfaces
          of
          Right kcore ->
            kcoreRepresentationCertificateCount kcore
              == length representationCertificates
          Left _ -> False
      params = maybe [] bbParams body
      hasOnlyRuntimeParam =
        case params of
          [BackendParam Expl _ (Just (BackendBinder (BackendBinderId n) _ _ _))] -> n >= 0
          _ -> False
      hasErasedCallArgOmitted =
        any
          ( \case
              BApp _ _ args -> length args == 1
              _ -> False
          )
          callTerms
      hasBoxCtorLayout =
        any
          ( \case
              BCtor _ layout _ ->
                bclCtor layout == mkBoxG
                  && bclRuntimeFields layout == 1
                  && maybe False (\info -> clArity info == 1 && clBoxedFootprintBytes info == Just 56) (bclInfo layout)
              _ -> False
          )
          terms
      hasMatchLayout =
        any
          ( \case
              BMatch _ _ _ layouts ->
                any
                  ( \(_, layout) ->
                      bclCtor layout == mkBoxG
                        && bclRuntimeFields layout == 1
                        && maybe False (\info -> clArity info == 1 && clBoxedFootprintBytes info == Just 56) (bclInfo layout)
                  )
                  layouts
              _ -> False
          )
          terms
      hasNodeIds = all backendTermNodeNonNegative (terms <> callTerms)
      hasOwnershipUse =
        any
          ( \case
              BVar _ (Just (BackendUse (BackendUseId n) _ _)) _ -> n >= 0
              _ -> False
          )
          (terms <> callTerms)
      hasErasedRecordFieldOmitted =
        any
          ( \case
              BRecord _ [("b", _)] -> True
              _ -> False
          )
          recordTerms
      hasRecordProjectionReindexed =
        any
          ( \case
              BProj _ _ "b" (Just 0) -> True
              _ -> False
          )
          recordProjTerms
      hasComputedErasedRecordFieldOmitted =
        any
          ( \case
              BRecord _ [("b", _)] -> True
              _ -> False
          )
          computedRecordTerms
      hasComputedRecordProjectionReindexed =
        any
          ( \case
              BProj _ _ "b" (Just 0) -> True
              _ -> False
          )
          computedRecordProjTerms
      equalityProofRecordFieldRetained =
        any
          ( \case
              BRecord _ fs -> map fst fs == [T.pack "proof", T.pack "value"]
              _ -> False
          )
          runtimeProofRecordTerms
      hasRuntimeErasedProofRecordFieldOmitted =
        any
          ( \case
              BRecord _ [("value", _)] -> True
              _ -> False
          )
          erasedProofRecordTerms
      hasQ0CtorFieldOmitted =
        any
          ( \case
              BCtor _ layout [_] ->
                bclCtor layout == mkGhostBoxG
                  && bclRuntimeFields layout == 1
                  && maybe False (\info -> clArity info == 1 && clBoxedFootprintBytes info == Just 56) (bclInfo layout)
              _ -> False
          )
          ghostTerms
      constructorPatternErasedTailReindexed =
        any
          ( \case
              BackendAlt _ (BPCtor g 2 [(0, BPWild), (1, BPVar n)]) binders _ _ ->
                g == mkErasedTailG && n == T.pack "b" && length binders == 1
              _ -> False
          )
          erasedTailAlts
      tuplePatternErasedFieldReindexed =
        any
          ( \case
              BackendAlt _ (BPTuple 1 [(0, BPVar n)]) binders _ _ ->
                n == T.pack "b" && length binders == 1
              _ -> False
          )
          tuplePatternAlts
      polyArgErasesTypeLambda =
        not $
          any
            ( \case
                BLam _ _ Expl _ "t" _ -> True
                _ -> False
            )
            polyArgTerms
      localPolyErasesTypeLambda =
        not $
          any
            ( \case
                BLam _ _ Expl _ "a" _ -> True
                _ -> False
            )
            localPolyTerms
      localPolyCallErasesTypeArg =
        any
          ( \case
              BApp _ _ args -> length args == 1
              _ -> False
          )
          localPolyTerms
      showTree = T.pack (show ir)
      noWrapperScaffold =
        not ("bbTerm" `T.isInfixOf` showTree)
          && not ("bbErasedSpines" `T.isInfixOf` showTree)
          && not ("boiCompat" `T.isInfixOf` showTree)
      checks =
        [ ("idBox lowered body exists", body /= Nothing)
        , ("useIdBox lowered body exists", callBody /= Nothing)
        , ("erased type parameter is absent from runtime params", hasOnlyRuntimeParam)
        , ("erased call argument is absent from runtime app", hasErasedCallArgOmitted)
        , ("constructor layout lives on ctor node", hasBoxCtorLayout)
        , ("match layout lives on match node", hasMatchLayout)
        , ("backend node identities live on terms", hasNodeIds)
        , ("ownership use identities live on variable nodes", hasOwnershipUse)
        , ("erased record field is absent from runtime record", hasErasedRecordFieldOmitted)
        , ("fixed record projection is reindexed to runtime fields", hasRecordProjectionReindexed)
        , ("computed erased record field is absent by record type", hasComputedErasedRecordFieldOmitted)
        , ("computed erased record projection is reindexed to runtime fields", hasComputedRecordProjectionReindexed)
        , ("plain equality proof field is retained without RuntimeErased evidence", equalityProofRecordFieldRetained)
        , ("RuntimeErased proof record field is absent by record type", hasRuntimeErasedProofRecordFieldOmitted)
        , ("explicit Q0 constructor field is absent from runtime ctor", hasQ0CtorFieldOmitted)
        , ("constructor pattern is reindexed to runtime fields after erased tail", constructorPatternErasedTailReindexed)
        , ("tuple pattern is reindexed to runtime fields after erased field", tuplePatternErasedFieldReindexed)
        , ("polymorphic lambda argument erases type binder from expected type", polyArgErasesTypeLambda)
        , ("local kind-domain lambda binder is erased", localPolyErasesTypeLambda)
        , ("local polymorphic call erases type argument", localPolyCallErasesTypeArg)
        , ("selected representation certificates are identity-unique", representationCertificatesAreUnique)
        , ("selected exact-natural certificate crosses the backend boundary", hasExactNaturalCertificate)
        , ("selected finite-ordinal certificate crosses the backend boundary", hasFiniteOrdinalCertificate)
        , ("selected representation certificates replay before emission", representationCertificatesReplay)
        , ("selected representation certificates are serialized in KCore", representationCertificatesSerialized)
        , ("lowered tree is not the old wrapper scaffold", noWrapperScaffold)
        ]
      failed = [name | (name, ok) <- checks, not ok]
  unless (null failed) $ do
    putStrLn "backendIRPhaseAS5 FAILED:"
    mapM_ (putStrLn . ("  " <>)) failed
    case renderedKCore of
      Left err ->
        putStrLn
          ( "  KCore emission="
              <> T.unpack (kcteCode err)
              <> ": "
              <> T.unpack (kcteMessage err)
          )
      Right dump ->
        case
            parseAndVerifyKCoreTextWithEnvironment
              importedEval
              importedGlobals
              importedDataInterfaces
              importedConstructorInterfaces
              dump
          of
          Left err ->
            putStrLn
              ( "  KCore parse="
                  <> T.unpack (kcteCode err)
                  <> ": "
                  <> T.unpack (kcteMessage err)
              )
          Right _ -> pure ()
  pure (null failed)

-- | S5.A regression: the backend-tree legality boundary must run on the real
-- KBackendIR tree rather than on Core.Term. A clean lowered program should
-- produce no tree-local findings, while malformed backend nodes must be
-- rejected for the invariants the C/LLVM emitters will rely on when they stop
-- consulting Core/path side tables.
backendIRValidatorS5 :: IO Bool
backendIRValidatorS5 = do
  let src =
        T.unlines
          [ "module main"
          , "data Box (a : Type) : Type = MkBox (value : a)"
          , "let idBox (a : Type) (b : Box a) ="
          , "    match b"
          , "    case MkBox x -> MkBox x"
          , "main : UIO Unit"
          , "let main = printlnString \"ok\""
          ]
      cleanCodes = map bivCode (validateKBackendIR (lowerKBackendIR (cuState (compileSourceWithPrelude "s5a-backendir-validate.kp" src))))
      m = ModuleName [T.pack "malformed"]
      gn s = GName m (T.pack s)
      owner = gn "f"
      meta0 = BackendMeta (BackendNodeId 0) []
      meta1 = BackendMeta (BackendNodeId 1) []
      meta2 = BackendMeta (BackendNodeId 2) []
      meta3 = BackendMeta (BackendNodeId 3) []
      malformed bodies violations =
        KBackendIR
          { kbirBodies = bodies
          , kbirCapabilities = Set.empty
          , kbirSourceFields = Map.empty
          , kbirRepresentations = Map.empty
          , kbirLoweringViolations = violations
          }
      badCtor =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                []
                []
                (BCtor meta0 (BackendCtorLayout (gn "MkBad") Nothing 2) [BGlob meta1 (gn "x")])
          )
          []
      staleInfo =
        CtorLayoutInfo
          { clArity = 2
          , clLayoutClass = LayoutBoxed
          , clBoxedFootprintBytes = Just 64
          , clFieldReps = [RepBoxed, RepBoxed]
          }
      badCtorInfo =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                []
                []
                (BCtor meta0 (BackendCtorLayout (gn "MkBad") (Just staleInfo) 1) [BGlob meta1 (gn "x")])
          )
          []
      badUse =
        malformed
          (Map.singleton owner $ BackendBody owner [] [] (BVar meta0 Nothing 0))
          []
      dupUse = BackendUse (BackendUseId 0) NonLast False
      badDuplicateUse =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                []
                []
                (BRecord meta0 [(T.pack "a", BVar meta1 (Just dupUse) 0), (T.pack "b", BVar meta2 (Just dupUse) 0)])
          )
          []
      badBinder =
        malformed
          (Map.singleton owner $ BackendBody owner [BackendParam Expl (T.pack "x") Nothing] [] (BUnit meta0))
          []
      badNodeId =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                []
                []
                (BLet meta0 Nothing Q1 (T.pack "x") (BUnit meta0) (BUnit meta1))
          )
          []
      badBranchDrop =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                []
                []
                (BIf (BackendMeta (BackendNodeId 2) [BackendBinder (BackendBinderId 99) (T.pack "dangling") (BinderOwn QW Nothing False True) False]) (BUnit meta0) (BUnit meta1) (BUnit (BackendMeta (BackendNodeId 3) [])))
          )
          []
      realDropBinder = BackendBinder (BackendBinderId 0) (T.pack "real") (BinderOwn QW Nothing False True) False
      forgedDropBinder = BackendBinder (BackendBinderId 0) (T.pack "forged") (BinderOwn QW Nothing False True) False
      badForgedBranchDrop =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                [BackendParam Expl (T.pack "x") (Just realDropBinder)]
                []
                (BIf (BackendMeta (BackendNodeId 2) [forgedDropBinder]) (BUnit meta0) (BUnit meta1) (BUnit (BackendMeta (BackendNodeId 3) [])))
          )
          []
      badDuplicateBranchDrop =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                [BackendParam Expl (T.pack "x") (Just realDropBinder)]
                []
                (BIf (BackendMeta (BackendNodeId 2) [realDropBinder, realDropBinder]) (BUnit meta0) (BUnit meta1) (BUnit (BackendMeta (BackendNodeId 3) [])))
          )
          []
      badItemBranchDrop =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                [BackendParam Expl (T.pack "x") (Just realDropBinder)]
                []
                (BDo meta0 Nothing [BKExpr (BackendMeta (BackendNodeId 2) [realDropBinder]) (BUnit meta1)])
          )
          []
      duplicateBinderA = BackendBinder (BackendBinderId 0) (T.pack "a") (BinderOwn QW Nothing False True) False
      duplicateBinderB = BackendBinder (BackendBinderId 0) (T.pack "b") (BinderOwn QW Nothing False True) False
      badDuplicateBinder =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                [ BackendParam Expl (T.pack "a") (Just duplicateBinderA)
                , BackendParam Expl (T.pack "b") (Just duplicateBinderB)
                ]
                []
                (BUnit meta0)
          )
          []
      badPattern =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                []
                []
                (BMatch meta0 (BUnit meta1) [BackendAlt meta0 (BPCtor (gn "MkBad") 2 [(0, BPWild), (1, BPWild)]) [] Nothing (BUnit meta1)] [(gn "MkBad", BackendCtorLayout (gn "MkBad") Nothing 1)])
          )
          []
      badPatternInfo =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                []
                []
                (BMatch meta0 (BUnit meta1) [BackendAlt meta0 (BPCtor (gn "MkBad") 1 [(0, BPWild)]) [] Nothing (BUnit meta1)] [(gn "MkBad", BackendCtorLayout (gn "MkBad") (Just staleInfo) 1)])
          )
          []
      badPatternMissingLayout =
        malformed
          ( Map.singleton owner $
              BackendBody
                owner
                []
                []
                (BMatch meta0 (BUnit meta1) [BackendAlt meta2 (BPCtor (gn "MkBad") 1 [(0, BPWild)]) [] Nothing (BUnit meta3)] [])
          )
          []
      codesOf = map bivCode . validateKBackendIR
      checks =
        [ ("clean lowered KBackendIR validates", null cleanCodes)
        , ("ctor runtime-field mismatch caught", T.pack "W_BACKENDIR_CTOR_FIELD_MISMATCH" `elem` codesOf badCtor)
        , ("ctor layout-info mismatch caught", T.pack "W_BACKENDIR_CTOR_LAYOUT_INCONSISTENT" `elem` codesOf badCtorInfo)
        , ("runtime variable missing ownership use caught", T.pack "W_BACKENDIR_MISSING_USE" `elem` codesOf badUse)
        , ("runtime parameter missing ownership binder caught", T.pack "W_BACKENDIR_MISSING_BINDER" `elem` codesOf badBinder)
        , ("duplicate backend node id caught", T.pack "W_BACKENDIR_DUPLICATE_NODE_ID" `elem` codesOf badNodeId)
        , ("duplicate backend binder id caught", T.pack "W_BACKENDIR_DUPLICATE_BINDER_ID" `elem` codesOf badDuplicateBinder)
        , ("duplicate backend use id caught", T.pack "W_BACKENDIR_DUPLICATE_USE_ID" `elem` codesOf badDuplicateUse)
        , ("dangling branch-drop binder caught", T.pack "W_BACKENDIR_BRANCH_DROP_OUT_OF_SCOPE" `elem` codesOf badBranchDrop)
        , ("forged branch-drop binder caught", T.pack "W_BACKENDIR_BRANCH_DROP_MISMATCH" `elem` codesOf badForgedBranchDrop)
        , ("duplicate branch-drop binder caught", T.pack "W_BACKENDIR_BRANCH_DROP_DUPLICATE" `elem` codesOf badDuplicateBranchDrop)
        , ("item-level branch-drop metadata rejected", T.pack "W_BACKENDIR_BRANCH_DROP_UNEMITTED_ITEM" `elem` codesOf badItemBranchDrop)
        , ("ctor pattern runtime-field mismatch caught", T.pack "W_BACKENDIR_CTOR_PATTERN_FIELD_MISMATCH" `elem` codesOf badPattern)
        , ("ctor pattern layout-info mismatch caught", T.pack "W_BACKENDIR_CTOR_LAYOUT_INCONSISTENT" `elem` codesOf badPatternInfo)
        , ("ctor pattern missing layout caught", T.pack "W_BACKENDIR_CTOR_PATTERN_LAYOUT_MISSING" `elem` codesOf badPatternMissingLayout)
        ]
      failed = [name | (name, ok) <- checks, not ok]
  unless (null failed) $ do
    putStrLn "backendIRValidatorS5 FAILED:"
    mapM_ (putStrLn . ("  " <>)) failed
    putStrLn ("  cleanCodes=" <> show cleanCodes)
    putStrLn ("  badCtor=" <> show (codesOf badCtor))
    putStrLn ("  badCtorInfo=" <> show (codesOf badCtorInfo))
    putStrLn ("  badUse=" <> show (codesOf badUse))
    putStrLn ("  badDuplicateUse=" <> show (codesOf badDuplicateUse))
    putStrLn ("  badBinder=" <> show (codesOf badBinder))
    putStrLn ("  badNodeId=" <> show (codesOf badNodeId))
    putStrLn ("  badDuplicateBinder=" <> show (codesOf badDuplicateBinder))
    putStrLn ("  badBranchDrop=" <> show (codesOf badBranchDrop))
    putStrLn ("  badForgedBranchDrop=" <> show (codesOf badForgedBranchDrop))
    putStrLn ("  badDuplicateBranchDrop=" <> show (codesOf badDuplicateBranchDrop))
    putStrLn ("  badItemBranchDrop=" <> show (codesOf badItemBranchDrop))
    putStrLn ("  badPattern=" <> show (codesOf badPattern))
    putStrLn ("  badPatternInfo=" <> show (codesOf badPatternInfo))
    putStrLn ("  badPatternMissingLayout=" <> show (codesOf badPatternMissingLayout))
  pure (null failed)

-- | S5.A consumer gate: once the real KBackendIR tree exists, native emitters
-- must consume it directly. Keeping a Core.Term emitter plus a structural
-- gsPath/UseSite side table would preserve the R-path failure class the split is
-- meant to retire, even if a separate tree validator runs first.
backendIRConsumerContractS5 :: IO Bool
backendIRConsumerContractS5 = do
  let files =
        [ ("C", "src/Kappa/Backend/C.hs")
        , ("LLVM", "src/Kappa/Backend/LLVM.hs")
        , ("Backend.IR", "src/Kappa/Backend/IR.hs")
        , ("Driver", "src/Kappa/Backend/Driver.hs")
        , ("native suite", "test/native/run-native-tests.sh")
        , ("LLVM parity", "test/native/llvm-parity.sh")
        ]
      banned =
        [ "compile :: Term ->"
        , "compileTerm :: Term ->"
        , "gsPath ::"
        , "gsCurOwn ::"
        , "gsOwnership ::"
        , "UseSite"
        , "withBodyOwn ::"
        , "lsOwn ::"
        , "assignBinderIds"
        , "assignUseIds"
        , "oiBranchDropSites"
        , "R-path walk-and-lookup"
        , "scalarPlan :: GName -> Gen (Maybe ([Bool], [ParamKind], ScalarKind, Term))"
        , "compileScalarWorker :: GName -> [ParamKind] -> ScalarKind -> Term ->"
        , "scalarFnPlanLL :: GName -> Gen (Maybe ([Bool], [ParamKindLL], ScalarKindLL, Term))"
        , "compileScalarFnWorkerLL :: GName -> [ParamKindLL] -> ScalarKindLL -> Term ->"
        ]
  findings <- fmap concat $
    forM files $ \(label, path) -> do
      src <- TIO.readFile path
      pure
        [ label <> " backend still contains old Core/path consumer marker " <> show needle
        | needle <- banned
        , T.pack needle `T.isInfixOf` src
        ]
  unless (null findings) $ do
    putStrLn "backendIRConsumerContractS5 FAILED:"
    mapM_ (putStrLn . ("  " <>)) findings
  pure (null findings)

-- | S5.A1/A2c regression: native backend ownership metadata must be produced
-- from KBackendIR binder identities, not by reattaching the legacy path-keyed
-- 'csOwnership' table. A checked program with its legacy ownership side table
-- deliberately erased must still lower to a fully annotated KBackendIR tree.
backendIRNoPathOwnershipS5 :: IO Bool
backendIRNoPathOwnershipS5 = do
  let src =
        T.unlines
          [ "module main"
          , "data Box : Type = MkBox (value : String)"
          , "let choose (flag : Bool) ="
          , "    let b = MkBox \"owned\""
          , "    if flag then b else MkBox \"fallback\""
          , "main : UIO Unit"
          , "let main = printlnString \"ok\""
          ]
      cu = compileSourceWithPrelude "s5a-backendir-ownids.kp" src
      st = (cuState cu) {csOwnership = Map.empty}
      ir = lowerKBackendIR st
      codes = map bivCode (validateKBackendIR ir)
      m = ModuleName [T.pack "main"]
      chooseG = GName m (T.pack "choose")
      terms = maybe [] (backendTerms . bbRoot) (Map.lookup chooseG (kbirBodies ir))
      useIds =
        [ n
        | BVar _ (Just (BackendUse (BackendUseId n) _ _)) _ <- terms
        ]
      branchDropCount =
        sum
          [ length drops
          | t <- terms
          , let BackendMeta _ drops = backendMetaOf t
          ]
      ok = null codes && not (null useIds) && branchDropCount > 0
  unless ok $ do
    putStrLn "backendIRNoPathOwnershipS5 FAILED:"
    putStrLn ("  validation codes=" <> show codes)
    putStrLn ("  useIds=" <> show useIds)
    putStrLn ("  branchDropCount=" <> show branchDropCount)
    putStrLn ("  ir=" <> show ir)
  pure ok

-- | S5.B4 regression: the remaining observe-only ownership audit table must
-- not be keyed by structural child paths. Native emission was already off the
-- old bridge; this pins the physical cleanup so future work cannot accidentally
-- reattach path-keyed ownership by reusing the legacy producer.
ownershipPhysicalRPathRetiredS5 :: IO Bool
ownershipPhysicalRPathRetiredS5 = do
  src <- TIO.readFile "src/Kappa/Ownership.hs"
  let banned =
        [ "Kappa.PathScheme"
        , "biPath"
        , "usPath"
        , "Map [Int] [BinderId]"
        , "renderPath"
        ]
      failed =
        [ "Ownership.hs still contains legacy R-path marker " <> show needle
        | needle <- banned
        , T.pack needle `T.isInfixOf` src
        ]
  unless (null failed) $ do
    putStrLn "ownershipPhysicalRPathRetiredS5 FAILED:"
    mapM_ (putStrLn . ("  " <>)) failed
  pure (null failed)

-- | S5.A regression: first-class/projected callees must carry the same
-- type-derived argument convention facts as the legacy Core ownership analyzer.
-- The call @r.f y@ below applies a projected function field with type
-- @(& x : Box) -> Int@, so @y@ is a read-only NonLast use, not an ownership
-- transfer. This must be represented directly on KBackendIR, with no
-- path-keyed ownership table.
backendIRProjectedBorrowedCalleeS5 :: IO Bool
backendIRProjectedBorrowedCalleeS5 = do
  let src =
        T.unlines
          [ "module main"
          , "type Box = (v : Int,)"
          , "type PeekBox = (& x : Box) -> Int"
          , "peekBox : (& x : Box) -> Int"
          , "let peekBox x = x.v"
          , "type RecAlias = (f : PeekBox,)"
          , "useProjectedTwice : RecAlias -> Box -> Int"
          , "let useProjectedTwice r y = r.f y + y.v"
          , "type PolyBox (a : Type) = (v : a,)"
          , "type PolyRec (a : Type) = (f : (& x : PolyBox a) -> a,)"
          , "polyPeek : (a : Type) -> (& x : PolyBox a) -> a"
          , "let polyPeek a x = x.v"
          , "usePolyProjected : (a : Type) -> PolyRec a -> PolyBox a -> (a, a)"
          , "let usePolyProjected a r y = (r.f y, y.v)"
          , "polyId : (a : Type) -> a -> a"
          , "let polyId a x = x"
          , "firstClassPoly : ((a : Type) -> a -> a) -> Int"
          , "let firstClassPoly f = f Int 1"
          , "main : UIO Unit"
          , "let main = printInt (useProjectedTwice (f = peekBox,) (v = 1,))"
          ]
      cu = compileSourceWithPrelude "s5a-projected-borrowed-callee.kp" src
      ir = lowerKBackendIR (cuState cu)
      codes = map bivCode (validateKBackendIR ir)
      m = ModuleName [T.pack "main"]
      target = GName m (T.pack "useProjectedTwice")
      polyTarget = GName m (T.pack "usePolyProjected")
      firstClassTarget = GName m (T.pack "firstClassPoly")
      termsOf g = maybe [] (backendTerms . bbRoot) (Map.lookup g (kbirBodies ir))
      projectedBorrowedCalls g =
        [ use
        | BApp _ (BProj _ _ field _) [(Expl, Just ArgBorrowed, BVar _ (Just use) _)] <- termsOf g
        , field == T.pack "f"
        ]
      hasReadOnlyNonLast g =
        any
          ( \(BackendUse _ kind consumes) ->
              kind == NonLast && not consumes
          )
          (projectedBorrowedCalls g)
      firstClassApps =
        [ args
        | BApp _ (BVar _ _ _) args <- termsOf firstClassTarget
        ]
      firstClassErasesTypeArg = any ((== 1) . length) firstClassApps
      ok = null codes && hasReadOnlyNonLast target && hasReadOnlyNonLast polyTarget && firstClassErasesTypeArg
  unless ok $ do
    putStrLn "backendIRProjectedBorrowedCalleeS5 FAILED:"
    putStrLn ("  validation codes=" <> show codes)
    putStrLn ("  projectedBorrowedCall=" <> show (projectedBorrowedCalls target))
    putStrLn ("  polyProjectedBorrowedCall=" <> show (projectedBorrowedCalls polyTarget))
    putStrLn ("  firstClassApps=" <> show firstClassApps)
    putStrLn ("  body=" <> show (Map.lookup target (kbirBodies ir)))
    putStrLn ("  polyBody=" <> show (Map.lookup polyTarget (kbirBodies ir)))
    putStrLn ("  firstClassBody=" <> show (Map.lookup firstClassTarget (kbirBodies ir)))
  pure ok

-- | S5.A regression: erased existential indices in dependent constructor
-- patterns are Core-only scope slots. KBackendIR must keep them out of the
-- runtime pattern/binder stream and instead renumber body variables through
-- erased ScopeSlot Nothing entries during lowering.
backendIRPatternErasesExistentialsS5 :: IO Bool
backendIRPatternErasesExistentialsS5 = do
  let src =
        T.unlines
          [ "module main"
          , "data Tag (b : Bool) : Type ="
          , "    TT : Tag True"
          , "    FF : Tag False"
          , "data Q : Type ="
          , "    MkQ : forall (s : Bool). forall (t : Bool). Tag s -> Tag t -> Q"
          , "use2 : Int -> Int -> Q -> Int"
          , "let use2 a b q ="
          , "    match q"
          , "      case MkQ y z ->"
          , "        match y"
          , "          case TT ->"
          , "            match z"
          , "              case TT -> a + b"
          , "              case FF -> a"
          , "          case FF ->"
          , "            match z"
          , "              case TT -> b"
          , "              case FF -> a + b"
          , "main : UIO Unit"
          , "let main = printlnString (showInt (use2 10 3 (MkQ TT FF)))"
          ]
      cu = compileSourceWithPrelude "s5a-pattern-erased-existentials.kp" src
      st = cuState cu
      ir = lowerKBackendIR st
      codes = map bivCode (validateKBackendIR ir)
      m = ModuleName [T.pack "main"]
      use2G = GName m (T.pack "use2")
      mkQ = GName m (T.pack "MkQ")
      alts = maybe [] (backendAlts . bbRoot) (Map.lookup use2G (kbirBodies ir))
      mkQAltRuntimeBinders =
        [ length binders
        | BackendAlt _ (BPCtor g _ _) binders _ _ <- alts
        , g == mkQ
        ]
      mainG = GName m (T.pack "main")
      generatedC = case generateC False True st mainG Set.empty Map.empty of
        Right (c, _) -> c
        Left (errs, _) -> T.pack (show errs)
      ok =
        null codes
          && mkQAltRuntimeBinders == [2]
          && not (T.pack "kpush(kunit()" `T.isInfixOf` generatedC)
  unless ok $ do
    putStrLn "backendIRPatternErasesExistentialsS5 FAILED:"
    putStrLn ("  validation codes=" <> show codes)
    putStrLn ("  MkQ runtime binder counts=" <> show mkQAltRuntimeBinders <> ", want [2]")
    when (T.pack "kpush(kunit()" `T.isInfixOf` generatedC) $
      putStrLn "  generated C still pushes erased existential placeholders with kpush(kunit())"
    putStrLn ("  body=" <> show (Map.lookup use2G (kbirBodies ir)))
  pure ok

backendTerms :: BackendTerm -> [BackendTerm]
backendTerms t =
  t : case t of
    BUnit {} -> []
    BVar {} -> []
    BGlob {} -> []
    BLit {} -> []
    BLam _ _ _ _ _ b -> backendTerms b
    BApp _ h args -> backendTerms h ++ concatMap (\(_, _, a) -> backendTerms a) args
    BCtor _ _ args -> concatMap backendTerms args
    BMatch _ s alts _ -> backendTerms s ++ concatMap backendAltTerms alts
    BRecord _ fs -> concatMap (backendTerms . snd) fs
    BProj _ e _ _ -> backendTerms e
    BInject _ _ e -> backendTerms e
    BLet _ _ _ _ rhs body -> backendTerms rhs ++ backendTerms body
    BLetRec _ _ _ _ rhs body -> backendTerms rhs ++ backendTerms body
    BDo _ _ items -> concatMap backendItemTerms items
    BSeal _ _ e -> backendTerms e
    BThunk _ e -> backendTerms e
    BLazy _ e -> backendTerms e
    BForce _ e -> backendTerms e
    BIf _ c th el -> backendTerms c ++ backendTerms th ++ backendTerms el

backendAlts :: BackendTerm -> [BackendAlt]
backendAlts = concatMap altsOfTerm . backendTerms
  where
    altsOfTerm = \case
      BMatch _ _ alts _ -> alts ++ concatMap (\(BackendAlt _ _ _ guard body) -> maybe [] backendAlts guard ++ backendAlts body) alts
      _ -> []

backendAltTerms :: BackendAlt -> [BackendTerm]
backendAltTerms (BackendAlt _ _ _ guard body) =
  maybe [] backendTerms guard ++ backendTerms body

backendItemTerms :: BackendItem -> [BackendTerm]
backendItemTerms = \case
  BKBind _ _ _ _ action _ -> backendTerms action
  BKLet _ _ _ _ value -> backendTerms value
  BKLetQ _ _ _ scrut mElse ->
    backendTerms scrut
      ++ maybe [] (\(_, _, body) -> backendTerms body) mElse
  BKExpr _ action -> backendTerms action
  BKVarItem _ _ initT action _ -> backendTerms initT ++ backendTerms action
  BKAssign _ _ rhs action _ -> backendTerms rhs ++ backendTerms action
  BKReturn _ value -> backendTerms value
  BKWhile _ _ cond body mElse ->
    backendCondTerms cond
      ++ concatMap backendItemTerms body
      ++ maybe [] (concatMap backendItemTerms) mElse
  BKFor _ _ _ _ source body mElse ->
    backendTerms source
      ++ concatMap backendItemTerms body
      ++ maybe [] (concatMap backendItemTerms) mElse
  BKIf _ arms mElse ->
    concatMap (\(cond, body) -> backendTerms cond ++ concatMap backendItemTerms body) arms
      ++ maybe [] (concatMap backendItemTerms) mElse
  BKDefer _ _ action -> backendTerms action
  BKUsing _ _ _ acquire release -> backendTerms acquire ++ backendTerms release
  BKSubDo _ _ body -> concatMap backendItemTerms body
  BKBreak {} -> []
  BKContinue {} -> []

backendCondTerms :: BackendCond -> [BackendTerm]
backendCondTerms = \case
  BKCondPure t -> backendTerms t
  BKCondAction t -> backendTerms t

backendTermNodeNonNegative :: BackendTerm -> Bool
backendTermNodeNonNegative t =
  case backendMetaOf t of
    BackendMeta (BackendNodeId n) drops -> n >= 0 && all (\(BackendBinder (BackendBinderId b) _ _ _) -> b >= 0) drops

backendMetaOf :: BackendTerm -> BackendMeta
backendMetaOf = \case
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

-- | Perceus S1.3 regression: 'Kappa.Backend.Repr.ctorLayoutOf' must count a
-- constructor's RUNTIME fields — the field set the backend actually builds the
-- node with ('Kappa.Check.etaCtor' / 'Kappa.Backend.C.compileCtor': an explicit
-- field always counts, an implicit non-'Q0' field — an EVIDENCE\/DICTIONARY
-- field — counts too). The earlier implementation delegated to 'repSelect',
-- whose explicit-only gate DROPPED the dictionary field of an existential
-- constructor (@MkShowable : forall (a:Type). Show a => a -> Showable@, whose
-- @Show a =>@ is an implicit 'QW' dictionary): it reported arity 1 while the
-- runtime builds arity 2 @[dict, value]@. An S5 FBIP reuse reading that layout
-- would rebuild a same-tag node with the wrong field count (a miscompile).
--
-- This pins, for an EXISTENTIAL-DICTIONARY constructor, that
-- 'ctorLayoutOf''s @(arity, fieldReps)@ matches the runtime arity computed by an
-- INDEPENDENT walk of the constructor type's leading 'CPi' telescope under the
-- runtime field rule ('runtimeCtorArity', which does NOT call 'ctorLayoutOf'),
-- with the dictionary field surfaced as 'RepBoxed'; and that the existing
-- non-evidence cases (nullary, single boxed, scalar 'Int', a 2-field pair) are
-- unchanged.
ctorLayoutEvidenceFields :: IO Bool
ctorLayoutEvidenceFields = do
  let src =
        T.unlines
          [ "module main"
          , "trait Show (a : Type) ="
          , "    show : a -> String"
          , "trait Eqt (a : Type) ="
          , "    eqt : a -> a -> Bool"
          , -- existential dictionary constructors (the bug's target)
            "data Showable : Type ="
          , "    MkShowable : forall (a : Type). Show a => a -> Showable"
          , "data Eqd : Type ="
          , "    MkEqd : forall (a : Type). Eqt a => a -> a -> Eqd"
          , -- the previously-correct cases that must stay unchanged
            "data MyUnit : Type ="
          , "    MkMyUnit"
          , "data MyBox (a : Type) : Type ="
          , "    MkMyBox (val : a)"
          , "data IntBox : Type ="
          , "    MkIntBox (v : Int)"
          , "data MyPair (a : Type) (b : Type) : Type ="
          , "    MkMyPair (fst : a) (snd : b)"
          ]
      cu = compileSourceWithPrelude "ctorlayout.kp" src
      st = cuState cu
      ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
      m = ModuleName [T.pack "main"]
      -- the INDEPENDENT runtime-arity oracle: walk the constructor type's
      -- leading Pi telescope under the shared runtime-field classifier, without
      -- consulting ctorLayoutOf.
      runtimeCtorArity :: Term -> Int
      runtimeCtorArity = goCount 0 . eval ctx []
        where
          goCount lvl ty = case force ctx ty of
            VPi ic q _ _ dom (Closure env cod) ->
              (if runtimeConstructorField ctx lvl ic q dom then 1 else 0)
                + goCount (lvl + 1) (eval ctx (VRigid lvl [] : env) cod)
            _ -> 0
      look cname = Map.lookup (GName m (T.pack cname)) (csCtors st)
      -- (ctorLayoutOf-arity, ctorLayoutOf-fieldReps, layout class, boxed footprint,
      -- runtime-oracle-arity)
      probe cname = case look cname of
        Nothing -> Nothing
        Just ci ->
          case ctorLayoutOf ctx (Just (ciType ci)) of
            Nothing -> Nothing
            Just info ->
              Just
                ( clArity info
                , clFieldReps info
                , clLayoutClass info
                , clBoxedFootprintBytes info
                , runtimeCtorArity (ciType ci)
                )
      -- every existential-dictionary ctor: layout arity == runtime arity, and
      -- the dictionary field is RepBoxed.
      evidenceOK cname expectArity =
        case probe cname of
          Just (a, reps, layout, boxedBytes, oracle) ->
            a == expectArity
              && a == oracle
              && length reps == expectArity
              && all (== RepBoxed) reps
              && layout == LayoutBoxed
              && boxedBytes == Just (48 + 8 * expectArity)
          Nothing -> False
      -- a known-good case: exact (arity, fieldReps) tuple.
      exactOK cname want wantLayout wantBytes =
        case probe cname of
          Just (a, reps, layout, boxedBytes, oracle) ->
            (a, reps) == want && layout == wantLayout && boxedBytes == wantBytes && a == oracle
          Nothing -> False
      checks =
        [ ("MkShowable evidence", evidenceOK "MkShowable" 2, probe "MkShowable") -- [Show dict, a]
        , ("MkEqd evidence", evidenceOK "MkEqd" 3, probe "MkEqd") -- [Eqt dict, a, a]
        , ("MkMyUnit nullary", exactOK "MkMyUnit" (0, []) LayoutImmediate Nothing, probe "MkMyUnit")
        , ("MkMyBox single boxed", exactOK "MkMyBox" (1, [RepBoxed]) LayoutBoxed (Just 56), probe "MkMyBox")
        , ("MkIntBox scalar", exactOK "MkIntBox" (1, [RepInt]) LayoutMayPack (Just 56), probe "MkIntBox")
        , ("MkMyPair pair boxed", exactOK "MkMyPair" (2, [RepBoxed, RepBoxed]) LayoutBoxed (Just 64), probe "MkMyPair")
        ]
      failed = [(name, p) | (name, ok, p) <- checks, not ok]
  unless (null failed) $ do
    putStrLn "ctorLayoutEvidenceFields FAILED:"
    mapM_ (\(name, p) -> putStrLn ("  " <> name <> ": got " <> show p)) failed
  pure (null failed)

-- | Perceus S1.4 §3a regression for the CORRECTED whole-program-static model.
-- The refinement is whole-program SOUND (the analysis sees every use), and its
-- genuine gating boundary — the dynamic-link \/ separately-compiled interface —
-- is EMPTY in the current compile. So the earlier module-export\/re-export
-- gating (which kept exported and §8.4 re-exported params unrefined) was
-- premature conservatism and is removed. This pins the corrected behaviour:
--
--   * a directly-EXPORTED single-use ω param NOW refines to @[1,1]@;
--   * a §8.4 RE-EXPORTED (origin-private) single-use ω param ALSO refines to
--     @[1,1]@;
--   * a genuinely-PRIVATE single-use ω param refines to @[1,1]@;
--   * the cross-check stays clean on these honest refinements, AND still FIRES
--     if a binder is force-WIDENED past its declared quantity (the tighten-only
--     invariant — the soundness gate that survives).
reExportBoundaryRefinement :: IO Bool
reExportBoundaryRefinement = do
  let libSrc =
        T.unlines
          [ "module lib"
          , -- exported, single-use ω → now refines to [1,1]
            "pub : (ω a : Int) -> Int"
          , "let pub (ω a : Int) = a"
          , -- private, single-use ω → refines to [1,1]
            "private priv : (ω b : Int) -> Int"
          , "let priv (ω b : Int) = b"
          , -- private in lib, but re-exported by app below → now refines to [1,1]
            "private reExported : (ω c : Int) -> Int"
          , "let reExported (ω c : Int) = c"
          ]
      appSrc =
        T.unlines
          [ "module app"
          , "export lib.(reExported as reExp)"
          , "appVal : Int"
          , "let appVal = 7"
          ]
      cu = compileFiles [("lib.kp", libSrc), ("app.kp", appSrc)]
      st = cuState cu
      ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st)
      ctorTypes = Map.map (\ci -> OwnershipCtorType (ciUniverses ci) (ciType ci)) (csCtors st)
      lib = ModuleName [T.pack "lib"]
      -- The first value binder in each one-arg body receives owner-local ordinal 0.
      refinedOf cname =
        case Map.lookup (GName lib (T.pack cname)) (csOwnership st) of
          Nothing -> Left ("no OwnInfo for " <> cname)
          Just oi ->
            case Map.lookup (BinderId (GName lib (T.pack cname)) 0) (oiBinders oi) of
              Nothing -> Left ("no param binder for " <> cname)
              Just bo -> Right (boRefined bo)
      xcClean =
        crossCheckBodiesWithUniverses
          ctx
          ctorTypes
          (csCoreBodies st)
          (csOwnership st)
      -- The surviving soundness gate is tighten-only: a 'boRefined' interval must
      -- be contained in its declared 'boDeclQ' interval. Exercise it by forcing a
      -- WIDEN. Declared ω = [0,ω] is the widest interval, so first narrow a
      -- param's declared quantity to the bounded Q1 = [1,1], then set its
      -- 'boRefined' to [1,ω] = (1, Nothing) — not a sub-interval of [1,1] — so the
      -- cross-check must fire.
      forcedWiden =
        Map.adjust
          ( \oi ->
              oi
                { oiBinders =
                    Map.adjust
                      (\bo -> bo {boDeclQ = Q1, boRefined = Just (1, Nothing)})
                      (BinderId (GName lib (T.pack "priv")) 0)
                      (oiBinders oi)
                }
          )
          (GName lib (T.pack "priv"))
          (csOwnership st)
      xcForced =
        crossCheckBodiesWithUniverses
          ctx
          ctorTypes
          (csCoreBodies st)
          forcedWiden
      results =
        [ ("exported pub refines to [1,1]", refinedOf "pub" == Right (Just (1, Just 1)))
        , ("re-exported refines to [1,1]", refinedOf "reExported" == Right (Just (1, Just 1)))
        , ("private refines to [1,1]", refinedOf "priv" == Right (Just (1, Just 1)))
        , ("cross-check clean on honest refinement", null xcClean)
        , ("cross-check FIRES on force-widened binder", not (null xcForced))
        ]
      failed = [name | (name, ok) <- results, not ok]
  unless (null failed) $ do
    putStrLn "reExportBoundaryRefinement FAILED:"
    mapM_ (putStrLn . ("  " <>)) failed
    putStrLn ("  pub=" <> show (refinedOf "pub"))
    putStrLn ("  reExported=" <> show (refinedOf "reExported"))
    putStrLn ("  priv=" <> show (refinedOf "priv"))
    putStrLn ("  xcClean=" <> show xcClean)
    putStrLn ("  xcForced=" <> show xcForced)
  pure (null failed)

-- | Appendix-T harness-faithfulness mirrors (gaps G32–G35). Each fixed
-- requirement is pinned here as an expected 'Outcome' over a crafted
-- directive file or directory suite, since these are properties of the
-- harness's §T.8 *classification* (not of any one program) and so cannot
-- be expressed as an ordinary @--!@ assertion inside the conformance
-- tree. Builds the fixtures in a scratch directory under the system
-- temp dir, runs them through the in-process harness, and checks the
-- classification.
harnessFaithful :: IO Bool
harnessFaithful = do
  tmp0 <- getTemporaryDirectory
  let root = tmp0 </> "kappa-harness-mirror"
  removeIfExists root
  createDirectoryIfMissing True root
  -- §T.5.1 (G33): a purely numeric diagnostic code is ill-typed.
  numeric <- fileCase root "g33-numeric.kp"
    "--! assertDiagnostic error 12345\nlet x : Int = 5\n"
  -- §T.5.1 (G33): an unregistered code is ill-typed too.
  unreg <- fileCase root "g33-unregistered.kp"
    "--! assertDiagnostic error E_NO_SUCH_REGISTERED_CODE\nlet x : Int = 5\n"
  -- §T.5.1 (G33): a registered code that simply is not produced FAILs.
  realCode <- fileCase root "g33-real.kp"
    "--! assertDiagnostic error E_TYPE_MISMATCH\nlet x : Int = 5\n"
  -- §T.5.1 (G33): inline @--!!@ markers are validated the same way.
  inlineNum <- fileCase root "g33-inline.kp"
    "let x : Int = 5 --!! 999\n"
  -- §T.6 (G34): a duplicate config key with conflicting values is
  -- ill-formed; with the same value it is fine.
  conflict <- fileCase root "g34-conflict.kp"
    "--! dumpFormat json\n--! dumpFormat sexpr\nlet x : Int = 5\n"
  agree <- fileCase root "g34-agree.kp"
    "--! dumpFormat json\n--! dumpFormat json\nlet x : Int = 5\n"
  modeConflict <- fileCase root "g34-modemode.kp"
    "--! packageMode\n--! scriptMode\nlet x : Int = 5\n"
  -- §T.4 (G32): runArgs is honored (this run task has no argv surface,
  -- so the program's behavior matches the empty-argument default);
  -- stdinFile must name a readable suite file.
  runArgsOk <- fileCase root "g32-runargs.kp"
    "--! mode run\n--! runArgs \"a\" \"b\"\nlet main : UIO Unit = printlnString \"hi\"\n"
  stdinMissing <- fileCase root "g32-stdin-missing.kp"
    "--! mode run\n--! stdinFile does-not-exist.txt\nlet main : UIO Unit = printlnString \"hi\"\n"
  -- §T.5.3 (G32): stageDumps is a real capability, but an unknown checkpoint
  -- remains ill-formed whether or not the capability requirement is repeated.
  stageDump <- fileCase root "g32-stagedump.kp"
    "--! assertStageDump kfront equals expected.json\nlet x : Int = 5\n"
  stageGated <- fileCase root "g32-stagedump-gated.kp"
    "--! requires capability stageDumps\n--! assertStageDump kfront equals expected.json\nlet x : Int = 5\n"
  -- §T.5.2: non-entailment requires a satisfiable strict refutation. A
  -- blocked/false abstract comparison is accepted, while the strict
  -- refutation of reflexivity has no model and therefore fails the assertion.
  neutralNonEntail <- fileCase root "level-neutral-nonentail.kp"
    "--! assertLevelDoesNotEntail f x <= g x\nlet x : Int = 5\n"
  impossibleRefutation <- fileCase root "level-impossible-refutation.kp"
    "--! assertLevelDoesNotEntail u <= u\nlet x : Int = 5\n"
  -- §T.2 (G35): walking a container directory recurses; a nested
  -- directory that declares itself a suite (suite.ktest/main.kp)
  -- compiles its .kp files as ONE unit (so a cross-module reference
  -- resolves and the whole subdir is a single report); a nested bare
  -- directory of .kp files runs each file as an independent single-file
  -- inline test (so unrelated tests are not conflated). The conformance
  -- tree itself relies on the latter reading.
  let container = root </> "g35-container"
  createDirectoryIfMissing True (container </> "declared")
  writeFile (container </> "declared" </> "suite.ktest") "--! assertNoErrors\n"
  writeFile (container </> "declared" </> "a.kp") "module a\npublic let helperA : Int = 5\n"
  writeFile (container </> "declared" </> "b.kp") "module b\nimport a.*\nlet useIt : Int = helperA\n"
  createDirectoryIfMissing True (container </> "bare")
  writeFile (container </> "bare" </> "t1.kp") "--! assertNoErrors\nlet a : Int = 1\n"
  writeFile (container </> "bare" </> "t2.kp") "--! assertNoErrors\nlet b : Int = 2\n"
  walkReps <- runTestPath container
  let declaredReps = [r | r <- walkReps, "g35-container/declared" `isInfixOf` trPath r]
      bareReps = [r | r <- walkReps, "g35-container/bare" `isInfixOf` trPath r]
  removeIfExists root
  let checks =
        [ ("G33 numeric code → harnessError", trOutcome numeric == HarnessError)
        , ("G33 unregistered code → harnessError", trOutcome unreg == HarnessError)
        , ("G33 registered-but-absent code → fail", trOutcome realCode == Fail)
        , ("G33 inline numeric marker → harnessError", trOutcome inlineNum == HarnessError)
        , ("G34 conflicting dumpFormat → harnessError", trOutcome conflict == HarnessError)
        , ("G34 agreeing dumpFormat → pass", trOutcome agree == Pass)
        , ("G34 packageMode+scriptMode → harnessError", trOutcome modeConflict == HarnessError)
        , ("G32 runArgs honored → pass", trOutcome runArgsOk == Pass)
        , ("G32 missing stdinFile → harnessError", trOutcome stdinMissing == HarnessError)
        , ("G32 un-gated assertStageDump → harnessError", trOutcome stageDump == HarnessError)
        , ("G32 gated unknown assertStageDump → harnessError", trOutcome stageGated == HarnessError)
        , ("level non-entailment accepts a satisfiable refutation", trOutcome neutralNonEntail == Pass)
        , ("level non-entailment rejects an inconsistent refutation", trOutcome impossibleRefutation == Fail)
        , ("G35 declared suite is exactly one report", length declaredReps == 1)
        , ("G35 declared suite passes as one unit", all ((== Pass) . trOutcome) declaredReps)
        , ("G35 bare dir → one report per file", length bareReps == 2)
        , ("G35 bare dir files pass independently", all ((== Pass) . trOutcome) bareReps)
        ]
      failed = [name | (name, ok) <- checks, not ok]
  unless (null failed) $ do
    putStrLn "Appendix-T harness-faithfulness mirrors failed:"
    mapM_ (putStrLn . ("  " <>)) failed
  pure (null failed)
  where
    removeIfExists d = do
      there <- doesDirectoryExist d
      unless (not there) (removeDirectoryRecursive d)
    fileCase root name contents = do
      let p = root </> name
      writeFile p contents
      runTestFile p

-- | §3.1.1 / §4.7 JSON-encoder soundness. Both the machine-readable
-- diagnostic producer (§3.1.1) and the audit-ledger producer (§4.7,
-- @kappa audit@) emit through the single canonical encoder exported by
-- 'Kappa.Diagnostic' ('jStr' \/ 'jObject' \/ 'jArray'). A producer that
-- failed to escape control characters (tab, CR, NUL, U+001F) or the
-- structural @"@ \/ @\\@ would emit invalid JSON, so a tool could not
-- parse the structured output the spec requires. This pins the full
-- escape obligation directly on the encoder so no second, weaker copy
-- can drift back in (the audit path previously hand-rolled one that
-- escaped only @"@, @\\@, and @\\n@).
jsonEncoderSound :: IO Bool
jsonEncoderSound = do
  let probe = T.pack "tab\there\rret\NUL nul\US end \"quote\" \\back"
      escaped = jStr probe
      mustContain =
        [ ("\\t", T.pack "\\t")
        , ("\\r", T.pack "\\r")
        , ("NUL → \\u0000", T.pack "\\u0000")
        , ("U+001F → \\u001f", T.pack "\\u001f")
        , ("quote → \\\"", T.pack "\\\"")
        , ("backslash → \\\\", T.pack "\\\\")
        ]
      mustNotContain =
        -- raw control bytes must never survive into the JSON text
        [ ("raw TAB", T.pack "\t")
        , ("raw CR", T.pack "\r")
        , ("raw NUL", T.pack "\NUL")
        , ("raw U+001F", T.pack "\US")
        ]
      structural =
        [ ("jObject braces", jObject [(T.pack "k", jStr (T.pack "v"))] == T.pack "{\"k\":\"v\"}")
        , ("jArray brackets", jArray [jStr (T.pack "a"), jStr (T.pack "b")] == T.pack "[\"a\",\"b\"]")
        ]
      checks =
        [ (name, frag `T.isInfixOf` escaped) | (name, frag) <- mustContain ]
          ++ [ (name, not (frag `T.isInfixOf` escaped)) | (name, frag) <- mustNotContain ]
          ++ structural
      failed = [name | (name, ok) <- checks, not ok]
  unless (null failed) $ do
    putStrLn "JSON encoder soundness checks failed (Kappa.Diagnostic jStr/jObject/jArray):"
    mapM_ (putStrLn . ("  " <>)) failed
    putStrLn ("  encoded: " <> T.unpack escaped)
  pure (null failed)

-- | §34.3.3 / §34.3.4: the KBackendIR Stage-3 lowering-legality verifier
-- ("Kappa.Backend.Verify") must (a) be CLEAN on well-formed inputs and (b)
-- actually CATCH the legality violations it is responsible for — otherwise it
-- is vacuous. The corpus-clean half is established by running the whole
-- conformance tree (0 false positives); this in-process test pins the
-- non-vacuity half by hand-building deliberately-MALFORMED KBackendIR and
-- asserting each of the three checkpoints fires with its precise code.
verifierCatchesViolations :: IO Bool
verifierCatchesViolations = do
  let m = ModuleName [T.pack "t"]
      gn s = GName m (T.pack s)
      -- ── a tiny world: a datatype D with two unary constructors ────────
      dN = gn "D"
      aN = gn "A" -- a stand-in field/element type
      c1 = gn "C1"
      c2 = gn "C2"
      tyA = CGlob aN
      tyD = CGlob dN
      -- C1, C2 : A -> D  (declared runtime arity 1)
      ctorTy = CPiFormedM Ordinary FormationOrdinary Expl Q1 False (T.pack "_") tyA tyD
      ci =
        CtorInfo
          { ciData = dN
          , ciUniverses = emptyDeclarationUniverseTelescope
          , ciType = ctorTy
          , ciFields = [(Nothing, Nothing)]
          , ciSourceFields = [(Expl, Nothing)]
          }
      datas = Map.fromList [(dN, DataInfo {diCtors = [c1, c2], diParamCount = 0, diLevel = LZero})]
      ctors = Map.fromList [(c1, ci), (c2, ci)]
      -- a unit-typed global 'u' (declared type Unit) and a real function 'f'.
      -- The type VALUEs are obtained by evaluating Core type terms (so their
      -- Pi closures are real, as the verifier's 'force'/'eval' walk requires).
      uN = gn "u"
      fN = gn "f"
      evalTy = eval (EvalCtx (Globals Map.empty) emptyMetas False Map.empty) []
      gd tyTm = GlobalDef (evalTy tyTm) Nothing False
      -- f : A -> A   (one explicit, runtime-kept argument)
      fTyTm = CPiFormedM Ordinary FormationOrdinary Expl Q1 False (T.pack "_") tyA tyA
      -- u : Unit  (a non-function value head: 'prelUnit', the canonical erased
      -- unit type the verifier recognizes).
      uTyTm = CGlob prelUnit
      globals = Map.fromList [(uN, gd uTyTm), (fN, gd fTyTm)]

      base =
        VerifyInputs
          { viGlobals = globals
          , viMetas = emptyMetas
          , viBodies = Map.empty
          , viDatas = datas
          , viCtors = ctors
          }

      codesFor body =
        sort (nub (map (T.unpack . dCode) (verifyUnit base {viBodies = Map.fromList [(gn "main", body)]})))

      -- 1a. erased/non-function head: u applied to an argument → kapp(unit, …).
      nonFnHead = CApp Expl (CGlob uN) (CGlob aN)
      -- 1b. erased TYPE form (a universe) in f's runtime-kept argument slot.
      erasedArg = CApp Expl (CGlob fN) (CSort LZero)
      -- 2. arity mismatch: C1 has runtime arity 1, built with 0 fields.
      arityBad = CCtor c1 Nothing []
      -- 3a. tag-id collision: a datatype listing the SAME ctor twice.
      collideInputs =
        base {viDatas = Map.fromList [(dN, DataInfo {diCtors = [c1, c1], diParamCount = 0, diLevel = LZero})]}
      -- 3b. parent back-reference: a ctor whose ciData points to a DIFFERENT
      -- datatype than the one listing it.
      eN = gn "E"
      wrongParent =
        base
          { viDatas = Map.fromList [(eN, DataInfo {diCtors = [c1], diParamCount = 0, diLevel = LZero})]
          }
      -- 3c. field-count: a ctor declaring 2 explicit fields but whose type has
      -- runtime arity 1.
      fatCtor = ci {ciFields = [(Nothing, Nothing), (Nothing, Nothing)]}
      fieldCountBad =
        base {viCtors = Map.fromList [(c1, fatCtor), (c2, ci)]}
      erasedExplicitSrc =
        T.unlines
          [ "module main"
          , "data T : Type = MkT (0 ghost : Int) (value : Int)"
          , "setValue : T -> T"
          , "let setValue t = t.{ value = 30 }"
          , "getValue : T -> Int"
          , "let getValue t ="
          , "    match t"
          , "    case MkT _ value -> value"
          , "main : UIO Unit"
          , "let main = printlnString (showInt (getValue (setValue (MkT 10 20))))"
          ]
      erasedExplicitCodes =
        map
          (T.unpack . dCode)
          (verifyUnit (verifyInputs (cuState (compileSourceWithPrelude "verify-erased-explicit-ctor.kp" erasedExplicitSrc))))

      -- a CLEAN body for the same world: f applied to a value (a let-bound
      -- var), and a well-formed C1 application — must produce NOTHING.
      cleanBody = CCtor c1 Nothing [CGlob aN]

      checks =
        [ ("1a non-function head flagged", "W_BACKENDIR_NON_FUNCTION_HEAD" `elem` codesFor nonFnHead)
        , ("1b erased type-form arg flagged", "W_BACKENDIR_ERASED_REFERENCE" `elem` codesFor erasedArg)
        , ("2 ctor arity mismatch flagged", "W_BACKENDIR_ARITY_MISMATCH" `elem` codesFor arityBad)
        , ("3a tag-id collision flagged", "W_BACKENDIR_LAYOUT_INCONSISTENT" `elem` map (T.unpack . dCode) (verifyUnit collideInputs))
        , ("3b ctor parent mismatch flagged", "W_BACKENDIR_LAYOUT_INCONSISTENT" `elem` map (T.unpack . dCode) (verifyUnit wrongParent))
        , ("3c ctor field-count overflow flagged", "W_BACKENDIR_LAYOUT_INCONSISTENT" `elem` map (T.unpack . dCode) (verifyUnit fieldCountBad))
        , ("erased explicit constructor field is verifier-clean", null erasedExplicitCodes)
        , ("clean body produces no findings", null (codesFor cleanBody))
        , ("clean world (no body) produces no findings", null (map (T.unpack . dCode) (verifyUnit base)))
        ]
      failed = [name | (name, ok) <- checks, not ok]
  unless (null failed) $ do
    putStrLn "KBackendIR Stage-3 verifier non-vacuity checks failed:"
    mapM_ (putStrLn . ("  " <>)) failed
  pure (null failed)

-- | §3.1.2A: "A diagnostic emitted in ordinary user-facing compilation
-- MUST NOT use an unregistered code." Every @\"E_...\"@ \/ @\"W_...\"@
-- string literal in the sources (emit sites and alias tables alike)
-- must be present in the 'Kappa.Explain' registry.
registryComplete :: IO Bool
registryComplete = do
  files <- haskellSources ["src/Kappa", "src/Kappa/Parser", "src/Kappa/Build", "src/Kappa/Backend", "app"]
  codes <- concat <$> mapM (fmap codeLiterals . TIO.readFile) files
  let missing = sort (nub [c | c <- codes, not (explainExists c)])
  if null missing
    then pure True
    else do
      putStrLn "diagnostic codes missing from the §3.1.2A registry (Kappa.Explain):"
      mapM_ (putStrLn . ("  " <>) . T.unpack) missing
      pure False

-- | §3.1.2/§3.1.2A family-namespace hygiene: the @kappa.@ namespace is
-- reserved for the specification, so every family literal in the
-- sources that begins with @kappa.@ must be a spelling Spec.md itself
-- defines; implementation-defined families must use this
-- implementation's reserved prefix (@kappa-hs.@); and every family
-- spelled at an emission site must be carried by some registry entry.
familiesHygienic :: IO Bool
familiesHygienic = do
  files <- haskellSources ["src/Kappa", "src/Kappa/Parser", "src/Kappa/Build", "src/Kappa/Backend", "app"]
  fams <- concat <$> mapM (fmap familyLiterals . TIO.readFile) files
  hasSpec <- doesFileExist "docs/Spec.md"
  specFams <-
    if hasSpec
      then specFamilyTokens <$> TIO.readFile "docs/Spec.md"
      else pure []
  let emitted = sort (nub fams)
      squatting =
        [ f | f <- emitted, "kappa." `T.isPrefixOf` f
        , hasSpec, f `notElem` specFams
        ]
      misprefixed =
        [ f | f <- emitted
        , not ("kappa." `T.isPrefixOf` f)
        , not ("kappa-hs." `T.isPrefixOf` f)
        ]
      unregistered =
        [f | f <- emitted, not (any ((== Just f) . eeFamily) registry)]
      bad =
        [ (m, fs)
        | (m, fs) <-
            [ ("families squatting the reserved kappa. namespace without a Spec.md spelling:", squatting)
            , ("families outside both kappa. and the kappa-hs. implementation prefix:", misprefixed)
            , ("families at emission sites missing from the §3.1.2A registry (Kappa.Explain):", unregistered)
            ]
        , not (null fs)
        ]
  if null bad
    then pure True
    else do
      mapM_
        (\(m, fs) -> putStrLn m >> mapM_ (putStrLn . ("  " <>) . T.unpack) fs)
        bad
      pure False

-- | Every @kappa.…@ dotted token spelled anywhere in Spec.md (the
-- standardized family spellings, plus harmless non-family tokens that
-- never collide with emitted families).
specFamilyTokens :: T.Text -> [T.Text]
specFamilyTokens = go
  where
    go t = case T.breakOn "kappa." t of
      (_, rest)
        | T.null rest -> []
        | otherwise ->
            let tok = T.dropWhileEnd (`elem` (".-" :: String)) (T.takeWhile famChar rest)
             in tok : go (T.drop 6 rest)

-- | All double-quoted string literals that are family spellings
-- (@kappa.…@ or @kappa-hs.…@).
familyLiterals :: T.Text -> [T.Text]
familyLiterals = go
  where
    go t = case T.breakOn "\"" t of
      (_, rest)
        | T.null rest -> []
        | otherwise ->
            let body = T.drop 1 rest
                (lit, rest') = T.breakOn "\"" body
             in [lit | isFam lit] ++ go (T.drop 1 rest')
    isFam f =
      (("kappa." `T.isPrefixOf` f) || ("kappa-hs." `T.isPrefixOf` f))
        && T.all famChar f
        && f `notElem` ["kappa.", "kappa-hs."] -- bare prefix-test literals

famChar :: Char -> Bool
famChar ch = isAsciiLower ch || isDigit ch || ch == '.' || ch == '-'

haskellSources :: [FilePath] -> IO [FilePath]
haskellSources dirs =
  fmap concat . sequence $
    [ do
        ok <- doesDirectoryExist d
        if ok
          then map ((d <> "/") <>) . filter (".hs" `isSuffixOf`) <$> listDirectory d
          else pure []
    | d <- dirs
    ]

-- | All double-quoted string literals of shape @E_CODE@ \/ @W_CODE@,
-- plus the spec-spelled @KAPPA_…@ codes of §22 shape reflection.
codeLiterals :: T.Text -> [T.Text]
codeLiterals = go
  where
    go t = case T.breakOn "\"" t of
      (_, rest)
        | T.null rest -> []
        | otherwise ->
            let body = T.drop 1 rest
                (lit, rest') = T.breakOn "\"" body
             in [lit | isCode lit] ++ go (T.drop 1 rest')
    isCode c =
      any
        (\p -> p `T.isPrefixOf` c && T.length c > T.length p)
        ["E_", "W_", "KAPPA_"]
        && T.all (\ch -> isAsciiUpper ch || isDigit ch || ch == '_') c
