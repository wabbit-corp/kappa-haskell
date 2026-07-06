-- | Cabal test-suite driver: runs the Appendix T conformance tree
-- under @tests/conformance@ through the in-process harness, then
-- cross-checks the §3.1.2A diagnostic code registry against every
-- diagnostic code spelled in the implementation sources.
module Main (main) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (isInfixOf, isSuffixOf, nub, sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Monad (forM, unless, when)
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
  , BackendPat (..)
  , BackendTerm (..)
  , BackendIRViolation (..)
  , BackendUse (..)
  , KBackendIR (..)
  , BackendUseId (..)
  , lowerKBackendIR
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
import Kappa.Builtins (gPrel, prelDouble, prelInt, prelUnit, primModule)
import Kappa.Check (CheckState (..), CtorInfo (..), DataInfo (..))
import Kappa.Core
  ( Closure (..)
  , GName (..)
  , Icit (..)
  , Q (..)
  , Term (..)
  , Value (..)
  )
import Kappa.Diagnostic (dCode, jArray, jObject, jStr)
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), emptyMetas, eval, force)
import Kappa.Explain (ExplainEntry (..), explainExists, registry)
import Kappa.Ownership
  ( BinderId (..)
  , BinderOwn (..)
  , BranchSite (..)
  , OwnInfo (..)
  , UseKind (..)
  , annotateOwnership
  , argConvBodies
  , crossCheckBodies
  , renderOwnInfo
  )
import Kappa.Pipeline (CompiledUnit (..), compileFiles, compileSourceWithPrelude)
import Kappa.Source (ModuleName (..))
import Kappa.TestHarness
  ( Outcome (..)
  , Summary (..)
  , TestReport (..)
  , runTestFile
  , runTestPath
  , summarize
  )
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , getTemporaryDirectory
  , listDirectory
  , removeDirectoryRecursive
  )
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.IO (BufferMode (..), hSetBuffering, stdout)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  regOk0 <- registryComplete
  famOk <- familiesHygienic
  harnessOk <- harnessFaithful
  jsonOk <- jsonEncoderSound
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
  let regOk =
        regOk0 && famOk && harnessOk && jsonOk && verifyOk && reprOk
          && primConvOk && spineErasureOk && ownOk && s23dOk && s23dDiagOk && s32Ok && cachePubOk && backendIrOk && backendIrValidateOk && backendIrConsumerOk && backendIrNoPathOwnOk && ownershipNoRPathOk && backendIrProjectedBorrowedOk && backendIrPatternErasureOk && scalarKindParamOk
          && scalarDoubleEscapeOk && ctorLayoutOk && reExportOk
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
        CPi Expl Q1 False (T.pack "a") (CSort 0) $
          CPi Expl QW False (T.pack "r") (CGlob prelInt) $
            CPi Expl QW False (T.pack "v") (CGlob prelInt) $
              CGlob prelUnit
      fakePrimCtx =
        let gd =
              GlobalDef
                { gdType = eval ctx [] fakePrimTy
                , gdValue = Just (VPrim (T.pack "__ioWriteRef") [])
                , gdReducible = False
                }
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
      CLam ic q n body -> CLam ic q n (go body)
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
            ctorTypes = Map.map ciType (csCtors st)
            -- S1.1 last-use + S1.4 §3a refinement tighten-only invariant.
            xc =
              crossCheckBodies
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
          , "type RecAlias = (f : PeekInt)"
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
          , "foo : (a : Type) -> Int"
          , "let foo a = 0"
          , "typeOnly : (a : Type) -> Int"
          , "let typeOnly a = foo a"
          , "type K = Type"
          , "fooK : (a : K) -> Int"
          , "let fooK a = 0"
          , "typeOnlyAlias : (a : K) -> Int"
          , "let typeOnlyAlias a = fooK a"
          , "projOnly : (r : (v : Int)) -> Int"
          , "let projOnly r = r.v"
          , "type Box = (v : Int)"
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
            ctorTypes = Map.map ciType (csCtors st)
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
            forcedMsgs = crossCheckBodies ctx ctorTypes forcedBodies forcedLinear
            missingMsgs = crossCheckBodies ctx ctorTypes forcedBodies Map.empty
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
            driftUsesMsgs = crossCheckBodies ctx ctorTypes forcedBodies driftUses
            driftBinderUsesMsgs = crossCheckBodies ctx ctorTypes forcedBodies driftBinderUses
            driftBindersMsgs = crossCheckBodies ctx ctorTypes forcedBodies driftBinders
            focusedXc = crossCheckBodies ctx ctorTypes (csCoreBodies st) (csOwnership st)
            directPrimReadBody =
              replaceGlobInSimpleApp
                (gPrel (T.pack "__ioReadRef"))
                (GName primModule (T.pack "__ioReadRef"))
                <$> Map.lookup primReadRefBorrowG (csCoreBodies st)
            directPrimReadOwn =
              maybe
                Map.empty
                (\body -> annotateOwnership ctx ctorTypes (Map.singleton primReadRefBorrowG body))
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
          , "type RHolder : Type = (box : Box)"
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
          , "    let h : RHolder = (box = MkBox 9)"
          , "    let y = h.box"
          , "    if c"
          , "    then consumeBox y"
          , "    else peekRHolder h"
          , "branchBorrowedNestedAlias : Bool -> Int"
          , "let branchBorrowedNestedAlias c ="
          , "    let h : RHolder = (box = MkBox 12)"
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
  case generateC True st mainG Set.empty Map.empty of
    Left (errs, mLog) -> do
      putStrLn ("perceusS23dDeadBinderDrops FAILED: generateC rejected: " <> show errs)
      putStrLn ("  rcLog=" <> show mLog)
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
            "if (kas_bool(ktrampoline(kw_main_2e_peekBox(let_" `T.isInfixOf` guardWorker
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
                case generateC True stCase mainG Set.empty Map.empty of
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
  case generateC True st mainG Set.empty Map.empty of
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
    case generateC True st mainG Set.empty Map.empty of
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
    case generateLL True st mainG Set.empty Map.empty of
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
    case generateC False st mainG Set.empty Map.empty of
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
    case generateLL False st mainG Set.empty Map.empty of
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
  case generateLL False st mainG Set.empty Map.empty of
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
          , "type TypeOnly = (a : Type)"
          , "type TupleErased = (a : Type, b : Int)"
          , "type RuntimeProofRec = (proof : (=) 1 1, value : Int)"
          , "type ErasedProofRec = (prop : IsProp ((=) \"x\" \"x\"), value : Int)"
          , "data GhostBox : Type = MkGhostBox (0 ghost : Int) (value : Int)"
          , "data ErasedTail : Type = MkErasedTail (a : Int) (b : Int) (c : Type)"
          , "foo : R"
          , "let foo = (a = Int, b = 5)"
          , "let useRecord = foo.b"
          , "sourceType : TypeOnly"
          , "let sourceType = (a = Int)"
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
              BackendAlt _ (BPCtor g [BPWild, BPVar n]) binders _ _ ->
                g == mkErasedTailG && n == T.pack "b" && length binders == 1
              _ -> False
          )
          erasedTailAlts
      tuplePatternErasedFieldReindexed =
        any
          ( \case
              BackendAlt _ (BPTuple [BPVar n]) binders _ _ ->
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
        , ("lowered tree is not the old wrapper scaffold", noWrapperScaffold)
        ]
      failed = [name | (name, ok) <- checks, not ok]
  unless (null failed) $ do
    putStrLn "backendIRPhaseAS5 FAILED:"
    mapM_ (putStrLn . ("  " <>)) failed
    putStrLn ("  bodies=" <> show (Map.keys backendBodies))
    putStrLn ("  idBox=" <> show body)
    putStrLn ("  useIdBox=" <> show callBody)
    putStrLn ("  foo=" <> show recordBody)
    putStrLn ("  useRecord=" <> show recordProjBody)
    putStrLn ("  fooComputed=" <> show computedRecordBody)
    putStrLn ("  useRecordComputed=" <> show computedRecordProjBody)
    putStrLn ("  runtimeProofRec=" <> show runtimeProofRecordBody)
    putStrLn ("  erasedProofRec=" <> show erasedProofRecordBody)
    putStrLn ("  makeGhost=" <> show ghostBody)
    putStrLn ("  useErasedTail=" <> show erasedTailBody)
    putStrLn ("  useTuplePattern=" <> show tuplePatternBody)
    putStrLn ("  usePolyArg=" <> show polyArgBody)
    putStrLn ("  localPoly=" <> show localPolyBody)
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
      badCtor =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
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
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                []
                (BCtor meta0 (BackendCtorLayout (gn "MkBad") (Just staleInfo) 1) [BGlob meta1 (gn "x")])
          )
          []
      badUse =
        KBackendIR
          (Map.singleton owner $ BackendBody owner [] (BVar meta0 Nothing 0))
          []
      dupUse = BackendUse (BackendUseId 0) NonLast False
      badDuplicateUse =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                []
                (BRecord meta0 [(T.pack "a", BVar meta1 (Just dupUse) 0), (T.pack "b", BVar meta2 (Just dupUse) 0)])
          )
          []
      badBinder =
        KBackendIR
          (Map.singleton owner $ BackendBody owner [BackendParam Expl (T.pack "x") Nothing] (BUnit meta0))
          []
      badNodeId =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                []
                (BLet meta0 Nothing Q1 (T.pack "x") (BUnit meta0) (BUnit meta1))
          )
          []
      badBranchDrop =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                []
                (BIf (BackendMeta (BackendNodeId 2) [BackendBinder (BackendBinderId 99) (T.pack "dangling") (BinderOwn QW Nothing False True) False]) (BUnit meta0) (BUnit meta1) (BUnit (BackendMeta (BackendNodeId 3) [])))
          )
          []
      realDropBinder = BackendBinder (BackendBinderId 0) (T.pack "real") (BinderOwn QW Nothing False True) False
      forgedDropBinder = BackendBinder (BackendBinderId 0) (T.pack "forged") (BinderOwn QW Nothing False True) False
      badForgedBranchDrop =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                [BackendParam Expl (T.pack "x") (Just realDropBinder)]
                (BIf (BackendMeta (BackendNodeId 2) [forgedDropBinder]) (BUnit meta0) (BUnit meta1) (BUnit (BackendMeta (BackendNodeId 3) [])))
          )
          []
      badDuplicateBranchDrop =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                [BackendParam Expl (T.pack "x") (Just realDropBinder)]
                (BIf (BackendMeta (BackendNodeId 2) [realDropBinder, realDropBinder]) (BUnit meta0) (BUnit meta1) (BUnit (BackendMeta (BackendNodeId 3) [])))
          )
          []
      badItemBranchDrop =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                [BackendParam Expl (T.pack "x") (Just realDropBinder)]
                (BDo meta0 Nothing [BKExpr (BackendMeta (BackendNodeId 2) [realDropBinder]) (BUnit meta1)])
          )
          []
      duplicateBinderA = BackendBinder (BackendBinderId 0) (T.pack "a") (BinderOwn QW Nothing False True) False
      duplicateBinderB = BackendBinder (BackendBinderId 0) (T.pack "b") (BinderOwn QW Nothing False True) False
      badDuplicateBinder =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                [ BackendParam Expl (T.pack "a") (Just duplicateBinderA)
                , BackendParam Expl (T.pack "b") (Just duplicateBinderB)
                ]
                (BUnit meta0)
          )
          []
      badPattern =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                []
                (BMatch meta0 (BUnit meta1) [BackendAlt meta0 (BPCtor (gn "MkBad") [BPWild, BPWild]) [] Nothing (BUnit meta1)] [(gn "MkBad", BackendCtorLayout (gn "MkBad") Nothing 1)])
          )
          []
      badPatternInfo =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                []
                (BMatch meta0 (BUnit meta1) [BackendAlt meta0 (BPCtor (gn "MkBad") [BPWild]) [] Nothing (BUnit meta1)] [(gn "MkBad", BackendCtorLayout (gn "MkBad") (Just staleInfo) 1)])
          )
          []
      badPatternMissingLayout =
        KBackendIR
          ( Map.singleton owner $
              BackendBody
                owner
                []
                (BMatch meta0 (BUnit meta1) [BackendAlt meta2 (BPCtor (gn "MkBad") [BPWild]) [] Nothing (BUnit meta3)] [])
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
          , "type Box = (v : Int)"
          , "type PeekBox = (& x : Box) -> Int"
          , "peekBox : (& x : Box) -> Int"
          , "let peekBox x = x.v"
          , "type RecAlias = (f : PeekBox)"
          , "useProjectedTwice : RecAlias -> Box -> Int"
          , "let useProjectedTwice r y = r.f y + y.v"
          , "type PolyBox (a : Type) = (v : a)"
          , "type PolyRec (a : Type) = (f : (& x : PolyBox a) -> a)"
          , "polyPeek : (a : Type) -> (& x : PolyBox a) -> a"
          , "let polyPeek a x = x.v"
          , "usePolyProjected : (a : Type) -> PolyRec a -> PolyBox a -> (a, a)"
          , "let usePolyProjected a r y = (r.f y, y.v)"
          , "polyId : (a : Type) -> a -> a"
          , "let polyId a x = x"
          , "firstClassPoly : ((a : Type) -> a -> a) -> Int"
          , "let firstClassPoly f = f Int 1"
          , "main : UIO Unit"
          , "let main = printInt (useProjectedTwice (f = peekBox) (v = 1))"
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
        | BackendAlt _ (BPCtor g _) binders _ _ <- alts
        , g == mkQ
        ]
      mainG = GName m (T.pack "main")
      generatedC = case generateC False st mainG Set.empty Map.empty of
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
      ctorTypes = Map.map ciType (csCtors st)
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
        crossCheckBodies
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
        crossCheckBodies
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
  -- §T.5.3 (G32): an un-gated assertStageDump names a checkpoint this
  -- implementation cannot serve, so the suite is ill-formed; gating it
  -- behind 'requires capability stageDumps' yields the soft outcome.
  stageDump <- fileCase root "g32-stagedump.kp"
    "--! assertStageDump kfront equals expected.json\nlet x : Int = 5\n"
  stageGated <- fileCase root "g32-stagedump-gated.kp"
    "--! requires capability stageDumps\n--! assertStageDump kfront equals expected.json\nlet x : Int = 5\n"
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
        , ("G32 gated assertStageDump → unsupported", trOutcome stageGated == Unsupported)
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
      ctorTy = CPi Expl Q1 False (T.pack "_") tyA tyD
      ci = CtorInfo {ciData = dN, ciType = ctorTy, ciFields = [(Nothing, Nothing)]}
      datas = Map.fromList [(dN, DataInfo {diCtors = [c1, c2], diParamCount = 0})]
      ctors = Map.fromList [(c1, ci), (c2, ci)]
      -- a unit-typed global 'u' (declared type Unit) and a real function 'f'.
      -- The type VALUEs are obtained by evaluating Core type terms (so their
      -- Pi closures are real, as the verifier's 'force'/'eval' walk requires).
      uN = gn "u"
      fN = gn "f"
      evalTy = eval (EvalCtx (Globals Map.empty) emptyMetas False Map.empty) []
      gd tyTm = GlobalDef {gdType = evalTy tyTm, gdValue = Nothing, gdReducible = False}
      -- f : A -> A   (one explicit, runtime-kept argument)
      fTyTm = CPi Expl Q1 False (T.pack "_") tyA tyA
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
      erasedArg = CApp Expl (CGlob fN) (CSort 0)
      -- 2. arity mismatch: C1 has runtime arity 1, built with 0 fields.
      arityBad = CCtor c1 Nothing []
      -- 3a. tag-id collision: a datatype listing the SAME ctor twice.
      collideInputs =
        base {viDatas = Map.fromList [(dN, DataInfo {diCtors = [c1, c1], diParamCount = 0})]}
      -- 3b. parent back-reference: a ctor whose ciData points to a DIFFERENT
      -- datatype than the one listing it.
      eN = gn "E"
      wrongParent =
        base
          { viDatas = Map.fromList [(eN, DataInfo {diCtors = [c1], diParamCount = 0})]
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
