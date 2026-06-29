-- | Cabal test-suite driver: runs the Appendix T conformance tree
-- under @tests/conformance@ through the in-process harness, then
-- cross-checks the §3.1.2A diagnostic code registry against every
-- diagnostic code spelled in the implementation sources.
module Main (main) where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (isInfixOf, isSuffixOf, nub, sort)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Monad (unless)
import Kappa.Backend.Repr
  ( CtorLayoutInfo (..)
  , Rep (..)
  , ctorLayoutOf
  , scalarRep
  )
import Kappa.Backend.Verify (VerifyInputs (..), verifyUnit)
import Kappa.Builtins (prelDouble, prelInt, prelUnit)
import Kappa.Check (CheckState (..), CtorInfo (..), DataInfo (..))
import Kappa.Core
  ( GName (..)
  , Icit (..)
  , Q (..)
  , Term (..)
  , Value (..)
  )
import Kappa.Diagnostic (dCode, jArray, jObject, jStr)
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), emptyMetas, eval, quote)
import Kappa.Explain (ExplainEntry (..), explainExists, registry)
import Kappa.Ownership
  ( BinderId (..)
  , BinderOwn (..)
  , OwnInfo (..)
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
  ownOk <- ownershipCrossCheckClean
  ctorLayoutOk <- ctorLayoutEvidenceFields
  reExportOk <- reExportBoundaryRefinement
  let regOk =
        regOk0 && famOk && harnessOk && jsonOk && verifyOk && reprOk
          && ownOk && ctorLayoutOk && reExportOk
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
            paramBid g = BinderId g []
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
      -- leading CPi telescope under the SAME runtime field rule etaCtor uses
      -- (Expl _ -> True; Impl q -> q /= Q0), without consulting ctorLayoutOf.
      runtimeCtorArity :: Term -> Int
      runtimeCtorArity = goCount . quote ctx 0 . eval ctx []
        where
          goCount = \case
            CPi ic q _ _ _ cod ->
              (if runtimeField ic q then 1 else 0) + goCount cod
            _ -> 0
          runtimeField Expl _ = True
          runtimeField Impl q = q /= Q0
      look cname = Map.lookup (GName m (T.pack cname)) (csCtors st)
      -- (ctorLayoutOf-arity, ctorLayoutOf-fieldReps, runtime-oracle-arity)
      probe cname = case look cname of
        Nothing -> Nothing
        Just ci ->
          case ctorLayoutOf ctx (Just (ciType ci)) of
            Nothing -> Nothing
            Just info -> Just (clArity info, clFieldReps info, runtimeCtorArity (ciType ci))
      -- every existential-dictionary ctor: layout arity == runtime arity, and
      -- the dictionary field is RepBoxed.
      evidenceOK cname expectArity =
        case probe cname of
          Just (a, reps, oracle) ->
            a == expectArity
              && a == oracle
              && length reps == expectArity
              && all (== RepBoxed) reps
          Nothing -> False
      -- a known-good case: exact (arity, fieldReps) tuple.
      exactOK cname want =
        case probe cname of
          Just (a, reps, oracle) -> (a, reps) == want && a == oracle
          Nothing -> False
      checks =
        [ ("MkShowable evidence", evidenceOK "MkShowable" 2, probe "MkShowable") -- [Show dict, a]
        , ("MkEqd evidence", evidenceOK "MkEqd" 3, probe "MkEqd") -- [Eqt dict, a, a]
        , ("MkMyUnit nullary", exactOK "MkMyUnit" (0, []), probe "MkMyUnit")
        , ("MkMyBox single boxed", exactOK "MkMyBox" (1, [RepBoxed]), probe "MkMyBox")
        , ("MkIntBox scalar", exactOK "MkIntBox" (1, [RepInt]), probe "MkIntBox")
        , ("MkMyPair pair boxed", exactOK "MkMyPair" (2, [RepBoxed, RepBoxed]), probe "MkMyPair")
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
      -- the single leading ω parameter of each one-arg body sits at biPath [].
      refinedOf cname =
        case Map.lookup (GName lib (T.pack cname)) (csOwnership st) of
          Nothing -> Left ("no OwnInfo for " <> cname)
          Just oi ->
            case Map.lookup (BinderId (GName lib (T.pack cname)) []) (oiBinders oi) of
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
                      (BinderId (GName lib (T.pack "priv")) [])
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
