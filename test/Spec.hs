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
import Kappa.Backend.Repr (Rep (..), scalarRep)
import Kappa.Backend.Verify (VerifyInputs (..), verifyUnit)
import Kappa.Builtins (prelDouble, prelInt, prelUnit)
import Kappa.Check (CtorInfo (..), DataInfo (..))
import Kappa.Core
  ( GName (..)
  , Icit (..)
  , Q (..)
  , Term (..)
  , Value (..)
  )
import Kappa.Diagnostic (dCode, jArray, jObject, jStr)
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), emptyMetas, eval)
import Kappa.Explain (ExplainEntry (..), explainExists, registry)
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
  let regOk = regOk0 && famOk && harnessOk && jsonOk && verifyOk && reprOk
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
