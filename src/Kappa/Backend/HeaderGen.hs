-- | Mechanical generation of a native binding's raw @host.native@ surface from
-- a real C header (§27.1.1/§36.28). This is the realization of a manifest
-- 'Kappa.Build.Types.GeneratedSurface': given a header and a list of C function
-- names, it
--
--   * resolves the binding's include path from its pkg-config @--cflags@,
--     explicit include dirs, and header dirs, plus its @-D@ defines;
--   * preprocesses a probe translation unit that @#include@s the header with
--     the selected target ABI defines (@cc -E -P@) — so macros, typedefs, and
--     conditional declarations resolve exactly as the real compile sees them;
--   * parses each named function's declaration out of the preprocessed text
--     (return type + parameter types), stripping GCC attributes and storage
--     classes; and
--   * maps each C type to the CONSERVATIVE std.ffi / opaque / Option 'CType'
--     vocabulary (a non-@char@ pointer ⇒ @Option RawPtr@, a @char@ pointer ⇒
--     the C-string convention, integer/float scalars ⇒ their exact-width
--     std.ffi nominal, @void@ result ⇒ Unit).
--
-- There is NO hand-authored 'SymbolDecl': the surface is DERIVED from the real
-- header bytes (which the lockfile pins, §36.7). A requested symbol whose
-- declaration cannot be located, or whose types are not conservatively
-- mappable (e.g. a by-value struct or a callback-typedef parameter), is a
-- fail-closed build error — the binding must not silently omit or guess it.
module Kappa.Backend.HeaderGen
  ( generateSurfaceDecls
  ) where

import Control.Exception (SomeException, catch, finally)
import Data.Char (isAlphaNum, isSpace)
import Data.List (isPrefixOf)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Build.Types (CType (..), NativeInput (..), SymbolDecl (..))
import Kappa.Diagnostic
import Kappa.Source (Pos (..), Span (..))
import System.Directory (findExecutable, removeFile)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import System.Process (readProcessWithExitCode)

-- | Generate the @[SymbolDecl]@ for a 'GeneratedSurface'. @cc@ is the detected
-- C driver @(exe, leadingArgs)@; @baseDir@ is the manifest directory (header /
-- include paths resolve against it); @workDir@ holds the generated probe TU.
-- The Kappa member of each generated symbol is its C function name verbatim.
generateSurfaceDecls
  :: (String, [String]) -> FilePath -> FilePath -> [NativeInput] -> Text -> [Text]
  -> IO (Either Diagnostics [SymbolDecl])
generateSurfaceDecls (ccExe, ccLead) baseDir workDir inputs header symbols = do
  cflags <- pkgCflags [(p) | PkgConfigInput p _ <- inputs]
  let incDirs = [baseDir </> T.unpack d | IncludeDirInput d <- inputs]
      hdrDirs = [takeDirectory (baseDir </> T.unpack h) | HeadersInput hs <- inputs, h <- hs]
      defs = ["-D" <> T.unpack n <> "=" <> T.unpack v | DefineInput n v <- inputs]
      iflags = concat [["-I", d] | d <- baseDir : incDirs ++ hdrDirs ++ systemIncludeDirs]
      probePath = workDir </> "native-header-gen-probe.c"
      probe =
        unlines
          [ "/* generated header-surface probe (Kappa.Backend.HeaderGen). */"
          , "#include <stdint.h>"
          , "#include <stddef.h>"
          , "#include \"" <> T.unpack header <> "\""
          ]
  writeFile probePath probe
  let args = ccLead ++ ["-std=c11", "-E", "-P"] ++ iflags ++ cflags ++ defs ++ [probePath]
  -- clean the probe TU from the package dir even if preprocessing throws.
  (ec, out, err) <-
    readProcessWithExitCode ccExe args ""
      `finally` (removeFile probePath `catch` \(_ :: SomeException) -> pure ())
  case ec of
    ExitFailure _ ->
      pure (Left [genErr ("could not preprocess header '" <> header <> "' for native surface generation (Spec §27.1.1/§36.28):\n" <> T.pack (trim (out ++ err)))])
    ExitSuccess ->
      let norm = normalize out
       in pure (traverse (parseOne header norm) symbols)
  where
    trim s = if length s <= 3000 then s else "...\n" ++ drop (length s - 3000) s

-- | Parse the one declaration of @sym@ out of the normalized preprocessed text
-- and build its 'SymbolDecl' (member = C symbol = @sym@). Fail-closed if it is
-- not found or any of its types are not conservatively mappable.
parseOne :: Text -> String -> Text -> Either Diagnostics SymbolDecl
parseOne header norm sym =
  case findDecl norm (T.unpack sym) of
    Nothing ->
      Left [genErr ("native binding header '" <> header <> "' does not declare a function '" <> sym <> "' (Spec §27.1.1)")]
    Just (retRaw, paramRaw) -> do
      result <- first (typeErr header sym) (mapType True retRaw)
      params <- first (typeErr header sym) (parseParams paramRaw)
      Right (SymbolDecl sym sym params result)
  where
    first f = either (Left . pure . f) Right

-- ── declaration location ───────────────────────────────────────────────

-- | Find the first real declaration of @sym@: a whole-word occurrence
-- immediately followed (after a normalized single space removal) by a
-- balanced @(...)@ parameter list, whose close paren is followed by @;@ or
-- @{@. Returns @(returnTypeText, parameterListText)@.
findDecl :: String -> String -> Maybe (String, String)
findDecl txt sym = go (zip3 (' ' : txt) [0 :: Int ..] (tailsList txt))
  where
    slen = length sym
    go [] = Nothing
    go ((pc, i, suf) : rest)
      | sym `isPrefixOf` suf
      , not (isIdentChar pc)
      , afterName <- dropWhile (== ' ') (drop slen suf)
      , take 1 afterName == ("(" :: String) =
          case matchParen afterName of
            Just (inner, after)
              | declTail after -> Just (returnType (take i txt), inner)
            _ -> go rest
      | otherwise = go rest
    -- a prototype ends in ';'; a definition body opens with '{' — both are
    -- genuine declarations (we never request a macro/call site).
    declTail after = case dropWhile (== ' ') after of
      (';' : _) -> True
      ('{' : _) -> True
      _ -> False

-- | The return-type text preceding the function name: everything since the
-- previous top-level declaration terminator, with storage classes stripped.
returnType :: String -> String
returnType prefix =
  let raw = reverse (takeWhile (`notElem` (";}{" :: String)) (reverse prefix))
   in unwords (filter (`notElem` storageClasses) (words raw))

storageClasses :: [String]
storageClasses = ["extern", "static", "typedef", "_Thread_local", "__inline", "__inline__", "inline", "__extension__"]

-- | Split @s@ (the text just after a '(') at its matching ')'. Returns the
-- inner parameter text and the text after the close paren.
matchParen :: String -> Maybe (String, String)
matchParen s0 = go (0 :: Int) (drop 1 s0) []
  where
    go _ [] _ = Nothing
    go depth (c : cs) acc
      | c == '(' = go (depth + 1) cs (c : acc)
      | c == ')' = if depth == 0 then Just (reverse acc, cs) else go (depth - 1) cs (c : acc)
      | otherwise = go depth cs (c : acc)

-- ── parameter + type mapping ───────────────────────────────────────────

-- | Map a parameter list's inner text to conservative parameter CTypes. An
-- empty list or a lone @void@ means no parameters.
parseParams :: String -> Either Text [CType]
parseParams inner =
  case trimStr inner of
    "" -> Right []
    "void" -> Right []
    s -> traverse (mapType False) (splitTop s)

-- | Split a parameter list on top-level commas (respecting nested parens, so a
-- function-pointer parameter stays intact — it will then fail to map, which is
-- the intended fail-closed outcome for a callback parameter).
splitTop :: String -> [String]
splitTop = go (0 :: Int) "" []
  where
    go _ cur acc [] = reverse (reverse cur : acc)
    go d cur acc (c : cs)
      | c == '(' = go (d + 1) (c : cur) acc cs
      | c == ')' = go (d - 1) (c : cur) acc cs
      | c == ',' && d == 0 = go d "" (reverse cur : acc) cs
      | otherwise = go d (c : cur) acc cs

-- | Map a single C type (a return type or a parameter declaration, possibly
-- carrying a parameter name) to a conservative 'CType'. @isResult@ selects the
-- @void@→Unit result framing.
mapType :: Bool -> String -> Either Text CType
mapType isResult raw =
  let s = trimStr raw
      ptr = length (filter (== '*') s)
      toks = words (map (\c -> if c == '*' then ' ' else c) s)
      qual = ["const", "volatile", "struct", "union", "enum", "restrict", "__restrict", "__restrict__", "_Atomic"]
      baseToks = filter (`notElem` qual) toks
   in if '(' `elem` s
        -- a parenthesized declarator — a function-pointer / callback parameter
        -- (e.g. `int (*cb)(int)`) — has no conservative C-ABI mapping; fail
        -- closed rather than silently treating it as a void* pointer.
        then Left ("cannot map the C type '" <> T.pack s <> "' (a function-pointer/callback or parenthesized declarator has no conservative C-ABI correspondence)")
        else if ptr >= 1
          then
            if "char" `elem` baseToks
              then Right CtString -- a char pointer is the conservative C-string surface
              else Right CtRawPtr -- §26.1.1: a pointer we cannot prove non-null ⇒ Option RawPtr
          else classifyScalar isResult raw baseToks

-- | Classify a non-pointer C type. A parameter name (a trailing identifier
-- that is not a type keyword) is tolerated; an unrecognized by-value type
-- (a typedef/struct/enum/callback) is unmappable and fails closed.
classifyScalar :: Bool -> String -> [String] -> Either Text CType
classifyScalar isResult raw toks0 =
  let unsigned = "unsigned" `elem` toks0
      signed = "signed" `elem` toks0
      core = filter (`notElem` ["signed", "unsigned"]) (filter isTypeWord toks0)
      -- C 'long long' is ABI-identical to int64_t on our targets, but is a
      -- DISTINCT C type, so the fixed-width prototype the ABI verifier
      -- reconstructs (int64_t) would conflict with the real 'long long'
      -- declaration. Fail closed with a clear message rather than emit a
      -- surface the verifier rejects with an opaque C error.
      longLong = Left ("C 'long long' has no exact std.ffi correspondence the ABI verifier accepts; declare a fixed-width type (int64_t/uint64_t) in the header")
      -- 'long double' (e.g. 80-bit on x86_64) is NOT 'double'; fail closed for
      -- the same reason as 'long long' rather than emit a wrong-width surface.
      longDouble = Left ("C 'long double' has no exact std.ffi correspondence (it is not 'double'); declare a fixed-width floating type in the header")
   in case core of
        [] | unsigned -> Right CtU32 -- bare 'unsigned' == unsigned int
        [] | signed -> Right CtInt -- bare 'signed' == int
        ["void"] | isResult -> Right CtUnit
        ["int"] -> Right (if unsigned then CtU32 else CtInt)
        ["char"] -> Right (if unsigned then CtU8 else CtI8)
        ["short"] -> Right (if unsigned then CtU16 else CtI16)
        ["short", "int"] -> Right (if unsigned then CtU16 else CtI16)
        -- §26.1.1: 'long'/'unsigned long' map to 64-bit on the LP64 model
        -- (the realized native target, e.g. x86_64-linux-gnu, where int64_t is
        -- 'long'); a scalar mismatch on a non-LP64 target is caught fail-closed
        -- by the ABI verifier's reconstructed prototype.
        ["long"] -> Right (if unsigned then CtU64 else CtI64)
        ["long", "int"] -> Right (if unsigned then CtU64 else CtI64)
        ["long", "long"] -> longLong
        ["long", "long", "int"] -> longLong
        ["double"] -> Right CtF64
        ["long", "double"] -> longDouble
        ["float"] -> Right CtF32
        ["_Bool"] -> Right CtBool
        ["bool"] -> Right CtBool
        ["int8_t"] -> Right CtI8
        ["int16_t"] -> Right CtI16
        ["int32_t"] -> Right CtI32
        ["int64_t"] -> Right CtI64
        ["uint8_t"] -> Right CtU8
        ["uint16_t"] -> Right CtU16
        ["uint32_t"] -> Right CtU32
        ["uint64_t"] -> Right CtU64
        ["size_t"] -> Right CtUsize
        ["ssize_t"] -> Right CtIsize
        ["intptr_t"] -> Right CtIsize
        ["uintptr_t"] -> Right CtUsize
        _ -> Left ("cannot conservatively map the C type '" <> T.pack (trimStr raw) <> "' (no std.ffi correspondence; a by-value struct/enum or callback parameter is unsupported)")

-- | The recognized C base/qualifier words; everything else in a by-value type
-- position is treated as a parameter name (tolerated) unless it is the sole
-- token (then it is an unknown type and fails to classify).
isTypeWord :: String -> Bool
isTypeWord w =
  w `elem`
    [ "void", "char", "short", "int", "long", "float", "double", "_Bool", "bool"
    , "int8_t", "int16_t", "int32_t", "int64_t"
    , "uint8_t", "uint16_t", "uint32_t", "uint64_t"
    , "size_t", "ssize_t", "intptr_t", "uintptr_t"
    ]

-- ── preprocessed-text normalization ────────────────────────────────────

-- | Normalize preprocessed C into a single-spaced stream with GCC attribute
-- noise removed, so declarations parse uniformly. Newlines/tabs collapse to
-- spaces; @__attribute__((...))@ and a few decorator keywords are dropped.
normalize :: String -> String
normalize = collapse . dropAttrs . map sp
  where
    sp c = if c == '\n' || c == '\t' || c == '\r' then ' ' else c
    collapse (' ' : ' ' : rest) = collapse (' ' : rest)
    collapse (c : rest) = c : collapse rest
    collapse [] = []

-- | Remove @__attribute__((...))@ (balanced) and bare decorator keywords that
-- can sit between the return type and the function name.
dropAttrs :: String -> String
dropAttrs = go
  where
    attrKw = "__attribute__" :: String
    go s = case s of
      [] -> []
      _ | attrKw `isPrefixOf` s ->
            let afterKw = drop (length attrKw) s
                afterSp = dropWhile isSpace afterKw
             in case afterSp of
                  ('(' : rest) -> go (skipBalanced 1 rest)
                  _ -> ' ' : go afterKw
      (c : cs) -> c : go cs
    skipBalanced :: Int -> String -> String
    skipBalanced 0 s = s
    skipBalanced _ [] = []
    skipBalanced d ('(' : cs) = skipBalanced (d + 1) cs
    skipBalanced d (')' : cs) = skipBalanced (d - 1) cs
    skipBalanced d (_ : cs) = skipBalanced d cs

-- ── helpers ────────────────────────────────────────────────────────────

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_'

trimStr :: String -> String
trimStr = f . f where f = reverse . dropWhile isSpace

tailsList :: [a] -> [[a]]
tailsList xs = xs : case xs of [] -> []; (_ : t) -> tailsList t

systemIncludeDirs :: [FilePath]
systemIncludeDirs = ["/usr/include", "/usr/local/include"]

-- | Run @pkg-config --cflags@ for each package (best-effort: missing
-- pkg-config / package contributes no flags here; discovery + fail-closed
-- verification of the package itself happens in "Kappa.Backend.NativeProbe").
pkgCflags :: [Text] -> IO [String]
pkgCflags pkgs = do
  mpc <- findExecutable "pkg-config"
  case mpc of
    Nothing -> pure []
    Just pc -> concat <$> mapM (one pc) pkgs
  where
    one pc p = do
      (ec, out, _) <- readProcessWithExitCode pc ["--cflags", T.unpack p] ""
      pure (if ec == ExitSuccess then words out else [])

genErr :: Text -> Diagnostic
genErr msg =
  diag SevError StageElaborate "E_BUILD_NATIVE_HEADER_GEN" (Just "kappa-hs.build.native-header-gen")
    (Span "<native-binding>" (Pos 1 1) (Pos 1 1))
    msg

typeErr :: Text -> Text -> Text -> Diagnostic
typeErr header sym msg =
  genErr ("native binding header '" <> header <> "' function '" <> sym <> "': " <> msg)
