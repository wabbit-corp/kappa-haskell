-- | Hand-rolled lexer with Python-style layout (Spec §5–§6).
--
-- Design notes:
--
--   * Keywords are soft (§5.2): emitted as 'TokIdent'; the parser decides.
--   * Layout (§5.4): 'TokIndent'\/'TokDedent' are produced only at bracket
--     depth zero. Indentation of a logical line is the column of its first
--     token, which makes comment-leading lines behave per spec (blank and
--     comment-only lines never affect layout). Tabs are an error (§5.4).
--   * Longest-match rules of §5.5.1: @let?@\/@for?@, @?.@, @?:@, named
--     holes @?name@, @~=@, @<[@, @]>@ all take priority as specified.
--   * Numeric literals follow §6.1 exactly, including the rule that @.@
--     begins a fraction only before a digit not followed by another @.@,
--     suffix adjacency, and the @e@-suffix\/exponent split.
--   * All string families of §6.3 are lexed here, including raw\/multiline
--     dedent (§6.3.3) and prefixed-string interpolation fragments
--     (§6.3.4); interpolation payloads are re-parsed by the parser.
--
-- Lexical recovery (§3.1, §2.1A "parser recognition is not acceptance"):
-- gated Unicode names, unterminated string\/quoted\/backtick literals and
-- invalid scalar literals are recorded as diagnostics while lexing
-- continues with a recovered token, so one source file can report several
-- independent lexical errors. Structural errors (bad dedent, tabs,
-- malformed escapes) remain fatal.
module Kappa.Lexer
  ( lexSource
  , lexSourceTokens
  ) where

import Data.Char
  ( chr
  , isAlpha
  , isAlphaNum
  , isAscii
  , isDigit
  , isHexDigit
  , isOctDigit
  , ord
  )
import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word8)
import Kappa.Diagnostic
import Kappa.Source
import Kappa.Token

-- | Lexer state: remaining input plus position and layout bookkeeping,
-- and diagnostics recovered so far (in reverse order).
data St = St
  { stIn :: !Text
  , stLine :: !Int
  , stCol :: !Int
  , stDiags :: ![Diagnostic]
  }

data LexError = LexError !Span !DiagnosticCode !(Maybe DiagnosticFamily) !Text ![Text]

type LexM a = Either LexError a

lexErr :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> LexM a
lexErr sp code fam msg = Left (LexError sp code fam msg [])

-- | Lex a whole file. Returns recovered diagnostics plus tokens, or a
-- single fatal diagnostic.
lexSource :: FilePath -> Text -> Either Diagnostic ([Diagnostic], [Located])
lexSource path src =
  case lexSourceTokens path src of
    Right r -> Right r
    Left (LexError sp code fam msg notes) ->
      Left (foldl' (flip withNote) (diag SevError StageLex code fam sp msg) notes)

lexSourceTokens :: FilePath -> Text -> LexM ([Diagnostic], [Located])
lexSourceTokens path src = goLineStart st0 (1 :| []) []
  where
    st0 = St src 1 1 []

    -- Record a recovered (non-fatal) lexical diagnostic.
    record :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> [Text] -> St -> St
    record sp code fam msg notes s =
      s {stDiags = foldl' (flip withNote) (diag SevError StageLex code fam sp msg) notes : stDiags s}

    -- As 'record' but attaches a §3.1.9 structured payload (used for the
    -- §3.2.1 feature-gated diagnostics, which MUST carry the gate/profile
    -- payload).
    recordP :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> [Text] -> Payload -> St -> St
    recordP sp code fam msg notes pl s =
      s {stDiags = withPayload pl (foldl' (flip withNote) (diag SevError StageLex code fam sp msg) notes) : stDiags s}

    pos :: St -> Pos
    pos s = Pos (stLine s) (stCol s)

    spanAt :: St -> St -> Span
    spanAt a b = Span path (pos a) (pos b)

    here :: St -> Span
    here s = Span path (pos s) (pos s)

    -- Advance over one character (which must be the head of input).
    adv :: Char -> St -> St
    adv c s
      | c == '\n' = s {stIn = T.drop 1 (stIn s), stLine = stLine s + 1, stCol = 1}
      | otherwise = s {stIn = T.drop 1 (stIn s), stCol = stCol s + 1}

    advN :: Int -> St -> St
    advN n s = case T.uncons (stIn s) of
      Just (c, _) | n > 0 -> advN (n - 1) (adv c s)
      _ -> s

    peek :: St -> Maybe Char
    peek = fmap fst . T.uncons . stIn

    -- O(n) lookahead (n <= 2 at every call site). Crucially this avoids
    -- 'T.length'/'T.index' on the remaining input, which are O(rest) in
    -- text-2.x and would make literal-heavy files quadratic to lex.
    peekAt :: Int -> St -> Maybe Char
    peekAt n s = fmap fst (T.uncons (T.drop n (stIn s)))

    startsWith :: Text -> St -> Bool
    startsWith t s = t `T.isPrefixOf` stIn s

    -- ── Layout at the start of a logical line (depth 0) ──────────────

    -- Skip whitespace, blank lines and comments until the first real
    -- token of the next logical line, then apply the indent rule. The
    -- indent stack is non-empty by construction (the base level 1 is
    -- never popped).
    goLineStart :: St -> NonEmpty Int -> [Located] -> LexM ([Diagnostic], [Located])
    goLineStart s indents acc = do
      s' <- skipBlank s
      case peek s' of
        Nothing -> do
          let nl = [Located (TokNewline False) (here s') | needsNewline acc]
              dedents = map (const (Located TokDedent (here s'))) (NE.tail indents)
          pure (reverse (stDiags s'), reverse (Located TokEOF (here s') : dedents ++ nl ++ acc))
        Just _ -> do
          let col = stCol s'
              top = NE.head indents
          if
            | col > top ->
                goLine s' (NE.cons col indents) (Located TokIndent (here s') : acc) [] False
            | col == top -> goLine s' indents acc [] False
            | otherwise -> do
                let (popped, rest) = NE.span (> col) indents
                case rest of
                  (r : more)
                    | r == col ->
                        goLine s' (r :| more) (map (const (Located TokDedent (here s'))) popped ++ acc) [] False
                  _ ->
                    lexErr (here s') "E_LAYOUT_BAD_DEDENT" Nothing
                      "dedent does not match any enclosing indentation level"

    needsNewline :: [Located] -> Bool
    needsNewline (Located t _ : _) = case t of
      TokNewline _ -> False
      TokIndent -> False
      TokDedent -> False
      _ -> True
    needsNewline [] = False

    -- Skip spaces, newlines and comments while at depth 0 between
    -- logical lines. Tabs are a hard error per §5.4.
    skipBlank :: St -> LexM St
    skipBlank s = case peek s of
      Just ' ' -> skipBlank (adv ' ' s)
      Just '\n' -> skipBlank (adv '\n' s)
      Just '\r' -> skipBlank (adv '\r' s)
      Just '\t' ->
        lexErr (here s) "E_TAB_IN_INDENTATION" Nothing
          "tab character in source layout; indentation is measured in spaces (Spec §5.4)"
      Just '-' | startsWith "--" s -> skipBlank (skipLineComment s)
      Just '{' | startsWith "{-" s -> skipBlock s >>= skipBlank
      _ -> pure s

    skipLineComment :: St -> St
    skipLineComment s = case peek s of
      Just '\n' -> s
      Just c -> skipLineComment (adv c s)
      Nothing -> s

    skipBlock :: St -> LexM St
    skipBlock s0 = go (advN 2 s0) (1 :: Int)
      where
        go s 0 = pure s
        go s n
          | startsWith "-}" s = go (advN 2 s) (n - 1)
          | startsWith "{-" s = go (advN 2 s) (n + 1)
          | otherwise = case peek s of
              Just c -> go (adv c s) n
              Nothing ->
                lexErr (spanAt s0 s) "E_UNTERMINATED_BLOCK_COMMENT" Nothing
                  "unterminated block comment"

    -- ── Tokens within a logical line ──────────────────────────────────
    --
    -- The bracket stack tracks open delimiters: depth > 0 disables
    -- layout and softens newlines.

    -- The final 'Bool' records whether an unclosed bracket has already
    -- swallowed a line break that was followed by further real content
    -- (a soft, in-bracket newline followed by another token). At EOF this
    -- distinguishes a bracket left dangling at the very end of the file
    -- (one structural error; the parser reports it) from a bracket that
    -- absorbed one or more following declarations (§5.2 soft newlines):
    -- only the latter needs the lexer to surface the unbalanced-bracket
    -- diagnostic so the swallowed declarations are not dropped silently
    -- (§3.1.14A in-bracket recovery).
    goLine :: St -> NonEmpty Int -> [Located] -> [Token] -> Bool -> LexM ([Diagnostic], [Located])
    goLine s indents acc brackets swallowed = case peek s of
      Nothing
        | null brackets -> goLineStart s indents acc
        | not swallowed -> goLineStart s indents acc -- dangling bracket at EOF: the parser reports it
        | otherwise ->
            -- an unclosed bracket absorbed following declarations; record
            -- the §5.2 unbalanced-bracket cause so declaration-level
            -- recovery does not silently lose them
            let unclosed = openDelimName (last brackets)
                s' =
                  record (here s) "E_EXPECTED_SYNTAX_TOKEN" (Just "kappa-hs.parse.error")
                    ("unclosed " <> unclosed <> " at end of input (Spec §5.2)")
                    ["a " <> unclosed <> " opened earlier has no matching closing delimiter"]
                    s
             in goLineStart s' indents acc
      Just ' ' -> goLine (adv ' ' s) indents acc brackets swallowed
      Just '\r' -> goLine (adv '\r' s) indents acc brackets swallowed
      Just '\t' ->
        lexErr (here s) "E_TAB_IN_SOURCE" Nothing
          "tab character in source; use spaces (Spec §5.4)"
      Just '\n'
        -- a splice bracket '$(' is layout-transparent (§21.2): its body
        -- keeps ordinary §5.4 indentation so 'do' suites and argument
        -- continuation lines work inside '$( ... )'
        | all (== TokSplice) brackets ->
            goLineStart (adv '\n' s) indents (Located (TokNewline False) (here s) : acc)
        | otherwise ->
            goLine (adv '\n' s) indents (Located (TokNewline True) (here s) : acc) brackets swallowed
      Just '-' | startsWith "--" s -> goLine (skipLineComment s) indents acc brackets swallowed
      Just '{' | startsWith "{-" s -> do
        s' <- skipBlock s
        goLine s' indents acc brackets swallowed
      Just c -> do
        (tok, s') <- scanToken s c
        let sp = spanAt s s'
            brackets' = updateBrackets tok brackets
            -- a real token landing on a fresh in-bracket line means the
            -- currently open bracket has absorbed following content; once
            -- every bracket has closed the slate is wiped, so content
            -- swallowed by a since-balanced group does not implicate a
            -- later, genuinely unclosed delimiter
            swallowed'
              | null brackets' = False
              | swallowed = True
              | not (null brackets) =
                  case acc of
                    (Located (TokNewline _) _ : _) -> True
                    _ -> False
              | otherwise = False
        goLine s' indents (Located tok sp : acc) brackets' swallowed'

    -- A human-readable name for an open-delimiter token (for the
    -- §5.2 unbalanced-bracket diagnostic).
    openDelimName :: Token -> Text
    openDelimName = \case
      TokLParen -> "'('"
      TokLBracket -> "'['"
      TokLBrace -> "'{'"
      TokVariantOpen -> "'(|'"
      TokSetOpen -> "set literal"
      TokEffOpen -> "'<['"
      TokQuoteBrace -> "quote brace"
      TokSplice -> "'$('"
      TokQuoteSplice -> "splice"
      _ -> "bracket"

    updateBrackets :: Token -> [Token] -> [Token]
    updateBrackets t bs = case t of
      TokLParen -> t : bs
      TokLBracket -> t : bs
      TokLBrace -> t : bs
      TokVariantOpen -> t : bs
      TokSetOpen -> t : bs
      TokEffOpen -> t : bs
      TokQuoteBrace -> t : bs
      TokSplice -> t : bs
      TokQuoteSplice -> t : bs
      TokRParen -> popB
      TokRBracket -> popB
      TokRBrace -> popB
      TokVariantClose -> popB
      TokSetClose -> popB
      TokEffClose -> popB
      _ -> bs
      where
        popB = drop 1 bs

    -- ── Single-token scanner ─────────────────────────────────────────

    scanToken :: St -> Char -> LexM (Token, St)
    scanToken s c
      | isDigit c = scanNumber s
      | isIdentStart c = scanIdentish s
      | not (isAscii c) && (isAlpha c || c == '_') =
          -- Recovery (§2.1A): scan the whole Unicode identifier, record
          -- the gating diagnostic, and hand the parser an ordinary
          -- identifier token. A lone @ω@ is the §12.1.1 quantity token of
          -- the base grammar, not a gated Unicode name; likewise a lone
          -- @ρ@ is the region-variable spelling used by the §20.10.2
          -- capture-annotation grammar.
          let (name, s') = takeUniIdent s
           in if name == "ω" || name == "ρ"
                then pure (TokIdent name, s')
                else
                  pure
                    ( TokIdent name
                    , recordP (spanAt s s') "E_FEATURE_INACTIVE" (Just "kappa.feature.gated")
                        "unquoted Unicode identifiers require the 'unicode-names' feature gate (Spec §2.1A)"
                        ["this implementation does not enable 'unicode-names'; use a backtick identifier instead"]
                        (featureGatedPayload "unicode-identifier" "unicode-names")
                        s'
                    )
      | c == '`' = scanBacktick s
      | c == '"' = scanStringFrom Nothing 0 s
      | c == '#' = scanHashes s
      | c == '\'' = scanQuoteOrChar Nothing s
      | c == '(' =
          if startsWith "(|" s && not (ambiguousVariantOpen s)
            then pure (TokVariantOpen, advN 2 s)
            else pure (TokLParen, adv '(' s)
      | c == ')' = pure (TokRParen, adv ')' s)
      | c == '[' = pure (TokLBracket, adv '[' s)
      | c == ']' =
          if startsWith "]>" s
            then pure (TokEffClose, advN 2 s)
            else pure (TokRBracket, adv ']' s)
      | c == '{' =
          if startsWith "{|" s && peekAt 2 s /= Just '}'
            then pure (TokSetOpen, advN 2 s)
            else pure (TokLBrace, adv '{' s)
      | c == '}' = pure (TokRBrace, adv '}' s)
      | c == ',' = pure (TokComma, adv ',' s)
      | c == '@' = pure (TokAt, adv '@' s)
      | c == '\\' = pure (TokBackslash, adv '\\' s)
      | startsWith "<[" s = pure (TokEffOpen, advN 2 s)
      | startsWith "|)" s = pure (TokVariantClose, advN 2 s)
      | startsWith "|}" s = pure (TokSetClose, advN 2 s)
      | startsWith "$(" s = pure (TokSplice, advN 2 s)
      | startsWith "${" s = pure (TokQuoteSplice, advN 2 s)
      | isOpChar c = scanOperator s
      | otherwise =
          lexErr (here s) "E_UNEXPECTED_CHARACTER" Nothing
            ("unexpected character '" <> T.singleton c <> "'")

    -- `(||)`, `(|>)` etc: `(` followed by an operator beginning with `|`
    -- is an operator reference, not a variant opener. We treat `(|` as a
    -- variant opener unless the run of operator characters starting at
    -- the `|` is longer than one (e.g. `(||`, `(|>`), in which case the
    -- `(` stands alone.
    ambiguousVariantOpen :: St -> Bool
    ambiguousVariantOpen s = case peekAt 2 s of
      Just c2 -> isOpChar c2 || c2 == ')'
      Nothing -> True

    isIdentStart ch = (isAscii ch && isAlpha ch) || ch == '_'
    isIdentCont ch = (isAscii ch && isAlphaNum ch) || ch == '_'
    isOpChar ch = ch `elem` ("!$%^&*-+=<>./:?|~" :: String)

    -- ── Identifiers, soft keywords, prefixed literals ─────────────────

    scanIdentish :: St -> LexM (Token, St)
    scanIdentish s = do
      let (name, s') = takeIdent s
      case peek s' of
        -- §5.5.1: let? / for? are single tokens.
        Just '?'
          | name == "let" || name == "for" ->
              pure (TokIdent (name <> "?"), adv '?' s')
        -- §6.3.4: prefixed string (no intervening whitespace).
        Just '"' -> scanStringFrom (Just name) 0 s'
        Just '#' | hashThenQuote s' -> scanHashesPrefixed name s'
        -- §6.5: prefixed quoted literal.
        Just '\'' -> scanQuoteOrChar (Just name) s'
        _ -> pure (TokIdent name, s')

    takeIdent :: St -> (Text, St)
    takeIdent s =
      let txt = T.takeWhile isIdentCont (stIn s)
       in (txt, advN (T.length txt) s)

    -- A Unicode identifier (recovery only; §2.1A).
    takeUniIdent :: St -> (Text, St)
    takeUniIdent s =
      let txt = T.takeWhile (\ch -> isAlphaNum ch || ch == '_') (stIn s)
       in (txt, advN (T.length txt) s)

    hashThenQuote :: St -> Bool
    hashThenQuote s =
      let rest = T.dropWhile (== '#') (stIn s)
       in not (T.null (T.takeWhile (== '#') (stIn s))) && T.isPrefixOf "\"" rest

    scanBacktick :: St -> LexM (Token, St)
    scanBacktick s0 = go (adv '`' s0) []
      where
        go s chs = case peek s of
          Just '`'
            | null chs ->
                lexErr (spanAt s0 (adv '`' s)) "E_EMPTY_BACKTICK_IDENT" Nothing
                  "empty backtick identifier"
            | otherwise -> pure (TokBacktick (T.pack (reverse chs)), adv '`' s)
          Just '\n' -> unterminated s
          Just ch -> go (adv ch s) (ch : chs)
          Nothing -> unterminated s
        -- Recovery: an error token; the parser reports the resulting
        -- syntax error at the use site (one lexical + one parse error).
        unterminated s =
          pure
            ( TokError
            , record (spanAt s0 s) "E_UNTERMINATED_BACKTICK_IDENTIFIER" Nothing
                "unterminated backtick identifier" [] s
            )

    -- ── Operators and reserved punctuation ────────────────────────────

    scanOperator :: St -> LexM (Token, St)
    scanOperator s = do
      let run = T.takeWhile isOpChar (stIn s)
          s' = advN (T.length run) s
      case run of
        "->" -> pure (TokArrow, s')
        "<-" -> pure (TokBackArrow, s')
        "=" -> pure (TokEquals, s')
        ":" -> pure (TokColon, s')
        "." -> pure (TokDot, s')
        "~" -> pure (TokTilde, s')
        "|" -> pure (TokBar, s')
        "?." -> pure (TokQDot, s')
        "?:" -> pure (TokElvis, s')
        "!" -> pure (TokBang, s')
        "?"
          -- §5.5.1: `?` immediately followed by an identifier start is a
          -- named hole.
          | Just c2 <- peek s'
          , isIdentStart c2 -> do
              let (name, s'') = takeIdent s'
              pure (TokHole name, s'')
          | otherwise -> pure (TokOperator "?", s')
        _
          | T.any (not . isAscii) run ->
              pure
                ( TokOperator run
                , recordP (spanAt s s') "E_FEATURE_INACTIVE" (Just "kappa.feature.gated")
                    "Unicode operator tokens require the 'unicode-names' feature gate (Spec §2.1A)"
                    ["this implementation does not enable 'unicode-names'"]
                    (featureGatedPayload "unicode-operator" "unicode-names")
                    s'
                )
          | otherwise -> pure (TokOperator run, s')

    -- ── Numbers (§6.1) ────────────────────────────────────────────────

    scanNumber :: St -> LexM (Token, St)
    scanNumber s0
      | startsWith "0x" s0 = radix 16 isHexDigit (advN 2 s0) "hexadecimal"
      | startsWith "0o" s0 = radix 8 isOctDigit (advN 2 s0) "octal"
      | startsWith "0b" s0 = radix 2 (`elem` ("01" :: String)) (advN 2 s0) "binary"
      | otherwise = decimal
      where
        radix base ok s name = do
          (digits, s') <- takeDigits ok s name
          -- §6.1.1: underscores are digit-group separators with no
          -- semantic effect; strip them before accumulating (the decimal
          -- path strips them too).
          let val = foldl' (\acc d -> acc * base + toInteger (digitToIntH d)) 0 (filter (/= '_') (T.unpack digits))
          (suffix, s'') <- takeSuffix s'
          pure (TokInt val suffix, s'')

        digitToIntH d
          | isDigit d = ord d - ord '0'
          | d >= 'a' && d <= 'f' = ord d - ord 'a' + 10
          | otherwise = ord d - ord 'A' + 10

        decimal = do
          (intPart, s1) <- takeDigits isDigit s0 "decimal"
          case peek s1 of
            -- §5.5.1: '.' is part of the literal only before a digit not
            -- followed by another '.'.
            Just '.'
              | Just d <- peekAt 1 s1
              , isDigit d -> do
                  (fracPart, s2) <- takeDigits isDigit (adv '.' s1) "decimal"
                  (expPart, s3) <- takeExponent s2
                  finishFloat intPart (Just fracPart) expPart s3
            Just e
              | (e == 'e' || e == 'E')
              , hasExponent s1 -> do
                  (expPart, s2) <- takeExponent s1
                  finishFloat intPart Nothing expPart s2
            _ -> do
              let val = T.foldl' (\acc d -> acc * 10 + toInteger (ord d - ord '0')) 0 (T.filter (/= '_') intPart)
              (suffix, s') <- takeSuffix s1
              pure (TokInt val suffix, s')

        -- 'e' begins an exponent only when followed by optional sign and
        -- at least one digit (§6.1.6); otherwise it begins a suffix.
        hasExponent s = case peekAt 1 s of
          Just d | isDigit d -> True
          Just sign
            | sign == '+' || sign == '-' ->
                maybe False isDigit (peekAt 2 s)
          _ -> False

        takeExponent s = case peek s of
          Just e
            | (e == 'e' || e == 'E')
            , hasExponent s -> do
                let s1 = adv e s
                    (sign, s2) = case peek s1 of
                      Just c | c == '+' || c == '-' -> (T.singleton c, adv c s1)
                      _ -> ("", s1)
                (ds, s3) <- takeDigits isDigit s2 "exponent"
                pure (Just (sign <> ds), s3)
          _ -> pure (Nothing, s)

        finishFloat intPart mfrac mexp s = do
          let clean = T.unpack . T.filter (/= '_')
              str =
                clean intPart
                  ++ "." ++ maybe "0" clean mfrac
                  ++ maybe "" (\e -> "e" ++ clean e) mexp
              val = read str :: Double
          (suffix, s') <- takeSuffix s
          pure (TokFloat val suffix, s')

        -- Consume `digit ('_'? digit)*`: an underscore is part of the
        -- literal only when followed by another digit (§6.1.1), so e.g.
        -- @0xFF_u8@ lexes as digits @FF@ with suffix @_u8@.
        takeDigits ok s name = do
          let raw = scanDs (stIn s)
              scanDs t = case T.uncons t of
                Just (d, rest) | ok d -> T.cons d (scanCont rest)
                _ -> ""
              scanCont t = case T.uncons t of
                Just (d, rest) | ok d -> T.cons d (scanCont rest)
                Just ('_', rest)
                  | Just (d, _) <- T.uncons rest
                  , ok d ->
                      T.cons '_' (scanDs rest)
                _ -> ""
          if T.null raw
            then
              lexErr (here s) "E_NUMERIC_LITERAL_MALFORMED" Nothing
                ("expected " <> name <> " digits")
            else pure (raw, advN (T.length raw) s)

        takeSuffix s = case peek s of
          Just ch
            | isIdentStart ch -> do
                let (name, s') = takeIdent s
                pure (Just name, s')
            | not (isAscii ch) && isAlpha ch ->
                let (name, s') = takeUniIdent s
                 in pure
                      ( Just name
                      , recordP (spanAt s s') "E_FEATURE_INACTIVE" (Just "kappa.feature.gated")
                          "Unicode numeric-literal suffixes require the 'unicode-names' feature gate (Spec §6.1.6)"
                          [] (featureGatedPayload "unicode-numeric-suffix" "unicode-names") s'
                      )
          _ -> pure (Nothing, s)

    -- ── Strings (§6.3) ────────────────────────────────────────────────

    -- A bare '#' run: must introduce a raw string.
    scanHashes :: St -> LexM (Token, St)
    scanHashes s = do
      let hashes = T.length (T.takeWhile (== '#') (stIn s))
          s' = advN hashes s
      case peek s' of
        Just '"' -> scanStringFrom Nothing hashes s'
        _ ->
          lexErr (here s) "E_UNEXPECTED_CHARACTER" Nothing
            "'#' must introduce a raw string literal (Spec §6.3.2)"

    scanHashesPrefixed :: Text -> St -> LexM (Token, St)
    scanHashesPrefixed name s = do
      let hashes = T.length (T.takeWhile (== '#') (stIn s))
      scanStringFrom (Just name) hashes (advN hashes s)

    -- Scan a string starting at the opening '"' (hash count and prefix
    -- already consumed).
    scanStringFrom :: Maybe Text -> Int -> St -> LexM (Token, St)
    scanStringFrom mprefix hashes s0 = do
      let multi = startsWith "\"\"\"" s0
          openLen = if multi then 3 else 1
          s1 = advN openLen s0
          closer = T.replicate openLen "\"" <> T.replicate hashes "#"
      (body, s2) <- takeUntilCloser closer multi s1
      content <-
        if multi
          then dedentMultiline (spanAt s0 s2) body
          else pure body
      frags <- buildFragments (spanAt s0 s2) mprefix hashes s1 content
      pure (TokString (StringLit mprefix hashes multi frags), s2)
      where
        -- §6.3.4.2: inside an interpolation of a prefixed string,
        -- nested string literals (and brackets) are handled as in
        -- ordinary source, so a '"' inside `${...}` / `#{...}` must
        -- not close the literal.
        interpOpener
          | Nothing <- mprefix = Nothing
          | hashes == 0 = Just "${"
          | otherwise = Just (T.replicate hashes "#" <> "{")
        takeUntilCloser closer multi s = go s []
          where
            go cur chs
              | closer `T.isPrefixOf` stIn cur =
                  pure (T.pack (reverse chs), advN (T.length closer) cur)
              | Just op <- interpOpener
              , op `T.isPrefixOf` stIn cur =
                  goInterp (advN (T.length op) cur) (0 :: Int) (reverse (T.unpack op) ++ chs)
              | otherwise = case peek cur of
                  Nothing ->
                    -- Recovery: take the body so far as the literal.
                    pure
                      ( T.pack (reverse chs)
                      , record (spanAt s0 cur) "E_UNTERMINATED_STRING_LITERAL" Nothing
                          "unterminated string literal" [] cur
                      )
                  Just '\n'
                    | not multi ->
                        pure
                          ( T.pack (reverse chs)
                          , record (spanAt s0 cur) "E_UNTERMINATED_STRING_LITERAL" Nothing
                              "unterminated single-line string literal" [] cur
                          )
                  Just '\\'
                    -- In an ordinary (non-raw) string a backslash escapes
                    -- the next char, so an escaped '"' never closes.
                    | hashes == 0
                    , Just nxt <- peekAt 1 cur ->
                        go (adv nxt (adv '\\' cur)) (nxt : '\\' : chs)
                  Just ch -> go (adv ch cur) (ch : chs)
            -- scan an interpolation payload to its matching '}'
            goInterp cur depth chs = case peek cur of
              Nothing -> go cur chs
              Just '}'
                | depth == 0 -> go (adv '}' cur) ('}' : chs)
                | otherwise -> goInterp (adv '}' cur) (depth - 1) ('}' : chs)
              Just ch
                | ch `elem` ("([{" :: String) -> goInterp (adv ch cur) (depth + 1) (ch : chs)
                | ch `elem` (")]" :: String) -> goInterp (adv ch cur) (depth - 1) (ch : chs)
                | ch == '"' -> goNested (adv ch cur) depth (ch : chs)
                | not multi && ch == '\n' -> go cur chs
                | otherwise -> goInterp (adv ch cur) depth (ch : chs)
            -- a nested ordinary string literal inside an interpolation
            goNested cur depth chs = case peek cur of
              Nothing -> go cur chs
              Just '"' -> goInterp (adv '"' cur) depth ('"' : chs)
              Just '\\'
                | Just nxt <- peekAt 1 cur ->
                    goNested (adv nxt (adv '\\' cur)) depth (nxt : '\\' : chs)
              Just ch
                | not multi && ch == '\n' -> go cur chs
                | otherwise -> goNested (adv ch cur) depth (ch : chs)

    -- §6.3.3 fixed dedent.
    dedentMultiline :: Span -> Text -> LexM Text
    dedentMultiline sp body0 = do
      let body = case T.uncons body0 of
            Just ('\n', rest) -> rest
            _ -> body0
          ls = T.splitOn "\n" body
          -- the spaces-only line holding the closing delimiter defines
          -- I; it stays a content line and dedents to "" so the literal
          -- keeps its trailing newline (§6.3.3)
          indent = case reverse ls of
            (lastL : restRev)
              | T.all (== ' ') lastL && not (null restRev) -> lastL
            _ -> ""
          contentLines = ls
          strip ln
            | T.null ln = Right ln
            | T.all (== ' ') ln = Right (T.drop (T.length indent) ln)
            | indent `T.isPrefixOf` ln = Right (T.drop (T.length indent) ln)
            | otherwise = Left ln
      case traverse strip contentLines of
        Left _ ->
          lexErr sp "E_MULTILINE_STRING_BAD_INDENT" Nothing
            "multiline string line does not begin with the closing delimiter's indentation (Spec §6.3.3)"
        Right stripped -> pure (T.intercalate "\n" stripped)

    -- Build fragments: interpolation applies only to prefixed strings.
    -- Literal segments of ordinary (hash 0) strings are escape-decoded.
    buildFragments :: Span -> Maybe Text -> Int -> St -> Text -> LexM [StrFragment]
    buildFragments sp mprefix hashes bodyStart content = do
      raws <-
        case mprefix of
          Nothing -> pure [Left content]
          Just _ -> splitInterp sp hashes bodyStart content
      frags <- traverse decodeFrag raws
      pure (normalizeFrags frags)
      where
        decodeFrag (Left lit)
          | hashes == 0 = FragLit <$> decodeEscapes sp lit
          | otherwise = pure (FragLit lit)
        decodeFrag (Right frag) = pure frag

    normalizeFrags :: [StrFragment] -> [StrFragment]
    normalizeFrags fs = case go fs of
      [] -> [FragLit ""]
      out -> out
      where
        go (FragLit a : FragLit b : rest) = go (FragLit (a <> b) : rest)
        go (FragLit a : rest)
          | T.null a = go rest
          | otherwise = FragLit a : go rest
        go (f : rest) = f : go rest
        go [] = []

    -- Split prefixed-string content into literal and interpolation
    -- pieces (§6.3.4.1–§6.3.4.2). Positions of interpolation payloads are
    -- approximated to the string body start; exact within-line accuracy
    -- is kept for single-line literals.
    splitInterp :: Span -> Int -> St -> Text -> LexM [Either Text StrFragment]
    splitInterp sp hashes bodyStart = go bodyStart []
      where
        opener
          | hashes == 0 = "${"
          | otherwise = T.replicate hashes "#" <> "{"

        go st litAcc content =
          case T.uncons content of
            Nothing -> pure [Left (T.pack (reverse litAcc))]
            Just (c, rest)
              -- \$ escapes a literal dollar in ordinary prefixed strings
              -- (§6.3.4.1). It is a prefixed-string interpolation escape,
              -- not a general string escape, so it is consumed here and the
              -- bare '$' is emitted into the literal text; the surviving
              -- backslash must NOT reach decodeEscapes (which would reject
              -- "\$" as E_STRING_ESCAPE_INVALID).
              | hashes == 0 && c == '\\' && T.isPrefixOf "$" rest ->
                  go (advN 2 st) ('$' : litAcc) (T.drop 1 rest)
              -- $name sugar (ordinary prefixed only)
              | hashes == 0
              , c == '$'
              , Just (c2, _) <- T.uncons rest
              , isIdentStart c2 -> do
                  let name = T.takeWhile isIdentCont rest
                      rest' = T.drop (T.length name) rest
                      st' = advN (1 + T.length name) st
                  more <- go st' [] rest'
                  pure (Left (T.pack (reverse litAcc)) : Right (FragInterp name (spanAt (adv '$' st) st')) : more)
              | opener `T.isPrefixOf` content -> do
                  let exprStart = advN (T.length opener) st
                  (payload, restContent, st') <- scanBraced exprStart (T.drop (T.length opener) content)
                  frag <- mkInterp payload (spanAt exprStart st')
                  more <- go (adv '}' st') [] restContent
                  pure (Left (T.pack (reverse litAcc)) : Right frag : more)
              | otherwise -> go (adv c st) (c : litAcc) rest

        -- Scan the string CONTENT to the matching '}' at nesting level
        -- 0 starting after the opener; returns payload text, the content
        -- remaining after the '}', and the state at the '}' (for spans).
        scanBraced st0' txt0 = goB st0' txt0 (0 :: Int) []
          where
            goB cur txt depth chs = case T.uncons txt of
              Nothing ->
                lexErr sp "E_UNTERMINATED_INTERPOLATION" Nothing
                  "unterminated interpolation in prefixed string (Spec §6.3.4)"
              Just ('}', restT)
                | depth == 0 -> pure (T.pack (reverse chs), restT, cur)
                | otherwise -> goB (adv '}' cur) restT (depth - 1) ('}' : chs)
              Just (ch, restT)
                | ch `elem` ("([{" :: String) -> goB (adv ch cur) restT (depth + 1) (ch : chs)
                | ch `elem` (")]" :: String) -> goB (adv ch cur) restT (depth - 1) (ch : chs)
                | ch == '"' -> do
                    (lit, restT', cur') <- skipStringLit (adv ch cur) restT
                    goB cur' restT' depth (reverse ('"' : lit ++ "\"") ++ chs)
                | otherwise -> goB (adv ch cur) restT depth (ch : chs)

            skipStringLit cur txt = goS cur txt []
              where
                goS c2 t2 chs2 = case T.uncons t2 of
                  Just ('"', r2) -> pure (reverse chs2, r2, adv '"' c2)
                  Just ('\\', r2)
                    | Just (nxt, r3) <- T.uncons r2 ->
                        goS (adv nxt (adv '\\' c2)) r3 (nxt : '\\' : chs2)
                  Just (ch2, r2) -> goS (adv ch2 c2) r2 (ch2 : chs2)
                  Nothing ->
                    lexErr sp "E_UNTERMINATED_INTERPOLATION" Nothing
                      "unterminated string inside interpolation"

        -- Split a top-level ':' format specifier (§6.3.4.2).
        mkInterp payload pspan = do
          case topLevelColon payload of
            Nothing -> pure (FragInterp (T.strip payload) pspan)
            Just (expr, fmt) ->
              pure (FragInterpFmt (T.strip expr) pspan (trimFmt fmt))

        trimFmt f =
          let f1 = case T.uncons f of
                Just (' ', r) -> r
                _ -> f
           in case T.unsnoc f1 of
                Just (r, ' ') -> r
                _ -> f1

        topLevelColon t = goC 0 0 (T.unpack t)
          where
            goC :: Int -> Int -> String -> Maybe (Text, Text)
            goC _ _ [] = Nothing
            goC i depth (ch : rest)
              | ch `elem` ("([{" :: String) = goC (i + 1) (depth + 1) rest
              | ch `elem` (")]}" :: String) = goC (i + 1) (depth - 1) rest
              | ch == '"' = skipStr (i + 1) depth rest
              | ch == ':' && depth == 0 = Just (T.take i t, T.drop (i + 1) t)
              | otherwise = goC (i + 1) depth rest
            skipStr i depth ('\\' : _ : rest) = skipStr (i + 2) depth rest
            skipStr i depth ('"' : rest) = goC (i + 1) depth rest
            skipStr i depth (_ : rest) = skipStr (i + 1) depth rest
            skipStr _ _ [] = Nothing

    -- ── Quoted literals and syntax quotes (§6.4–§6.5, §21.1) ─────────

    scanQuoteOrChar :: Maybe Text -> St -> LexM (Token, St)
    scanQuoteOrChar mprefix s0
      -- Syntax quote '{ ... }: only when unprefixed and not a char
      -- literal '{'.
      | Nothing <- mprefix
      , Just '{' <- peekAt 1 s0
      , peekAt 2 s0 /= Just '\'' =
          pure (TokQuoteBrace, advN 2 s0)
      | otherwise = do
          let s1 = adv '\'' s0
          (body, s2, terminated) <- takeBody s1 []
          let sp = spanAt s0 s2
              -- §6.5: the text view is present only when the payload
              -- decodes to valid Unicode scalar text; a bad escape means
              -- "no text view", reported per literal family below.
              mtext = case decodeEscapes sp body of
                Right txt -> Just txt
                Left _ -> Nothing
          let mbytes = decodeByteView body
              -- Recovery placeholder: a well-formed single-scalar view so
              -- later stages do not cascade after a reported lex error.
              placeholder st =
                pure (TokQuoted (QuotedLit mprefix body (Just "?") mbytes), st)
          case mprefix of
            Nothing
              | not terminated ->
                  -- The literal's scalar content is indeterminate.
                  placeholder
                    ( record sp "E_UNICODE_INVALID_SCALAR_LITERAL" Nothing
                        "invalid Unicode scalar literal" [] s2
                    )
              | otherwise ->
                  case fmap T.unpack mtext of
                    Just [_] -> pure (TokQuoted (QuotedLit Nothing body mtext mbytes), s2)
                    _ ->
                      placeholder
                        ( record sp "E_UNICODE_INVALID_SCALAR_LITERAL" Nothing
                            "a Unicode scalar literal must contain exactly one Unicode scalar value (Spec §6.4)"
                            ["for one user-perceived character with several scalars, use a prefixed literal such as g'...'"]
                            s2
                        )
            Just _ -> pure (TokQuoted (QuotedLit mprefix body mtext mbytes), s2)
      where
        takeBody cur chs = case peek cur of
          Just '\'' -> pure (T.pack (reverse chs), adv '\'' cur, True)
          Just '\n' -> unterminated cur chs
          Just '\\'
            | Just nxt <- peekAt 1 cur ->
                takeBody (adv nxt (adv '\\' cur)) (nxt : '\\' : chs)
          Just ch -> takeBody (adv ch cur) (ch : chs)
          Nothing -> unterminated cur chs
        unterminated cur chs =
          pure
            ( T.pack (reverse chs)
            , record (spanAt s0 cur) "E_UNTERMINATED_CHARACTER_LITERAL" Nothing
                "unterminated quoted literal" [] cur
            , False
            )

        -- §6.5: byte view exists when every unit has a one-byte reading
        -- (a Unicode escape contributes a byte only when its scalar's
        -- UTF-8 encoding is exactly one byte, i.e. <= U+007F).
        decodeByteView :: Text -> Maybe [Word8]
        decodeByteView = goBytes . T.unpack
          where
            goBytes [] = Just []
            goBytes ('\\' : 'x' : h1 : h2 : rest)
              | isHexDigit h1 && isHexDigit h2 =
                  (fromIntegral (hexVal h1 * 16 + hexVal h2) :) <$> goBytes rest
            goBytes ('\\' : 'u' : '{' : rest)
              | (hs, '}' : rest') <- span isHexDigit rest
              , not (null hs)
              , length hs <= 6
              , v <- foldl' (\a d -> a * 16 + hexVal d) 0 hs
              , v <= 0x7F =
                  (fromIntegral v :) <$> goBytes rest'
            goBytes ('\\' : 'u' : h1 : h2 : h3 : h4 : rest)
              | all isHexDigit [h1, h2, h3, h4]
              , v <- foldl' (\a d -> a * 16 + hexVal d) 0 [h1, h2, h3, h4]
              , v <= 0x7F =
                  (fromIntegral v :) <$> goBytes rest
            goBytes ('\\' : e : rest) = do
              b <- simpleEscByte e
              (b :) <$> goBytes rest
            goBytes (ch : rest)
              | isAscii ch = (fromIntegral (ord ch) :) <$> goBytes rest
              | otherwise = Nothing
            simpleEscByte = \case
              'n' -> Just 10
              'r' -> Just 13
              't' -> Just 9
              'b' -> Just 8
              'f' -> Just 12
              '0' -> Just 0
              '\\' -> Just 92
              '\'' -> Just 39
              '"' -> Just 34
              _ -> Nothing

    hexVal :: Char -> Int
    hexVal d
      | isDigit d = ord d - ord '0'
      | d >= 'a' && d <= 'f' = ord d - ord 'a' + 10
      | otherwise = ord d - ord 'A' + 10

    -- ── Escape decoding (§6.3.1) ──────────────────────────────────────

    decodeEscapes :: Span -> Text -> LexM Text
    decodeEscapes sp = fmap T.pack . goD . T.unpack
      where
        goD [] = pure []
        goD ('\\' : rest) = case rest of
          '\\' : r -> ('\\' :) <$> goD r
          '"' : r -> ('"' :) <$> goD r
          '\'' : r -> ('\'' :) <$> goD r
          'n' : r -> ('\n' :) <$> goD r
          'r' : r -> ('\r' :) <$> goD r
          't' : r -> ('\t' :) <$> goD r
          'b' : r -> ('\b' :) <$> goD r
          'f' : r -> ('\f' :) <$> goD r
          '0' : r -> ('\0' :) <$> goD r
          'x' : h1 : h2 : r
            | isHexDigit h1 && isHexDigit h2 ->
                (chr (hexVal h1 * 16 + hexVal h2) :) <$> goD r
          'u' : '{' : r ->
            let (hs, r') = span isHexDigit r
             in case r' of
                  '}' : r''
                    | not (null hs) && length hs <= 6 -> do
                        c <- scalar (foldl' (\a d -> a * 16 + hexVal d) 0 hs)
                        (c :) <$> goD r''
                  _ -> badEscape
          'u' : h1 : h2 : h3 : h4 : r
            | all isHexDigit [h1, h2, h3, h4] -> do
                c <- scalar (foldl' (\a d -> a * 16 + hexVal d) 0 [h1, h2, h3, h4])
                (c :) <$> goD r
          _ -> badEscape
        goD (ch : rest) = (ch :) <$> goD rest

        scalar n
          | n > 0x10FFFF =
              lexErr sp "E_STRING_ESCAPE_INVALID" Nothing
                "escape denotes a code point beyond U+10FFFF (Spec §6.3.1)"
          | n >= 0xD800 && n <= 0xDFFF =
              lexErr sp "E_STRING_ESCAPE_INVALID" Nothing
                "escape denotes a surrogate code point (Spec §6.3.1)"
          | otherwise = pure (chr n)

        badEscape =
          lexErr sp "E_STRING_ESCAPE_INVALID" Nothing
            "unknown or malformed escape sequence (Spec §6.3.1)"
