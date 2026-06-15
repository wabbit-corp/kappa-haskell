-- | Recursive-descent parser for the Kappa surface grammar (Spec Part II–IV).
--
-- Types and terms share one expression grammar (the language is
-- dependently typed); the elaborator interprets expressions found in type
-- position. Operator expressions are parsed as flat chains and
-- re-associated by the resolver once block-scoped fixities (§5.5.2) are
-- known. Postfix @?@ (Option sugar, §13.1.9) is recognized only when
-- adjacent to its operand, which realizes the tighter-than-application
-- binding of the type grammar while leaving spaced @?@ available as a
-- user postfix operator.
--
-- Recovery: a malformed top-level declaration is skipped to the next
-- plausible declaration start and recorded as a diagnostic (§3.1.14A).
module Kappa.Parser
  ( parseModule
  , parseExprText
  ) where

import Control.Applicative (Alternative (..), optional)
import Control.Monad (guard, unless, void, when)
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Diagnostic
import Kappa.Lexer (lexSource)
import Kappa.Parser.Monad
import Kappa.Source
import Kappa.Syntax
import Kappa.Token

-- ── Entry points ─────────────────────────────────────────────────────

parseModule :: FilePath -> Text -> Either Diagnostics (Module, Diagnostics)
parseModule path src = do
  (lexDiags, toks) <- either (Left . pure) Right (lexSource path src)
  case runP pModule toks of
    Left e -> Left (lexDiags ++ [errToDiag e])
    Right (m, recovered) -> Right (m, lexDiags ++ recovered)

-- | Parse a standalone expression (used for interpolation payloads and
-- the Appendix T @assertType@ directive).
parseExprText :: FilePath -> Text -> Either Diagnostic Expr
parseExprText path src = do
  (lexDiags, toks) <- lexSource path src
  case lexDiags of
    (d : _) -> Left d
    [] -> pure ()
  case runP (pTopExpr <* pSkipLayout <* eof) toks of
    Left e -> Left (errToDiag e)
    Right (e, _) -> Right e
  where
    pTopExpr = pSkipLayout *> pExpr

errToDiag :: PErr -> Diagnostic
errToDiag (PErr sp msg expected) =
  let d = diag SevError StageParse "E_EXPECTED_SYNTAX_TOKEN" (Just "kappa-hs.parse.error") sp msg
   in case expected of
        [] -> d
        es -> withNote ("expected one of: " <> T.intercalate ", " (dedup es)) d
  where
    dedup = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- Skip stray layout tokens (used at entry boundaries).
pSkipLayout :: P ()
pSkipLayout = void (many (pNewline <|> token TokIndent <|> token TokDedent))

-- ── Small token-level helpers ────────────────────────────────────────

pNewline :: P ()
pNewline = satisfy "newline" $ \case
  TokNewline _ -> Just ()
  _ -> Nothing

pHardNewline :: P ()
pHardNewline = satisfy "end of statement" $ \case
  TokNewline False -> Just ()
  _ -> Nothing

pIdent :: P Name
pIdent = do
  sp <- currentSpan
  t <- satisfy "identifier" $ \case
    TokIdent t -> Just t
    TokBacktick t -> Just t
    _ -> Nothing
  pure (Name t sp)

-- | A specific soft keyword (§5.2). Backtick spellings do not count as
-- keywords.
pKeyword :: Text -> P ()
pKeyword kw = satisfy ("'" <> kw <> "'") $ \case
  TokIdent t | t == kw -> Just ()
  _ -> Nothing

pOperatorTok :: P Name
pOperatorTok = do
  sp <- currentSpan
  t <- satisfy "operator" $ \case
    TokOperator t -> Just t
    _ -> Nothing
  pure (Name t sp)

pOperatorNamed :: Text -> P ()
pOperatorNamed t = satisfy ("'" <> t <> "'") $ \case
  TokOperator t' | t' == t -> Just ()
  _ -> Nothing

pInt :: P (Integer, Maybe Text, Span)
pInt = do
  sp <- currentSpan
  (v, suf) <- satisfy "integer" $ \case
    TokInt v s -> Just (v, s)
    _ -> Nothing
  pure (v, suf, sp)

peekIdent :: P (Maybe Text)
peekIdent =
  peekToken >>= \case
    TokIdent t -> pure (Just t)
    _ -> pure Nothing

spanFrom :: Span -> P Span
spanFrom start = do
  end <- lastSpan
  pure start {spanEnd = spanEnd end}

-- Keywords that always terminate an application-argument sequence when
-- they appear unparenthesized: each introduces the next part of an
-- enclosing construct (branch, clause, or statement), so it can never be
-- a bare argument. Query-clause keywords are deliberately NOT in this
-- set — §5.2 requires them to parse as ordinary identifiers outside the
-- contexts where the keyword reading is grammatically possible; see
-- 'queryStopKeywords' and 'isStopKeywordAt'.
stopKeywords :: [Text]
stopKeywords =
  [ "then", "else", "elif", "in", "with", "case", "except", "finally"
  , "do", "is", "captures", "decreases", "using", "as", "on"
  , "where", "if", "match", "while", "for", "for?", "let", "let?", "var"
  , "return", "break", "continue", "defer", "import", "export", "instance"
  , "derive"
  ]

-- Comprehension/query clause keywords (§20.3): they terminate an
-- argument sequence only while a comprehension body is being parsed
-- ("by" is additionally activated inside a `decreases` measure clause).
-- Everywhere else they are ordinary identifiers (§5.2).
queryStopKeywords :: [Text]
queryStopKeywords =
  ["yield", "into", "group", "by", "order", "skip", "take", "distinct", "join"]

-- Is the identifier @kw@, located @n@ tokens ahead of the cursor, acting
-- as a stop keyword here? `deep` stops only when it begins a
-- `deep handle` expression (one-token lookahead); query keywords stop
-- only inside their clause contexts ('withExtraStops').
isStopKeywordAt :: Int -> Text -> P Bool
isStopKeywordAt n kw
  | kw `elem` stopKeywords = pure True
  | kw == "deep" = (== TokIdent "handle") <$> peekTokenAt (n + 1)
  | otherwise = (kw `elem`) <$> extraStops

-- Does a stop keyword begin at the current token?
pAtStopKeyword :: P Bool
pAtStopKeyword =
  peekToken >>= \case
    TokIdent kw -> isStopKeywordAt 0 kw
    _ -> pure False

-- ── Module structure ─────────────────────────────────────────────────

pModule :: P Module
pModule = do
  pSkipLayout
  (attrs, header) <- pModuleHeader <|> pure ([], Nothing)
  decls <- pTopDecls
  eof
  pure (Module attrs header decls)

pModuleHeader :: P ([Name], Maybe ModPath)
pModuleHeader = try $ do
  -- module attributes may sit on their own lines (§8.1)
  attrs <- many (token TokAt *> pIdent <* pSkipLayout)
  pKeyword "module"
  path <- pModPath
  pHardNewline <|> eof
  -- Layout after the header is handled by 'pTopDecls' (so a misindented
  -- first declaration is reported, §5.4).
  pure (attrs, Just path)

pModPath :: P ModPath
pModPath = ModPath <$> sepBy1 pIdent (token TokDot)

pTopDecls :: P [Decl]
pTopDecls = do
  pSkipLayoutTop
  done <- lookAheadIs eof
  if done
    then pure []
    else do
      mdecl <- (Just <$> pDecl) <|> (recoverDecl >> pure Nothing)
      pSkipLayoutTop
      rest <- pTopDecls
      pure (maybe rest (: rest) mdecl)

-- Between top-level declarations an INDENT is a layout error (§5.4: a
-- top-level declaration begins at the module indentation level); report
-- it once and continue parsing the indented declaration.
pSkipLayoutTop :: P ()
pSkipLayoutTop = void (many (pNewline <|> token TokDedent <|> flaggedIndent))
  where
    flaggedIndent = do
      sp <- currentSpan
      token TokIndent
      recordRecovered $
        diag SevError StageParse "E_UNEXPECTED_INDENTATION" (Just "kappa-hs.parse.error") sp
          "unexpected indentation: a top-level declaration must start at the module indentation level (Spec §5.4)"

-- Declaration-level recovery (§3.1.14A): report and skip to the next
-- hard newline at depth zero, together with any indented continuation
-- block that belongs to the failed declaration.
recoverDecl :: P ()
recoverDecl = do
  sp <- currentSpan
  t <- peekToken
  toks <- pendingTokens
  recordRecovered $
    if misindentSignal toks
      then
        -- §5.4 layout: the declaration failed because a clause body is
        -- indented less than its clause header (the body line dedents
        -- and a sibling `case` re-indents)
        diag SevError StageParse "E_UNEXPECTED_INDENTATION" (Just "kappa-hs.parse.error") sp
          "a clause body is indented less than its clause header (Spec §5.4 layout)"
      else
        diag SevError StageParse "E_EXPECTED_SYNTAX_TOKEN" (Just "kappa-hs.parse.error") sp
          ("unexpected " <> tokenDescr t <> " at start of declaration")
  skipPast (\case TokNewline False -> True; TokEOF -> True; _ -> False)
  void (optional pHardNewline)
  skipIndentedBlocks
  where
    -- The body of the failed declaration: any whole indented blocks
    -- that follow it are part of it, not new declarations.
    skipIndentedBlocks = do
      t <- peekToken
      case t of
        TokIndent -> do
          _ <- anyToken
          skipToDedent (0 :: Int)
          void (optional pHardNewline)
          skipIndentedBlocks
        _ -> pure ()
    skipToDedent depth = do
      t <- peekToken
      case t of
        TokEOF -> pure ()
        TokIndent -> anyToken >> skipToDedent (depth + 1)
        TokDedent
          | depth == 0 -> void anyToken
          | otherwise -> anyToken >> skipToDedent (depth - 1)
        _ -> anyToken >> skipToDedent depth

-- A misindented clause body inside the failed declaration: a body
-- line dedents below its clause header while a sibling `case` clause
-- re-indents afterwards (the §5.4 signature of a case body written
-- left of its `case`).
misindentSignal :: [Located] -> Bool
misindentSignal = go (0 :: Int)
  where
    go _ [] = False
    go d (Located t _ : rest) = case t of
      TokIndent -> go (d + 1) rest
      TokDedent
        | d <= 1 -> False
        | indentCase rest -> True
        | otherwise -> go (d - 1) rest
      TokEOF -> False
      _ -> go d rest
    indentCase (Located TokIndent _ : Located (TokIdent "case") _ : _) = True
    indentCase (Located t _ : rest) = case t of
      TokIndent -> False
      TokDedent -> False
      TokEOF -> False
      _ -> indentCase rest
    indentCase [] = False

-- ── Declarations ─────────────────────────────────────────────────────

pDecl :: P Decl
pDecl = do
  start <- currentSpan
  mods <- pMods
  let withSpan f = f <$> spanFrom start
  kw <- peekIdent
  case kw of
    Just "data" -> do
      d <- pDataDecl
      withSpan (DData mods d)
    Just "type" -> do
      -- `type` may also begin a kind-qualified expression, but at
      -- declaration position it is always the alias form.
      pTypeAlias mods start
    Just "trait" -> do
      d <- pTraitDecl
      withSpan (DTrait mods d)
    Just "instance" -> do
      requireUnmodified mods "instance"
      d <- pInstanceDecl
      withSpan (DInstance d)
    Just "derive" -> do
      requireUnmodified mods "derive"
      pKeyword "derive"
      e <- pAppExpr
      pEndDecl
      withSpan (DDerive e)
    Just "effect" -> do
      d <- pEffectDecl
      withSpan (DEffect mods d)
    Just "import" -> do
      requireUnmodified mods "import"
      pKeyword "import"
      specs <- sepBy1 pImportSpec (token TokComma)
      pEndDecl
      withSpan (DImport specs)
    Just "export" -> do
      requireUnmodified mods "export"
      pKeyword "export"
      specs <- sepBy1 pImportSpec (token TokComma)
      pEndDecl
      withSpan (DExport specs)
    Just "expect" -> do
      pKeyword "expect"
      form <- pExpectForm
      pEndDecl
      withSpan (DExpect mods form)
    Just "let" -> do
      pKeyword "let"
      d <- pLetDef
      pEndDecl
      withSpan (DLet mods d)
    Just "pattern" -> do
      pKeyword "pattern"
      d <- pLetDef
      pEndDecl
      withSpan (DPattern mods d)
    Just "projection" -> do
      pKeyword "projection"
      d <- pProjection mods start
      pure d
    Just k
      | k `elem` ["infix", "prefix", "postfix"] -> do
          requireUnmodified mods "fixity declaration"
          d <- pFixityDecl
          pEndDecl
          withSpan (DFixity d)
    _ ->
      case kw of
        _ | dmScoped mods -> parseFail "expected data, type, trait, or effect after 'scoped'"
        _ -> do
          -- signature declaration: name : Type  /  (op) : Type
          (n, ty) <- try $ do
            n <- pSigName
            token TokColon
            ty <- pExprIndented
            pure (n, ty)
          pEndDecl
          withSpan (DSig mods n ty)

requireUnmodified :: DeclMods -> Text -> P ()
requireUnmodified mods what =
  unless (mods == noMods) $
    parseFail (what <> " does not accept visibility or opacity modifiers")

pSigName :: P Name
pSigName =
  pIdent <|> do
    token TokLParen
    op <- pOperatorTok <|> coreOpName
    token TokRParen
    pure op

-- Reserved spellings usable as operator names in signatures, e.g. (=).
coreOpName :: P Name
coreOpName = do
  sp <- currentSpan
  t <- satisfy "operator" $ \case
    TokEquals -> Just "="
    TokColon -> Just ":"
    TokDot -> Just "."
    TokBar -> Just "|"
    _ -> Nothing
  pure (Name t sp)

-- A declaration ends at a hard newline, EOF, or an enclosing dedent.
-- After an indented suite the newline was already consumed inside the
-- suite, so this succeeds silently otherwise; stray tokens are then
-- reported by the next declaration parse.
pEndDecl :: P ()
pEndDecl = pHardNewline <|> pure ()

pMods :: P DeclMods
pMods = go noMods
  where
    go acc =
      peekIdent >>= \case
        Just "public" | dmVisibility acc == VisDefault -> pKeyword "public" >> go acc {dmVisibility = VisPublic}
        Just "private" | dmVisibility acc == VisDefault -> pKeyword "private" >> go acc {dmVisibility = VisPrivate}
        Just "opaque" | not (dmOpaque acc) -> pKeyword "opaque" >> go acc {dmOpaque = True}
        Just "scoped" | not (dmScoped acc) -> do
          -- `scoped` only before data/type/trait/effect
          nxt <- peekTokenAt 1
          case nxt of
            TokIdent k | k `elem` ["data", "type", "trait", "effect"] -> pKeyword "scoped" >> go acc {dmScoped = True}
            _ -> pure acc
        _ -> pure acc

-- let definitions: named function, simple value, or pattern binding.
pLetDef :: P LetDef
pLetDef = do
  -- Try named definition first: name binder* [: T] [decreases ...] = body
  implicitBinding <|> named <|> patBinding
  where
    -- `let (@q x : T) = e` implicit local candidate (§9.3)
    implicitBinding = try $ do
      token TokLParen
      token TokAt
      prefix <- pBinderPrefix
      n <- pIdent
      token TokColon
      ty <- noEq pExpr
      token TokRParen
      token TokEquals
      body <- pDefBody
      pure (LetDef Nothing True (Just (PVar n)) prefix [] (Just ty) Nothing body)
    named = try $ do
      n <- pSigName
      binders <- pParamBinders
      -- "decreases" is a global stop keyword, so the result type ends
      -- before any decreases clause
      resTy <- optionMaybe (token TokColon *> noEq pExpr)
      dec <- optionMaybe pDecreases
      token TokEquals
      body <- pDefBody
      pure (LetDef (Just n) False Nothing emptyPrefix binders resTy dec (desugarRecordParams binders body))
    patBinding = do
      -- `let 1 x = e` / `let &b = e` prefixed bindings (§12.2, §12.3.1)
      prefix <- pBinderPrefix
      pat <- pPattern
      ty <- optionMaybe (token TokColon *> noEq pExpr)
      token TokEquals
      body <- pDefBody
      pure (LetDef Nothing False (Just pat) prefix [] ty Nothing body)

-- | Bind the fields of a §13.2 record-typed parameter
-- ('(x : Int, y : Int)', parsed as a hidden '__rp*' binder) by
-- prefixing the body with a destructuring let.
desugarRecordParams :: [Binder] -> Expr -> Expr
desugarRecordParams bs body = foldr wrap body bs
  where
    wrap b acc
      | Just n <- bName b
      , "__rp" `T.isPrefixOf` nameText n
      , Just (ERecordType fs _ _) <- bType b =
          ELet
            [ LetBind False emptyPrefix
                (PRecord [(False, rtfName f, Nothing) | f <- fs] Nothing (bSpan b))
                Nothing (EVar n) (bSpan b)
            ]
            acc
            (bSpan b)
      | otherwise = acc

pDecreases :: P Decreases
pDecreases = do
  pKeyword "decreases"
  structural <|> measure
  where
    structural = do
      pKeyword "structural"
      ns <- tupleOf <|> ((: []) <$> pIdent)
      pure (DecStructural ns)
    tupleOf = do
      token TokLParen
      ns <- sepBy1 pIdent (token TokComma)
      token TokRParen
      pure ns
    measure = do
      -- `by` separates the measure from its ordering relation here, so
      -- it is an active stop keyword within the measure expression only.
      -- The measure must stop at `=` (the definition body follows), so
      -- propositional-equality chains are disabled (§9.1 vs §11.4.1).
      m <- withExtraStops ["by"] (noEq pExpr)
      by <- optionMaybe (pKeyword "by" *> noEq pExpr)
      us <- optionMaybe (pKeyword "using" *> pExpr)
      pure (DecMeasure m by us)

-- A definition body: inline expression or indented suite (§9.3.1 sugar).
pDefBody :: P Expr
pDefBody = pSuiteOrExpr

-- data declarations (§10.1)
pDataDecl :: P DataDecl
pDataDecl = do
  pKeyword "data"
  n <- pSigName
  params <- pParamBinders
  kind <- optionMaybe (token TokColon *> noEq pExpr)
  ctors <-
    optionMaybe (token TokEquals) >>= \case
      Nothing -> pure []
      Just () -> pCtorBlock
  pure (DataDecl n params kind ctors)

pCtorBlock :: P [CtorDecl]
pCtorBlock = indentedCtors <|> inlineCtors
  where
    indentedCtors = do
      pNewline
      token TokIndent
      -- optional '|' before the first and each subsequent alternative
      -- (§10.1 writes both "C1 ‖ C2" stacked and "C1 ‖ | C2" styles)
      void (optional (token TokBar))
      goodCtors <|> salvageCtors
    goodCtors = do
      cs <- ctorSeq
      token TokDedent
      pure cs
    -- §3.1.14A: a malformed constructor alternative is reported and the
    -- block skipped, salvaging the data declaration's header (the type
    -- stays usable; its constructors are gone)
    salvageCtors = do
      sp <- currentSpan
      t <- peekToken
      recordRecovered $
        diag SevError StageParse "E_EXPECTED_SYNTAX_TOKEN" (Just "kappa-hs.parse.error") sp
          ("unexpected " <> tokenDescr t <> " in a constructor alternative")
      skipCtorBlock (0 :: Int)
      pure []
    skipCtorBlock depth = do
      t <- peekToken
      case t of
        TokEOF -> pure ()
        TokIndent -> anyToken >> skipCtorBlock (depth + 1)
        TokDedent
          | depth == 0 -> void anyToken
          | otherwise -> anyToken >> skipCtorBlock (depth - 1)
        _ -> anyToken >> skipCtorBlock depth
    ctorSeq = do
      x <- pCtorDecl
      void (many pNewline)
      done <- lookAheadIs (token TokDedent)
      if done
        then pure [x]
        else do
          void (optional (token TokBar))
          (x :) <$> ctorSeq
    -- single-line: C1 a | C2 b  (used by spec prelude examples)
    inlineCtors = sepBy1 pCtorDecl (token TokBar)

sepEndByNewlines :: P a -> () -> P [a]
sepEndByNewlines p () = do
  x <- p
  void (many pNewline)
  done <- suiteEnds
  if done
    then pure [x]
    else (x :) <$> sepEndByNewlines p ()

-- | Does the suite end here? Either a dedent, or — inside a
-- layout-transparent '$( ... )' splice (§21.2) — the closing bracket
-- arrives before the dedent.
suiteEnds :: P Bool
suiteEnds = do
  t <- peekToken
  pure $ case t of
    TokDedent -> True
    TokRParen -> True
    TokRBracket -> True
    TokRBrace -> True
    TokVariantClose -> True
    TokSetClose -> True
    TokEOF -> True
    _ -> False

-- | Close an indented suite: consume the dedent when present; a suite
-- cut short by a splice's closing bracket leaves no dedent here.
suiteDedent :: P ()
suiteDedent = token TokDedent <|> pure ()

pCtorDecl :: P CtorDecl
pCtorDecl = do
  start <- currentSpan
  n <- pSigName
  -- GADT-style: C : Pi-type
  gadt <- optionMaybe (token TokColon *> pExpr)
  case gadt of
    Just ty -> CtorDecl n [] (Just ty) <$> spanFrom start
    Nothing -> do
      -- Parse exactly one constructor; the '|' separator between inline
      -- alternatives (§10.1 "data Tree a = Leaf | Branch ...", L8697) is
      -- consumed by the block-level splitter (inlineCtors / ctorSeq), not
      -- here, so a non-first constructor is registered correctly.
      binders <- concat <$> many pCtorBinder
      CtorDecl n binders Nothing <$> spanFrom start

-- Constructor binders (§10.1): bare field, parenthesized param/type,
-- record-style {...} block.
pCtorBinder :: P [Binder]
pCtorBinder =
  recordStyle <|> parenParam <|> ((: []) <$> bareField)
  where
    recordStyle = do
      sp <- currentSpan
      token TokLBrace
      fs <- sepBy1 (pFieldDecl sp) (token TokComma)
      void (optional (token TokComma))
      token TokRBrace
      pure fs
    pFieldDecl sp = do
      prefix <- pBinderPrefix
      susp <- pSuspension
      n <- pIdent
      token TokColon
      ty <- noEq pExprArg
      -- a field default is a full expression (operators allowed, §10.1.1)
      def <- optionMaybe (token TokEquals *> noEq pExpr)
      pure (Binder False prefix susp NoReceiver False (Just n) False (Just ty) def sp)
    parenParam = try $ do
      sp <- currentSpan
      token TokLParen
      b <- pBinderBody sp True
      token TokRParen
      pure b
    bareField = do
      sp <- currentSpan
      e <- pAtomNoSection
      pure (Binder False emptyPrefix Nothing NoReceiver False Nothing False (Just e) Nothing sp)

-- type alias (§10.3)
pTypeAlias :: DeclMods -> Span -> P Decl
pTypeAlias mods start = do
  pKeyword "type"
  n <- pSigName
  params <- pParamBinders
  kind <- optionMaybe (token TokColon *> noEq pExpr)
  rhs <- optionMaybe (token TokEquals *> pSuiteOrExpr)
  pEndDecl
  DTypeAlias mods n params kind rhs <$> spanFrom start

-- trait declarations (§14.1)
pTraitDecl :: P TraitDecl
pTraitDecl = do
  pKeyword "trait"
  (supers, n, params) <- pTraitHead
  members <-
    optionMaybe (token TokEquals) >>= \case
      Nothing -> pure []
      Just () -> pTraitMembers
  pure (TraitDecl supers n params members)

-- Heads: [C1, ..., Cn =>] Name params
pTraitHead :: P ([Expr], Name, [Binder])
pTraitHead = withSupers <|> plain
  where
    withSupers = try $ do
      supers <- sepBy1 pAppExpr (token TokComma)
      pOperatorNamed "=>"
      (n, ps) <- nameParams
      pure (supers, n, ps)
    plain = do
      (n, ps) <- nameParams
      pure ([], n, ps)
    nameParams = do
      n <- pSigName
      ps <- pParamBinders
      pure (n, ps)

pTraitMembers :: P [TraitMember]
pTraitMembers = do
  pNewline
  token TokIndent
  ms <- pTraitMember `sepEndByNewlines` ()
  token TokDedent
  pure ms

pTraitMember :: P TraitMember
pTraitMember = do
  start <- currentSpan
  defMember start <|> sigMember start
  where
    defMember start = do
      pKeyword "let"
      d <- pLetDef
      TraitDefault d <$> spanFrom start
    sigMember start = do
      n <- pSigName
      token TokColon
      ty <- pExprIndented
      TraitSig n ty <$> spanFrom start

-- instance declarations (§14.3)
pInstanceDecl :: P InstanceDecl
pInstanceDecl = do
  pKeyword "instance"
  (premises, hd) <- pInstanceHead
  members <-
    optionMaybe (token TokEquals) >>= \case
      Nothing -> pure []
      -- an empty member suite is permitted: `instance Shareable Cell =`
      Just () -> pInstanceMembers <|> pure []
  pure (InstanceDecl premises hd members)

pInstanceHead :: P ([Expr], Expr)
pInstanceHead = withPremises <|> plain
  where
    withPremises = try $ do
      ps <- premiseGroup
      pOperatorNamed "=>"
      hd <- pAppExpr
      pure (ps, hd)
    premiseGroup =
      try (token TokLParen *> sepBy1 pAppExpr (token TokComma) <* token TokRParen)
        <|> ((: []) <$> pAppExpr)
    plain = do
      hd <- pAppExpr
      pure ([], hd)

pInstanceMembers :: P [Decl]
pInstanceMembers = do
  pNewline
  token TokIndent
  ms <- pInstanceMember `sepEndByNewlines` ()
  token TokDedent
  pure ms

pInstanceMember :: P Decl
pInstanceMember = do
  start <- currentSpan
  letMember start <|> sigMember start
  where
    letMember start = do
      pKeyword "let"
      d <- pLetDef
      DLet noMods d <$> spanFrom start
    sigMember start = do
      n <- pSigName
      token TokColon
      ty <- pExprIndented
      DSig noMods n ty <$> spanFrom start

-- effect declarations (§18.1.15)
pEffectDecl :: P EffectDecl
pEffectDecl = do
  pKeyword "effect"
  labelForm <|> interfaceForm
  where
    labelForm = try $ do
      pKeyword "label"
      n <- pIdent
      token TokColon
      ty <- pExpr
      pure (EffectDecl n [] [] True (Just ty))
    interfaceForm = do
      n <- pIdent
      params <- pParamBinders
      ops <-
        optionMaybe (token TokEquals) >>= \case
          Nothing -> pure []
          Just () -> do
            pNewline
            token TokIndent
            os <- pEffectOp `sepEndByNewlines` ()
            token TokDedent
            pure os
      pure (EffectDecl n params ops False Nothing)

pEffectOp :: P EffectOp
pEffectOp = do
  start <- currentSpan
  q <- optionMaybe pQuantity
  n <- pIdent
  token TokColon
  ty <- pExprIndented
  EffectOp q n ty <$> spanFrom start

-- fixity declarations (§5.5.2)
pFixityDecl :: P FixityDecl
pFixityDecl = do
  kindTok <- pIdent
  kind <- case nameText kindTok of
    "infix" ->
      peekIdent >>= \case
        Just "left" -> pKeyword "left" >> pure InfixL
        Just "right" -> pKeyword "right" >> pure InfixR
        _ -> pure InfixN
    "prefix" -> pure Prefix
    "postfix" -> pure Postfix
    _ -> parseFail "expected fixity keyword"
  (prec, _, _) <- pInt
  token TokLParen
  op <- pOperatorTok <|> coreOpName
  token TokRParen
  pure (FixityDecl kind (fromInteger prec) op)

-- import/export specs (§8.3–§8.4)
pImportSpec :: P ImportSpec
pImportSpec = do
  ref <- pModuleRef
  choiceOf ref
  where
    choiceOf ref =
      itemsForm ref <|> wildcardForm ref <|> aliasForm ref <|> singletonForm ref <|> pure (ImportModule ref Nothing)
    itemsForm ref = try $ do
      token TokDot
      token TokLParen
      items <- sepBy1 pImportItem (token TokComma)
      void (optional (token TokComma))
      token TokRParen
      pure (ImportItems ref items)
    wildcardForm ref = try $ do
      -- `.*` lexes as one operator token (maximal munch); accept both.
      pOperatorNamed ".*" <|> (token TokDot *> pOperatorNamed "*")
      exc <-
        optionMaybe (pKeyword "except") >>= \case
          Nothing -> pure []
          Just () -> do
            token TokLParen
            xs <- sepBy1 pExceptItem (token TokComma)
            token TokRParen
            pure xs
      pure (ImportAll ref exc)
    aliasForm ref = try $ do
      pKeyword "as"
      a <- pIdent
      pure (ImportModule ref (Just a))
    singletonForm ref = try $ do
      token TokDot
      n <- pNameRef
      pure (ImportSingleton ref n)

pModuleRef :: P ModuleRef
pModuleRef = urlRef <|> (RefPath <$> pathPrefix)
  where
    urlRef = do
      sp <- currentSpan
      sl <- satisfy "module URL string" $ \case
        TokString s | slPrefix s == Nothing -> Just s
        _ -> Nothing
      case slFragments sl of
        [FragLit t] -> pure (RefUrl t sp)
        _ -> parseFail "module URL must be a plain string literal"
    -- A module path stops before a final `.()`/`.*`/`.name` selector;
    -- we parse greedily and let pImportSpec backtrack via try.
    pathPrefix = do
      n <- pIdent
      rest <- many (try (token TokDot *> pIdent))
      pure (ModPath (n : rest))

pNameRef :: P Name
pNameRef =
  pIdent <|> do
    token TokLParen
    op <- pOperatorTok <|> coreOpName
    token TokRParen
    pure op

pImportItem :: P ImportItem
pImportItem = do
  flags <- many pFlag
  ksel <- optionMaybe pKindSelector
  n <- pNameRef
  ctorAll <- isJust <$> optionMaybe (try (token TokLParen *> pOperatorNamed ".." *> token TokRParen))
  alias <- optionMaybe (pKeyword "as" *> pIdent)
  pure (ImportItem ("unhide" `elem` flags) ("clarify" `elem` flags) ksel n ctorAll alias)
  where
    pFlag =
      -- a flag only counts when another item token follows it
      try $ do
        n <- pIdent
        guard (nameText n `elem` ["unhide", "clarify"])
        nxt <- peekToken
        case nxt of
          TokComma -> parseFail "flag requires an item"
          TokRParen -> parseFail "flag requires an item"
          _ -> pure (nameText n)

pKindSelector :: P KindSelector
pKindSelector = try $ do
  t <- pIdent
  nxt <- peekToken
  -- a kind selector must be followed by a name, not by `,` or `)`
  case nxt of
    TokComma -> parseFail "kind selector requires a name"
    TokRParen -> parseFail "kind selector requires a name"
    _ -> pure ()
  case nameText t of
    "term" -> pure SelTerm
    "type" -> pure SelType
    "trait" -> pure SelTrait
    "ctor" -> pure SelCtor
    "effectLabel" -> pure SelEffectLabel
    "module" -> pure SelModule
    _ -> parseFail "not a kind selector"

pExceptItem :: P ExceptItem
pExceptItem = do
  ksel <- optionMaybe pKindSelector
  n <- pNameRef
  pure (ExceptItem ksel n)

pExpectForm :: P ExpectForm
pExpectForm =
  termForm <|> dataForm <|> typeForm <|> traitForm
  where
    termForm = do
      pKeyword "term"
      n <- pSigName
      token TokColon
      ty <- pExprIndented
      pure (ExpectTerm n ty)
    dataForm = do
      pKeyword "data"
      n <- pSigName
      params <- pParamBinders
      -- §9.4 dataHeader requires ': type', but the headerless form is
      -- accepted with the kind derived from the parameters
      ty <- optionMaybe (token TokColon *> pExpr)
      pure (ExpectData n params ty)
    typeForm = do
      pKeyword "type"
      n <- pSigName
      params <- pParamBinders
      ty <- optionMaybe (token TokColon *> pExpr)
      pure (ExpectType n params ty)
    traitForm = do
      pKeyword "trait"
      n <- pSigName
      params <- pParamBinders
      ty <- optionMaybe (token TokColon *> pExpr)
      pure (ExpectTrait n params ty)

-- projection declarations (§9.1.1)
pProjection :: DeclMods -> Span -> P Decl
pProjection mods start = do
  n <- pIdent
  binders <- pParamBinders
  token TokColon
  resTy <- noEq pExpr
  token TokEquals
  body <- accessorBody <|> (ProjSelector <$> pSuiteOrExpr)
  pEndDecl
  DProjection mods n binders resTy body <$> spanFrom start
  where
    accessorBody = try $ do
      pNewline
      token TokIndent
      clauses <- pAccessorClause `sepEndByNewlines` ()
      token TokDedent
      pure (ProjAccessors clauses)
    pAccessorClause = do
      kw <- pIdent
      k <- case nameText kw of
        "get" -> pure "get"
        "inout" -> pure "inout"
        "sink" -> pure "sink"
        "set" -> pure "set"
        _ -> parseFail "expected get/set/inout/sink accessor clause"
      arg <-
        if k == "set"
          then do
            sp <- currentSpan
            token TokLParen
            n2 <- pIdent
            token TokColon
            ty <- pExpr
            token TokRParen
            pure (Just (Binder False emptyPrefix Nothing NoReceiver False (Just n2) False (Just ty) Nothing sp))
          else pure Nothing
      token TokArrow
      body <- pSuiteOrExpr
      pure (k, arg, body)

-- ── Binders ──────────────────────────────────────────────────────────

pQuantity :: P Quantity
pQuantity =
  zeroOne <|> omega <|> bounded
  where
    zeroOne = do
      (v, _, _) <- try $ do
        r@(v, suf, _) <- pInt
        guard (suf == Nothing && (v == 0 || v == 1))
        pure r
      pure (if v == 0 then QZero else QOne)
    omega = do
      void $ try $ do
        n <- pIdent
        guard (nameText n == "ω")
        pure n
      pure QOmega
    bounded = try $ do
      op <- pOperatorTok
      case nameText op of
        "<=" -> intOne >> pure QAtMostOne
        ">=" -> intOne >> pure QAtLeastOne
        _ -> parseFail "expected quantity"
    intOne = do
      (v, suf, _) <- pInt
      guard (v == 1 && suf == Nothing)

pBorrowMark :: P BorrowMark
pBorrowMark = do
  pOperatorNamed "&"
  region <- optionMaybe (token TokLBracket *> pIdent <* token TokRBracket)
  pure (BorrowMark region)

pBinderPrefix :: P BinderPrefix
pBinderPrefix = do
  q <- optionMaybe (try quantityBeforeName)
  b <- optionMaybe pBorrowMark
  pure (BinderPrefix q b)
  where
    -- A quantity must be followed by something binder-like, otherwise
    -- `(1, 2)` would mis-parse.
    quantityBeforeName = do
      q <- pQuantity
      nxt <- peekToken
      case nxt of
        TokIdent _ -> pure q
        TokBacktick _ -> pure q
        TokOperator "&" -> pure q
        _ -> parseFail "not a quantity prefix"

pSuspension :: P (Maybe Suspension)
pSuspension =
  peekIdent >>= \case
    Just "thunk" -> do
      nxt <- peekTokenAt 1
      case nxt of
        TokIdent _ -> pKeyword "thunk" >> pure (Just SuspThunk)
        _ -> pure Nothing
    Just "lazy" -> do
      nxt <- peekTokenAt 1
      case nxt of
        TokIdent _ -> pKeyword "lazy" >> pure (Just SuspLazy)
        _ -> pure Nothing
    _ -> pure Nothing

-- A parameter binder group for named functions / data / trait headers.
-- A parenthesized group may bind several names (`(x y : A)`).
pParamBinder :: P [Binder]
pParamBinder = unitBinder <|> bareImplicit <|> recordParam <|> parenBinder <|> bare
  where
    -- `let f (x : Int, y : Int) : T = ...` — a record-typed parameter
    -- destructured into its fields (§13.2); desugared by 'pLetDef'
    recordParam = try $ do
      sp <- currentSpan
      token TokLParen
      f1 <- recField
      fs <- many1 (token TokComma *> recField)
      token TokRParen
      let nm =
            "__rp" <> T.pack (show (posLine (spanStart sp)))
              <> "_" <> T.pack (show (posCol (spanStart sp)))
          field (n, t) = RecTypeField False False emptyPrefix Nothing n t
          recTy = ERecordType (map field (f1 : fs)) Nothing sp
      pure [Binder False emptyPrefix Nothing NoReceiver False (Just (Name nm sp)) False (Just recTy) Nothing sp]
    recField = do
      n <- pIdent
      token TokColon
      t <- noEq pExpr
      pure (n, t)
    -- `let f () : T = ...` — the unit binder (§12.1)
    unitBinder = try $ do
      sp <- currentSpan
      token TokLParen
      token TokRParen
      pure [Binder False emptyPrefix Nothing NoReceiver False Nothing True Nothing Nothing sp]
    -- `let f @ev x = ...` — bare implicit binder without annotation (§12.1)
    bareImplicit = try $ do
      sp <- currentSpan
      token TokAt
      n <- pIdent
      let mn = if nameText n == "_" then Nothing else Just n
      pure [Binder True emptyPrefix Nothing NoReceiver False mn False Nothing Nothing sp]
    parenBinder = try $ do
      sp <- currentSpan
      token TokLParen
      bs <- pBinderBody sp False
      token TokRParen
      pure bs
    bare = do
      sp <- currentSpan
      n <- try $ do
        stop <- pAtStopKeyword
        guard (not stop)
        pIdent
      if nameText n == "_"
        then pure [Binder False emptyPrefix Nothing NoReceiver False Nothing False Nothing Nothing sp]
        else pure [(simpleBinder n) {bSpan = sp}]

pParamBinders :: P [Binder]
pParamBinders = concat <$> many pParamBinder

-- The body of a parenthesized binder. Handles implicit `@`, quantities,
-- borrow markers, suspension sugar, receiver markers, inout, and (for
-- constructors when @allowDefault@) default values. Several names may
-- share one prefix and annotation, e.g. @(x y z : m)@.
pBinderBody :: Span -> Bool -> P [Binder]
pBinderBody sp allowDefault = implicitB <|> inoutB <|> explicitB
  where
    implicitB = do
      token TokAt
      prefix <- pBinderPrefix
      susp <- pSuspension
      (recv, names) <- pBinderNames
      token TokColon
      ty <- tyP
      def <- pDefault
      pure [Binder True prefix susp recv False n False (Just ty) def sp | n <- names]
    inoutB = do
      void $ try $ do
        n <- pIdent
        guard (nameText n == "inout")
        pure n
      nm <- pIdent
      token TokColon
      ty <- pExpr
      pure [Binder False emptyPrefix Nothing NoReceiver True (Just nm) False (Just ty) Nothing sp]
    explicitB = do
      prefix <- pBinderPrefix
      susp <- pSuspension
      (recv, names) <- pBinderNames
      mty <- optionMaybe (token TokColon *> tyP)
      when (length names > 1 && not (isJust mty)) $
        parseFail "multiple binder names require a shared type annotation"
      def <- pDefault
      pure [Binder False prefix susp recv False n False mty def sp | n <- names]
    -- '=' may join the binder type's operator chain (propositional
    -- equality, §11.4.1) except where a default clause is admissible
    -- (constructor parameters, §10.1).
    tyP = if allowDefault then noEq pExpr else pExpr
    pDefault
      | allowDefault = optionMaybe (token TokEquals *> pExpr)
      | otherwise = pure Nothing

-- Binder names: receiver forms or one-or-more plain names\/wildcards.
pBinderNames :: P (Receiver, [Maybe Name])
pBinderNames = thisForm <|> nameForm
  where
    thisForm = try $ do
      n <- pIdent
      guard (nameText n == "this")
      mlocal <- optionMaybe pIdent
      pure (maybe ReceiverSelf ReceiverNamed mlocal, [Just (fromMaybe n mlocal)])
    nameForm = do
      ns <- many1 singleName
      pure (NoReceiver, ns)
    singleName = do
      n <- pIdent
      pure $ if nameText n == "_" then Nothing else Just n

-- Lambda binders (§16.2).
pLambdaBinder :: P [Binder]
pLambdaBinder = unitB <|> parenB <|> bare
  where
    unitB = try $ do
      sp <- currentSpan
      token TokLParen
      token TokRParen
      pure [Binder False emptyPrefix Nothing NoReceiver False Nothing True Nothing Nothing sp]
    parenB = try $ do
      sp <- currentSpan
      token TokLParen
      bs <- pBinderBody sp False
      token TokRParen
      pure bs
    bare = do
      sp <- currentSpan
      n <- pIdent
      if nameText n == "_"
        then pure [Binder False emptyPrefix Nothing NoReceiver False Nothing False Nothing Nothing sp]
        else pure [simpleBinder n]

-- ── Patterns (§17.2) ─────────────────────────────────────────────────

pPattern :: P Pattern
pPattern = do
  start <- currentSpan
  p <- pPatternNoOr
  alts <- many (token TokBar *> pPatternNoOr)
  case alts of
    [] -> pure p
    _ -> POr (p : alts) <$> spanFrom start

pPatternNoOr :: P Pattern
pPatternNoOr = do
  start <- currentSpan
  p <- pPatApp
  chain <- many ((,) <$> pPatInfixOp <*> pPatApp)
  case chain of
    [] -> pure p
    _ -> POpChain p chain <$> spanFrom start
  where
    pPatInfixOp = do
      op <- pOperatorTok
      pure op

-- Constructor application patterns and active patterns.
pPatApp :: P Pattern
pPatApp = do
  start <- currentSpan
  hd <- pPatAtom
  case hd of
    PCtor ref [] _ -> do
      namedArgs <- optionMaybe (pNamedPatArgs)
      case namedArgs of
        Just fields -> PCtorNamed ref fields <$> spanFrom start
        Nothing -> do
          args <- many pPatArgAtom
          case args of
            [] -> pure hd
            _ -> PCtor ref args <$> spanFrom start
    -- a lowercase head applied to argument atoms is an active-pattern
    -- application (§17.3.2); the checker validates the head
    PVar n -> do
      args <- many pPatArgAtom
      case args of
        [] -> pure hd
        _ -> PCtor (CtorRef Nothing n) args <$> spanFrom start
    _ -> pure hd

-- A constructor-argument pattern atom must not begin with a stop
-- keyword: `case True if g -> …` ends the pattern before the guard.
pPatArgAtom :: P Pattern
pPatArgAtom = do
  stop <- pAtStopKeyword
  if stop then parseFail "pattern argument" else pPatAtom

pNamedPatArgs :: P [(Name, Maybe Pattern)]
pNamedPatArgs = do
  token TokLBrace
  fs <- sepBy1 field (token TokComma)
  void (optional (token TokComma))
  token TokRBrace
  pure fs
  where
    field = do
      n <- pIdent
      mp <- optionMaybe (token TokEquals *> pPattern)
      pure (n, mp)

pPatAtom :: P Pattern
pPatAtom = do
  start <- currentSpan
  t <- peekToken
  case t of
    TokIdent "_" -> anyToken >> (PWild <$> spanFrom start)
    TokIdent _ -> identPattern start
    TokBacktick _ -> identPattern start
    TokInt v suf -> anyToken >> (PLit (LInt v suf) <$> spanFrom start)
    TokFloat v suf -> anyToken >> (PLit (LFloat v suf) <$> spanFrom start)
    TokString sl -> do
      void anyToken
      case slFragments sl of
        [FragLit txt] | slPrefix sl == Nothing -> PLit (LString txt) <$> spanFrom start
        [] | slPrefix sl == Nothing -> PLit (LString "") <$> spanFrom start
        _ -> parseFail "only plain string literals may appear in patterns"
    TokQuoted ql | qlPrefix ql == Nothing -> do
      void anyToken
      case T.unpack <$> qlText ql of
        Just [c] -> PLit (LScalar c) <$> spanFrom start
        _ -> parseFail "invalid scalar literal pattern"
    TokVariantOpen -> pVariantPattern start
    TokLParen -> pParenPattern start
    _ -> parseFail ("expected pattern, found " <> tokenDescr t)
  where
    identPattern _start = do
      n <- pIdent
      let isCtorName = startsUpper (nameText n)
      -- as-pattern: name@pat
      asPat <- optionMaybe (try (token TokAt *> pPatAtom))
      case asPat of
        Just p -> pure (PAs n p)
        Nothing -> do
          -- qualified constructor T.C
          qual <- optionMaybe (try (token TokDot *> pIdent))
          case qual of
            Just c -> pure (PCtor (CtorRef (Just n) c) [] (nameSpan n))
            Nothing
              | isCtorName -> pure (PCtor (CtorRef Nothing n) [] (nameSpan n))
              | otherwise -> pure (PVar n)

    startsUpper txt = case T.uncons txt of
      Just (c, _) -> c >= 'A' && c <= 'Z'
      Nothing -> False

pVariantPattern :: Span -> P Pattern
pVariantPattern start = do
  token TokVariantOpen
  p <- restForm <|> wildForm <|> bindForm
  token TokVariantClose
  pure p
  where
    restForm = do
      pOperatorNamed ".."
      n <- pIdent
      PVariant Nothing Nothing False (Just n) <$> spanFrom start
    wildForm = try $ do
      n <- pIdent
      guard (nameText n == "_")
      token TokColon
      ty <- pExpr
      PVariant Nothing (Just ty) True Nothing <$> spanFrom start
    bindForm = do
      n <- pIdent
      mty <- optionMaybe (token TokColon *> pExpr)
      PVariant (Just n) mty False Nothing <$> spanFrom start

pParenPattern :: Span -> P Pattern
pParenPattern start = do
  token TokLParen
  t <- peekToken
  case t of
    TokRParen -> do
      void anyToken
      PUnit <$> spanFrom start
    _ -> opCtorPat <|> recordPat <|> tupleOrTypedOrGroup
  where
    -- @((::) x xs)@: a parenthesized operator names a constructor in
    -- pattern position, exactly as in expressions (§17.1).
    opCtorPat = try $ do
      op <- pOperatorTok
      token TokRParen
      pure (PCtor (CtorRef Nothing op) [] (nameSpan op))
    recordPat = try $ do
      (fields, mrest) <- pRecordPatFields
      token TokRParen
      sp <- spanFrom start
      pure (PRecord fields mrest sp)
    tupleOrTypedOrGroup = do
      p <- pPattern
      t <- peekToken
      case t of
        TokColon -> do
          void anyToken
          ty <- pExpr
          token TokRParen
          PTyped p ty <$> spanFrom start
        TokComma -> do
          void anyToken
          rest <- sepBy pPattern (token TokComma)
          void (optional (token TokComma))
          token TokRParen
          PTuple (p : rest) <$> spanFrom start
        TokRParen -> do
          void anyToken
          pure p
        _ -> parseFail "expected ')', ',' or ':' in pattern"

-- Record patterns: (x = p, ..rest) / (..) / (@p = e, ...)
pRecordPatFields :: P (([(Bool, Name, Maybe Pattern)], Maybe PatRest))
pRecordPatFields = restOnly <|> withFields
  where
    restOnly = do
      r <- pRest
      void (optional (token TokComma))
      pure ([], Just r)
    withFields = do
      f1 <- pField
      rest <- many (try (token TokComma *> pField))
      r <- optionMaybe (try (token TokComma *> pRest))
      void (optional (token TokComma))
      pure (f1 : rest, r)
    pField = try $ do
      imp <- isJust <$> optionMaybe (token TokAt)
      n <- pIdent
      token TokEquals
      p <- pPattern
      pure (imp, n, Just p)
    pRest = do
      pOperatorNamed ".."
      mn <- optionMaybe pIdent
      pure (maybe PatRestDiscard PatRestBind mn)

-- ── Expressions ──────────────────────────────────────────────────────

-- Top-level expression: open forms first, then operator chains with
-- arrow/trait-arrow connectives.
pExpr :: P Expr
pExpr = pOpenExpr <|> pArrowExpr

-- Open expressions extend to the end of the construct.
pOpenExpr :: P Expr
pOpenExpr = do
  t <- peekToken
  case t of
    TokBackslash -> pLambda Nothing
    TokIdent kw -> case kw of
      "let" -> pLetIn
      "if" -> pIfExpr
      "match" -> pMatchExpr Nothing
      "do" -> pDoExpr Nothing
      "block" -> pBlockExpr
      "try" -> pTryExpr
      "handle" -> pHandleExpr False
      "deep" -> pHandleExpr True
      "forall" -> pForall
      "exists" -> pExists
      "thunk" -> pSuspExpr EThunk "thunk"
      "lazy" -> pSuspExpr ELazy "lazy"
      "force" -> pSuspExpr EForce "force"
      "seal" -> pSealExpr
      "open" -> pOpenExistsExpr
      "impossible" -> do
        sp <- currentSpan
        pKeyword "impossible"
        pure (EImpossible sp)
      _ -> labeledForm
    _ -> parseFail "expected expression"
  where
    -- label@\..., label@do, label@match...
    labeledForm = try $ do
      l <- pIdent
      token TokAt
      t <- peekToken
      case t of
        TokBackslash -> pLambda (Just l)
        TokIdent "do" -> pDoExpr (Just l)
        TokIdent "match" -> pMatchExpr (Just l)
        _ -> parseFail "expected lambda, do, or match after label@"

pSuspExpr :: (Expr -> Span -> Expr) -> Text -> P Expr
pSuspExpr mk kw = do
  start <- currentSpan
  pKeyword kw
  e <- pExprArg
  mk e <$> spanFrom start

-- Operator chain layer: operands and operators flat, then arrows.
pArrowExpr :: P Expr
pArrowExpr = do
  lhs <- pChainExpr
  t <- peekToken
  case t of
    TokArrow -> do
      void anyToken
      rhs <- pArrowRhs
      pure (mkArrow lhs rhs)
    TokOperator "=>" -> do
      void anyToken
      rhs <- pArrowRhs
      pure (ETraitArrow lhs rhs)
    _ -> pure lhs
  where
    -- an arrow at end of line continues on the next line (same or
    -- deeper indentation) within signatures and type expressions (§5.4)
    pArrowRhs = do
      pArrowCont
      pOpenExpr <|> pArrowExpr
    mkArrow lhs rhs =
      let b = case lhs of
            EAscription inner ty sp ->
              -- (x : A) -> B parsed as ascription: rebuild as binder
              case asBinderName inner of
                Just (recv, mn) ->
                  Binder False emptyPrefix Nothing recv False mn False (Just ty) Nothing sp
                Nothing -> anonBinder lhs
            _ -> anonBinder lhs
       in EArrow b rhs
    anonBinder l =
      Binder False emptyPrefix Nothing NoReceiver False Nothing False (Just l) Nothing (exprSpan l)
    asBinderName = \case
      EVar n
        | nameText n == "_" -> Just (NoReceiver, Nothing)
        | otherwise -> Just (NoReceiver, Just n)
      _ -> Nothing

-- | An arrow at end of line continues on the next line (same or deeper
-- indentation) within signatures and type expressions (§5.4).
pArrowCont :: P ()
pArrowCont = do
  t <- peekToken
  case t of
    TokNewline _ -> do
      nxt <- peekTokenAt 1
      case nxt of
        TokIndent -> anyToken >> anyToken >> pure ()
        TokDedent -> pure ()
        TokEOF -> pure ()
        TokNewline _ -> pure ()
        _ -> void anyToken
    _ -> pure ()

-- Operator chains: prefix ops and operands alternating with infix ops.
pChainExpr :: P Expr
pChainExpr = do
  els <- pChainElems
  case els of
    [ChainOperand e] -> do
      -- `is` test (§16.3.4) binds at comparison level over the operand
      pIsSuffix e
    _ -> do
      e <- pure (EOpChain els)
      pIsSuffix e

pIsSuffix :: Expr -> P Expr
pIsSuffix e = do
  isIt <- lookAheadIs (pKeyword "is")
  if not isIt
    then pure e
    else do
      pKeyword "is"
      c <- pCtorRef
      let ei = EIs e c
      -- the chain may continue after the test: `p is C && …` (§16.3.4);
      -- the right-hand side re-enters the chain parser, so further
      -- is-tests nest correctly
      t <- peekToken
      case t of
        TokOperator op | op /= "=>" -> do
          opN <- pOperatorTok
          rhs <- pChainExpr
          pure (EOpChain [ChainOperand ei, ChainOp opN, ChainOperand rhs])
        _ -> pure ei

pCtorRef :: P CtorRef
pCtorRef = do
  n <- pIdent
  qual <- optionMaybe (try (token TokDot *> pIdent))
  pure $ case qual of
    Just c -> CtorRef (Just n) c
    Nothing -> CtorRef Nothing n

-- | What follows an already-consumed operator in a chain (§5.5.1.1):
-- a stopping token (the operator was a trailing postfix candidate), more
-- operators (collect them too), or an operand.
data ChainEndKind = ChainEndStop | ChainEndMoreOps | ChainEndOperand

pChainElems :: P [OpElem]
pChainElems = do
  pre <- many (ChainOp <$> pPrefixOp)
  operand <- ChainOperand <$> pAppExpr
  rest <- pChainRest
  pure (pre ++ operand : rest)
  where
    pChainRest = do
      t <- peekToken
      eqok <- eqAllowed
      case t of
        TokEquals | eqok -> do
          sp <- currentSpan
          void anyToken
          continueAfterOp (Name "=" sp)
        TokOperator op
          -- '=>' never continues a chain; '*' could be a wildcard only
          -- in imports, so it is safe as an infix operator here.
          -- '.<', '>.', and '.~' are reserved §23.2 staging
          -- punctuation: '>.' closes a code quote and the other two
          -- begin operands, so none of them continues a chain.
          | op `notElem` ["=>", ".<", ">.", ".~"] -> do
              opN <- pOperatorTok
              continueAfterOp opN
        TokElvis -> do
          sp <- currentSpan
          void anyToken
          continueAfterOp (Name "?:" sp)
        TokBang -> do
          -- `!` infix? It is reserved; treat as operand prefix only.
          pure []
        _ -> pure []
    continueAfterOp opN = do
      -- a ')' right after an infix operator means this was a left
      -- section `(e op)` — refuse so the section parser can take over
      t <- peekToken
      case t of
        TokRParen -> parseFail "trailing operator before ')' (left section)"
        _ -> pure ()
      -- §5.5.1.1/§5.5.3: an operator with no operand after it is a
      -- /trailing postfix/ use, e.g. bare `5 ?`. The parser does not know
      -- fixities, so it leaves a trailing `ChainOp` for the re-associator,
      -- which applies a postfix fixity if one is in scope (and otherwise
      -- emits the §5.5.3 gating error). Without this, the chain parser
      -- would demand an operand and swallow the next declaration.
      trailing <- chainEndKind
      case trailing of
        -- end of the expression: a lone trailing operator (postfix
        -- candidate) — leave it for the re-associator.
        ChainEndStop -> pure [ChainOp opN]
        -- another operator follows: this one was postfix and the next
        -- begins a fresh postfix/infix form; keep collecting the chain
        -- (e.g. the double postfix `5 ? ?`).
        ChainEndMoreOps -> (ChainOp opN :) <$> pChainRest
        ChainEndOperand -> do
          -- operator may be followed by newline+indent continuation (§5.4)
          void (optional (try (pNewline *> token TokIndent)))
          -- an open expression (let-in, if, match, lambda, …) may close the
          -- chain as its final operand (§16.1.8)
          mOpen <- optionMaybe pOpenTailOperand
          case mOpen of
            Just e -> pure [ChainOp opN, ChainOperand e]
            Nothing -> do
              pre <- many (ChainOp <$> pPrefixOp)
              nxt <- ChainOperand <$> pAppExpr
              rest <- pChainRest
              pure (ChainOp opN : pre ++ nxt : rest)
    -- §5.5.1.1/§5.5.3: classify what follows an operator that has already
    -- been consumed. A trailing operator (no operand after it) is a
    -- postfix candidate; the parser does not validate fixities, so it
    -- leaves trailing `ChainOp`s for the re-associator. This is purely
    -- syntactic: end of statement / closing bracket / separator stops the
    -- chain, another operator keeps it going, anything else is an operand.
    chainEndKind = do
      t <- peekToken
      pure $ case t of
        TokNewline _ -> ChainEndStop
        TokDedent -> ChainEndStop
        TokRParen -> ChainEndStop
        TokRBracket -> ChainEndStop
        TokRBrace -> ChainEndStop
        TokComma -> ChainEndStop
        TokEOF -> ChainEndStop
        -- §23.2 staging punctuation is operand syntax, not a chain
        -- operator: '.<' and '.~' begin operands, '>.' closes a code
        -- quote. None of them continue or end the chain as a postfix op,
        -- so defer to the ordinary operand path (which handles them via
        -- 'pAtom'); only genuine operator tokens collect as further
        -- (postfix/infix) chain operators.
        TokOperator op
          | op `notElem` ["=>", ".<", ">.", ".~"] -> ChainEndMoreOps
          | otherwise -> ChainEndOperand
        _ -> ChainEndOperand

-- An open expression (let-in, if, match, lambda, …) as the final
-- operand of an operator chain (§16.1.8).
pOpenTailOperand :: P Expr
pOpenTailOperand = try pOpenExpr

pPrefixOp :: P Name
pPrefixOp = try $ do
  op <- pOperatorTok
  -- Only `-` and user prefix operators appear here; conservatively treat
  -- any operator directly preceding an operand as prefix when it begins
  -- the chain (resolution validates fixity). The §23.2 staging
  -- punctuation runs are operand syntax ('pAtom'), never prefix
  -- operators.
  when (nameText op `elem` [".<", ">.", ".~"]) $
    parseFail "staging punctuation is not a prefix operator"
  pure op

-- Application spines (§16.1.7): postfixExpr applicationArg*, with an
-- optional trailing same-line lambda argument (`f x \a b -> ...`).
pAppExpr :: P Expr
pAppExpr = do
  f <- pPostfixExpr
  args <- many pAppArg
  mlam <- trailingLambda
  targs <- pTrailingBlockArgs
  pure $ case args ++ maybe [] (: []) mlam ++ targs of
    [] -> f
    allArgs -> EApp f allArgs
  where
    -- a bare lambda operand is taken by 'pOpenExpr' before application
    -- parsing ever runs, so a '\' here is a final argument
    trailingLambda = do
      t <- peekToken
      case t of
        TokBackslash -> Just . ArgExplicit <$> pLambda Nothing
        _ -> pure Nothing

-- Deeper-indented continuation lines supply the final (block-shaped)
-- arguments of the application: `f\n    do ...`, or one argument per
-- continuation line, e.g. `f x\n    (\a -> ...)\n    (\b -> ...)`
-- (§16.1.7, layout §5.4).
pTrailingBlockArgs :: P [Arg]
pTrailingBlockArgs = fmap (fromMaybe []) $ optionMaybe $ try $ do
  pNewline
  token TokIndent
  stop <- pAtStopKeyword
  open <- (`elem` [Just "do", Just "match", Just "block", Just "if"]) <$> peekIdent
  if stop && not open
    then parseFail "stop keyword cannot begin a trailing argument"
    else argLines
  where
    argLines = do
      e <- pExpr
      void (many pNewline)
      done <- suiteEnds
      if done
        then suiteDedent >> pure [ArgExplicit e]
        else (ArgExplicit e :) <$> argLines

pAppArg :: P Arg
pAppArg = implicitArg <|> inoutArg <|> namedBlock <|> bangArg <|> plainArg
  where
    implicitArg = do
      token TokAt
      e <- pPostfixExpr
      pure (ArgImplicit e)
    inoutArg = do
      sp <- currentSpan
      token TokTilde
      e <- pPostfixExpr
      ArgInout e <$> spanFrom sp
    namedBlock = do
      ok <- namedBlockOk
      unless ok (parseFail "named-block argument suppressed here")
      sp <- currentSpan
      token TokLBrace
      items <- clearExtraStops (sepBy1 namedItem (token TokComma))
      void (optional (token TokComma))
      token TokRBrace
      sp' <- spanFrom sp
      pure (ArgNamedBlock items sp')
    namedItem = do
      n <- pIdent
      me <- optionMaybe (token TokEquals *> pExpr)
      pure (n, me)
    bangArg = do
      sp <- currentSpan
      token TokBang
      e <- pPostfixExpr
      sp' <- spanFrom sp
      pure (ArgExplicit (EBang False e sp'))
    plainArg = ArgExplicit <$> pArgOperand

-- An argument operand must not begin with a stop keyword.
pArgOperand :: P Expr
pArgOperand = do
  stop <- pAtStopKeyword
  if stop then parseFail "argument" else pPostfixExpr

-- Argument-position expression used by thunk/lazy/force.
pExprArg :: P Expr
pExprArg = pAppExpr

pPostfixExpr :: P Expr
pPostfixExpr = do
  atom <- pAtom
  pSuffixes atom

pSuffixes :: Expr -> P Expr
pSuffixes e = do
  t <- peekToken
  case t of
    TokDot -> do
      nxt <- peekTokenAt 1
      case nxt of
        TokLBrace -> do
          sp0 <- currentSpan
          void anyToken -- '.'
          void anyToken -- '{'
          items <- sepBy1 pPatchItem (token TokComma)
          void (optional (token TokComma))
          token TokRBrace
          sp <- spanFrom sp0
          pSuffixes (ERecordPatch e items sp)
        _ -> do
          void anyToken
          m <- pDotMember
          pSuffixes (EDot e m)
    TokQDot -> do
      void anyToken
      m <- pDotMember
      pSuffixes (EQDot e m)
    -- Adjacent `?` = Option sugar (§13.1.9), tighter than application.
    -- Adjacency is measured against the last consumed token (the
    -- closing paren of a parenthesized type, not the inner expression).
    TokOperator "?" -> do
      sp <- currentSpan
      prevEnd <- spanEnd <$> lastSpan
      let end = max prevEnd (spanEnd (exprSpan e))
      if spanStart sp == end
        then do
          void anyToken
          sp' <- spanFrom (exprSpan e)
          pSuffixes (EOptionSugar e sp')
        else pure e
    -- `captures (r1, ..., rn)` postfix type former (§12.3.1)
    TokIdent "captures" -> do
      nxt <- peekTokenAt 1
      case nxt of
        TokLParen -> do
          pKeyword "captures"
          token TokLParen
          rs <- sepBy1 pIdent (token TokComma)
          token TokRParen
          sp <- spanFrom (exprSpan e)
          pSuffixes (ECaptures e rs sp)
        _ -> pure e
    _ -> pure e

pDotMember :: P DotMember
pDotMember =
  (DotName <$> pIdent) <|> opMember
  where
    opMember = do
      token TokLParen
      op <- pOperatorTok <|> coreOpName
      token TokRParen
      pure (DotOperator op)

pPatchItem :: P PatchItem
pPatchItem = extension <|> sectionUpdate <|> try update <|> pun
  where
    extension = try $ do
      n <- pIdent
      pOperatorNamed ":="
      e <- pExpr
      pure (PatchExtend n e)
    -- a bare label parses as a (rejected, §13.2.5) punned item
    pun = do
      n <- pIdent
      nxt <- peekToken
      case nxt of
        TokComma -> pure (PatchPun n)
        TokRBrace -> pure (PatchPun n)
        _ -> parseFail "expected '=' in record update item"
    sectionUpdate = try $ do
      token TokLParen
      token TokDot
      m <- pDotMember
      args <- many pAppArg
      token TokRParen
      token TokEquals
      rhs <- pExpr
      sp <- lastSpan
      let recv = EReceiverSection [m] args sp
      pure (PatchSection recv rhs)
    update = do
      segs <- sepBy1 seg (token TokDot)
      token TokEquals
      e <- pExpr
      pure (PatchUpdate segs (PatchValue e))
    seg = do
      imp <- isJust <$> optionMaybe (token TokAt)
      n <- pIdent
      pure (imp, n)

-- ── Atoms ────────────────────────────────────────────────────────────

pAtom :: P Expr
pAtom = do
  t <- peekToken
  start <- currentSpan
  case t of
    TokInt v suf -> do
      void anyToken
      EIntLit v (fmap (`Name` start) suf) <$> spanFrom start
    TokFloat v suf -> do
      void anyToken
      EFloatLit v (fmap (`Name` start) suf) <$> spanFrom start
    TokString sl -> do
      void anyToken
      parts <- parseInterps sl start
      EStringLit sl parts <$> spanFrom start
    TokQuoted ql -> do
      void anyToken
      EQuotedLit ql <$> spanFrom start
    TokHole n -> do
      void anyToken
      EHole (Just (Name n start)) <$> spanFrom start
    TokIdent "_" -> do
      void anyToken
      EHole Nothing <$> spanFrom start
    TokIdent kw
      | kw `elem` ["type", "trait", "effectLabel", "module"] -> kindQualified start kw
    TokIdent "moduleSig" -> do
      pKeyword "moduleSig"
      n <- pIdent
      EModuleSig n <$> spanFrom start
    TokIdent _ -> EVar <$> pIdent
    TokBacktick _ -> EVar <$> pIdent
    -- Brackets close any enclosing clause context, so query keywords
    -- are ordinary identifiers inside them and their internal newlines
    -- are soft again (§5.2, §5.4).
    TokLParen -> inBrackets (pParenExpr start)
    TokVariantOpen -> inBrackets (pVariantExpr start)
    TokLBracket -> inBrackets (pListOrComp start)
    TokSetOpen -> inBrackets (pSetOrComp start)
    TokLBrace -> inBrackets (pMapOrComp start)
    TokEffOpen -> inBrackets (pEffRow start)
    TokQuoteBrace -> do
      void anyToken
      e <- inBrackets pExpr
      token TokRBrace
      EQuote e <$> spanFrom start
    -- §23.2 staged-code quotation '.< e >.' and escape '.~c' (the
    -- operator runs '.<', '>.', and '.~' are reserved staging
    -- punctuation; pChainRest never treats them as infix)
    TokOperator ".<" -> do
      void anyToken
      e <- inBrackets pExpr
      token (TokOperator ">.")
      ECodeQuote e <$> spanFrom start
    TokOperator ".~" -> do
      void anyToken
      e <- pPostfixExpr
      ECodeEscape e <$> spanFrom start
    TokSplice -> do
      void anyToken
      e <- inBrackets pExpr
      token TokRParen
      ESplice e <$> spanFrom start
    TokQuoteSplice -> do
      void anyToken
      e <- inBrackets pExpr
      token TokRBrace
      ESpliceInQuote e <$> spanFrom start
    TokBang -> do
      void anyToken
      e <- pPostfixExpr
      EBang False e <$> spanFrom start
    _ -> parseFail ("expected expression, found " <> tokenDescr t)
  where
    -- kind-qualified expressions: `type T`, `trait C`, etc. (§7.1.1).
    -- Only when followed by an identifier; otherwise the soft keyword is
    -- an ordinary variable (e.g. the `type` prefixed-string handler).
    kindQualified start kw = do
      nxt <- peekTokenAt 1
      qualifies <- case nxt of
        TokIdent t2 -> not <$> isStopKeywordAt 1 t2
        _ -> pure False
      if qualifies
        then do
          void anyToken
          n <- pIdent
          let sel = case kw of
                "type" -> SelType
                "trait" -> SelTrait
                "effectLabel" -> SelEffectLabel
                _ -> SelModule
          EKindQualified sel n <$> spanFrom start
        else EVar <$> pIdent

-- Atom without sections (constructor bare fields).
pAtomNoSection :: P Expr
pAtomNoSection = pAtom

-- Parse interpolation payloads of a string literal.
parseInterps :: StringLit -> Span -> P [InterpPart]
parseInterps sl _sp = go 0 (slFragments sl)
  where
    go _ [] = pure []
    go i (frag : rest) = case frag of
      FragLit _ -> go (i + 1) rest
      FragInterp src isp -> withParsed i src isp rest
      FragInterpFmt src isp _ -> withParsed i src isp rest
    withParsed i src isp rest =
      case parseExprText (spanFile isp) src of
        Left d -> parseFailAt isp (dMessage d)
        Right e -> (InterpPart i e :) <$> go (i + 1) rest

-- Parenthesized forms: unit, grouping, ascription, tuples, record
-- literals, record types, sections, operator references.
pParenExpr :: Span -> P Expr
pParenExpr start = do
  token TokLParen
  t <- peekToken
  case t of
    TokRParen -> do
      void anyToken
      EUnit <$> spanFrom start
    -- receiver section (.f args)
    TokDot -> do
      void anyToken
      m1 <- pDotMember
      more <- many (token TokDot *> pDotMember)
      args <- many pAppArg
      token TokRParen
      EReceiverSection (m1 : more) args <$> spanFrom start
    TokIdent k
      | k `elem` ["infix", "prefix", "postfix"] -> fixityRef k <|> generalParen
    _ -> generalParen
  where
    opRefOrSection = do
      opSp <- currentSpan
      op <- pOperatorTok <|> coreOpName
      t2 <- peekToken
      case t2 of
        TokRParen -> do
          void anyToken
          EOpRef Nothing (op {nameSpan = opSp}) <$> spanFrom start
        _ -> do
          e <- pChainExpr
          token TokRParen
          ESectionRight (op {nameSpan = opSp}) e <$> spanFrom start
    fixityRef k = try $ do
      pKeyword k
      op <- pOperatorTok
      token TokRParen
      let fk = case k of
            "infix" -> InfixN
            "prefix" -> Prefix
            _ -> Postfix
      EOpRef (Just fk) op <$> spanFrom start
    generalParen =
      try piBinderArrow
        <|> try opRefOrSection
        <|> try recordTypeFields
        <|> try recordLitFields
        -- exprBased first: trying leftSection eagerly would re-parse the
        -- inner expression of every paren level (exponential nesting)
        <|> try exprBased
        <|> leftSection

    -- (e op): left operator section (§16.1.6); reached only when the
    -- chain parser refused a trailing operator before ')'
    leftSection = do
      e <- pAppExpr
      opSp <- currentSpan
      op <- pOperatorTok
      token TokRParen
      ESectionLeft e (op {nameSpan = opSp}) <$> spanFrom start

    -- A parenthesized Pi binder: `(q x : A) -> B`, `(@t : Type) -> B`,
    -- `(& x : A) -> B`, `(thunk x : A) -> B`, `(x y : A) -> B` (§12.1).
    -- Recognized only when an annotated/marked binder is directly
    -- followed by `)` and `->`.
    piBinderArrow = do
      sp <- currentSpan
      bs <- pBinderBody sp False
      case bs of
        (b1 : _)
          | isJust (bType b1) || bImplicit b1 || bInout b1 -> pure ()
        _ -> parseFail "not a binder"
      token TokRParen
      token TokArrow
      pArrowCont
      rhs <- pExpr
      pure (foldr EArrow rhs bs)

    -- record type: (l : T, ...) — requires a comma, a row tail, or a
    -- binder prefix\/marker to distinguish from ascription.
    recordTypeFields = try $ do
      f1 <- pRecTypeField
      t2 <- peekToken
      case t2 of
        TokComma -> do
          void anyToken
          rest <- sepBy pRecTypeField (token TokComma)
          tailRow <- optionMaybe (token TokBar *> pExpr)
          void (optional (token TokComma))
          token TokRParen
          ERecordType (f1 : rest) tailRow <$> spanFrom start
        TokBar -> do
          void anyToken
          tailRow <- pExpr
          token TokRParen
          ERecordType [f1] (Just tailRow) <$> spanFrom start
        TokRParen
          -- single field with a distinguishing marker: (1 v : Int),
          -- (& b : Buf), (@x : T), (opaque x : T), (thunk v : T)
          | rtfOpaque f1
              || rtfImplicit f1
              || isJust (bpQuantity (rtfPrefix f1))
              || isJust (bpBorrow (rtfPrefix f1))
              || isJust (rtfSusp f1) -> do
              void anyToken
              ERecordType [f1] Nothing <$> spanFrom start
        _ -> parseFail "not a record type"

    recordLitFields = try $ do
      i1 <- pRecItem
      t2 <- peekToken
      case t2 of
        TokComma -> do
          void anyToken
          rest <- sepBy pRecItem (token TokComma)
          void (optional (token TokComma))
          token TokRParen
          -- punning needs at least one explicit `label = expr` item;
          -- an all-bare list is a tuple (positional record), not a
          -- punned record literal (§13.1.2)
          if any (\(RecItem _ _ mv) -> isJust mv) (i1 : rest)
            then ERecordLit (i1 : rest) <$> spanFrom start
            else parseFail "all-bare parenthesized names are a tuple"
        TokRParen -> do
          void anyToken
          case i1 of
            RecItem _ _ (Just _) -> ERecordLit [i1] <$> spanFrom start
            _ -> parseFail "bare name in parens is grouping, not a record"
        _ -> parseFail "not a record literal"

    exprBased = do
      e <- pExpr
      t2 <- peekToken
      case t2 of
        TokColon -> do
          void anyToken
          ty <- pExpr
          token TokRParen
          EAscription e ty <$> spanFrom start
        TokComma -> do
          void anyToken
          -- tuple; possibly single-element (e,)
          rest <- sepBy pExpr (token TokComma)
          void (optional (token TokComma))
          token TokRParen
          ETuple (e : rest) <$> spanFrom start
        TokRParen -> do
          void anyToken
          -- left section (e op)? Only when e ends with trailing operator —
          -- handled in pChainExpr; plain grouping here.
          -- §18.3.1: an explicitly parenthesised splice `(!e)` is a closed
          -- splice: it does not absorb application arguments written after
          -- the parens, so `(!f) x` splices `f` then applies the result to
          -- `x` (as opposed to the open `!f x` which splices `f x`).
          pure $ case e of
            EBang _ inner bsp -> EBang True inner bsp
            _ -> e
        TokOperator op -> do
          -- left section: (e op)
          opSp <- currentSpan
          void anyToken
          token TokRParen
          ESectionLeft e (Name op opSp) <$> spanFrom start
        _ -> parseFail "expected ')', ',' or ':'"

pRecItem :: P RecItem
pRecItem = implicitItem <|> namedItem
  where
    implicitItem = try $ do
      token TokAt
      n <- pIdent
      token TokEquals
      e <- pExpr
      pure (RecItem True n (Just e))
    namedItem = try $ do
      n <- pIdent
      me <- optionMaybe (token TokEquals *> pExpr)
      case me of
        Just e -> pure (RecItem False n (Just e))
        Nothing -> pure (RecItem False n Nothing) -- punning

pRecTypeField :: P RecTypeField
pRecTypeField = try $ do
  opq <- isJust <$> optionMaybe (pKeyword "opaque")
  imp <- isJust <$> optionMaybe (token TokAt)
  prefix <- pBinderPrefix
  susp <- pSuspension
  n <- pIdent
  token TokColon
  ty <- pExpr
  pure (RecTypeField opq imp prefix susp n ty)

-- Variant forms (§13.1): type or injection, disambiguated later.
pVariantExpr :: Span -> P Expr
pVariantExpr start = do
  token TokVariantOpen
  arms <- sepBy1 pArm (token TokBar)
  -- open row: last arm may be `| r` — represented as trailing arm; the
  -- resolver distinguishes a row variable by position.
  token TokVariantClose
  EVariant (map fst arms) Nothing <$> spanFrom start
  where
    pArm = do
      e <- pChainExpr
      mty <- optionMaybe (token TokColon *> pChainExpr)
      pure (VariantArm e mty, ())

-- Effect rows <[l : E, ... | r]> (§11.3.2)
pEffRow :: Span -> P Expr
pEffRow start = do
  token TokEffOpen
  entries <- sepBy pEntry (token TokComma)
  tailRow <- optionMaybe (token TokBar *> pExpr)
  token TokEffClose
  EEffRow entries tailRow <$> spanFrom start
  where
    pEntry = do
      l <- pIdent
      token TokColon
      e <- pExpr
      pure (l, e)

-- | Bracketed sub-expressions close any enclosing comprehension clause
-- context: stop keywords become ordinary identifiers and newlines are
-- soft again until the bracket closes (§5.2, §5.4).
inBrackets :: P a -> P a
inBrackets = hideSoftNewlines . clearExtraStops

-- Lists and list comprehensions (§20).
pListOrComp :: Span -> P Expr
pListOrComp start = do
  token TokLBracket
  t <- peekToken
  case t of
    TokRBracket -> do
      token TokRBracket
      EListLit [] <$> spanFrom start
    TokIdent kw | kw `elem` ["yield", "for", "for?"] -> do
      (cs, y) <- pCompBody
      token TokRBracket
      EComprehension CompList cs y <$> spanFrom start
    _ -> do
      es <- sepBy1 pExpr (token TokComma)
      void (optional (token TokComma))
      token TokRBracket
      EListLit es <$> spanFrom start

pSetOrComp :: Span -> P Expr
pSetOrComp start = do
  token TokSetOpen
  t <- peekToken
  case t of
    TokSetClose -> do
      token TokSetClose
      ESetLit [] <$> spanFrom start
    TokIdent kw | kw `elem` ["yield", "for", "for?"] -> do
      (cs, y) <- pCompBody
      token TokSetClose
      EComprehension CompSet cs y <$> spanFrom start
    _ -> do
      es <- sepBy1 pExpr (token TokComma)
      void (optional (token TokComma))
      token TokSetClose
      ESetLit es <$> spanFrom start

pMapOrComp :: Span -> P Expr
pMapOrComp start = do
  token TokLBrace
  t <- peekToken
  case t of
    TokRBrace -> do
      token TokRBrace
      EMapLit [] <$> spanFrom start
    TokIdent kw | kw `elem` ["yield", "for", "for?"] -> do
      (cs, y) <- pCompBody
      conflict <- optionMaybe pOnConflict
      token TokRBrace
      EComprehension (CompMap conflict) cs y <$> spanFrom start
    _ -> do
      es <- sepBy1 pMapEntry (token TokComma)
      void (optional (token TokComma))
      token TokRBrace
      EMapLit es <$> spanFrom start
  where
    pMapEntry = do
      k <- pChainExpr
      token TokColon
      v <- pExpr
      pure (k, v)

pOnConflict :: P OnConflict
pOnConflict = do
  void (many (pCompSep))
  pKeyword "on"
  pKeyword "conflict"
  keep <|> combine
  where
    keep = do
      pKeyword "keep"
      (pKeyword "last" >> pure KeepLast) <|> (pKeyword "first" >> pure KeepFirst)
    combine = do
      pKeyword "combine"
      usingF <|> withF
    usingF = pKeyword "using" >> (CombineUsing <$> pExpr)
    withF = pKeyword "with" >> (CombineWith <$> pExpr)

-- Comprehension bodies: clauses separated by commas or newlines, ending
-- with a yield (§20.3).
pCompBody :: P ([CompClause], CompYield)
pCompBody = keepSoftNewlines $ withExtraStops queryStopKeywords $ do
  void (many pCompSep)
  go []
  where
    go acc = do
      t <- peekToken
      case t of
        TokIdent "yield" -> do
          pKeyword "yield"
          k <- pExpr
          mv <- optionMaybe (token TokColon *> pExpr)
          let y = maybe (YieldExpr k) (YieldPair k) mv
          void (many pCompSep)
          pure (reverse acc, y)
        _ -> do
          c <- pCompClause
          void (many pCompSep)
          go (c : acc)

pCompSep :: P ()
pCompSep = token TokComma <|> pNewline

-- | A token that opens a bracketed expression form.
pOpenBracketTok :: P ()
pOpenBracketTok = satisfy "opening bracket" $ \case
  TokLBracket -> Just ()
  TokLParen -> Just ()
  TokLBrace -> Just ()
  TokSetOpen -> Just ()
  TokVariantOpen -> Just ()
  _ -> Nothing

pCompClause :: P CompClause
pCompClause = do
  start <- currentSpan
  t <- peekToken
  case t of
    TokIdent "for" -> forClause False start
    TokIdent "for?" -> forClause True start
    TokIdent "let" -> letClause False start
    TokIdent "let?" -> letClause True start
    TokIdent "if" -> do
      pKeyword "if"
      CIf <$> pCompExpr
    TokIdent "order" -> do
      pKeyword "order"
      pKeyword "by"
      keys <- orderKeys
      COrderBy keys <$> spanFrom start
    TokIdent "skip" -> do
      pKeyword "skip"
      e <- pCompExpr
      CSkip e <$> spanFrom start
    TokIdent "take" -> do
      pKeyword "take"
      e <- pCompExpr
      CTake e <$> spanFrom start
    TokIdent "distinct" -> do
      pKeyword "distinct"
      mBy <- optionMaybe (pKeyword "by" *> pCompExpr)
      CDistinct mBy <$> spanFrom start
    TokIdent "group" -> do
      pKeyword "group"
      pKeyword "by"
      key <- noNamedBlock pCompExpr
      token TokLBrace
      void (many pCompSep)
      aggs <- sepBy1 pAgg aggSep
      void (many pCompSep)
      token TokRBrace
      pKeyword "into"
      n <- pIdent
      CGroupBy key aggs n <$> spanFrom start
    TokIdent "join" -> joinClause False start
    TokIdent "left" -> do
      pKeyword "left"
      pKeyword "join"
      joinBody True start
    _ -> parseFail ("expected comprehension clause, found " <> tokenDescr t)
  where
    forClause refut start = do
      pKeyword (if refut then "for?" else "for")
      borrowedItems <- isJust <$> optionMaybe (pOperatorNamed "&")
      pat <- pPattern
      pKeyword "in"
      borrowedSrc <- isJust <$> optionMaybe (pOperatorNamed "&")
      src <- pCompExpr
      CFor refut (borrowedItems || borrowedSrc) pat src <$> spanFrom start
    letClause refut start = do
      pKeyword (if refut then "let?" else "let")
      pat <- pPattern
      mty <- optionMaybe (token TokColon *> pCompExpr)
      token TokEquals
      -- the bound expression may open on a continuation line (§5.4)
      cont <- lookAheadIs (pNewline *> pOpenBracketTok)
      when cont pNewline
      e <- pCompExpr
      CLet refut pat mty e <$> spanFrom start
    orderKeys =
      parenKeys <|> ((: []) <$> singleKey)
    parenKeys = try $ do
      token TokLParen
      ks <- sepBy1 singleKey (token TokComma)
      token TokRParen
      pure ks
    singleKey = do
      desc <-
        peekIdent >>= \case
          Just "asc" -> pKeyword "asc" >> pure False
          Just "desc" -> pKeyword "desc" >> pure True
          _ -> pure False
      e <- pCompExpr
      pure (desc, e)
    pAgg = do
      n <- pIdent
      token TokEquals
      e <- pCompExpr
      mUsing <- optionMaybe (pKeyword "using" *> pCompExpr)
      pure (n, e, mUsing)
    aggSep = token TokComma <|> pNewline
    joinClause left start = do
      pKeyword "join"
      joinBody left start
    joinBody left start = do
      pat <- pPattern
      pKeyword "in"
      src <- pCompExpr
      pKeyword "on"
      cond <- pCompExpr
      mInto <- optionMaybe (pKeyword "into" *> pIdent)
      CJoin left pat src cond mInto <$> spanFrom start

-- Inside comprehensions newlines separate clauses, so clause expressions
-- must not skip soft newlines: parse with chain expressions.
pCompExpr :: P Expr
pCompExpr = pChainExpr

-- ── Open expression forms ───────────────────────────────────────────

pLambda :: Maybe Name -> P Expr
pLambda label = do
  start <- currentSpan
  token TokBackslash
  binders <- concat <$> many1 pLambdaBinder
  token TokArrow
  body <- pSuiteOrExpr
  ELambda label binders body <$> spanFrom start

pLetIn :: P Expr
pLetIn = do
  start <- currentSpan
  pKeyword "let"
  binds <- letBlock <|> ((: []) <$> pLetBind)
  -- `in` may start its own (equally indented) continuation line
  void $ optional $ try $ do
    void (many1 pNewline)
    ok <- lookAheadIs (pKeyword "in")
    if ok then pure () else parseFail "expected 'in'"
  pKeyword "in"
  body <- pSuiteOrExpr
  ELet binds body <$> spanFrom start
  where
    letBlock = try $ do
      pNewline
      token TokIndent
      bs <- pLetBind `sepEndByNewlines` ()
      token TokDedent
      void (many pNewline)
      pure bs

pLetBind :: P LetBind
pLetBind = implicitBind <|> ordinaryBind
  where
    implicitBind = try $ do
      start <- currentSpan
      token TokLParen
      token TokAt
      prefix <- pBinderPrefix
      n <- pIdent
      token TokColon
      ty <- pExpr
      token TokRParen
      token TokEquals
      e <- pSuiteOrExpr
      sp <- spanFrom start
      pure (LetBind True prefix (PVar n) (Just ty) e sp)
    ordinaryBind = do
      start <- currentSpan
      prefix <- pBinderPrefix
      pat <- pPattern
      mty <- optionMaybe (token TokColon *> noEq pExpr)
      token TokEquals
      e <- pSuiteOrExpr
      sp <- spanFrom start
      pure (LetBind False prefix pat mty e sp)

pIfExpr :: P Expr
pIfExpr = do
  start <- currentSpan
  pKeyword "if"
  c <- pExpr
  -- `then` may open its own continuation line (§5.4)
  void (many pNewline)
  pKeyword "then"
  t <- pSuiteOrExpr
  branches <- pElifs
  els <- pElse
  EIf ((c, t) : branches) els <$> spanFrom start
  where
    pElifs = many $ try $ do
      void (many pNewline)
      pKeyword "elif"
      c <- pExpr
      pKeyword "then"
      t <- pSuiteOrExpr
      pure (c, t)
    pElse = optionMaybe $ try $ do
      void (many pNewline)
      pKeyword "else"
      pSuiteOrExpr

-- A match label is inert in the supported subset: no construct may
-- target it (break/continue target loops, defer targets do-scopes,
-- return targets functions and lambdas, §18.2.5), so it is accepted
-- and dropped here.
pMatchExpr :: Maybe Name -> P Expr
pMatchExpr _inertLabel = do
  start <- currentSpan
  pKeyword "match"
  scrut <- pExpr
  cases <- pCaseBlock
  sp <- spanFrom start
  pure (EMatch scrut cases sp)

-- Aligned or indented case clauses (§17.1).
pCaseBlock :: P [MatchCase]
pCaseBlock = indented <|> aligned
  where
    indented = try $ do
      pNewline
      token TokIndent
      cs <- pMatchCase `sepEndByNewlines` ()
      token TokDedent
      pure cs
    aligned = do
      cs <- many1 $ try $ do
        void (many pNewline)
        pMatchCase
      pure cs

pMatchCase :: P MatchCase
pMatchCase = do
  start <- currentSpan
  pKeyword "case"
  impossibleCase start <|> ordinaryCase start
  where
    impossibleCase start = try $ do
      pKeyword "impossible"
      MatchImpossible <$> spanFrom start
    ordinaryCase start = do
      pat <- pPattern
      -- guard: a chain expression; the case's '->' must stay visible
      g <- optionMaybe (pKeyword "if" *> pChainExpr)
      token TokArrow
      body <- pSuiteOrExpr
      MatchCase pat g body <$> spanFrom start

pDoExpr :: Maybe Name -> P Expr
pDoExpr label = do
  start <- currentSpan
  pKeyword "do"
  items <- pDoSuite
  EDo label items <$> spanFrom start

pDoSuite :: P [DoItem]
pDoSuite = do
  pNewline
  token TokIndent
  items <- pDoItem `sepEndByNewlines` ()
  suiteDedent
  pure items

pBlockExpr :: P Expr
pBlockExpr = do
  start <- currentSpan
  pKeyword "block"
  pNewline
  token TokIndent
  (decls, final) <- pBlockItems
  token TokDedent
  EBlock decls final <$> spanFrom start

-- Pure-block items: declarations followed by one final expression.
pBlockItems :: P ([Decl], Maybe Expr)
pBlockItems = go []
  where
    go acc = do
      void (many pNewline)
      done <- lookAheadIs (token TokDedent)
      if done
        then pure (reverse acc, Nothing)
        else do
          -- `let … <newline> in …` is a let-in expression, not a local
          -- declaration followed by a stray `in`
          item <-
            (Right <$> try letInExpr)
              <|> (Left <$> try pLocalDecl)
              <|> (Right <$> pExpr)
          case item of
            Left d -> go (d : acc)
            Right e -> do
              void (many pNewline)
              isEnd <- lookAheadIs (token TokDedent)
              if isEnd
                then pure (reverse acc, Just e)
                else parseFail "only the final item of a block may be an expression"
    letInExpr = do
      ok <- lookAheadIs (pKeyword "let")
      if ok then pLetIn else parseFail "not a let-in expression"

-- Local declarations inside block/do (§9.3.1).
pLocalDecl :: P Decl
pLocalDecl = do
  t <- peekIdent
  case t of
    Just kw
      | kw `elem` localKeywords -> pDecl
      | otherwise -> sigDecl
    Nothing -> parseFail "expected declaration"
  where
    localKeywords =
      ["data", "type", "trait", "instance", "derive", "import", "infix", "prefix", "postfix", "scoped", "effect", "let"]
    sigDecl = do
      start <- currentSpan
      (n, ty) <- try $ do
        n <- pSigName
        token TokColon
        ty <- pExprIndented
        pure (n, ty)
      DSig noMods n ty <$> spanFrom start

-- do items (§18.2)
pDoItem :: P DoItem
pDoItem = do
  start <- currentSpan
  t <- peekToken
  case t of
    TokIdent "let" -> pLetItem start
    TokIdent "let?" -> pLetQItem start
    TokIdent "var" -> do
      pKeyword "var"
      n <- pIdent
      token TokEquals
      e <- pExpr
      DoVar n e <$> spanFrom start
    TokIdent "using" -> do
      pKeyword "using"
      pstart <- currentSpan
      prefix <- pBinderPrefix
      psp <- spanFrom pstart
      -- §9.3: using always binds borrowed at the default quantity ω; an
      -- explicit prefix parses but is flagged for elaboration to reject
      let mPref = case prefix of
            BinderPrefix Nothing Nothing -> Nothing
            _ -> Just psp
      pat <- pPattern
      token TokBackArrow
      e <- pExpr
      DoUsing mPref pat e <$> spanFrom start
    TokIdent "defer" -> do
      pKeyword "defer"
      lbl <- optionMaybe (token TokAt *> pIdent)
      e <- pSuiteOrExpr
      DoDefer lbl e <$> spanFrom start
    TokIdent "return" -> do
      pKeyword "return"
      lbl <- optionMaybe (token TokAt *> pIdent)
      e <- optionMaybe pExpr
      DoReturn lbl e <$> spanFrom start
    TokIdent "break" -> do
      pKeyword "break"
      lbl <- optionMaybe (token TokAt *> pIdent)
      DoBreak lbl <$> spanFrom start
    TokIdent "continue" -> do
      pKeyword "continue"
      lbl <- optionMaybe (token TokAt *> pIdent)
      DoContinue lbl <$> spanFrom start
    TokIdent "while" -> pWhile Nothing start
    TokIdent "for" -> pFor Nothing start
    TokIdent "if" -> pDoIf start
    TokIdent kw
      | kw `elem` ["data", "type", "trait", "instance", "derive", "import", "infix", "prefix", "postfix", "scoped", "effect"] ->
          DoDecl <$> pDecl
    _ -> assignOrExpr start
  where
    pLetItem start = do
      -- could be: monadic bind, local def, or local decl `let name ... = ...`
      bindItem start <|> (DoDecl <$> pDecl)
    bindItem start = try $ do
      pKeyword "let"
      bind <- pDoLetBind start
      pure bind
    pDoLetBind start = implicitBindDo start <|> ordinaryDo start
    implicitBindDo start = try $ do
      token TokLParen
      token TokAt
      prefix <- pBinderPrefix
      n <- pIdent
      token TokColon
      ty <- pExpr
      token TokRParen
      arrow <- (token TokBackArrow >> pure True) <|> (token TokEquals >> pure False)
      e <- pSuiteOrExpr
      sp <- spanFrom start
      let lb = LetBind True prefix (PVar n) (Just ty) e sp
      pure (if arrow then DoBind lb else DoLet lb)
    ordinaryDo start = try $ do
      prefix <- pBinderPrefix
      pat <- pPattern
      mty <- optionMaybe (token TokColon *> noEq pExpr)
      arrow <- (token TokBackArrow >> pure True) <|> (token TokEquals >> pure False)
      e <- pSuiteOrExpr
      sp <- spanFrom start
      let lb = LetBind False prefix pat mty e sp
      pure (if arrow then DoBind lb else DoLet lb)
    pLetQItem start = do
      pKeyword "let?"
      pat <- pPattern
      token TokEquals
      e <- pExpr
      els <- optionMaybe $ try $ do
        void (many pNewline)
        pKeyword "else"
        rp <- pPattern
        token TokArrow
        fe <- pSuiteOrExpr
        pure (rp, fe)
      DoLetQ pat e els <$> spanFrom start
    assignOrExpr start = assignItem start <|> labeledLoop start <|> (DoExpr <$> pExpr)
    assignItem start = try $ do
      stop <- pAtStopKeyword
      guard (not stop)
      n <- pIdent
      t2 <- peekToken
      case t2 of
        TokEquals -> do
          void anyToken
          e <- pExpr
          DoAssign n False e <$> spanFrom start
        TokBackArrow -> do
          void anyToken
          e <- pExpr
          DoAssign n True e <$> spanFrom start
        _ -> parseFail "not an assignment"
    labeledLoop start = try $ do
      l <- pIdent
      token TokAt
      t2 <- peekToken
      case t2 of
        TokIdent "while" -> pWhile (Just l) start
        TokIdent "for" -> pFor (Just l) start
        _ -> parseFail "expected loop after label"

pWhile :: Maybe Name -> Span -> P DoItem
pWhile label start = do
  pKeyword "while"
  c <- pExpr
  pKeyword "do"
  body <- pDoSuite
  els <- pLoopElse
  DoWhile label c body els <$> spanFrom start

pFor :: Maybe Name -> Span -> P DoItem
pFor label start = do
  pKeyword "for"
  pat <- pPattern
  pKeyword "in"
  src <- pExpr
  pKeyword "do"
  body <- pDoSuite
  els <- pLoopElse
  DoFor label pat src body els <$> spanFrom start

pLoopElse :: P (Maybe [DoItem])
pLoopElse = optionMaybe $ try $ do
  void (many pNewline)
  pKeyword "else"
  pKeyword "do"
  pDoSuite

-- statement-if inside do (§18.4): branches are suites.
pDoIf :: Span -> P DoItem
pDoIf start = do
  pKeyword "if"
  c <- pExpr
  pKeyword "then"
  thenItems <- branchSuite
  elifs <- many $ try $ do
    void (many pNewline)
    pKeyword "elif"
    c2 <- pExpr
    pKeyword "then"
    items2 <- branchSuite
    pure (c2, items2)
  els <- optionMaybe $ try $ do
    void (many pNewline)
    pKeyword "else"
    branchSuite
  DoIf ((c, thenItems) : elifs) els <$> spanFrom start
  where
    -- inline branches are single do-items so break/continue/return work
    branchSuite = pDoSuite <|> ((: []) <$> pDoItem)

-- try / except / finally (§19.2) and try match (§19.3)
pTryExpr :: P Expr
pTryExpr = do
  start <- currentSpan
  pKeyword "try"
  isMatch <- lookAheadIs (pKeyword "match")
  if isMatch
    then do
      pKeyword "match"
      scrut <- pExpr
      (cases, excepts, fin) <- pTryMatchBlock
      ETryMatch scrut cases excepts fin <$> spanFrom start
    else do
      e <- pSuiteOrExpr
      (excepts, fin) <- pExceptBlock
      ETry e excepts fin <$> spanFrom start

pExceptBlock :: P ([ExceptCase], Maybe Expr)
pExceptBlock = indented <|> aligned
  where
    indented = try $ do
      pNewline
      token TokIndent
      (ex, fin) <- clauses
      void (many pNewline)
      token TokDedent
      pure (ex, fin)
    aligned = do
      void (many pNewline)
      clauses
    clauses = do
      ex <- many (try pExceptCase)
      fin <- optionMaybe (try pFinally)
      pure (ex, fin)

pExceptCase :: P ExceptCase
pExceptCase = do
  void (many pNewline)
  start <- currentSpan
  pKeyword "except"
  pat <- pPattern
  g <- optionMaybe (pKeyword "if" *> pChainExpr)
  token TokArrow
  body <- pSuiteOrExpr
  ExceptCase pat g body <$> spanFrom start

pFinally :: P Expr
pFinally = do
  void (many pNewline)
  pKeyword "finally"
  token TokArrow
  pSuiteOrExpr

pTryMatchBlock :: P ([MatchCase], [ExceptCase], Maybe Expr)
pTryMatchBlock = do
  pNewline
  token TokIndent
  cases <- many (try (pMatchCase <* many pNewline))
  ex <- many (try (pExceptCase <* many pNewline))
  fin <- optionMaybe (try (pFinally <* many pNewline))
  token TokDedent
  pure (cases, ex, fin)

-- handle / deep handle (§18.1.21–.22)
pHandleExpr :: Bool -> P Expr
pHandleExpr deep = do
  start <- currentSpan
  when deep (pKeyword "deep")
  pKeyword "handle"
  lbl <- pPostfixExpr
  scrut <- pExpr
  pKeyword "with"
  cases <- pHandlerBlock
  EHandle deep lbl scrut cases <$> spanFrom start

pHandlerBlock :: P [HandlerCase]
pHandlerBlock = do
  pNewline
  token TokIndent
  cs <- pHandlerCase `sepEndByNewlines` ()
  token TokDedent
  pure cs

pHandlerCase :: P HandlerCase
pHandlerCase = do
  start <- currentSpan
  pKeyword "case"
  retCase start <|> opCase start
  where
    retCase start = try $ do
      pKeyword "return"
      pat <- pPatAtom
      token TokArrow
      body <- pSuiteOrExpr
      HandlerReturn pat body <$> spanFrom start
    opCase start = do
      opName <- pIdent
      args <- many pPatAtom
      case reverse args of
        [] -> parseFail "handler operation clause requires a continuation binder"
        (kPat : argsRev) -> do
          k <- case kPat of
            PVar n -> pure n
            PWild sp -> pure (Name "_" sp)
            _ -> parseFail "continuation binder must be an identifier"
          token TokArrow
          body <- pSuiteOrExpr
          HandlerOp opName (reverse argsRev) k body <$> spanFrom start

pForall :: P Expr
pForall = do
  start <- currentSpan
  pKeyword "forall"
  bs <- concat <$> many1 pQuantBinder
  token TokDot
  pQuantBodyNewline
  body <- pExpr
  EForall bs body <$> spanFrom start

-- the body of a quantifier may continue on the next line (§5.4)
pQuantBodyNewline :: P ()
pQuantBodyNewline = do
  t <- peekToken
  case t of
    TokNewline _ -> do
      nxt <- peekTokenAt 1
      case nxt of
        TokIndent -> anyToken >> anyToken >> pure ()
        TokDedent -> pure ()
        TokEOF -> pure ()
        TokNewline _ -> pure ()
        _ -> void anyToken
    _ -> pure ()

pExists :: P Expr
pExists = do
  start <- currentSpan
  pKeyword "exists"
  bs <- concat <$> many1 pQuantBinder
  token TokDot
  pQuantBodyNewline
  body <- pExpr
  EExists bs body <$> spanFrom start

-- forall/exists binders: a (b : T) (@0 c : T) (x y : m)
pQuantBinder :: P [Binder]
pQuantBinder = parenB <|> bare
  where
    parenB = try $ do
      sp <- currentSpan
      token TokLParen
      bs <- pBinderBody sp False
      token TokRParen
      pure bs
    bare = do
      n <- try $ do
        n <- pIdent
        guard (nameText n /= "_")
        pure n
      pure [simpleBinder n]

pSealExpr :: P Expr
pSealExpr = do
  start <- currentSpan
  pKeyword "seal"
  existsForm start <|> plainForm start
  where
    existsForm start = try $ do
      pKeyword "exists"
      token TokLParen
      ws <- sepBy1 witness (token TokComma)
      token TokRParen
      token TokDot
      e <- pChainExpr
      pKeyword "as"
      ty <- pExpr
      ESealExists ws e ty <$> spanFrom start
    witness = do
      n <- pIdent
      token TokEquals
      e <- pExpr
      pure (n, e)
    plainForm start = do
      e <- pSuiteOrExpr1
      pKeyword "as"
      ty <- pExpr
      ESeal e ty <$> spanFrom start
    -- seal body may be an indented record literal
    pSuiteOrExpr1 = pSuiteOrExpr

pOpenExistsExpr :: P Expr
pOpenExistsExpr = do
  start <- currentSpan
  pKeyword "open"
  e <- pChainExpr
  pKeyword "as"
  pKeyword "exists"
  token TokLParen
  ns <- sepBy1 pIdent (token TokComma)
  token TokRParen
  token TokDot
  pat <- pPattern
  pKeyword "in"
  body <- pSuiteOrExpr
  EOpenExists e ns pat body <$> spanFrom start

-- An expression, or an indented continuation suite (§5.4, §9.3.1).
pSuiteOrExpr :: P Expr
pSuiteOrExpr = indentedSuite <|> pExpr
  where
    indentedSuite = try $ do
      start <- currentSpan
      pNewline
      token TokIndent
      (decls, final) <- pBlockItems
      token TokDedent
      sp <- spanFrom start
      case (decls, final) of
        ([], Just e) -> pure e
        (_, Just e) -> pure (EBlock decls (Just e) sp)
        (_, Nothing) -> parseFail "indented suite must end with an expression"

-- Expression continued on indented lines (used after ':' in signatures).
pExprIndented :: P Expr
pExprIndented = contForm <|> pExpr
  where
    contForm = try $ do
      pNewline
      token TokIndent
      e <- pExpr
      void (many pNewline)
      token TokDedent
      pure e
