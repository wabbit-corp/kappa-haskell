-- | Resolution pre-pass (Spec §5.5.2, §7, §8).
--
-- This pass runs per module after parsing and before elaboration:
--
--   1. collects fixity declarations (module-scoped, plus imported and
--      prelude fixities) and re-associates the flat operator chains the
--      parser produced ('EOpChain' \/ 'POpChain') into applications;
--   2. checks import\/export well-formedness against the loaded module
--      graph and computes the module's import scope.
--
-- Identifier-to-declaration resolution itself happens during
-- elaboration, where the scope stack is available; this pass guarantees
-- that operator parse trees no longer depend on fixity.
module Kappa.Resolve
  ( FixityEnv
  , Fixity (..)
  , defaultFixities
  , fixitiesOf
  , resolveModule
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Kappa.Diagnostic
import Kappa.Source (Span)
import Kappa.Syntax

-- | One operator's fixity: kind and precedence (§5.5.2).
data Fixity = Fixity
  { fKind :: !FixityKind
  , fPrec :: !Int
  }
  deriving stock (Eq, Show)

-- | Operator text → in-scope fixities, by kind. An operator may carry an
-- infix and a prefix\/postfix fixity simultaneously (e.g. @-@).
type FixityEnv = Map Text [Fixity]

-- | The normative minimum prelude fixity table (§28.2.3).
defaultFixities :: FixityEnv
defaultFixities =
  Map.fromListWith (++) $
    [ (op, [Fixity InfixN 40]) | op <- ["==", "~=", "/=", "!=", "<", "<=", ">", ">="] ]
      ++ [ ("&&", [Fixity InfixR 30])
         , ("||", [Fixity InfixR 20])
         , ("..", [Fixity InfixN 45])
         , ("..<", [Fixity InfixN 45])
         , ("::", [Fixity InfixR 50])
         , ("++", [Fixity InfixR 50])
         , ("+", [Fixity InfixL 60])
         , ("-", [Fixity InfixL 60])
         , ("*", [Fixity InfixL 70])
         , ("/", [Fixity InfixL 70])
         , ("%", [Fixity InfixL 70])
         , ("-", [Fixity Prefix 80])
         , (":&", [Fixity InfixR 4])
         , ("|>", [Fixity InfixL 1])
         , ("<|", [Fixity InfixR 0])
         , ("<*>", [Fixity InfixL 65])
         , ("<|>", [Fixity InfixL 25])
         , (">>=", [Fixity InfixL 10])
         , (">>", [Fixity InfixL 10])
         ]

-- | Collect the module's own top-level fixity declarations.
fixitiesOf :: [Decl] -> FixityEnv
fixitiesOf = foldr add Map.empty
  where
    add (DFixity (FixityDecl k p op) _) env =
      Map.insertWith (++) (nameText op) [Fixity k p] env
    add _ env = env

-- | Re-associate all operator chains in a module using the fixity
-- environment, and validate fixity usage (§5.5.3 infix gating).
resolveModule :: FixityEnv -> Module -> (Module, Diagnostics)
resolveModule env0 m =
  let env = Map.unionWith (++) (fixitiesOf (modDecls m)) env0
      (ds, diags) = runRW (mapM (rDecl env) (modDecls m))
   in (m {modDecls = ds}, diags)

-- A tiny writer for diagnostics.
newtype RW a = RW {runRW :: (a, Diagnostics)}

instance Functor RW where
  fmap f (RW (a, w)) = RW (f a, w)

instance Applicative RW where
  pure a = RW (a, [])
  RW (f, w1) <*> RW (a, w2) = RW (f a, w1 ++ w2)

instance Monad RW where
  RW (a, w1) >>= k = let RW (b, w2) = k a in RW (b, w1 ++ w2)

emit :: Diagnostic -> RW ()
emit d = RW ((), [d])

-- ── Operator chain re-association ────────────────────────────────────
--
-- Precedence-climbing over the flat element list. Prefix operators bind
-- per their declared precedence; postfix operators are applied when the
-- following element is an operator or the chain ends.

lookupFix :: FixityEnv -> Text -> [Fixity]
lookupFix env t = Map.findWithDefault [] t env

infixOf :: FixityEnv -> Text -> Maybe Fixity
infixOf env t = case [f | f <- lookupFix env t, fKind f `elem` [InfixN, InfixL, InfixR]] of
  (f : _) -> Just f
  [] -> Nothing

prefixOf :: FixityEnv -> Text -> Maybe Fixity
prefixOf env t = case [f | f <- lookupFix env t, fKind f == Prefix] of
  (f : _) -> Just f
  [] -> Nothing

postfixOf :: FixityEnv -> Text -> Maybe Fixity
postfixOf env t = case [f | f <- lookupFix env t, fKind f == Postfix] of
  (f : _) -> Just f
  [] -> Nothing

-- Reserved chain operators with built-in fixity (§5.5.3, §28.2.3).
reservedInfix :: Text -> Maybe Fixity
reservedInfix = \case
  "?:" -> Just (Fixity InfixR 2)
  "=" -> Just (Fixity InfixN 35) -- propositional equality in type positions
  ":=" -> Nothing
  _ -> Nothing

opApply :: Name -> Expr -> Expr -> Expr
opApply op l r = EApp (EVar op) [ArgExplicit l, ArgExplicit r]

opApply1 :: Name -> Expr -> Expr
opApply1 op x
  -- `-` is a unary operator, not part of the literal: `-123` is
  -- `negate 123`, even for literal operands (§6.1.4, §6.1.5). The
  -- literal payload stays nonnegative; `-123 : Nat` is rejected
  -- because the portable prelude provides no `Negatable Nat`.
  | nameText op == "-" = EApp (EVar op {nameText = "negate"}) [ArgExplicit x]
  | otherwise = EApp (EVar op) [ArgExplicit x]

-- | Re-associate one chain. On unknown operator fixity, emits the
-- §5.5.3 infix-gating diagnostic and associates left at precedence 9.
reassoc :: FixityEnv -> Span -> [OpElem] -> RW Expr
reassoc env sp els0 = do
  (e, rest) <- parseExprAt 0 els0
  case rest of
    [] -> pure e
    (ChainOp op : _) -> do
      emit (gatingErr op)
      pure e
    _ -> pure e -- impossible by construction
  where
    gatingErr op =
      withHelp "declare a fixity, e.g. infix left 60 (...), or use the operator as a function: (op) x y" $
        diag SevError StageResolve "E_OPERATOR_NO_FIXITY" (Just "kappa-hs.fixity.unbound")
          (nameSpan op)
          ("operator '" <> nameText op <> "' is used in infix position but no fixity is in scope (Spec §5.5.3)")

    fixFor op =
      case infixOf env (nameText op) of
        Just f -> Just f
        Nothing -> reservedInfix (nameText op)

    -- parse one operand (with prefix ops) then loop infix operators with
    -- precedence climbing.
    parseExprAt :: Int -> [OpElem] -> RW (Expr, [OpElem])
    parseExprAt minPrec els = do
      (lhs, rest) <- parseOperand els
      loop lhs minPrec rest

    parseOperand :: [OpElem] -> RW (Expr, [OpElem])
    parseOperand (ChainOp op : rest) =
      case prefixOf env (nameText op) of
        Just f -> do
          (operand, rest') <- parsePrefixOperand (fPrec f) rest
          pure (opApply1 op operand, rest')
        Nothing -> do
          emit (gatingErrPrefix op)
          (operand, rest') <- parseOperand rest
          pure (opApply1 op operand, rest')
    parseOperand (ChainOperand e : rest) = applyPostfix e rest
    parseOperand [] = pure (EHole Nothing sp, [])

    parsePrefixOperand prec els = do
      (e, rest) <- parseOperand els
      -- bind following infix operators tighter than the prefix op
      loopTight e prec rest

    loopTight lhs prec els = case els of
      (ChainOp op : rest)
        | Just f <- fixFor op
        , fPrec f > prec -> do
            (rhs, rest') <- parseExprAt (fPrec f + 1) rest
            loopTight (opApply op lhs rhs) prec rest'
      _ -> pure (lhs, els)

    gatingErrPrefix op =
      diag SevError StageResolve "E_OPERATOR_NO_FIXITY" (Just "kappa-hs.fixity.unbound")
        (nameSpan op)
        ("operator '" <> nameText op <> "' is used in prefix position but no prefix fixity is in scope (Spec §5.5.3)")

    nonAssocErr op op2 =
      withHelp "parenthesize one side, e.g. (a == b) == c" $
        diag SevError StageResolve "E_OPERATOR_NON_ASSOCIATIVE" (Just "kappa-hs.fixity.non-associative")
          (nameSpan op2)
          ("operators '" <> nameText op <> "' and '" <> nameText op2
             <> "' are non-associative at the same precedence; the chain has no grouping (Spec §5.5.2)")

    applyPostfix e els = case els of
      (ChainOp op : rest)
        | Just _ <- postfixOf env (nameText op)
        , postfixApplies rest ->
            applyPostfix (opApply1 op e) rest
      _ -> pure (e, els)

    -- a postfix op applies if the next element is another operator or
    -- the chain ends (otherwise it is infix).
    postfixApplies rest = case rest of
      [] -> True
      (ChainOp _ : _) -> True
      (ChainOperand _ : _) -> False

    loop lhs minPrec els = case els of
      (ChainOp op : rest) ->
        case fixFor op of
          Just f
            | fPrec f >= minPrec -> do
                let nextMin = case fKind f of
                      InfixL -> fPrec f + 1
                      InfixN -> fPrec f + 1
                      _ -> fPrec f -- right-assoc reuses same level
                (rhs, rest') <- parseExprAt nextMin rest
                -- §5.5.2: plain `infix` is non-associative — a chain of
                -- same-precedence non-associative operators has no
                -- grouping; reject it (recovering left-associatively)
                case rest' of
                  (ChainOp op2 : _)
                    | fKind f == InfixN
                    , Just f2 <- fixFor op2
                    , fKind f2 == InfixN
                    , fPrec f2 == fPrec f ->
                        emit (nonAssocErr op op2)
                  _ -> pure ()
                loop (mkOp op lhs rhs) minPrec rest'
          Just _ -> pure (lhs, els)
          Nothing ->
            case postfixOf env (nameText op) of
              Just _ -> do
                -- trailing postfix
                applyPostfix lhs els >>= \(e, rest') -> loop e minPrec rest'
              Nothing -> do
                emit (gatingErr op)
                -- recover: treat as left-assoc tight application
                (rhs, rest') <- parseExprAt 100 rest
                loop (opApply op lhs rhs) minPrec rest'
      _ -> pure (lhs, els)

    -- `?:` is reserved syntax (§16.1.2): elaborated as the Elvis form
    mkOp op l r
      | nameText op == "?:" = EElvis l r (nameSpan op)
      | otherwise = opApply op l r

-- ── Traversal ────────────────────────────────────────────────────────

rDecl :: FixityEnv -> Decl -> RW Decl
rDecl env = \case
  DSig m n e sp -> DSig m n <$> rExpr env e <*> pure sp
  DLet m d sp -> DLet m <$> rLetDef env d <*> pure sp
  DData m d sp -> DData m <$> rData env d <*> pure sp
  DTypeAlias m n bs k rhs sp ->
    DTypeAlias m n <$> mapM (rBinder env) bs <*> mapM (rExpr env) k <*> mapM (rExpr env) rhs <*> pure sp
  DTrait m t sp -> DTrait m <$> rTrait env t <*> pure sp
  DInstance i sp -> DInstance <$> rInstance env i <*> pure sp
  DDerive e sp -> DDerive <$> rExpr env e <*> pure sp
  DEffect m e sp -> DEffect m <$> rEffect env e <*> pure sp
  d@DFixity {} -> pure d
  d@DImport {} -> pure d
  d@DExport {} -> pure d
  DExpect m f sp -> DExpect m <$> rExpect env f <*> pure sp
  DPattern m d sp -> DPattern m <$> rLetDef env d <*> pure sp
  DProjection m n bs ty body sp ->
    DProjection m n <$> mapM (rBinder env) bs <*> rExpr env ty <*> rProjBody env body <*> pure sp
  DTopSplice e sp -> DTopSplice <$> rExpr env e <*> pure sp

rProjBody :: FixityEnv -> ProjBody -> RW ProjBody
rProjBody env = \case
  ProjSelector e -> ProjSelector <$> rExpr env e
  ProjAccessors cs ->
    ProjAccessors <$> mapM (\(k, b, e) -> (,,) k <$> mapM (rBinder env) b <*> rExpr env e) cs

rExpect :: FixityEnv -> ExpectForm -> RW ExpectForm
rExpect env = \case
  ExpectTerm n e -> ExpectTerm n <$> rExpr env e
  ExpectType n bs k -> ExpectType n <$> mapM (rBinder env) bs <*> mapM (rExpr env) k
  ExpectData n bs k -> ExpectData n <$> mapM (rBinder env) bs <*> mapM (rExpr env) k
  ExpectTrait n bs k -> ExpectTrait n <$> mapM (rBinder env) bs <*> mapM (rExpr env) k

rLetDef :: FixityEnv -> LetDef -> RW LetDef
rLetDef env (LetDef n imp p brw bs ty dec body) =
  LetDef n imp
    <$> mapM (rPattern env) p
    <*> pure brw
    <*> mapM (rBinder env) bs
    <*> mapM (rExpr env) ty
    <*> mapM (rDecreases env) dec
    <*> rExpr env body

rDecreases :: FixityEnv -> Decreases -> RW Decreases
rDecreases env = \case
  DecMeasure e by us -> DecMeasure <$> rExpr env e <*> mapM (rExpr env) by <*> mapM (rExpr env) us
  d@DecStructural {} -> pure d

rData :: FixityEnv -> DataDecl -> RW DataDecl
rData env (DataDecl n ps k cs) =
  DataDecl n <$> mapM (rBinder env) ps <*> mapM (rExpr env) k <*> mapM rCtor cs
  where
    rCtor (CtorDecl cn bs g sp) = CtorDecl cn <$> mapM (rBinder env) bs <*> mapM (rExpr env) g <*> pure sp

rTrait :: FixityEnv -> TraitDecl -> RW TraitDecl
rTrait env (TraitDecl sups n ps ms) =
  TraitDecl <$> mapM (rExpr env) sups <*> pure n <*> mapM (rBinder env) ps <*> mapM rMember ms
  where
    rMember (TraitSig mn ty sp) = TraitSig mn <$> rExpr env ty <*> pure sp
    rMember (TraitDefault d sp) = TraitDefault <$> rLetDef env d <*> pure sp

rInstance :: FixityEnv -> InstanceDecl -> RW InstanceDecl
rInstance env (InstanceDecl prems hd ms) =
  InstanceDecl <$> mapM (rExpr env) prems <*> rExpr env hd <*> mapM (rDecl env) ms

rEffect :: FixityEnv -> EffectDecl -> RW EffectDecl
rEffect env (EffectDecl n ps ops lbl lty) =
  EffectDecl n
    <$> mapM (rBinder env) ps
    <*> mapM (\(EffectOp q on ty sp) -> EffectOp q on <$> rExpr env ty <*> pure sp) ops
    <*> pure lbl
    <*> mapM (rExpr env) lty

rBinder :: FixityEnv -> Binder -> RW Binder
rBinder env b = do
  ty <- mapM (rExpr env) (bType b)
  def <- mapM (rExpr env) (bDefault b)
  pure b {bType = ty, bDefault = def}

rLetBind :: FixityEnv -> LetBind -> RW LetBind
rLetBind env (LetBind imp pre pat ty e sp) =
  LetBind imp pre <$> rPattern env pat <*> mapM (rExpr env) ty <*> rExpr env e <*> pure sp

rMatchCase :: FixityEnv -> MatchCase -> RW MatchCase
rMatchCase env = \case
  MatchCase p g e sp -> MatchCase <$> rPattern env p <*> mapM (rExpr env) g <*> rExpr env e <*> pure sp
  c@MatchImpossible {} -> pure c

rExpr :: FixityEnv -> Expr -> RW Expr
rExpr env = go
  where
    go :: Expr -> RW Expr
    go = \case
      EOpChain els -> do
        els' <- mapM goElem els
        let sp = exprSpan (EOpChain els)
        reassoc env sp els'
      e@EVar {} -> pure e
      e@EHole {} -> pure e
      e@EIntLit {} -> pure e
      e@EFloatLit {} -> pure e
      EStringLit sl parts sp ->
        EStringLit sl <$> mapM (\(InterpPart i e) -> InterpPart i <$> go e) parts <*> pure sp
      e@EQuotedLit {} -> pure e
      e@EUnit {} -> pure e
      ETuple es sp -> ETuple <$> mapM go es <*> pure sp
      ERecordLit items sp ->
        ERecordLit <$> mapM (\(RecItem i n v) -> RecItem i n <$> mapM go v) items <*> pure sp
      ERecordType fs t sp ->
        ERecordType
          <$> mapM (\f -> (\ty -> f {rtfType = ty}) <$> go (rtfType f)) fs
          <*> mapM go t
          <*> pure sp
      EApp f args -> EApp <$> go f <*> mapM goArg args
      EDot e m -> EDot <$> go e <*> pure m
      EQDot e m -> EQDot <$> go e <*> pure m
      ERecordPatch e items sp -> ERecordPatch <$> go e <*> mapM goPatch items <*> pure sp
      EReceiverSection ms args sp -> EReceiverSection ms <$> mapM goArg args <*> pure sp
      ESectionLeft e op sp -> ESectionLeft <$> go e <*> pure op <*> pure sp
      -- §5.5.1.1: `(op e)` is unary prefix application when a matching
      -- `prefix` fixity for `op` is in scope (e.g. `(-1)` is negation);
      -- only otherwise is it a right operator section.
      ESectionRight op e sp
        | Just _ <- prefixOf env (nameText op) -> do
            let els = case e of
                  EOpChain inner -> ChainOp op : inner
                  _ -> [ChainOp op, ChainOperand e]
            els' <- mapM goElem els
            reassoc env sp els'
        | otherwise -> ESectionRight op <$> go e <*> pure sp
      -- §5.5.1: `(prefix -)` denotes unary negation, not checked
      -- subtraction (the prefix reading of `-` is `negate`, §6.1.4).
      EOpRef (Just Prefix) op sp
        | nameText op == "-" -> pure (EVar (op {nameText = "negate", nameSpan = sp}))
      e@EOpRef {} -> pure e
      ELambda l bs body sp -> ELambda l <$> mapM (rBinder env) bs <*> go body <*> pure sp
      ELet binds body sp -> ELet <$> mapM (rLetBind env) binds <*> go body <*> pure sp
      EBlock ds fin sp -> EBlock <$> mapM (rDecl env) ds <*> mapM go fin <*> pure sp
      EDo l items sp -> EDo l <$> mapM (goDoItem) items <*> pure sp
      EIf alts e sp ->
        EIf <$> mapM (\(c, t) -> (,) <$> go c <*> go t) alts <*> mapM go e <*> pure sp
      EMatch scrut cs sp -> EMatch <$> go scrut <*> mapM (rMatchCase env) cs <*> pure sp
      ETry e exs fin sp ->
        ETry <$> go e <*> mapM goExcept exs <*> mapM go fin <*> pure sp
      ETryMatch e cs exs fin sp ->
        ETryMatch <$> go e <*> mapM (rMatchCase env) cs <*> mapM goExcept exs <*> mapM go fin <*> pure sp
      EHandle d l scrut cs sp ->
        EHandle d <$> go l <*> go scrut <*> mapM goHandler cs <*> pure sp
      EIs e c -> EIs <$> go e <*> pure c
      EElvis l r sp -> EElvis <$> go l <*> go r <*> pure sp
      EThunk e sp -> EThunk <$> go e <*> pure sp
      ELazy e sp -> ELazy <$> go e <*> pure sp
      EForce e sp -> EForce <$> go e <*> pure sp
      ESeal e t sp -> ESeal <$> go e <*> go t <*> pure sp
      EOpenExists e ns p body sp ->
        EOpenExists <$> go e <*> pure ns <*> rPattern env p <*> go body <*> pure sp
      ESealExists ws e t sp ->
        ESealExists <$> mapM (\(n, x) -> (,) n <$> go x) ws <*> go e <*> go t <*> pure sp
      EListLit es sp -> EListLit <$> mapM go es <*> pure sp
      ESetLit es sp -> ESetLit <$> mapM go es <*> pure sp
      EMapLit es sp -> EMapLit <$> mapM (\(k, v) -> (,) <$> go k <*> go v) es <*> pure sp
      EComprehension k cs y sp ->
        EComprehension k <$> mapM goClause cs <*> goYield y <*> pure sp
      EArrow b e -> EArrow <$> rBinder env b <*> go e
      EForall bs e sp -> EForall <$> mapM (rBinder env) bs <*> go e <*> pure sp
      EExists bs e sp -> EExists <$> mapM (rBinder env) bs <*> go e <*> pure sp
      ETraitArrow a b -> ETraitArrow <$> go a <*> go b
      EEffRow es t sp -> EEffRow <$> mapM (\(l, e) -> (,) l <$> go e) es <*> mapM go t <*> pure sp
      EVariant arms t sp ->
        EVariant <$> mapM (\(VariantArm e mt) -> VariantArm <$> go e <*> mapM go mt) arms <*> mapM go t <*> pure sp
      EOptionSugar e sp -> EOptionSugar <$> go e <*> pure sp
      EAscription e t sp -> EAscription <$> go e <*> go t <*> pure sp
      ECaptures e rs sp -> ECaptures <$> go e <*> pure rs <*> pure sp
      EBang e sp -> EBang <$> go e <*> pure sp
      EQuote e sp -> EQuote <$> go e <*> pure sp
      ECodeQuote e sp -> ECodeQuote <$> go e <*> pure sp
      ECodeEscape e sp -> ECodeEscape <$> go e <*> pure sp
      ESplice e sp -> ESplice <$> go e <*> pure sp
      ESpliceInQuote e sp -> ESpliceInQuote <$> go e <*> pure sp
      e@EQuoteHole {} -> pure e
      e@EImpossible {} -> pure e
      e@EKindQualified {} -> pure e
      e@EModuleSig {} -> pure e

    goElem = \case
      ChainOperand e -> ChainOperand <$> go e
      o@ChainOp {} -> pure o

    goArg = \case
      ArgExplicit e -> ArgExplicit <$> go e
      ArgImplicit e -> ArgImplicit <$> go e
      ArgNamedBlock items sp ->
        ArgNamedBlock <$> mapM (\(n, me) -> (,) n <$> mapM go me) items <*> pure sp
      ArgInout e sp -> ArgInout <$> go e <*> pure sp

    goPatch = \case
      PatchUpdate path (PatchValue e) -> PatchUpdate path . PatchValue <$> go e
      PatchExtend n e -> PatchExtend n <$> go e
      PatchSection r e -> PatchSection <$> go r <*> go e
      PatchPun n -> pure (PatchPun n)

    goExcept (ExceptCase p g e sp) =
      ExceptCase <$> rPattern env p <*> mapM go g <*> go e <*> pure sp

    goHandler = \case
      HandlerReturn p e sp -> HandlerReturn <$> rPattern env p <*> go e <*> pure sp
      HandlerOp op ps k e sp -> HandlerOp op <$> mapM (rPattern env) ps <*> pure k <*> go e <*> pure sp

    goDoItem :: DoItem -> RW DoItem
    goDoItem = \case
      DoBind lb -> DoBind <$> rLetBind env lb
      DoLet lb -> DoLet <$> rLetBind env lb
      DoLetQ p e mElse sp ->
        DoLetQ
          <$> rPattern env p
          <*> go e
          <*> mapM (\(rp, fe) -> (,) <$> rPattern env rp <*> go fe) mElse
          <*> pure sp
      DoVar n e sp -> DoVar n <$> go e <*> pure sp
      DoAssign n m e sp -> DoAssign n m <$> go e <*> pure sp
      DoExpr e -> DoExpr <$> go e
      DoUsing mq p e sp -> DoUsing mq <$> rPattern env p <*> go e <*> pure sp
      DoDefer l e sp -> DoDefer l <$> go e <*> pure sp
      DoReturn l e sp -> DoReturn l <$> mapM go e <*> pure sp
      d@DoBreak {} -> pure d
      d@DoContinue {} -> pure d
      DoWhile l c body els sp ->
        DoWhile l <$> go c <*> mapM goDoItem body <*> mapM (mapM goDoItem) els <*> pure sp
      DoFor l p src body els sp ->
        DoFor l <$> rPattern env p <*> go src <*> mapM goDoItem body <*> mapM (mapM goDoItem) els <*> pure sp
      DoIf alts els sp ->
        DoIf
          <$> mapM (\(c, items) -> (,) <$> go c <*> mapM goDoItem items) alts
          <*> mapM (mapM goDoItem) els
          <*> pure sp
      DoDecl d -> DoDecl <$> rDecl env d

    goClause :: CompClause -> RW CompClause
    goClause = \case
      CFor r b p src sp -> CFor r b <$> rPattern env p <*> go src <*> pure sp
      CLet r p t e sp -> CLet r <$> rPattern env p <*> mapM go t <*> go e <*> pure sp
      CIf e -> CIf <$> go e
      COrderBy ks sp -> COrderBy <$> mapM (\(d, e) -> (,) d <$> go e) ks <*> pure sp
      CSkip e sp -> CSkip <$> go e <*> pure sp
      CTake e sp -> CTake <$> go e <*> pure sp
      CDistinct me sp -> CDistinct <$> mapM go me <*> pure sp
      CGroupBy k aggs n sp ->
        CGroupBy <$> go k <*> mapM (\(an, ae, au) -> (,,) an <$> go ae <*> mapM go au) aggs <*> pure n <*> pure sp
      CJoin l p src cond mInto sp ->
        CJoin l <$> rPattern env p <*> go src <*> go cond <*> pure mInto <*> pure sp

    goYield = \case
      YieldExpr e -> YieldExpr <$> go e
      YieldPair k v -> YieldPair <$> go k <*> go v

rPattern :: FixityEnv -> Pattern -> RW Pattern
rPattern env = goP
  where
    goP :: Pattern -> RW Pattern
    goP = \case
      POpChain p chain sp -> do
        p' <- goP p
        chain' <- mapM (\(op, q) -> (,) op <$> goP q) chain
        reassocPat sp p' chain'
      p@PWild {} -> pure p
      p@PVar {} -> pure p
      p@PLit {} -> pure p
      PAs n p -> PAs n <$> goP p
      PCtor r ps sp -> PCtor r <$> mapM goP ps <*> pure sp
      PCtorNamed r fs sp -> PCtorNamed r <$> mapM (\(n, mp) -> (,) n <$> mapM goP mp) fs <*> pure sp
      PActive r es p sp -> PActive r <$> mapM (rExpr env) es <*> goP p <*> pure sp
      PTuple ps sp -> PTuple <$> mapM goP ps <*> pure sp
      p@PUnit {} -> pure p
      PRecord fs rest sp -> PRecord <$> mapM (\(i, n, mp) -> (,,) i n <$> mapM goP mp) fs <*> pure rest <*> pure sp
      PTyped p t sp -> PTyped <$> goP p <*> rExpr env t <*> pure sp
      POr ps sp -> POr <$> mapM goP ps <*> pure sp
      PVariant n t w r sp -> PVariant n <$> mapM (rExpr env) t <*> pure w <*> pure r <*> pure sp

    -- Constructor-operator patterns: re-associate by fixity; all
    -- operators in a pattern chain must be infix constructors.
    reassocPat sp p0 chain = go1 p0 chain
      where
        go1 lhs [] = pure lhs
        go1 lhs ((op, rhs) : rest) =
          case infixOf env (nameText op) of
            Just f | fKind f == InfixR -> do
              -- right-assoc: fold the remainder first
              rhs' <- go1 rhs rest
              pure (mkCtorPat op lhs rhs')
            _ -> go1 (mkCtorPat op lhs rhs) rest
        mkCtorPat op l r = PCtor (CtorRef Nothing op) [l, r] sp
