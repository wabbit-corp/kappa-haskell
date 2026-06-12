-- | Surface abstract syntax (Spec Part II–IV).
--
-- Kappa is dependently typed, so the surface grammar of types and terms is
-- unified into one 'Expr' family; the elaborator interprets expressions in
-- type position. Operator applications are kept as flat 'EOpChain's at
-- parse time and re-associated during resolution, because fixity is
-- block-scoped and import-sensitive (§5.5.2) and therefore not known to a
-- single-pass parser.
module Kappa.Syntax
  ( Name (..)
  , ModPath (..)
  , modPathName
  , Quantity (..)
  , BorrowMark (..)
  , BinderPrefix (..)
  , emptyPrefix
  , Suspension (..)
  , Receiver (..)
  , Binder (..)
  , simpleBinder
  , Arg (..)
  , OpElem (..)
  , DotMember (..)
  , RecItem (..)
  , RecTypeField (..)
  , PatchItem (..)
  , PatchValue (..)
  , VariantArm (..)
  , Expr (..)
  , InterpPart (..)
  , CompKind (..)
  , ProjBody (..)
  , projBinderGroups
  , projYieldPlaces
  , surfaceThisRefs
  , surfaceVarNames
  , exprSpan
  , LetBind (..)
  , DoItem (..)
  , MatchCase (..)
  , HandlerCase (..)
  , ExceptCase (..)
  , CompClause (..)
  , CompYield (..)
  , OnConflict (..)
  , Pattern (..)
  , patternSpan
  , PatRest (..)
  , Lit (..)
  , CtorRef (..)
  , Decl (..)
  , Visibility (..)
  , DeclMods (..)
  , noMods
  , LetDef (..)
  , Decreases (..)
  , DataDecl (..)
  , CtorDecl (..)
  , TraitDecl (..)
  , TraitMember (..)
  , InstanceDecl (..)
  , EffectDecl (..)
  , EffectOp (..)
  , FixityDecl (..)
  , FixityKind (..)
  , ImportSpec (..)
  , ModuleRef (..)
  , ImportItem (..)
  , KindSelector (..)
  , ExceptItem (..)
  , ExpectForm (..)
  , Module (..)
  ) where

import Data.Data (Data)
import Data.List (nub)
import Data.Text (Text)
import Kappa.Source (Span (..))
import Kappa.Token (QuotedLit, StringLit)

-- | An identifier occurrence with its source span.
data Name = Name
  { nameText :: !Text
  , nameSpan :: !Span
  }
  deriving stock (Eq, Show, Data)

newtype ModPath = ModPath [Name]
  deriving stock (Eq, Show, Data)

modPathName :: ModPath -> [Text]
modPathName (ModPath ns) = map nameText ns

-- | Surface quantities (§12.1.1). @QTerm@ is a quantity expression
-- (a variable of classifier @Quantity@).
data Quantity
  = QZero
  | QOne
  | QOmega
  | QAtMostOne -- ^ @<=1@
  | QAtLeastOne -- ^ @>=1@
  | QTerm !Name
  deriving stock (Eq, Show, Data)

-- | @&@ or @&[region]@.
newtype BorrowMark = BorrowMark (Maybe Name)
  deriving stock (Eq, Show, Data)

data BinderPrefix = BinderPrefix
  { bpQuantity :: !(Maybe Quantity)
  , bpBorrow :: !(Maybe BorrowMark)
  }
  deriving stock (Eq, Show, Data)

emptyPrefix :: BinderPrefix
emptyPrefix = BinderPrefix Nothing Nothing

data Suspension = SuspThunk | SuspLazy
  deriving stock (Eq, Show, Data)

-- | Receiver marking on binders: @(this : T)@ / @(this x : T)@ (§12.1.1).
data Receiver
  = NoReceiver
  | ReceiverSelf
  | ReceiverNamed !Name
  deriving stock (Eq, Show, Data)

-- | A unified binder, used by lambdas, named-function parameters,
-- constructor parameters, Pi types, and trait\/data headers.
data Binder = Binder
  { bImplicit :: !Bool
  , bPrefix :: !BinderPrefix
  , bSusp :: !(Maybe Suspension)
  , bReceiver :: !Receiver
  , bInout :: !Bool
  , bName :: !(Maybe Name)
  -- ^ 'Nothing' for @_@ and the unit binder @()@.
  , bUnitBinder :: !Bool
  , bType :: !(Maybe Expr)
  , bDefault :: !(Maybe Expr)
  -- ^ Constructor parameter default (§10.1).
  , bSpan :: !Span
  }
  deriving stock (Show, Data)

simpleBinder :: Name -> Binder
simpleBinder n =
  Binder False emptyPrefix Nothing NoReceiver False (Just n) False Nothing Nothing (nameSpan n)

-- | One argument of an application spine (§16.1.7).
data Arg
  = ArgExplicit !Expr
  | ArgImplicit !Expr -- ^ @\@e@
  | ArgNamedBlock ![(Name, Maybe Expr)] !Span -- ^ @f { x = 1, y }@
  | ArgInout !Expr !Span -- ^ @~place@ (§18.9.3)
  deriving stock (Show, Data)

-- | Flat operator-chain element; re-associated by the resolver.
data OpElem
  = ChainOperand !Expr
  | ChainOp !Name
  deriving stock (Show, Data)

-- | The member position of a dotted chain step.
data DotMember
  = DotName !Name
  | DotOperator !Name -- ^ @d.(==)@
  deriving stock (Show, Data)

-- | Record-literal item: @x = e@, punning @x@, or implicit @\@ok = e@.
data RecItem = RecItem
  { riImplicit :: !Bool
  , riName :: !Name
  , riValue :: !(Maybe Expr)
  }
  deriving stock (Show, Data)

-- | Record-type field (§13.2.1).
data RecTypeField = RecTypeField
  { rtfOpaque :: !Bool
  , rtfImplicit :: !Bool
  , rtfPrefix :: !BinderPrefix
  , rtfSusp :: !(Maybe Suspension)
  , rtfName :: !Name
  , rtfType :: !Expr
  }
  deriving stock (Show, Data)

-- | Record-patch item (§13.2.5–§13.2.6).
data PatchItem
  = PatchUpdate ![(Bool, Name)] !PatchValue -- ^ path of (implicit?, seg) with @=@
  | PatchExtend !Name !Expr -- ^ @l := e@
  | PatchSection !Expr !Expr -- ^ @(.proj args) = e@
  | PatchPun !Name -- ^ bare @x@ (invalid, §13.2.5)
  deriving stock (Show, Data)

newtype PatchValue = PatchValue Expr
  deriving stock (Show, Data)

-- | One arm of a variant form @(| ... |)@: payload with optional
-- ascription. Interpretation (type vs injection) is position-dependent.
data VariantArm = VariantArm
  { vaExpr :: !Expr
  , vaType :: !(Maybe Expr)
  }
  deriving stock (Show, Data)

data Expr
  = EVar !Name
  | EHole !(Maybe Name) !Span -- ^ @_@ (expression position) or @?name@
  | EIntLit !Integer !(Maybe Name) !Span
  | EFloatLit !Double !(Maybe Name) !Span
  | EStringLit !StringLit ![InterpPart] !Span
  | EQuotedLit !QuotedLit !Span
  | EUnit !Span
  | ETuple ![Expr] !Span
  | ERecordLit ![RecItem] !Span
  | ERecordType ![RecTypeField] !(Maybe Expr) !Span
  | EApp !Expr ![Arg]
  | EDot !Expr !DotMember
  | EQDot !Expr !DotMember
  | ERecordPatch !Expr ![PatchItem] !Span
  | EReceiverSection ![DotMember] ![Arg] !Span -- ^ @(.f args)@
  | ESectionLeft !Expr !Name !Span -- ^ @(e op)@
  | ESectionRight !Name !Expr !Span -- ^ @(op e)@
  | EOpRef !(Maybe FixityKind) !Name !Span -- ^ @(op)@, @(infix -)@, @(prefix -)@
  | EOpChain ![OpElem]
  | EElvis !Expr !Expr !Span -- ^ @l ?: r@ (§16.1.2), built by the resolver
  -- ^ Alternating operands\/operators, re-associated at resolution.
  | ELambda !(Maybe Name) ![Binder] !Expr !Span
  | ELet ![LetBind] !Expr !Span -- ^ @let ... in@
  | EBlock ![Decl] !(Maybe Expr) !Span -- ^ pure @block@ (§9.3.1)
  | EDo !(Maybe Name) ![DoItem] !Span
  | EIf ![(Expr, Expr)] !(Maybe Expr) !Span
  | EMatch !Expr ![MatchCase] !Span
  | ETry !Expr ![ExceptCase] !(Maybe Expr) !Span
  | ETryMatch !Expr ![MatchCase] ![ExceptCase] !(Maybe Expr) !Span
  | EHandle !Bool !Expr !Expr ![HandlerCase] !Span -- ^ deep? label scrutinee cases
  | EIs !Expr !CtorRef
  | EThunk !Expr !Span
  | ELazy !Expr !Span
  | EForce !Expr !Span
  | ESeal !Expr !Expr !Span
  | EOpenExists !Expr ![Name] !Pattern !Expr !Span
  | ESealExists ![(Name, Expr)] !Expr !Expr !Span
  | EListLit ![Expr] !Span
  | ESetLit ![Expr] !Span
  | EMapLit ![(Expr, Expr)] !Span
  | EComprehension !CompKind ![CompClause] !CompYield !Span
  | EArrow !Binder !Expr -- ^ Pi: @(q x : A) -> B@ or @A -> B@
  | EForall ![Binder] !Expr !Span
  | EExists ![Binder] !Expr !Span
  | ETraitArrow !Expr !Expr -- ^ @C => T@
  | EEffRow ![(Name, Expr)] !(Maybe Expr) !Span
  | EVariant ![VariantArm] !(Maybe Expr) !Span
  | EOptionSugar !Expr !Span -- ^ @T?@
  | EAscription !Expr !Expr !Span -- ^ @(e : T)@
  | ECaptures !Expr ![Name] !Span
  | EBang !Expr !Span -- ^ @!e@ monadic splice
  | EQuote !Expr !Span -- ^ @'{ e }@
  | ECodeQuote !Expr !Span -- ^ @.< e >.@ staged code quotation (§23.2)
  | ECodeEscape !Expr !Span -- ^ @.~c@ escape inside a code quote (§23.2)
  | ESplice !Expr !Span -- ^ @$( e )@
  | ESpliceInQuote !Expr !Span -- ^ @${ e }@ inside a quote (§21.1)
  | EQuoteHole !Int !Span -- ^ internal: grafting slot of an elaborated quote
  | EImpossible !Span
  | EKindQualified !KindSelector !Name !Span -- ^ @type T@, @trait C@, ... (§7.1.1)
  | EModuleSig !Name !Span -- ^ @moduleSig M@ (§7.5)
  deriving stock (Show, Data)

-- | A parsed interpolation: index into the string fragments and the
-- parsed payload expression.
data InterpPart = InterpPart
  { ipIndex :: !Int
  , ipExpr :: !Expr
  }
  deriving stock (Show, Data)

data CompKind = CompList | CompSet | CompMap !(Maybe OnConflict) | CompCarrier !Expr
  deriving stock (Show, Data)

data CompClause
  = CFor !Bool !Bool !Pattern !Expr !Span
  -- ^ refutable? borrowedItems? pat source; @for x in &e@ is borrowed source
  | CLet !Bool !Pattern !(Maybe Expr) !Expr !Span -- ^ refutable? pat type rhs
  | CIf !Expr
  | COrderBy ![(Bool, Expr)] !Span -- ^ (descending?, key)
  | CSkip !Expr !Span
  | CTake !Expr !Span
  | CDistinct !(Maybe Expr) !Span
  | CGroupBy !Expr ![(Name, Expr, Maybe Expr)] !Name !Span -- ^ key, aggregates (name, expr, using), into
  | CJoin !Bool !Pattern !Expr !Expr !(Maybe Name) !Span -- ^ left? pat source on into
  deriving stock (Show, Data)

data CompYield
  = YieldExpr !Expr
  | YieldPair !Expr !Expr -- ^ map comprehension @yield k : v@
  deriving stock (Show, Data)

data OnConflict
  = KeepLast
  | KeepFirst
  | CombineUsing !Expr
  | CombineWith !Expr
  deriving stock (Show, Data)

data LetBind = LetBind
  { lbImplicit :: !Bool -- ^ @(\@q x : T) = e@ implicit local (§9.3)
  , lbPrefix :: !BinderPrefix
  , lbPattern :: !Pattern
  , lbType :: !(Maybe Expr)
  , lbExpr :: !Expr
  , lbSpan :: !Span
  }
  deriving stock (Show, Data)

data DoItem
  = DoBind !LetBind -- ^ @let pat <- e@ (lbExpr is the action)
  | DoLet !LetBind -- ^ @let pat = e@
  | DoLetQ !Pattern !Expr !(Maybe (Pattern, Expr)) !Span -- ^ @let? p = e [else rp -> fe]@
  | DoVar !Name !Expr !Span -- ^ @var x = e@
  | DoAssign !Name !Bool !Expr !Span -- ^ @x = e@ \/ @x <- e@ (monadic?)
  | DoExpr !Expr
  | DoUsing !(Maybe Span) !Pattern !Expr !Span
  -- ^ @using pat <- e@; the span flags an explicit quantity\/borrow
  -- prefix, which §9.3 forbids (using always binds borrowed at ω)
  | DoDefer !(Maybe Name) !Expr !Span -- ^ @defer[\@label] e@
  | DoReturn !(Maybe Name) !(Maybe Expr) !Span
  | DoBreak !(Maybe Name) !Span
  | DoContinue !(Maybe Name) !Span
  | DoWhile !(Maybe Name) !Expr ![DoItem] !(Maybe [DoItem]) !Span -- ^ label cond body else
  | DoFor !(Maybe Name) !Pattern !Expr ![DoItem] !(Maybe [DoItem]) !Span
  | DoIf ![(Expr, [DoItem])] !(Maybe [DoItem]) !Span -- ^ statement-if with suites
  | DoDecl !Decl -- ^ block-scope declaration (§18.2, §9.3.1)
  deriving stock (Show, Data)

data MatchCase
  = MatchCase !Pattern !(Maybe Expr) !Expr !Span -- ^ pat guard body
  | MatchImpossible !Span -- ^ @case impossible@
  deriving stock (Show, Data)

data HandlerCase
  = HandlerReturn !Pattern !Expr !Span
  | HandlerOp !Name ![Pattern] !Name !Expr !Span -- ^ op, arg pats, k, body
  deriving stock (Show, Data)

data ExceptCase = ExceptCase !Pattern !(Maybe Expr) !Expr !Span
  deriving stock (Show, Data)

data Pattern
  = PWild !Span
  | PVar !Name
  | PLit !Lit !Span
  | PAs !Name !Pattern
  | PCtor !CtorRef ![Pattern] !Span
  | PCtorNamed !CtorRef ![(Name, Maybe Pattern)] !Span
  | PActive !CtorRef ![Expr] !Pattern !Span -- ^ active pattern: head, args, view pattern
  | PTuple ![Pattern] !Span
  | PUnit !Span
  | PRecord ![(Bool, Name, Maybe Pattern)] !(Maybe PatRest) !Span
  | PTyped !Pattern !Expr !Span
  | POr ![Pattern] !Span
  | POpChain !Pattern ![(Name, Pattern)] !Span -- ^ infix ctor chains, e.g. @x :: xs@
  | PVariant !(Maybe Name) !(Maybe Expr) !Bool !(Maybe Name) !Span
  -- ^ @(| x : T |)@ \/ @(| x |)@ \/ @(| _ : T |)@ \/ @(| ..rest |)@:
  -- binder, type, isWild, restBinder
  deriving stock (Show, Data)

data PatRest = PatRestDiscard | PatRestBind !Name
  deriving stock (Show, Data)

data Lit
  = LInt !Integer !(Maybe Text)
  | LFloat !Double !(Maybe Text)
  | LString !Text
  | LScalar !Char
  deriving stock (Eq, Show, Data)

-- | A constructor reference: bare @C@ or type-scoped @T.C@.
data CtorRef = CtorRef
  { crQualifier :: !(Maybe Name)
  , crName :: !Name
  }
  deriving stock (Show, Data)

data Visibility = VisDefault | VisPublic | VisPrivate
  deriving stock (Eq, Show, Data)

data DeclMods = DeclMods
  { dmVisibility :: !Visibility
  , dmOpaque :: !Bool
  , dmScoped :: !Bool
  }
  deriving stock (Eq, Show, Data)

noMods :: DeclMods
noMods = DeclMods VisDefault False False

data Decl
  = DSig !DeclMods !Name !Expr !Span
  | DLet !DeclMods !LetDef !Span
  | DData !DeclMods !DataDecl !Span
  | DTypeAlias !DeclMods !Name ![Binder] !(Maybe Expr) !(Maybe Expr) !Span
  -- ^ name params kind rhs
  | DTrait !DeclMods !TraitDecl !Span
  | DInstance !InstanceDecl !Span
  | DDerive !Expr !Span -- ^ @derive Eq Foo@: applied trait expression
  | DEffect !DeclMods !EffectDecl !Span
  | DFixity !FixityDecl !Span
  | DImport ![ImportSpec] !Span
  | DExport ![ImportSpec] !Span
  | DExpect !DeclMods !ExpectForm !Span
  | DPattern !DeclMods !LetDef !Span -- ^ active-pattern definition (§17.3.1)
  | DProjection !DeclMods !Name ![Binder] !Expr !ProjBody !Span
  | DTopSplice !Expr !Span -- ^ top-level @$( ... )@ (§21.2)
  deriving stock (Show, Data)

data ProjBody
  = ProjSelector !Expr -- ^ selector body (yield\/if\/match expression form)
  | ProjAccessors ![(Text, Maybe Binder, Expr)] -- ^ get\/set\/inout\/sink clauses
  deriving stock (Show, Data)

-- | Recover the §9.1.1 binder structure of a projection declaration:
-- a @(place x : T)@ group parses as two same-span binders, the first
-- spelled @place@. Returns the effective explicit binders in
-- declaration order, flagged with whether each is a place binder
-- (the @place@ marker and any receiver spelling are collapsed away).
projBinderGroups :: [Binder] -> [(Bool, Binder)]
projBinderGroups = go
  where
    go [] = []
    go (b : rest)
      | Just n <- bName b
      , nameText n == "place"
      , (grp@(_ : _), rest') <- span (\b' -> bSpan b' == bSpan b) rest =
          (True, last grp) : go rest'
      | otherwise = (False, b) : go rest

-- | Surface §13.2.1 sibling references: the labels of @this.label@
-- occurrences in an expression.
surfaceThisRefs :: Expr -> [Text]
surfaceThisRefs = nub . go
  where
    go = \case
      EDot (EVar b) (DotName l)
        | nameText b == "this" -> [nameText l]
      EDot e _ -> go e
      EQDot e _ -> go e
      EVar _ -> []
      EApp f args -> go f ++ concatMap goArg args
      EAscription e t _ -> go e ++ go t
      EArrow b e -> maybe [] go (bType b) ++ go e
      EForall bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      EExists bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      ETraitArrow a b -> go a ++ go b
      ETuple es _ -> concatMap go es
      ERecordLit items _ -> concat [go e | RecItem _ _ (Just e) <- items]
      ERecordType rfs mtail _ ->
        concatMap (go . rtfType) rfs ++ maybe [] go mtail
      EOptionSugar e _ -> go e
      EVariant arms mtail _ ->
        concatMap (go . vaExpr) arms ++ maybe [] go mtail
      EOpChain els -> concat [go x | ChainOperand x <- els]
      EIf alts mels _ -> concat [go c ++ go b | (c, b) <- alts] ++ maybe [] go mels
      ECaptures e _ _ -> go e
      EElvis a b _ -> go a ++ go b
      ESectionLeft e _ _ -> go e
      ESectionRight _ e _ -> go e
      EThunk e _ -> go e
      ELazy e _ -> go e
      EForce e _ -> go e
      EListLit es _ -> concatMap go es
      ERecordPatch e items _ ->
        go e
          ++ concat
            [ case it of
                PatchUpdate _ (PatchValue v) -> go v
                PatchExtend _ v -> go v
                PatchSection r v -> go r ++ go v
                PatchPun _ -> []
            | it <- items
            ]
      _ -> []
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      ArgInout e _ -> go e
      ArgNamedBlock items _ -> concat [maybe [] go me | (_, me) <- items]

-- | The bare identifiers a surface type/initializer expression
-- mentions in head positions (§13.2.1 bare sibling-reference
-- shorthand candidates). Conservative: does not account for shadowing
-- under inner binders.
surfaceVarNames :: Expr -> [Text]
surfaceVarNames = nub . go
  where
    go = \case
      EVar n -> [nameText n]
      EDot e _ -> go e
      EQDot e _ -> go e
      EApp f args -> go f ++ concatMap goArg args
      EAscription e t _ -> go e ++ go t
      EArrow b e -> maybe [] go (bType b) ++ go e
      EForall bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      EExists bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      ETraitArrow a b -> go a ++ go b
      ETuple es _ -> concatMap go es
      ERecordLit items _ -> concat [go e | RecItem _ _ (Just e) <- items]
      ERecordType rfs mtail _ ->
        concatMap (go . rtfType) rfs ++ maybe [] go mtail
      EOptionSugar e _ -> go e
      EVariant arms mtail _ ->
        concatMap (go . vaExpr) arms ++ maybe [] go mtail
      EOpChain els -> concat [go x | ChainOperand x <- els]
      EIf alts mels _ -> concat [go c ++ go b | (c, b) <- alts] ++ maybe [] go mels
      ECaptures e _ _ -> go e
      EElvis a b _ -> go a ++ go b
      ESectionLeft e _ _ -> go e
      ESectionRight _ e _ -> go e
      EThunk e _ -> go e
      ELazy e _ -> go e
      EForce e _ -> go e
      EListLit es _ -> concatMap go es
      _ -> []
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      ArgInout e _ -> go e
      ArgNamedBlock items _ -> concat [maybe [] go me | (_, me) <- items]

-- | The stable places a selector-form projection body yields: pairs of
-- (root binder name, field-path suffix). Yields whose operand is not a
-- variable-rooted dotted path are reported as 'Left' spans.
projYieldPlaces :: Expr -> [Either Span (Text, [Text])]
projYieldPlaces = go
  where
    go = \case
      EApp (EVar y) [ArgExplicit e]
        | nameText y == "yield" -> [classify e]
      EIf alts mels _ ->
        concatMap (go . snd) alts ++ maybe [] go mels
      EMatch _ cases _ ->
        concat [go body | MatchCase _ _ body _ <- cases]
      EBlock _ (Just fin) _ -> go fin
      EAscription e _ _ -> go e
      e -> [Left (exprSpan e)]
    classify e = case placePath e of
      Just (root, path) -> Right (root, path)
      Nothing -> Left (exprSpan e)
    placePath = \case
      EVar n -> Just (nameText n, [])
      EDot b (DotName f) -> do
        (root, path) <- placePath b
        Just (root, path ++ [nameText f])
      EAscription e _ _ -> placePath e
      _ -> Nothing

data LetDef = LetDef
  { ldName :: !(Maybe Name) -- ^ 'Just' for named definitions
  , ldImplicit :: !Bool -- ^ @let (\@q x : T) = e@ implicit local (§9.3)
  , ldPattern :: !(Maybe Pattern) -- ^ 'Just' for pattern bindings
  , ldPrefix :: !BinderPrefix -- ^ @let 1 pat = e@ / @let & pat = e@ prefix (§12.2, §12.3.1)
  , ldBinders :: ![Binder]
  , ldResultType :: !(Maybe Expr)
  , ldDecreases :: !(Maybe Decreases)
  , ldBody :: !Expr
  }
  deriving stock (Show, Data)

data Decreases
  = DecMeasure !Expr !(Maybe Expr) !(Maybe Expr) -- ^ measure [by R] [using proof]
  | DecStructural ![Name]
  deriving stock (Show, Data)

data DataDecl = DataDecl
  { ddName :: !Name
  , ddParams :: ![Binder]
  , ddKind :: !(Maybe Expr)
  , ddCtors :: ![CtorDecl]
  }
  deriving stock (Show, Data)

data CtorDecl = CtorDecl
  { cdName :: !Name
  , cdBinders :: ![Binder] -- ^ positional fields become unnamed binders
  , cdGadtType :: !(Maybe Expr) -- ^ GADT-style result signature (§10.2)
  , cdSpan :: !Span
  }
  deriving stock (Show, Data)

data TraitDecl = TraitDecl
  { trSupers :: ![Expr] -- ^ supertrait context @C1, ..., Cn =>@
  , trName :: !Name
  , trParams :: ![Binder]
  , trMembers :: ![TraitMember]
  }
  deriving stock (Show, Data)

data TraitMember
  = TraitSig !Name !Expr !Span
  | TraitDefault !LetDef !Span
  deriving stock (Show, Data)

data InstanceDecl = InstanceDecl
  { inPremises :: ![Expr] -- ^ @Eq a =>@ premises
  , inHead :: !Expr
  , inMembers :: ![Decl] -- ^ member signatures and definitions
  }
  deriving stock (Show, Data)

data EffectDecl = EffectDecl
  { effName :: !Name
  , effParams :: ![Binder]
  , effOps :: ![EffectOp]
  , effIsLabelDecl :: !Bool -- ^ @effect label l : E@ form
  , effLabelType :: !(Maybe Expr)
  }
  deriving stock (Show, Data)

data EffectOp = EffectOp
  { eoQuantity :: !(Maybe Quantity)
  , eoName :: !Name
  , eoType :: !Expr
  , eoSpan :: !Span
  }
  deriving stock (Show, Data)

data FixityDecl = FixityDecl
  { fxKind :: !FixityKind
  , fxPrec :: !Int
  , fxOp :: !Name
  }
  deriving stock (Show, Data)

data FixityKind
  = InfixN
  | InfixL
  | InfixR
  | Prefix
  | Postfix
  deriving stock (Eq, Show, Data)

data ModuleRef
  = RefPath !ModPath
  | RefUrl !Text !Span
  deriving stock (Show, Data)

data ImportSpec
  = ImportModule !ModuleRef !(Maybe Name) -- ^ @import M [as A]@
  | ImportItems !ModuleRef ![ImportItem]
  | ImportAll !ModuleRef ![ExceptItem]
  | ImportSingleton !ModuleRef !Name -- ^ @import M.x@ sugar (disambiguated semantically, §8.3)
  deriving stock (Show, Data)

data ImportItem = ImportItem
  { iiUnhide :: !Bool
  , iiClarify :: !Bool
  , iiKind :: !(Maybe KindSelector)
  , iiName :: !Name
  , iiCtorAll :: !Bool -- ^ @T(..)@
  , iiAlias :: !(Maybe Name)
  }
  deriving stock (Show, Data)

data KindSelector = SelTerm | SelType | SelTrait | SelCtor | SelEffectLabel | SelModule
  deriving stock (Eq, Show, Data)

data ExceptItem = ExceptItem !(Maybe KindSelector) !Name
  deriving stock (Show, Data)

data ExpectForm
  = ExpectTerm !Name !Expr
  | ExpectType !Name ![Binder] !(Maybe Expr)
  | ExpectData !Name ![Binder] !(Maybe Expr)
  | ExpectTrait !Name ![Binder] !(Maybe Expr)
  deriving stock (Show, Data)

-- | A parsed source file.
data Module = Module
  { modAttrs :: ![Name]
  , modHeader :: !(Maybe ModPath)
  , modDecls :: ![Decl]
  }
  deriving stock (Show, Data)

exprSpan :: Expr -> Span
exprSpan = \case
  EVar n -> nameSpan n
  EHole _ sp -> sp
  EIntLit _ _ sp -> sp
  EFloatLit _ _ sp -> sp
  EStringLit _ _ sp -> sp
  EQuotedLit _ sp -> sp
  EUnit sp -> sp
  ETuple _ sp -> sp
  ERecordLit _ sp -> sp
  ERecordType _ _ sp -> sp
  EApp f args -> case args of
    [] -> exprSpan f
    _ -> exprSpan f `spanTo` lastArgSpan (last args)
  EDot e m -> exprSpan e `spanTo` memberSpan m
  EQDot e m -> exprSpan e `spanTo` memberSpan m
  ERecordPatch _ _ sp -> sp
  EReceiverSection _ _ sp -> sp
  ESectionLeft _ _ sp -> sp
  ESectionRight _ _ sp -> sp
  EOpRef _ _ sp -> sp
  EElvis _ _ sp -> sp
  EOpChain els -> case els of
    -- the parser builds chains from at least one operand ('pChainElems')
    [] -> error "Kappa.Syntax.exprSpan: internal error: empty operator chain"
    (e : _) -> elemSpan e `spanTo` elemSpan (last els)
  ELambda _ _ _ sp -> sp
  ELet _ _ sp -> sp
  EBlock _ _ sp -> sp
  EDo _ _ sp -> sp
  EIf _ _ sp -> sp
  EMatch _ _ sp -> sp
  ETry _ _ _ sp -> sp
  ETryMatch _ _ _ _ sp -> sp
  EHandle _ _ _ _ sp -> sp
  EIs e c -> exprSpan e `spanTo` nameSpan (crName c)
  EThunk _ sp -> sp
  ELazy _ sp -> sp
  EForce _ sp -> sp
  ESeal _ _ sp -> sp
  EOpenExists _ _ _ _ sp -> sp
  ESealExists _ _ _ sp -> sp
  EListLit _ sp -> sp
  ESetLit _ sp -> sp
  EMapLit _ sp -> sp
  EComprehension _ _ _ sp -> sp
  EArrow b e -> bSpan b `spanTo` exprSpan e
  EForall _ _ sp -> sp
  EExists _ _ sp -> sp
  ETraitArrow a b -> exprSpan a `spanTo` exprSpan b
  EEffRow _ _ sp -> sp
  EVariant _ _ sp -> sp
  EOptionSugar _ sp -> sp
  EAscription _ _ sp -> sp
  ECaptures _ _ sp -> sp
  EBang _ sp -> sp
  EQuote _ sp -> sp
  ECodeQuote _ sp -> sp
  ECodeEscape _ sp -> sp
  ESplice _ sp -> sp
  ESpliceInQuote _ sp -> sp
  EQuoteHole _ sp -> sp
  EImpossible sp -> sp
  EKindQualified _ _ sp -> sp
  EModuleSig _ sp -> sp
  where
    memberSpan (DotName n) = nameSpan n
    memberSpan (DotOperator n) = nameSpan n
    elemSpan (ChainOperand e) = exprSpan e
    elemSpan (ChainOp n) = nameSpan n
    lastArgSpan = \case
      ArgExplicit e -> exprSpan e
      ArgImplicit e -> exprSpan e
      ArgNamedBlock _ sp -> sp
      ArgInout _ sp -> sp

spanTo :: Span -> Span -> Span
spanTo a b = a {spanEnd = spanEnd b}

patternSpan :: Pattern -> Span
patternSpan = \case
  PWild sp -> sp
  PVar n -> nameSpan n
  PLit _ sp -> sp
  PAs n p -> nameSpan n `spanTo` patternSpan p
  PCtor _ _ sp -> sp
  PCtorNamed _ _ sp -> sp
  PActive _ _ _ sp -> sp
  PTuple _ sp -> sp
  PUnit sp -> sp
  PRecord _ _ sp -> sp
  PTyped _ _ sp -> sp
  POr _ sp -> sp
  POpChain _ _ sp -> sp
  PVariant _ _ _ _ sp -> sp
