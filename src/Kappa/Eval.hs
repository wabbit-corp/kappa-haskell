{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Normalization by evaluation and definitional equality (Spec §31.1).
--
-- This is the engine the type checker leans on to decide when two types are
-- "the same." The round-trip is: 'eval' a 'Term' into a 'Value' (β-reducing
-- for free via Haskell 'Closure's), 'force' a value to expose its head, and
-- 'quote' a value back into a normalized 'Term'. 'convertible' compares two
-- values directly. (Background: docs/CONCEPTS.md.)
--
-- Conversion (definitional equality) includes β, δ (transparent
-- conversion-reducible definitions only), ι (match\/if reduction on known
-- scrutinees), record\/variant canonical-form equality, suspension
-- reduction (@force (thunk e) ↦ e@), and function η. Quantities participate
-- in Pi identity. Normalization is fuel-bounded for safety but only ever
-- answers "equal" soundly.
module Kappa.Eval
  ( Globals (..)
  , GlobalDef (GlobalDefData, GlobalDef, gdUniverses, gdProvisionalUniverseProjection, gdObservationMode, gdNominalSummary, gdType, gdCoreType, gdValue, gdCoreBody, gdRecordInterface, gdReducible)
  , globalDefWithObservationMode
  , globalDefWithUniverses
  , globalDefWithCoreType
  , globalDefWithCoreBody
  , globalDefWithNominalSummary
  , globalDefinitionBodyUniversesReplayable
  , specializeGlobalDefinitionBody
  , specializeGlobalDefinitionTypePrefix
  , MetaState
  , emptyMetas
  , EvalCtx (..)
  , RigidFact (..)
  , eval
  , evalApp
  , force
  , quote
  , convertible
  , canonicalEqualityPayload
  , globalSpineRelevantPairs
  , matchPat
  , vapp
  , vproj
  , evalPurePrim
  , evalPrimCtx
  , lookupEnv
  ) where

import Control.Monad (guard)
import Data.Bits (xor, (.&.), (.|.))
import qualified Data.ByteString as BS
import Data.Char (chr, ord)
import Data.List (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import Data.Word (Word64, Word8)
import GHC.Float (castDoubleToWord64)
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import Kappa.Builtins
import Kappa.Core
import Kappa.Observation (ObservationMode (..))
import Kappa.CoreOps (levelMetasOfTerm, zonkTermWith)
import Kappa.Level (LevelMeta, compareClosedLevel, instantiateLocalLevelParams, normalizeLevel, substituteLevelMetas, substituteLevelParams)
import Kappa.NominalVariance (NominalCumulativitySummary)
import Kappa.Unicode
  ( NormForm (..)
  , graphemeClusters
  , isSingleGrapheme
  , normalizeText
  , sentenceChunks
  , wordChunks
  )
import Numeric (showFFloat, showHex)

-- | Recover the carrier and endpoints of the canonical equality family from
-- its checked semantic application. Declaration-universe instantiation and
-- explicit cumulative lifts are representation details; the term telescope
-- remains @(0 A : Type u) -> A -> A -> Type u@.
--
-- This is not a proof rule. User-defined equality families are handled by the
-- ordinary h-level and constructor machinery; consumers use this query only
-- for standard-library facts whose semantic identity is exactly 'prelEqType'.
canonicalEqualityPayload :: EvalCtx -> Value -> Maybe (Value, Value, Value)
canonicalEqualityPayload ctx = go
  where
    go = \case
      VUniverseLift _ _ _ proposition -> go proposition
      VGlobI equality _ spine
        | equality == prelEqType ->
            case reverse spine of
              (Expl, rhs) : (Expl, lhs) : (Impl, carrier) : _ ->
                Just (carrier, lhs, rhs)
              _ -> Nothing
      value ->
        case force ctx value of
          VUniverseLift _ _ _ proposition -> go proposition
          VGlobI equality _ spine
            | equality == prelEqType ->
                case reverse spine of
                  (Expl, rhs) : (Expl, lhs) : (Impl, carrier) : _ ->
                    Just (carrier, lhs, rhs)
                  _ -> Nothing
          _ -> Nothing

-- §6.1.7: the C libm 'atan2', imported so the interpreter produces the EXACT
-- same binary64 as the C/LLVM backends (which call kp_atan2 over the same
-- libm).  GHC's own 'Data.atan2'/'RealFloat' 'atan2' can round differently in
-- the last ULP on some platforms (atan2 1 2 disagrees by 1 ULP), which would
-- break the interp == C == LLVM byte-for-byte parity; every other libm prim
-- (sqrt/sin/cos/tan/asin/acos/atan/exp/log/pow) already agrees bit-for-bit, so
-- only atan2 needs the FFI bridge.
foreign import ccall unsafe "math.h atan2"
  c_atan2 :: Double -> Double -> Double

-- | One global definition.
data GlobalDef = GlobalDefData
  { gdUniverses :: !DeclarationUniverseTelescope
  , gdProvisionalUniverseProjection :: ![(LevelMeta, Int)]
  -- ^ Source-meta to occurrence-spine projection for an inferred declaration.
  -- Before SCC finalization it covers the complete provisional source spine,
  -- so reducible occurrences freshen every interface meta. Finalization
  -- replaces it with the exact retained source-meta to stable hidden-telescope
  -- projection; discarded provisional positions never become final params.
  , gdObservationMode :: !ObservationMode
  , gdNominalSummary :: !(Maybe NominalCumulativitySummary)
  , gdType :: !Value
  , gdCoreType :: !(Maybe Term)
  -- ^ Closed generalized Core type when one exists. NbE deliberately erases
  -- universe-lift and proof evidence, so serialization and declaration
  -- generalization must prefer this authority over re-quoting 'gdType'.
  , gdValue :: !(Maybe Value)
  -- ^ 'Nothing' for primitives\/postulates and opaque-at-use-site defs.
  , gdCoreBody :: !(Maybe Term)
  -- ^ Closed generalized Core body when one exists. Universe specialization
  -- uses this authority directly instead of re-quoting an NbE closure, whose
  -- captured environments are intentionally not serialized by 'quote'.
  , gdRecordInterface :: !(Maybe Term)
  -- ^ Closed checked structural record interface when NbE is intentionally
  -- lossy. In particular, an all-erased trait dictionary evaluates to unit,
  -- but KCore still needs its field telescope to verify projections and
  -- dictionary literals independently.
  , gdReducible :: !Bool
  -- ^ Conversion-reducible (§15.1): may δ-unfold during conversion.
  }

pattern GlobalDef :: Value -> Maybe Value -> Bool -> GlobalDef
pattern GlobalDef ty value reducible <- GlobalDefData _ _ _ _ ty _ value _ _ reducible
  where
    GlobalDef ty value reducible =
      GlobalDefData emptyDeclarationUniverseTelescope [] Ordinary Nothing ty Nothing value Nothing Nothing reducible

{-# COMPLETE GlobalDef #-}

globalDefWithUniverses :: DeclarationUniverseTelescope -> GlobalDef -> GlobalDef
globalDefWithUniverses universes def = def {gdUniverses = universes}

globalDefWithCoreType :: Term -> GlobalDef -> GlobalDef
globalDefWithCoreType coreType def = def {gdCoreType = Just coreType}

globalDefWithObservationMode :: ObservationMode -> GlobalDef -> GlobalDef
globalDefWithObservationMode mode def = def {gdObservationMode = mode}

globalDefWithCoreBody :: Term -> GlobalDef -> GlobalDef
globalDefWithCoreBody body def = def {gdCoreBody = Just body}

globalDefWithNominalSummary :: NominalCumulativitySummary -> GlobalDef -> GlobalDef
globalDefWithNominalSummary summary def = def {gdNominalSummary = Just summary}

-- | Specialize the leading declaration-universe prefix selected by an
-- enclosing nominal occurrence while leaving any declaration-local suffix
-- polymorphic. Trait members use this when the trait occurrence fixes the
-- trait's universes but the member generalized additional levels of its own.
specializeGlobalDefinitionTypePrefix :: EvalCtx -> [Level] -> GlobalDef -> Maybe Value
specializeGlobalDefinitionTypePrefix ctx universes definition
  | length universes > dutParameterCount (gdUniverses definition) = Nothing
  | null universes = Just (gdType definition)
  | otherwise =
      let raw = quote (ctx {ecFacts = Map.empty}) 0 (gdType definition)
          specialized =
            zonkTermWith (\_ _ -> Nothing) (substituteLevelParams universes) 0 raw
       in Just (eval ctx [] specialized)

-- | Specialize a retained Core body at one occurrence of its declaration
-- universe telescope.  Consumers that inspect transparent Core must share
-- this operation: some bodies still carry the declaration's provisional meta
-- projection, while finalized bodies carry stable level parameters.
specializeGlobalDefinitionBody :: [Level] -> GlobalDef -> Maybe Term
specializeGlobalDefinitionBody universes definition = do
  body <- gdCoreBody definition
  let projection = gdProvisionalUniverseProjection definition
  pure $
    if null universes
      then body
      else
        if not (null projection)
            && all ((< length universes) . snd) projection
            && any (`elem` map fst projection) (levelMetasOfTerm body)
          then
            zonkTermWith
              (\_ _ -> Nothing)
              (substituteLevelMetas (Map.fromList [(meta, universes !! index) | (meta, index) <- projection]))
              0
              body
          else
            zonkTermWith
              (\_ _ -> Nothing)
              (substituteLevelParams universes)
              0
              body

-- | A transparent global body may cross a declaration boundary only when its
-- universe occurrence is replayable in full. Before SCC finalization, the
-- declaration projection records source-interface metas, but the body can also
-- contain nested occurrence metas introduced by transparent dependencies. Such
-- metas belong to the declaration's pending solver component and cannot be
-- freshened from the caller's universe spine. Delta-reducing that body would
-- leak those local identities into another declaration's retained Core.
--
-- Finalized bodies contain rigid 'LParam's (and therefore no level metas);
-- monomorphic bodies likewise pass directly. A provisional body is reducible
-- only when every level meta is authenticated by its source projection.
globalDefinitionBodyUniversesReplayable :: GlobalDef -> Bool
globalDefinitionBodyUniversesReplayable definition =
  case gdCoreBody definition of
    Nothing -> True
    Just body ->
      let projected =
            Set.fromList (map fst (gdProvisionalUniverseProjection definition))
       in Set.fromList (levelMetasOfTerm body) `Set.isSubsetOf` projected

newtype Globals = Globals {globalsMap :: Map GName GlobalDef}

type MetaState = Map MetaId (Maybe Value)

emptyMetas :: MetaState
emptyMetas = Map.empty

-- | Branch-local fact about a rigid variable, established by the
-- enclosing match case (§7.4.1 flow refinement at conversion level):
-- either solved to a constructor value, or known to lack constructors.
data RigidFact = FactIs !Value | FactNot ![GName]

-- | Evaluation context: globals plus current meta solutions.
data EvalCtx = EvalCtx
  { ecGlobals :: !Globals
  , ecMetas :: !MetaState
  , ecRuntime :: !Bool
  -- ^ Runtime evaluation (§32.1): every global with a value unfolds,
  -- with a deep fuel budget. Conversion-time forcing (False) unfolds
  -- only conversion-reducible definitions and stays tightly bounded.
  , ecFacts :: !(Map Int RigidFact)
  -- ^ Branch-local facts about rigid levels (dependent-match
  -- normalization; see Check.checkMatchPlain).
  }

lookupGlobal :: EvalCtx -> GName -> Maybe GlobalDef
lookupGlobal ctx g = Map.lookup g (globalsMap (ecGlobals ctx))

-- | Align two occurrences of one checked global and return the arguments
-- whose values participate in definitional equality.  Generated
-- declaration-universe proofs are an authenticated leading prefix: their
-- propositions are part of the global interface, but §11.1.2.3A explicitly
-- excludes the arbitrary witness identity from interface semantics.  All
-- other implicit and explicit arguments remain relevant.
globalSpineRelevantPairs
  :: EvalCtx
  -> GName
  -> [(Icit, Value)]
  -> [(Icit, Value)]
  -> Maybe [(Value, Value)]
globalSpineRelevantPairs ctx global left right = do
  guard (length left == length right)
  guard (and (zipWith (\(leftIcit, _) (rightIcit, _) -> leftIcit == rightIcit) left right))
  let proofCount =
        maybe 0 (maybe 0 generatedProofPrefixLength . gdCoreType) (lookupGlobal ctx global)
      skipped = min proofCount (length left)
  pure
    [ (leftValue, rightValue)
    | ((_, leftValue), (_, rightValue)) <- zip (drop skipped left) (drop skipped right)
    ]
  where
    generatedProofPrefixLength = \case
      CPiEvidenceM _ _ Impl Q0 _ _ (Just _) BinderGenerated _ codomain ->
        1 + generatedProofPrefixLength codomain
      _ -> 0

-- ── Evaluation ───────────────────────────────────────────────────────

-- | Checked de Bruijn lookup. An out-of-range index is an elaborator
-- bug; fail with context instead of a bare 'Prelude.!!' pattern error.
lookupEnv :: HasCallStack => Int -> Env -> Value
lookupEnv i env = case drop i env of
  v : _ -> v
  [] ->
    error
      ("Kappa.Eval.lookupEnv: internal error: de Bruijn index " ++ show i
         ++ " out of range (environment has " ++ show (length env) ++ " entries)\n"
         ++ prettyCallStack callStack)

-- | Evaluate a 'Term' to a 'Value' under an environment @env@ (one entry
-- per enclosing binder, innermost first — so a 'CVar' index is just a list
-- lookup). A lambda body and a Pi /codomain/ aren't entered here; they
-- capture @env@ in a 'Closure' and defer (the Pi /domain/ is still evaluated
-- eagerly). Deferring the body is what makes β-reduction fall out of
-- 'closApply'\/'vapp' for free.
eval :: HasCallStack => EvalCtx -> Env -> Term -> Value
eval ctx env = \case
  CVar i -> lookupEnv i env
  CLocal i [] -> lookupEnv i env
  CLocal i universes ->
    -- Local declaration universes are static identity, not term arguments.
    -- Specialize the generalized semantic value at the occurrence before it
    -- participates in conversion; runtime lowering erases the same spine.
    let generalized = lookupEnv i env
        generalizedTerm = quote ctx (length env) generalized
        specialized =
          zonkTermWith
            (\_ _ -> Nothing)
            (instantiateLocalLevelParams (length universes) (map (evalLevel ctx env) universes))
            0
            generalizedTerm
     in eval ctx env specialized
  -- primitives quoted by 'quote' round-trip back to 'VPrim'
  CGlobal g@(GName m p) universes ->
    if m == primModule
      then VPrim p []
      else VGlobal g (map (evalLevel ctx env) universes) []
  CLamM mode ic q n body -> VLamM mode ic q n (Closure env body)
  CPiRuntimeM mode formation ic q brw n assumption origin runtimeErasure a b ->
    VPiRuntimeM mode formation ic q brw n
      (fmap (\(lower, upper) -> (evalLevel ctx env lower, evalLevel ctx env upper)) assumption)
      origin
      (fmap (eval ctx env) runtimeErasure)
      (eval ctx env a)
      (Closure env b)
  CApp ic f a -> vapp ctx (eval ctx env f) ic (eval ctx env a)
  CSort n -> VSort (evalLevel ctx env n)
  CLevel n -> VLevel (evalLevel ctx env n)
  CUniverseLift from to evidence t
    | ecRuntime ctx -> eval ctx env t
    | otherwise ->
        let resolve = evalLevel ctx env
         in VUniverseLift
              (resolve from)
              (resolve to)
              (mapUniverseEvidenceLevels resolve evidence)
              (eval ctx env t)
  CSchemaLift _ _ _ _ _ _ _ _ t -> eval ctx env t
  CArithmeticProof certificate ->
    VArithmeticProof (mapArithmeticCertificate (eval ctx env) certificate)
  CLit l -> VLit l
  -- The head-type annotation remains observe-only, but universes and the
  -- complete typed argument spine survive in the semantic domain so quoting
  -- cannot turn a polymorphic constructor occurrence into a monomorphic one.
  CCtorI g universes _ arguments ->
    VCtorI g (map (evalLevel ctx env) universes)
      [ ConstructorValueArg (caIcit argument) (caPayload argument) (caName argument)
          (eval ctx env (caTerm argument))
      | argument <- arguments
      ]
  CMatch scrut scrutineeAnnotation resultAnnotation alts ->
    reduceMatch
      ctx
      (eval ctx env scrut)
      (eval ctx env <$> scrutineeAnnotation)
      (eval ctx env <$> resultAnnotation)
      alts
      env
  CRecordTQ fs -> VRecordTQ (map (fmap (eval ctx env)) fs)
  CRecordV fs -> VRecordV [(n, eval ctx env t) | (n, t) <- fs]
  CProjM mode e f -> vproj ctx mode (eval ctx env e) f
  -- P0.4: the fixed-offset index is a backend-only hint; the interpreter
  -- projects by NAME exactly as for CProj (so check/run/test are unchanged).
  CProjAtM mode e f _ -> vproj ctx mode (eval ctx env e) f
  CVariantT ms -> VVariantT (map (eval ctx env) ms)
  CInject tag e -> VInject tag (eval ctx env e)
  CLetRuntimeM _ _ _ _ _ rhs body -> eval ctx (eval ctx env rhs : env) body
  CLetRecRuntimeM _ _ _ _ _ rhs body ->
    -- recursive local definition: tie the knot lazily (the rhs is a
    -- lambda, so forcing the binding terminates)
    let env' = eval ctx env' rhs : env in eval ctx env' body
  CLetPolyRuntimeM _ _ _ _ _ _ rhs body ->
    eval ctx (eval ctx env rhs : env) body
  CLetRecPolyRuntimeM _ _ _ _ _ _ rhs body ->
    let env' = eval ctx env' rhs : env in eval ctx env' body
  CLetRecGroupM _ definitions body ->
    let values = [eval ctx env' (clrdRhs definition) | definition <- definitions]
        env' = reverse values ++ env
     in eval ctx env' body
  CMeta m -> case Map.lookup m (ecMetas ctx) of
    Just (Just v) -> v
    _ -> VFlex m []
  CDo lbl items -> VDoV lbl items env
  CSealE ls e -> VSealV ls (eval ctx env e)
  CSigT ls e -> VSigT ls (eval ctx env e)
  CThunkE e _ -> VThunkV (Closure env e)
  CLazyE e _ -> VLazyV (Closure env e)
  CForceE e _ -> vforce ctx (eval ctx env e)
  CIf c t f ->
    case force ctx (eval ctx env c) of
      VCtor g [] | g == prelTrue -> eval ctx env t
      VCtor g [] | g == prelFalse -> eval ctx env f
      v -> VIfN v (Closure env t) (Closure env f)
  CQuote qs slots -> VQuote qs (map (eval ctx env) slots)

closApply :: EvalCtx -> Closure -> Value -> Value
closApply ctx (Closure env body) v = eval ctx (v : env) body

vapp :: EvalCtx -> Value -> Icit -> Value -> Value
vapp ctx fv ic av = case fv of
  VLam _ _ _ clo -> closApply ctx clo av
  VRigid l sp -> VRigid l (sp ++ [(ic, av)])
  VFlex m sp -> VFlex m (sp ++ [(ic, av)])
  VGlobI g universes sp -> VGlobI g universes (sp ++ [(ic, av)])
  -- implicit arguments are erased at runtime for constructors and
  -- primitives (§31.2); neutral globals keep them (types).
  VCtorI g universes arguments
    | ic == Impl -> VCtorI g universes arguments
    | otherwise ->
        VCtorI g universes
          (arguments ++ [ConstructorValueArg Expl True Nothing av])
  VPrim p args
    | ic == Impl -> VPrim p args
    | otherwise ->
        -- Force ONLY the freshly-appended argument and keep the existing
        -- spine as-is. The existing args were each forced as they were
        -- appended, so 'evalPrimCtx' sees forced arguments without the
        -- previous @map (force) args'@ that re-forced the entire prefix on
        -- every append — a per-append re-descent that compounded to
        -- exponential time on deep neutral spines (e.g. left-nested
        -- @addInt (… ) 1@ / left-associative operator chains).
        let av' = force ctx av
            args' = args ++ [av']
         in case evalPrimCtx ctx p args' of
              Just v -> v
              Nothing -> VPrim p args'
  -- stuck application: keep the icit so 'force' can re-apply once the
  -- head becomes canonical (e.g. a solved meta's dictionary projection).
  _ -> VAppN ic fv av

instantiateGlobalValue :: EvalCtx -> [Level] -> GlobalDef -> Value
instantiateGlobalValue ctx universes definition
  | null universes = value
  | Just body <- specializeGlobalDefinitionBody universes definition =
      eval ctx [] body
  | projection <- gdProvisionalUniverseProjection definition
  , not (null projection)
  , all ((< length universes) . snd) projection =
      eval ctx [] $
        zonkTermWith
          (\_ _ -> Nothing)
          (substituteLevelMetas (Map.fromList [(meta, universes !! index) | (meta, index) <- projection]))
          0
          (quote (ctx {ecFacts = Map.empty}) 0 value)
  | otherwise =
      eval ctx [] $
        zonkTermWith
          (\_ _ -> Nothing)
          (substituteLevelParams universes)
          0
          (quote (ctx {ecFacts = Map.empty}) 0 value)
      -- A declaration value is closed, while 'ecFacts' describes rigid levels
      -- in the caller's local branch. Re-quoting the declaration under those
      -- facts lets fresh quotation rigids (which start at level 0) collide with
      -- unrelated caller levels and can spuriously reduce matches. Universe
      -- specialization therefore quotes in a facts-free context; the resulting
      -- value is still forced later under the real call-site facts.
  where
    value = case gdValue definition of
      Just body -> body
      Nothing -> error "Kappa.Eval.instantiateGlobalValue: definition has no value"

evalApp :: EvalCtx -> Value -> [(Icit, Value)] -> Value
evalApp ctx = foldl (\f (ic, a) -> vapp ctx f ic a)

vproj :: EvalCtx -> ObservationMode -> Value -> Text -> Value
vproj ctx mode v f = case force ctx v of
  VRecordV fs | Just x <- lookup f fs -> x
  VCtorI _ _ arguments
    | Just argument <-
        find ((== Just f) . cvaName) (reverse arguments) ->
          cvaValue argument
  -- §13.2.10: projection computes through a seal except for opaque
  -- members, whose defining equations are hidden (runtime projections
  -- of retained ordinary fields always compute)
  VSealV ls r | f `notElem` ls || ecRuntime ctx -> vproj ctx mode r f
  v' -> VProjN mode v' f

vforce :: EvalCtx -> Value -> Value
vforce ctx v = case force ctx v of
  -- A thunk is @VThunkV (Closure env body)@ with no extra binder, so it
  -- runs as @eval ctx env body@. Force WHNF of that very evaluation (the
  -- previous @closApply ... (VRecordV [])@ ran the body under a binder
  -- shifted by one — every index off by one — and discarded the result).
  VThunkV clo -> let v' = runSusp clo in v' `seq` v'
  VLazyV clo -> runSusp clo
  v' -> VPrim "force" [v']
  where
    runSusp (Closure env body) = eval ctx env body

-- | Reduce a value to /weak-head normal form/: expose its outermost
-- constructor so callers can pattern-match on the head. Concretely: unfold
-- solved metas and (reducible) global heads at the value root, and
-- re-reduce values that got stuck on a then-unsolved metavariable
-- (projections, applications, ifs and matches re-fire once their head
-- becomes canonical).
force :: EvalCtx -> Value -> Value
force ctx = go (if ecRuntime ctx then 1000000 else 1000 :: Int)
  where
    -- runtime evaluation is depth-guarded (§32.1): a divergent
    -- *reduction* chain becomes a clean runtime error (the
    -- '__recursionDepth' marker) instead of an unbounded host-stack
    -- blowup. The complementary case — strict-accumulating recursion
    -- that grows the host call stack directly, outrunning this fuel —
    -- is caught as a recoverable 'StackOverflow' in 'Interp.runMainRT'
    -- (§18.8), so both forms of divergence surface a Kappa diagnostic.
    go 0 v
      | ecRuntime ctx = VPrim "__recursionDepth" []
      | otherwise = v
    go fuel v = case v of
      -- Nat keeps ordinary logical constructors in Core while canonical
      -- closed values use the exact compact integer normal form. Open
      -- successors stay structural, preserving the first-argument
      -- computation rules of the source definitions.
      VCtor g [] | g == prelNatZero -> VLit (LitInt 0)
      VCtor g [predecessor]
        | g == prelNatSucc
        , VLit (LitInt n) <- go (fuel - 1) predecessor
        , n >= 0 ->
            VLit (LitInt (n + 1))
      VGlobI g universes spine
        | Just result <- logicalNatOperationStep g universes spine ->
            go (fuel - 1) result
      -- Open logical-Nat operations stay headed by their authenticated
      -- declaration identity when their first computation argument is
      -- neutral.  Unfolding the source definition here would replace
      -- @natAdd n k@ by a stuck match and lose the arithmetic head needed by
      -- the proof-producing value solver.  Concrete left constructors still
      -- take exactly one ordinary computation step above.
      v@(VGlobI g _ _)
        | g == prelNatAdd
            || g == prelNatMultiply
            || g == prelNatCompare ->
            v
      VFlex m sp
        | Just (Just sol) <- Map.lookup m (ecMetas ctx) ->
            go (fuel - 1) (evalApp ctx sol sp)
      VUniverseLift _ _ _ inner ->
        go (fuel - 1) inner
      -- Branch-local dependent-match solution for a rigid (§7.4.1).  A
      -- neutral rigid retains its complete application spine, so replay that
      -- spine after substitution.  Restricting this rule to an empty spine
      -- loses generic GADT refinements under application (notably implicit
      -- dependent-function application) even though the constructor-result
      -- certificate established the head equation.
      VRigid l sp
        | Just (FactIs sol) <- Map.lookup l (ecFacts ctx) ->
            go (fuel - 1) (evalApp ctx sol sp)
      VGlobI g universes sp
        | Just gd <- lookupGlobal ctx g
        , Just body <- gdValue gd
        , ecRuntime ctx || globalDefinitionBodyUniversesReplayable gd
        , ecRuntime ctx || gdReducible gd || isPrimRoot body ->
            -- runtime is strict (§32.1): force arguments before entry so
            -- deep recursion does not pile up unreduced argument chains
            let sp' =
                  if ecRuntime ctx
                    then [(ic, go (fuel - 1) a) | (ic, a) <- sp]
                    else sp
                body' = instantiateGlobalValue ctx universes gd
             in go (fuel - 1) (evalApp ctx body' sp')
      VAppN ic f a
        | f' <- go (fuel - 1) f
        , reapplicable f' ->
            go (fuel - 1) (vapp ctx f' ic a)
      VPrim p sp
        | Just v' <- evalPrimCtx ctx p (map (go (fuel - 1)) sp) -> go (fuel - 1) v'
      VProjN mode inner fld ->
        -- §13.2.10: a projection re-fires through seal layers unless
        -- the member is opaque (always computes at runtime)
        let unseal x = case x of
              VSealV ls r | ecRuntime ctx || fld `notElem` ls -> unseal (go (fuel - 1) r)
              _ -> x
         in case unseal (go (fuel - 1) inner) of
              VRecordV fs | Just x <- lookup fld fs -> go (fuel - 1) x
              inner' -> VProjN mode inner' fld
      VIfN c t f -> case go (fuel - 1) c of
        VCtor g [] | g == prelTrue -> go (fuel - 1) (closRun t)
        VCtor g [] | g == prelFalse -> go (fuel - 1) (closRun f)
        _ -> v
      VMatchN scrut _ _ alts env
        | Just v' <- tryReduceMatch ctx scrut alts env ->
            go (fuel - 1) v'
      _ -> v
      where
        -- Representation-preserving logical-Nat computation keyed by
        -- resolved declaration identity.  Closed arithmetic uses exact
        -- compact integers; open arithmetic follows the declared recursion on
        -- the left argument one constructor at a time.
        logicalNatOperationStep global universes spine =
          case [argument | (Expl, argument) <- spine] of
            [left, right]
              | global == prelNatAdd ->
                  case go (fuel - 1) left of
                    VLit (LitInt 0) -> Just right
                    VLit (LitInt n)
                      | n > 0 ->
                          case go (fuel - 1) right of
                            VLit (LitInt m) | m >= 0 ->
                              Just (VLit (LitInt (n + m)))
                            _ ->
                              Just
                                ( VCtor prelNatSucc
                                    [ VGlobI global universes
                                        [ (Expl, VLit (LitInt (n - 1)))
                                        , (Expl, right)
                                        ]
                                    ]
                                )
                    VCtor constructor [predecessor]
                      | constructor == prelNatSucc ->
                          Just
                            ( VCtor prelNatSucc
                                [ VGlobI global universes
                                    [(Expl, predecessor), (Expl, right)]
                                ]
                            )
                    _ -> Nothing
              | global == prelNatMultiply ->
                  case go (fuel - 1) left of
                    VLit (LitInt 0) -> Just (VLit (LitInt 0))
                    VLit (LitInt n)
                      | n > 0 ->
                          case go (fuel - 1) right of
                            VLit (LitInt m) | m >= 0 ->
                              Just (VLit (LitInt (n * m)))
                            _ ->
                              Just
                                ( VGlobI prelNatAdd []
                                    [ (Expl, right)
                                    , ( Expl
                                      , VGlobI global universes
                                          [ (Expl, VLit (LitInt (n - 1)))
                                          , (Expl, right)
                                          ]
                                      )
                                    ]
                                )
                    VCtor constructor [predecessor]
                      | constructor == prelNatSucc ->
                          Just
                            ( VGlobI prelNatAdd []
                                [ (Expl, right)
                                , ( Expl
                                  , VGlobI global universes
                                      [(Expl, predecessor), (Expl, right)]
                                  )
                                ]
                            )
                    _ -> Nothing
              | global == prelNatCompare ->
                  case (go (fuel - 1) left, go (fuel - 1) right) of
                    (VLit (LitInt n), VLit (LitInt m))
                      | n >= 0, m >= 0 ->
                          Just (VCtor (prelOrdering (compare n m)) [])
                    _ -> Nothing
            _ -> Nothing
        isPrimRoot = \case
          VPrim _ [] -> True
          _ -> False
        -- shapes 'vapp' can make progress on (avoids rebuilding the same
        -- stuck application forever)
        reapplicable = \case
          VLam {} -> True
          VRigid {} -> True
          VFlex {} -> True
          VGlobN {} -> True
          VCtor {} -> True
          VPrim {} -> True
          _ -> False
        closRun (Closure env body) = eval ctx env body

-- ι-reduction of match when the scrutinee is canonical.
reduceMatch :: EvalCtx -> Value -> Maybe Value -> Maybe Value -> [CaseAlt] -> Env -> Value
reduceMatch ctx scrut scrutineeAnnotation resultAnnotation alts env =
  case tryReduceMatch ctx scrut alts env of
    Just v -> v
    Nothing -> VMatchN scrut scrutineeAnnotation resultAnnotation alts env

-- | 'Just' iff some alternative definitely fires (used by 'force' to
-- re-reduce matches stuck on metavariables).
tryReduceMatch :: EvalCtx -> Value -> [CaseAlt] -> Env -> Maybe Value
tryReduceMatch ctx scrut alts env = tryAlts alts
  where
    scrut' = force ctx scrut
    tryAlts [] = Nothing
    tryAlts (CaseAlt pat g body : rest) =
      case matchPat ctx pat scrut' of
        Just binds ->
          let env' = reverse binds ++ env
           in case g of
                Nothing -> Just (eval ctx env' body)
                Just gd -> case force ctx (eval ctx env' gd) of
                  VCtor g [] | g == prelTrue -> Just (eval ctx env' body)
                  VCtor g [] | g == prelFalse -> tryAlts rest
                  _ -> Nothing -- stuck guard: whole match stuck
        Nothing
          | definitelyNoMatch pat scrut' -> tryAlts rest
          | otherwise -> Nothing -- stuck

    -- Recursive: a definite mismatch in any nested sub-pattern rules
    -- out the whole alternative (e.g. @_ :: y :: _@ vs @1 :: Nil@).
    definitelyNoMatch pat v0 = case (pat, force ctx v0) of
      -- a rigid known to lack the constructor cannot match it (§7.4.1)
      (CPCtor g _ _, VRigid l _)
        | Just (FactNot gs) <- Map.lookup l (ecFacts ctx) -> g `elem` gs
      (CPCtor g _ ps, VCtor g' args) ->
        g /= g'
          || ( length ps <= length args
                 && or
                   [ definitelyNoMatch p a
                   | (p, a) <- zip ps (drop (length args - length ps) args)
                   ]
             )
      (CPCtorM _ _ hidden g _ ps, VCtorI g' _ arguments) ->
        g /= g'
          || case typedConstructorSource hidden ps arguments of
               Nothing -> False
               Just source ->
                 or
                   [ definitelyNoMatch pattern' (cvaValue argument)
                   | (Right pattern', argument) <- source
                   ]
      (CPCtor g _ _, VLit (LitInt n))
        | g == prelNatZero -> n /= 0
        | g == prelNatSucc -> n <= 0
      (CPLit l, VLit l') -> l /= l'
      (CPTuple ps, VRecordV fs)
        | length ps == length fs ->
            or [definitelyNoMatch p a | (p, (_, a)) <- zip ps fs]
      (CPRecord pfs _, VRecordV fs) ->
        or [maybe False (definitelyNoMatch p) (lookup n fs) | (n, p) <- pfs]
      (CPInject t p, VInject t' x) -> t /= t' || definitelyNoMatch p x
      (CPInjectRest excl, VInject t _) -> t `elem` excl
      (CPOr ps _, v) -> all (`definitelyNoMatch` v) ps
      (CPAs _ p, v) -> definitelyNoMatch p v
      _ -> False

typedConstructorSource
  :: [ConstructorHiddenBinder]
  -> [a]
  -> [ConstructorValueArg]
  -> Maybe [(Either ConstructorHiddenBinder a, ConstructorValueArg)]
typedConstructorSource hidden explicit arguments = do
  source <- interleaveConstructorSourceBinders hidden explicit
  let sourceCount = length source
  guard (sourceCount <= length arguments)
  let sourceArguments = drop (length arguments - sourceCount) arguments
  guard
    ( and
        [ case slot of
            Left _ -> cvaIcit argument == Impl
            Right _ -> cvaIcit argument == Expl
        | (slot, argument) <- zip source sourceArguments
        ]
    )
  pure (zip source sourceArguments)

-- | First-order pattern matching on values. 'Nothing' means "did not
-- match or could not decide" — callers must distinguish via
-- 'definitelyNoMatch' for soundness during conversion.
matchPat :: EvalCtx -> CorePat -> Value -> Maybe [Value]
matchPat ctx pat v0 =
  let v = force ctx v0
   in case (pat, v) of
        (CPWild, _) -> Just []
        (CPVar _, _) -> Just [v]
        (CPLit l, VLit l') | l == l' -> Just []
        (CPCtorM existentialModes bridges hidden g _ ps, VLit (LitInt n))
          | g == prelNatZero
          , n == 0
          , null ps ->
              constructorBindings existentialModes bridges hidden [] []
          | g == prelNatSucc
          , n > 0
          , length ps <= 1 ->
              constructorBindings
                existentialModes
                bridges
                hidden
                ps
                [VLit (LitInt (n - 1))]
        (CPCtorM existentialModes bridges hidden g _ ps, VCtor g' args)
          | g == g', length ps <= length args ->
              constructorBindings
                existentialModes
                bridges
                hidden
                ps
                (drop (length args - length ps) args)
        (CPCtorM existentialModes bridges hidden g _ ps, VCtorI g' _ arguments)
          | g == g' ->
              typedConstructorBindings
                existentialModes
                bridges
                hidden
                ps
                arguments
        (CPTuple ps, VRecordV fs)
          | length ps == length fs ->
              concatM [matchPat ctx p a | (p, (_, a)) <- zip ps fs]
        (CPRecord pfs mrest, VRecordV fs) -> do
          sub <- concatM [maybe Nothing (matchPat ctx p) (lookup n fs) | (n, p) <- pfs]
          case mrest of
            Just nm | not (T.null nm) ->
              -- bind the remaining fields as a narrower record (§17.2.5)
              Just (sub ++ [VRecordV [(n, x) | (n, x) <- fs, n `notElem` map fst pfs]])
            _ -> Just sub
        (CPInject t p, VInject t' x) | t == t' -> matchPat ctx p x
        (CPInjectRest excl, VInject t _) | t `notElem` excl -> Just [v]
        -- §17.2.3: an alternative yields its bindings in ITS OWN structural
        -- order; reorder to the canonical (first-alternative) order via the
        -- alternative's permutation so the body's de Bruijn layout is correct.
        (CPOr ps perms, _) ->
          firstJust
            [ (\bs -> [bs !! j | j <- perm]) <$> matchPat ctx p v
            | (p, perm) <- zip ps perms
            ]
        (CPAs _ p, _) -> (v :) <$> matchPat ctx p v
        _ -> Nothing
  where
    constructorBindings existentialModes bridges hidden patterns arguments = do
      source <-
        interleaveConstructorSourceBinders hidden (zip patterns arguments)
      sourceBindings <-
        concatM
          [ case slot of
              Left _ -> Just [VRecordV []]
              Right (pattern', argument) -> matchPat ctx pattern' argument
          | slot <- source
          ]
      pure
        ( replicate
            (length existentialModes + constructorBridgeBinderCount bridges)
            (VRecordV [])
            ++ sourceBindings
        )
    typedConstructorBindings existentialModes bridges hidden patterns arguments = do
      source <- typedConstructorSource hidden patterns arguments
      sourceBindings <-
        concatM
          [ case slot of
              Left _ -> Just [cvaValue argument]
              Right pattern' -> matchPat ctx pattern' (cvaValue argument)
          | (slot, argument) <- source
          ]
      pure
        ( replicate
            (length existentialModes + constructorBridgeBinderCount bridges)
            (VRecordV [])
            ++ sourceBindings
        )
    concatM = fmap concat . sequence
    firstJust xs = case [x | Just x <- xs] of
      (x : _) -> Just x
      [] -> Nothing

-- ── Quotation ────────────────────────────────────────────────────────

-- | Quotation-time forcing: resolve solved metavariables and replay
-- applications stuck on them, but do NOT δ-unfold globals. Quoting must
-- terminate on recursive definitions and produce small, re-evaluable
-- terms (zonking depends on this; unfolding a recursive dictionary here
-- would diverge).
forceQ :: EvalCtx -> Value -> Value
forceQ ctx = go (1000 :: Int)
  where
    go :: Int -> Value -> Value
    go 0 v = v
    go fuel v = case v of
      VFlex m sp
        | Just (Just sol) <- Map.lookup m (ecMetas ctx) ->
            go (fuel - 1) (evalApp ctx sol sp)
      VAppN ic f a
        | f' <- go (fuel - 1) f
        , progressed f' ->
            go (fuel - 1) (vapp ctx f' ic a)
      VPrim p sp
        | Just v' <- evalPrimCtx ctx p (map (go (fuel - 1)) sp) -> go (fuel - 1) v'
      _ -> v
      where
        progressed = \case
          VLam {} -> True
          VRigid {} -> True
          VFlex {} -> True
          VGlobN {} -> True
          VCtor {} -> True
          VPrim {} -> True
          _ -> False

-- | Read a 'Value' back into a normalized 'Term'. @lvl@ is the current
-- depth (how many binders we're under). To go under a binder we apply the
-- closure to a fresh variable at the current level (@VRigid lvl []@) and
-- recurse at @lvl + 1@ — the standard NbE readback.
--
-- This is also where the de Bruijn /level/ → /index/ conversion happens:
-- a 'VRigid' at level @l@ becomes @CVar (lvl - 1 - l)@. (Worked example in
-- docs/CONCEPTS.md → "de Bruijn indices vs levels".)
quote :: EvalCtx -> Int -> Value -> Term
quote ctx lvl v = case forceQ ctx v of
  VRigid l sp -> quoteSpine (CVar (lvl - 1 - l)) sp
  VFlex m sp -> quoteSpine (CMeta m) sp
  VGlobal g universes sp -> quoteSpine (CGlobal g universes) sp
  VLamM mode ic q n clo ->
    CLamM mode ic q n (quote ctx (lvl + 1) (closApply ctx clo (VRigid lvl [])))
  VPiRuntimeM mode formation ic q brw n assumption origin runtimeErasure a clo ->
    CPiRuntimeM mode formation ic q brw n assumption origin
      (fmap (quote ctx lvl) runtimeErasure)
      (quote ctx lvl a)
      (quote ctx (lvl + 1) (closApply ctx clo (VRigid lvl [])))
  VSort n -> CSort n
  VLevel n -> CLevel n
  VUniverseLift from to evidence inner ->
    CUniverseLift from to evidence (quote ctx lvl inner)
  VArithmeticProof certificate ->
    CArithmeticProof (mapArithmeticCertificate (quote ctx lvl) certificate)
  VLit l -> CLit l
  -- The head-type annotation is a fresh-elaboration-only artifact, but hidden
  -- universes and erased typed arguments are stable KCore identity and survive
  -- the eval/quote round trip.
  VCtorI g universes arguments ->
    CCtorI g universes Nothing
      [ ConstructorArg (cvaIcit argument) (cvaPayload argument) (cvaName argument)
          (quote ctx lvl (cvaValue argument))
      | argument <- arguments
      ]
  VRecordTQ fs -> CRecordTQ (map (fmap (quote ctx lvl)) fs)
  VRecordV fs -> CRecordV [(n, quote ctx lvl t) | (n, t) <- fs]
  VVariantT ms -> CVariantT (map (quote ctx lvl) ms)
  VInject t x -> CInject t (quote ctx lvl x)
  VMatchN scrut scrutineeAnnotation resultAnnotation alts env ->
    -- Stuck match: quote scrutinee, keep alts with their env baked in
    -- only when env is empty; otherwise approximate via fresh rigids.
    CMatch
      (quote ctx lvl scrut)
      (quote ctx lvl <$> scrutineeAnnotation)
      (quote ctx lvl <$> resultAnnotation)
      (map (quoteAlt env) alts)
  VProjN mode e f -> CProjM mode (quote ctx lvl e) f
  VAppN ic f a -> CApp ic (quote ctx lvl f) (quote ctx lvl a)
  VSealV ls x -> CSealE ls (quote ctx lvl x)
  VSigT ls x -> CSigT ls (quote ctx lvl x)
  VDoV lbl items _ -> CDo lbl items
  VThunkV closure -> CThunkE (quote ctx lvl (closRun closure)) Nothing
  VLazyV closure -> CLazyE (quote ctx lvl (closRun closure)) Nothing
  VIfN c t f ->
    -- branch closures bind nothing: run them in their own env
    CIf
      (quote ctx lvl c)
      (quote ctx lvl (closRun t))
      (quote ctx lvl (closRun f))
  VPrim p args -> foldl (\f a -> CApp Expl f (quote ctx lvl a)) (CGlob (GName primModule p)) args
  -- runtime-only values; never legitimately quoted, render opaquely
  VRef _ -> CGlob (GName primModule "__ref")
  VArr _ _ -> CGlob (GName primModule "__array")
  VMVar _ -> CGlob (GName primModule "__mvar")
  VFiber _ _ -> CGlob (GName primModule "__fiber")
  VScope _ -> CGlob (GName primModule "__scope")
  VFiberRef _ -> CGlob (GName primModule "__fiberref")
  VTVar _ -> CGlob (GName primModule "__tvar")
  VIOAction p args -> foldl (\f a -> CApp Expl f (quote ctx lvl a)) (CGlob (GName primModule p)) args
  VQuote qs slots -> CQuote qs (map (quote ctx lvl) slots)
  where
    quoteSpine = foldl (\f (ic, a) -> CApp ic f (quote ctx lvl a))
    quoteAlt _ alt = alt
    closRun (Closure env body) = eval ctx env body

-- ── Conversion ───────────────────────────────────────────────────────

-- | Definitional equality (§31.1). Sound; may conservatively answer
-- 'False' on stuck terms it cannot decide.
convertible :: EvalCtx -> Int -> Value -> Value -> Bool
convertible ctx = go (200 :: Int)
  where
    go :: Int -> Int -> Value -> Value -> Bool
    go 0 _ _ _ = False
    -- §15.1: before δ-unfolding, a reducible recursive global applied to the
    -- same convertible spine on both sides is convertible WITHOUT unfolding.
    -- Unfolding here would loop forever on a recursion stuck on a neutral
    -- argument (e.g. 'listAppend t Nil' vs itself, whose cons branch
    -- re-introduces 'listAppend r Nil' under a fresh binder). This mirrors the
    -- post-force VGlobN rule below, but fires first so the structural match
    -- short-circuits the divergent unfold.
    go fuel lvl v1 v2
      | VGlobI g1 us1 sp1 <- forceQ ctx v1
      , VGlobI g2 us2 sp2 <- forceQ ctx v2
      , g1 == g2
      , hiddenUniversesCompatible us1 us2
      , Just relevant <- globalSpineRelevantPairs ctx g1 sp1 sp2
      , and (map (\(a, b) -> go (fuel - 1) lvl a b) relevant) =
          True
    go fuel lvl v1 v2 = case (force ctx v1, force ctx v2) of
      (VSort a, VSort b) -> a == b
      (VLevel a, VLevel b) -> a == b
      (VLit a, VLit b) -> a == b
      (VLit (LitInt n), VCtor g args)
        | g == prelNatZero -> n == 0 && null args
        | g == prelNatSucc
        , n > 0
        , [predecessor] <- args ->
            go (fuel - 1) lvl (VLit (LitInt (n - 1))) predecessor
      (VCtor g args, VLit (LitInt n))
        | g == prelNatZero -> n == 0 && null args
        | g == prelNatSucc
        , n > 0
        , [predecessor] <- args ->
            go (fuel - 1) lvl predecessor (VLit (LitInt (n - 1)))
      (VPiM m1 i1 q1 _ _ a1 b1, VPiM m2 i2 q2 _ _ a2 b2) ->
        i1 == i2
          && m1 == m2
          && q1 == q2 -- quantities are part of function-type identity
          && go (fuel - 1) lvl a1 a2
          && goClos fuel lvl b1 b2
      (VLamM m1 i1 _ _ b1, VLamM m2 i2 _ _ b2)
        | m1 == m2 && i1 == i2 -> goClos fuel lvl b1 b2
      -- η for functions
      (VLamM _ i _ _ b, f) ->
        let x = VRigid lvl []
         in go (fuel - 1) (lvl + 1) (closApply ctx b x) (vapp ctx f i x)
      (f, VLamM _ i _ _ b) ->
        let x = VRigid lvl []
         in go (fuel - 1) (lvl + 1) (vapp ctx f i x) (closApply ctx b x)
      (VRigid l1 sp1, VRigid l2 sp2) -> l1 == l2 && goSpine fuel lvl sp1 sp2
      (VFlex m1 sp1, VFlex m2 sp2) -> m1 == m2 && goSpine fuel lvl sp1 sp2
      (VGlobI g1 us1 sp1, VGlobI g2 us2 sp2)
        | g1 == g2
        , hiddenUniversesCompatible us1 us2
        , Just relevant <- globalSpineRelevantPairs ctx g1 sp1 sp2
        , and (map (\(a, b) -> go (fuel - 1) lvl a b) relevant) -> True
      -- unfold non-reducible-blocked globals only if reducible (force
      -- already unfolded those); different heads -> try nothing more
      (VCtorI g1 universes1 arguments1, VCtorI g2 universes2 arguments2) ->
        g1 == g2
          && hiddenUniversesCompatible universes1 universes2
          && length arguments1 == length arguments2
          && and
            ( zipWith
                (\left right ->
                   cvaIcit left == cvaIcit right
                     && cvaPayload left == cvaPayload right
                     && go (fuel - 1) lvl (cvaValue left) (cvaValue right))
                arguments1
                arguments2
            )
      (VRecordT f1, VRecordT f2) ->
        map fst f1 == map fst f2 && and (zipWith (go (fuel - 1) lvl) (map snd f1) (map snd f2))
      (VRecordV f1, VRecordV f2) ->
        map fst f1 == map fst f2 && and (zipWith (go (fuel - 1) lvl) (map snd f1) (map snd f2))
      -- record η: zero-field record ≡ Unit value
      (VRecordV [], VCtor g []) | g == prelUnit -> True
      (VCtor g [], VRecordV []) | g == prelUnit -> True
      -- record η (§31.1): a literal of projections of one neutral
      -- receiver is that receiver
      (VRecordV fs@(_ : _), t) | etaRecord fs t -> True
      (t, VRecordV fs@(_ : _)) | etaRecord fs t -> True
      (VVariantT m1, VVariantT m2) ->
        length m1 == length m2 && and (zipWith (go (fuel - 1) lvl) m1 m2)
      (VInject t1 x1, VInject t2 x2) -> t1 == t2 && go (fuel - 1) lvl x1 x2
      (VProjN _ e1 f1, VProjN _ e2 f2) -> f1 == f2 && go (fuel - 1) lvl e1 e2
      (VAppN ic1 f1 a1, VAppN ic2 f2 a2) ->
        ic1 == ic2 && go (fuel - 1) lvl f1 f2 && go (fuel - 1) lvl a1 a2
      -- §13.2.10: seal is pure and non-generative; sealed packages are
      -- equal iff the underlying records are (seal e as S ≡ e)
      (VSealV _ x1, y1) -> go (fuel - 1) lvl x1 y1
      (x1, VSealV _ y1) -> go (fuel - 1) lvl x1 y1
      (VSigT l1 x1, VSigT l2 x2) -> l1 == l2 && go (fuel - 1) lvl x1 x2
      (VIfN c1 t1 f1, VIfN c2 t2 f2) ->
        -- if-branch closures bind nothing
        go (fuel - 1) lvl c1 c2
          && go (fuel - 1) lvl (closRun t1) (closRun t2)
          && go (fuel - 1) lvl (closRun f1) (closRun f2)
      (VPrim p1 a1, VPrim p2 a2) ->
        p1 == p2 && length a1 == length a2 && and (zipWith (go (fuel - 1) lvl) a1 a2)
      -- §21.1 syntax values: conservative payload comparison
      (VQuote q1 s1, VQuote q2 s2) ->
        q1 == q2 && length s1 == length s2 && and (zipWith (go (fuel - 1) lvl) s1 s2)
      -- Two stuck matches: a recursive function applied to a NEUTRAL argument
      -- δ-unfolds to a 'match' stuck on that argument, so an honest inductive
      -- proof must compare such matches. They are convertible when the
      -- scrutinees are convertible and, alternative-for-alternative, the
      -- patterns coincide and the branch bodies are convertible under their
      -- own pattern binders (modelled by fresh rigids, one per binder).
      -- Guarded alternatives are compared conservatively: identical guard
      -- terms required (a stuck guard cannot have fired, so the surrounding
      -- match is genuinely neutral). This is the §7.4.1 neutral-eliminator
      -- rule for 'match', mirroring the existing 'VProjN'/'VIfN' cases.
      (VMatchN s1 _ _ alts1 e1, VMatchN s2 _ _ alts2 e2)
        | length alts1 == length alts2
        , all (\(CaseAlt _ g _) -> maybe True (const False) g) alts1
        , all (\(CaseAlt _ g _) -> maybe True (const False) g) alts2
        , go (fuel - 1) lvl s1 s2 ->
            and
              [ pat1 == pat2
                  && let n = patBinders pat1
                         xs = [VRigid (lvl + i) [] | i <- [0 .. n - 1]]
                         env1' = reverse xs ++ e1
                         env2' = reverse xs ++ e2
                      in go (fuel - 1) (lvl + n) (eval ctx env1' b1) (eval ctx env2' b2)
              | (CaseAlt pat1 _ b1, CaseAlt pat2 _ b2) <- zip alts1 alts2
              ]
      _ -> False
      where
        patBinders = \case
          CPWild -> 0
          CPVarM _ _ -> 1
          CPLit _ -> 0
          CPCtorM existentialModes bridges hidden _ _ ps ->
            length existentialModes
              + constructorBridgeBinderCount bridges
              + length hidden
              + sum (map patBinders ps)
          CPTuple ps -> sum (map patBinders ps)
          CPRecordM fs rest ->
            sum (map (patBinders . snd) fs)
              + case rest of Just (_, nm) | not (T.null nm) -> 1; _ -> 0
          CPInject _ p -> patBinders p
          CPInjectRestM _ _ -> 1
          CPOr ps _ -> case ps of p : _ -> patBinders p; [] -> 0
          CPAsM _ _ p -> 1 + patBinders p
        closRun (Closure env body) = eval ctx env body
        goClos fl l c1 c2 =
          let x = VRigid l []
           in go (fl - 1) (l + 1) (closApply ctx c1 x) (closApply ctx c2 x)
        goSpine fl l sp1 sp2 =
          length sp1 == length sp2
            && and (zipWith (\(_, a) (_, b) -> go (fl - 1) l a b) sp1 sp2)
        etaRecord fs t = case t of
          VRecordV _ -> False -- the structural rule above decides
          _ -> all (\(f, x) -> go (fuel - 1) lvl x (vproj ctx Ordinary t f)) fs

-- Pure conversion observes finalized hidden-universe identity. Fresh
-- instantiation metas are reconciled by the checker before this fallback;
-- treating an arbitrary meta as equal here would make distinct universe
-- instances definitionally equal without recording a constraint.
hiddenUniversesCompatible :: [Level] -> [Level] -> Bool
hiddenUniversesCompatible left right =
  map normalizeLevel left == map normalizeLevel right

-- | Read a closed compiler-owned TypeLevel primitive tree. Ordinary globals,
-- user functions, and neutral variables are deliberately not recognized.
closedTypeLevel :: Value -> Maybe Level
closedTypeLevel = \case
  VPrim "__typeLevelZero" [] -> Just LZero
  VPrim "__typeLevelFinite" [VLit (LitInt n)] | n >= 0 -> Just (finiteLevel n)
  VPrim "__typeLevelOmega" [] -> Just LOmega
  VPrim "__typeLevelSucc" [a] -> LSucc <$> closedTypeLevel a
  VPrim "__typeLevelAdd" [a, b] -> LAdd <$> closedTypeLevel a <*> closedTypeLevel b
  VPrim "__typeLevelMax" [a, b] -> LMax <$> closedTypeLevel a <*> closedTypeLevel b
  _ -> Nothing

-- | Instantiate rigid level leaves when a Core sort is evaluated under a
-- term environment. 'LVar' uses the same outermost-first level identity as
-- 'VRigid'; the environment itself is innermost-first, hence the conversion.
-- This is the universe analogue of evaluating a 'CVar' and is required for
-- applications of level-indexed type families.
evalLevel :: EvalCtx -> Env -> Level -> Level
evalLevel ctx env = normalizeLevel . go
  where
    go = \case
      LVar l
        | let i = length env - 1 - l
        , i >= 0
        , i < length env
        , Just level <- valueLevel (force ctx (lookupEnv i env)) -> level
      LProjection root path
        | let i = length env - 1 - root
        , i >= 0
        , i < length env
        , Just level <- valueLevel (foldl (vproj ctx Ordinary) (force ctx (lookupEnv i env)) path) -> level
      LSucc a -> LSucc (go a)
      LAdd a b -> LAdd (go a) (go b)
      LMax a b -> LMax (go a) (go b)
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels go atom)
      level -> level

    valueLevel = \case
      VLevel level -> Just level
      VRigid l [] -> Just (LVar l)
      VFlex m [] -> Just (LMeta m)
      projected@VProjN {} -> do
        (root, path) <- projectionRoot projected
        pure (LProjection root path)
      value -> closedTypeLevel value

    projectionRoot = go []
      where
        go path = \case
          VProjN _ receiver field -> go (field : path) receiver
          VRigid root [] -> Just (root, path)
          _ -> Nothing

closedLevelValue :: Level -> Maybe Value
closedLevelValue = \case
  LZero -> Just (VPrim "__typeLevelZero" [])
  LFinite n -> Just (VPrim "__typeLevelFinite" [VLit (LitInt n)])
  LOmega -> Just (VPrim "__typeLevelOmega" [])
  LSucc a -> VPrim "__typeLevelSucc" . pure <$> closedLevelValue a
  LAdd a b -> VPrim "__typeLevelAdd" <$> sequence [closedLevelValue a, closedLevelValue b]
  LMax a b -> VPrim "__typeLevelMax" <$> sequence [closedLevelValue a, closedLevelValue b]
  LVar _ -> Nothing
  LParam _ -> Nothing
  LField _ _ -> Nothing
  LProjection _ _ -> Nothing
  LNeutral _ -> Nothing
  LMeta _ -> Nothing

-- | Pure primitive reduction shared by conversion and runtime.
evalPurePrim :: Text -> [Value] -> Maybe Value
evalPurePrim p args = case (p, args) of
  ("__typeLevelFromNat", [VLit (LitInt n)])
    | n >= 0 -> closedLevelValue (finiteLevel n)
  ("__eqTypeLevel", [a, b])
    | Just la <- closedTypeLevel a
    , Just lb <- closedTypeLevel b -> bool (compareClosedLevel la lb == Just EQ)
  ("__compareTypeLevel", [a, b])
    | Just la <- closedTypeLevel a
    , Just lb <- closedTypeLevel b
    , Just ord <- compareClosedLevel la lb -> Just (VCtor (prelOrdering ord) [])
  ("addInt", [VLit (LitInt a), VLit (LitInt b)]) -> int (a + b)
  ("subInt", [VLit (LitInt a), VLit (LitInt b)]) -> int (a - b)
  ("mulInt", [VLit (LitInt a), VLit (LitInt b)]) -> int (a * b)
  ("divInt", [VLit (LitInt a), VLit (LitInt b)]) | b /= 0 -> int (a `quot` b)
  ("modInt", [VLit (LitInt a), VLit (LitInt b)]) | b /= 0 -> int (a `rem` b)
  ("negInt", [VLit (LitInt a)]) -> int (negate a)
  -- §18.1/§29: Duration/Instant construction + arithmetic now live in the
  -- std.time prelude fragment (ordinary Kappa over Int); no prim cases here.
  -- §13.2.6/§11.3.1A row extension: append the field to the record
  -- value, keeping canonical lexicographic field order (§31.4)
  ("__rowExtend", [VRecordV fs, VLit (LitStr l), v])
    | l `notElem` map fst fs ->
        Just (VRecordV (insertField (l, v) fs))
  ("eqInt", [VLit (LitInt a), VLit (LitInt b)]) -> bool (a == b)
  ("ltInt", [VLit (LitInt a), VLit (LitInt b)]) -> bool (a < b)
  ("leInt", [VLit (LitInt a), VLit (LitInt b)]) -> bool (a <= b)
  ("addDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a + b)
  ("subDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a - b)
  ("mulDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a * b)
  ("divDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a / b)
  ("negDouble", [VLit (LitDouble a)]) -> dbl (negate a)
  ("eqDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> bool (identicalIEEE a b)
  ("ltDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> bool (a < b)
  ("floatEq", [VLit (LitDouble a), VLit (LitDouble b)]) -> bool (a == b)
  -- §6.1.7 libm floating-point / transcendental math.  GHC's Prelude is backed
  -- by the SAME platform libm the C/LLVM backends call (kp_sqrt/kp_sin/…), so a
  -- correctly-rounded IEEE-754 result is bit-identical across all three.  Total:
  -- sqrt of a negative is NaN, log of a non-positive is NaN/-Infinity, etc.
  ("sqrt", [VLit (LitDouble a)]) -> dbl (sqrt a)
  ("sin", [VLit (LitDouble a)]) -> dbl (sin a)
  ("cos", [VLit (LitDouble a)]) -> dbl (cos a)
  ("tan", [VLit (LitDouble a)]) -> dbl (tan a)
  ("asin", [VLit (LitDouble a)]) -> dbl (asin a)
  ("acos", [VLit (LitDouble a)]) -> dbl (acos a)
  ("atan", [VLit (LitDouble a)]) -> dbl (atan a)
  ("atan2", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (c_atan2 a b)
  ("exp", [VLit (LitDouble a)]) -> dbl (exp a)
  ("log", [VLit (LitDouble a)]) -> dbl (log a)
  ("pow", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a ** b)
  ("floor", [VLit (LitDouble a)]) -> dbl (cDoubleFloor a)
  ("ceil", [VLit (LitDouble a)]) -> dbl (cDoubleCeil a)
  ("fabs", [VLit (LitDouble a)]) -> dbl (abs a)
  -- §6.1.7 fixed-precision formatting: render with N fractional digits exactly
  -- as C's snprintf("%.*f"), so the CLBG %.9f outputs are byte-identical.
  ("showFixed", [VLit (LitInt p), VLit (LitDouble a)]) ->
    str (T.pack (showFixedC (fromInteger p) a))
  -- §28.2 Rational: an exact normalized ratio of two Integers with a
  -- positive denominator, represented at runtime by the stuck prim spine
  -- '__rat num den'. '__ratOfInt n' builds n/1; the arithmetic prims
  -- re-normalize their result.
  ("__ratOfInt", [VLit (LitInt a)]) -> rat a 1
  ("__ratNum", [r]) | Just (n, _) <- asRat r -> int n
  ("__ratDen", [r]) | Just (_, d) <- asRat r -> int d
  ("addRat", [x, y]) | Just (a, b) <- asRat x, Just (c, d) <- asRat y -> rat (a * d + c * b) (b * d)
  ("subRat", [x, y]) | Just (a, b) <- asRat x, Just (c, d) <- asRat y -> rat (a * d - c * b) (b * d)
  ("mulRat", [x, y]) | Just (a, b) <- asRat x, Just (c, d) <- asRat y -> rat (a * c) (b * d)
  ("divRat", [x, y]) | Just (a, b) <- asRat x, Just (c, d) <- asRat y, c /= 0 -> rat (a * d) (b * c)
  ("negRat", [x]) | Just (a, b) <- asRat x -> rat (negate a) b
  ("eqRat", [x, y]) | Just (a, b) <- asRat x, Just (c, d) <- asRat y -> bool (a * d == c * b)
  ("ltRat", [x, y]) | Just (a, b) <- asRat x, Just (c, d) <- asRat y -> bool (a * d < c * b)
  ("showRat", [x]) | Just (a, b) <- asRat x -> str (if b == 1 then T.pack (show a) else T.pack (show a) <> "/" <> T.pack (show b))
  -- §6.1.6/§28.2.3 FromFloat Rational: a binary64 is an exact dyadic
  -- rational; decode the IEEE significand/exponent into num/den.
  ("ratOfDouble", [VLit (LitDouble d)]) ->
    let (n, den) = doubleToRatio d in rat n den
  ("eqStr", [VLit (LitStr a), VLit (LitStr b)]) -> bool (a == b)
  ("ltStr", [VLit (LitStr a), VLit (LitStr b)]) -> bool (a < b)
  ("eqScalar", [VLit (LitScalar a), VLit (LitScalar b)]) -> bool (a == b)
  ("ltScalar", [VLit (LitScalar a), VLit (LitScalar b)]) -> bool (a < b)
  -- §6.5/§29.5 text atoms: Byte/Bytes/Grapheme comparison + rendering
  ("eqByte", [VLit (LitByte a), VLit (LitByte b)]) -> bool (a == b)
  ("ltByte", [VLit (LitByte a), VLit (LitByte b)]) -> bool (a < b)
  ("showByte", [VLit (LitByte a)]) ->
    str (T.pack ("b'\\x" <> pad2 (showHex a "") <> "'"))
  ("eqBytes", [VLit (LitBytes a), VLit (LitBytes b)]) -> bool (a == b)
  ("ltBytes", [VLit (LitBytes a), VLit (LitBytes b)]) -> bool (a < b) -- lexicographic by byte
  ("showBytes", [VLit (LitBytes a)]) ->
    str (T.pack ("0x" <> concatMap (\w -> pad2 (showHex w "")) (BS.unpack a)))
  ("eqGrapheme", [VLit (LitGrapheme a), VLit (LitGrapheme b)]) -> bool (a == b) -- exact scalars
  ("showGrapheme", [VLit (LitGrapheme a)]) -> str ("g'" <> a <> "'")
  -- §29.5 std.bytes: portable operations over the exact byte sequence.
  ("__bytesEmpty", []) -> bytes BS.empty
  ("__bytesSingleton", [VLit (LitByte w)]) -> bytes (BS.singleton w)
  ("__bytesLength", [VLit (LitBytes bs)]) -> int (fromIntegral (BS.length bs))
  ("__bytesIsEmpty", [VLit (LitBytes bs)]) -> bool (BS.null bs)
  ("__bytesGet", [VLit (LitBytes bs), VLit (LitInt i)]) ->
    if i >= 0 && i < fromIntegral (BS.length bs)
      then Just (someV (VLit (LitByte (BS.index bs (fromIntegral i)))))
      else Just noneV
  ("__bytesIndexUnsafe", [VLit (LitBytes bs), VLit (LitInt i)])
    | i >= 0 && i < fromIntegral (BS.length bs) -> Just (VLit (LitByte (BS.index bs (fromIntegral i))))
  ("__bytesAppend", [VLit (LitBytes a), VLit (LitBytes b)]) -> bytes (a <> b)
  ("__bytesSlice", [VLit (LitBytes bs), VLit (LitInt start), VLit (LitInt len)]) ->
    bytes (BS.take (fromIntegral len) (BS.drop (fromIntegral start) bs))
  ("__bytesTake", [VLit (LitInt n), VLit (LitBytes bs)]) -> bytes (BS.take (clampNat n) bs)
  ("__bytesDrop", [VLit (LitInt n), VLit (LitBytes bs)]) -> bytes (BS.drop (clampNat n) bs)
  ("__bytesStartsWith", [VLit (LitBytes pre), VLit (LitBytes bs)]) -> bool (pre `BS.isPrefixOf` bs)
  ("__bytesEndsWith", [VLit (LitBytes suf), VLit (LitBytes bs)]) -> bool (suf `BS.isSuffixOf` bs)
  ("__bytesContains", [VLit (LitBytes needle), VLit (LitBytes hay)]) -> bool (needle `BS.isInfixOf` hay)
  ("__bytesFind", [VLit (LitByte w), VLit (LitBytes bs)]) ->
    case BS.elemIndex w bs of
      Just i -> Just (someV (VLit (LitInt (fromIntegral i))))
      Nothing -> Just noneV
  ("__bytesBreakIndex", [VLit (LitBytes sep), VLit (LitBytes bs)]) ->
    case bytesBreakIndex sep bs of
      Just i -> Just (someV (VLit (LitInt (fromIntegral i))))
      Nothing -> Just noneV
  ("__bytesToList", [VLit (LitBytes bs)]) ->
    Just (listV [VLit (LitByte w) | w <- BS.unpack bs])
  ("__bytesFromList", [v]) | Just ws <- listOfBytes v -> bytes (BS.pack ws)
  ("__bytesCompact", [v@(VLit (LitBytes _))]) -> Just v
  -- §29.5 builder: the linear accumulator is modelled by the bytes built
  -- so far (the prim spine '__bytesBuilder bs'); appends concatenate.
  ("__newBytesBuilder", []) -> Just (VPrim "__bytesBuilder" [VLit (LitBytes BS.empty)])
  ("__bytesBuilderByte", [VLit (LitByte w), VPrim "__bytesBuilder" [VLit (LitBytes acc)]]) ->
    Just (VPrim "__bytesBuilder" [VLit (LitBytes (BS.snoc acc w))])
  ("__bytesBuilderBytes", [VLit (LitBytes more), VPrim "__bytesBuilder" [VLit (LitBytes acc)]]) ->
    Just (VPrim "__bytesBuilder" [VLit (LitBytes (acc <> more))])
  ("__finishBytesBuilder", [VPrim "__bytesBuilder" [v]]) -> Just v
  -- §29.4 std.unicode StringBuilder: accumulated valid-UTF-8 text.
  ("__newStringBuilder", []) -> Just (VPrim "__stringBuilder" [VLit (LitStr "")])
  ("__stringBuilderString", [VLit (LitStr s), VPrim "__stringBuilder" [VLit (LitStr acc)]]) ->
    Just (VPrim "__stringBuilder" [VLit (LitStr (acc <> s))])
  ("__stringBuilderScalar", [VLit (LitScalar c), VPrim "__stringBuilder" [VLit (LitStr acc)]]) ->
    Just (VPrim "__stringBuilder" [VLit (LitStr (acc <> T.singleton c))])
  ("__stringBuilderGrapheme", [VLit (LitGrapheme g), VPrim "__stringBuilder" [VLit (LitStr acc)]]) ->
    Just (VPrim "__stringBuilder" [VLit (LitStr (acc <> g))])
  ("__finishStringBuilder", [VPrim "__stringBuilder" [v]]) -> Just v
  -- §29.4 string cursors: a cursor is a scalar index into the source
  -- string; the offset is reported as the UTF-8 byte offset.
  ("__stringStart", [_]) -> int 0
  ("__stringEnd", [VLit (LitStr s)]) -> int (fromIntegral (T.length s))
  ("__stringCursorOffset", [VLit (LitStr s), VLit (LitInt i)]) ->
    int (fromIntegral (BS.length (TE.encodeUtf8 (T.take (clampNat i) s))))
  ("__stringNextScalar", [VLit (LitStr s), VLit (LitInt i)]) ->
    if i >= 0 && i < fromIntegral (T.length s)
      then Just (someV (recV [("scalar", VLit (LitScalar (T.index s (fromIntegral i)))), ("next", VLit (LitInt (i + 1)))]))
      else Just noneV
  ("__stringPrevScalar", [VLit (LitStr s), VLit (LitInt i)]) ->
    if i > 0 && i <= fromIntegral (T.length s)
      then Just (someV (recV [("prev", VLit (LitInt (i - 1))), ("scalar", VLit (LitScalar (T.index s (fromIntegral (i - 1)))))]))
      else Just noneV
  ("__stringNextGrapheme", [VLit (LitStr s), VLit (LitInt i)]) ->
    if i >= 0 && i < fromIntegral (T.length s)
      then case graphemeClusters (T.drop (fromIntegral i) s) of
        (g : _) ->
          Just (someV (recV [("grapheme", VLit (LitGrapheme g)), ("next", VLit (LitInt (i + fromIntegral (T.length g))))]))
        [] -> Just noneV
      else Just noneV
  ("__stringSpan", [VLit (LitStr s), VLit (LitInt a), VLit (LitInt b)]) ->
    if a >= 0 && b <= fromIntegral (T.length s) && a <= b
      then Just (someV (VLit (LitStr (T.take (fromIntegral (b - a)) (T.drop (fromIntegral a) s)))))
      else Just noneV
  ("__stringCompact", [v@(VLit (LitStr _))]) -> Just v
  -- §29.4 incremental UTF-8 decoder. The decoder state buffers the
  -- trailing incomplete bytes ('__utf8Dec pending'); each chunk decodes
  -- the longest valid prefix of (pending <> chunk) and carries the rest.
  ("__newUtf8Decoder", []) -> Just (VPrim "__utf8Dec" [VLit (LitBytes BS.empty)])
  ("__decodeUtf8Chunk", [VLit (LitBytes chunk), VPrim "__utf8Dec" [VLit (LitBytes pending)]]) ->
    let combined = pending <> chunk
        (good, rest) = splitValidUtf8Prefix combined
     in if utf8HasInvalid rest
          then Just noneV
          else
            Just
              ( someV
                  ( recV
                      [ ("text", VLit (LitStr (TE.decodeUtf8With TEE.lenientDecode good)))
                      , ("decoder", VPrim "__utf8Dec" [VLit (LitBytes rest)])
                      ]
                  )
              )
  ("__finishUtf8Decoder", [VPrim "__utf8Dec" [VLit (LitBytes pending)]]) ->
    if BS.null pending
      then Just (someV (VLit (LitStr "")))
      else Just noneV
  -- §29.4 std.unicode internals
  ("__utf8Bytes", [VLit (LitStr s)]) -> bytes (TE.encodeUtf8 s)
  ("__utf8Valid", [VLit (LitBytes bs)]) ->
    bool (either (const False) (const True) (TE.decodeUtf8' bs))
  ("__decodeUtf8Lossy", [VLit (LitBytes bs)]) ->
    str (TE.decodeUtf8With TEE.lenientDecode bs)
  ("__byteLength", [VLit (LitStr s)]) -> int (fromIntegral (BS.length (TE.encodeUtf8 s)))
  ("__uniScalarValue", [VLit (LitScalar c)]) -> int (fromIntegral (ord c))
  ("__scalarInRange", [VLit (LitInt n)]) ->
    bool (n >= 0 && n <= 0x10FFFF && not (n >= 0xD800 && n <= 0xDFFF))
  ("__scalarOfValue", [VLit (LitInt n)])
    | n >= 0 && n <= 0x10FFFF && not (n >= 0xD800 && n <= 0xDFFF) ->
        Just (VLit (LitScalar (chr (fromIntegral n))))
  ("__scalarToString", [VLit (LitScalar c)]) -> str (T.singleton c)
  ("__stringScalars", [VLit (LitStr s)]) ->
    Just (listV [VLit (LitScalar c) | c <- T.unpack s])
  ("__scalarCount", [VLit (LitStr s)]) -> int (fromIntegral (T.length s))
  ("__graphemeToString", [VLit (LitGrapheme g)]) -> str g
  ("__graphemeValid", [VLit (LitStr s)]) -> bool (isSingleGrapheme s)
  ("__graphemeOfString", [VLit (LitStr s)])
    | isSingleGrapheme s -> Just (VLit (LitGrapheme s))
  ("__stringGraphemes", [VLit (LitStr s)]) ->
    Just (listV [VLit (LitGrapheme g) | g <- graphemeClusters s])
  ("__graphemeCount", [VLit (LitStr s)]) ->
    int (fromIntegral (length (graphemeClusters s)))
  ("__normalize", [VLit (LitInt form), VLit (LitStr s)]) ->
    let f = case form of
          0 -> NFC
          1 -> NFD
          2 -> NFKC
          _ -> NFKD
     in str (normalizeText f s)
  ("__caseFold", [VLit (LitStr s)]) -> str (T.toCaseFold s)
  ("__stringWords", [VLit (LitStr s)]) ->
    Just (listV [VLit (LitStr w) | w <- wordChunks s])
  ("__stringSentences", [VLit (LitStr s)]) ->
    Just (listV [VLit (LitStr w) | w <- sentenceChunks s])
  ("__byteToNat", [VLit (LitByte w)]) -> int (fromIntegral w)
  ("__natToByte", [VLit (LitInt n)]) -> Just (VLit (LitByte (fromIntegral (n `mod` 256))))
  -- §29.3 hash mixing: FNV-1a over a 64-bit lane, deterministic per run
  -- §29.1 std.atomic bitwise internals (two's-complement over Integer)
  ("__intAnd", [VLit (LitInt a), VLit (LitInt b)]) -> int (a .&. b)
  ("__intOr", [VLit (LitInt a), VLit (LitInt b)]) -> int (a .|. b)
  ("__intXor", [VLit (LitInt a), VLit (LitInt b)]) -> int (a `xor` b)
  ("__hashMixInt", [VLit (LitInt s), VLit (LitInt v)]) -> int (fnvMixInteger s v)
  ("__hashMixDouble", [VLit (LitInt s), VLit (LitDouble d)]) ->
    int (fnvMixInteger s (toInteger (castDoubleToWord64 d)))
  ("__hashMixString", [VLit (LitInt s), VLit (LitStr t)]) ->
    int (fnvMixBytes s (TE.encodeUtf8 t))
  ("__hashMixBytes", [VLit (LitInt s), VLit (LitBytes bs)]) ->
    int (fnvMixBytes s bs)
  ("stringAppend", [VLit (LitStr a), VLit (LitStr b)]) -> Just (VLit (LitStr (a <> b)))
  ("showInt", [VLit (LitInt a)]) -> str (T.pack (show a))
  ("primitiveIntToString", [VLit (LitInt a)]) -> str (T.pack (show a))
  ("showDouble", [VLit (LitDouble a)]) -> str (T.pack (show a))
  ("showStringLit", [VLit (LitStr a)]) -> str (T.pack (show a))
  ("showScalar", [VLit (LitScalar a)]) -> str (T.pack (show a))
  ("intToDouble", [VLit (LitInt a)]) -> dbl (fromInteger a)
  ("natOfInt", [VLit (LitInt a)]) -> int a
  ("natToInt", [VLit (LitInt a)]) -> int a
  -- partial: a negative Int has no Nat image; the application stays
  -- stuck and is reported as a runtime error
  ("intToNat", [VLit (LitInt a)]) | a >= 0 -> int a
  -- discard a (linear) value: implicit type argument + the value
  ("unsafeConsume", [_, _]) -> Just (VCtor prelUnit [])
  -- §20 collection carriers are list-backed at runtime (§20.10.11
  -- as-if rule); conversion/wrapping is the identity on the element
  -- stream (modes, quantities, and orderedness are static metadata)
  ("__queryFromList", [v]) -> Just v
  ("__queryToList", [v]) -> Just v
  ("__setFromList", [v]) -> Just v
  ("__setToList", [v]) -> Just v
  ("__arrayFromList", [v]) -> Just v
  ("__arrayToList", [v]) -> Just v
  -- §28.2 total in-bounds index over the list-backed array; the in-bounds
  -- proof guarantees the element exists, so out-of-bounds traps (stuck).
  ("__arrayIndexUnsafe", [xs, VLit (LitInt i)]) -> indexList xs i
  -- MUTABLE-ARRAY-DESIGN §4.1: arrayLen is PURE — an O(1) read of the length
  -- cached in the runtime array value (mirrors the native karr_len reading the
  -- stored K_ARRAY.len field, no IO).  Returns the count as an Int (the Nat
  -- surface re-wraps it via natOfInt).
  ("__arrayLen", [VArr n _]) -> int (fromIntegral n)
  -- §28.2 subst/pathInd transport is the identity on the runtime payload
  -- (the equality witness is erased and proof-irrelevant)
  ("__transport", [v]) -> Just v
  -- §20.2 range enumeration over the §28.2.3 Rangeable element types.
  -- Integer/Nat values share the LitInt representation; UnicodeScalar
  -- values are LitScalar (surrogates excluded by construction).
  ("__rangeEnum", [VLit (LitInt lo), VLit (LitInt hi), excl])
    | Just ex <- asBoolV excl ->
        let top = if ex then hi - 1 else hi
         in Just (listV [VLit (LitInt n) | n <- [lo .. top]])
  ("__rangeEnum", [VLit (LitScalar lo), VLit (LitScalar hi), excl])
    | Just ex <- asBoolV excl ->
        let topC = if ex then pred hi else hi
            codes = [c | c <- [ord lo .. ord topC], not (c >= 0xD800 && c <= 0xDFFF)]
         in Just (listV [VLit (LitScalar (chr c)) | c <- codes])
  ("__mapFromEntries", [v]) -> Just v
  ("__mapToList", [v]) -> Just v
  -- §21.6 'sameSymbol' compares resolved declaration identity
  ("sameSymbol", [VPrim "__symbolV" [VLit (LitStr a)], VPrim "__symbolV" [VLit (LitStr b)]]) ->
    bool (a == b)
  -- §23 staged code (the interpreter models a generative code value by
  -- its present-stage value; every constructed Code value is closed
  -- under §23.7 by construction)
  ("__codeEscape", [VPrim "__codeQuote" [v]]) -> Just v
  ("closeCode", [VPrim "__codeQuote" [v]]) ->
    Just (VCtor prelSome [VPrim "__closedCode" [v]])
  ("genlet", [c@(VPrim "__codeQuote" _)]) -> Just c
  _ -> Nothing
  where
    insertField f [] = [f]
    insertField f@(l, _) (g@(l', _) : rest)
      | l <= l' = f : g : rest
      | otherwise = g : insertField f rest
    int = Just . VLit . LitInt
    dbl = Just . VLit . LitDouble
    str = Just . VLit . LitStr
    -- §6.1.7 libm floor/ceil as Double -> Double, IEEE semantics preserved:
    -- floor/ceil of NaN is NaN and of ±Infinity is ±Infinity (Haskell's
    -- 'floor'/'ceiling' return an Integral and diverge on those, so we guard).
    cDoubleFloor :: Double -> Double
    cDoubleFloor a
      | isNaN a || isInfinite a = a
      | otherwise = fromInteger (floor a)
    cDoubleCeil :: Double -> Double
    cDoubleCeil a
      | isNaN a || isInfinite a = a
      | otherwise = fromInteger (ceiling a)
    -- §6.1.7 render exactly as C's snprintf("%.*f"): 'showFFloat' agrees with C
    -- on every FINITE value (digits, round-half-to-even, the sign of -0.0); the
    -- ONLY divergence is the special-value spelling, which C prints lowercase
    -- (nan / inf / -inf) — so we match that here.  'prec' is clamped to C's
    -- runtime bound [0, 99].
    showFixedC :: Int -> Double -> String
    showFixedC prec a
      | isNaN a = "nan"
      | isInfinite a = if a < 0 then "-inf" else "inf"
      | otherwise = showFFloat (Just (max 0 (min 99 prec))) a ""
    -- a normalized rational n/d (d > 0, gcd 1) as the stuck spine
    -- '__rat (LitInt n) (LitInt d)'
    rat :: Integer -> Integer -> Maybe Value
    rat n d
      | d == 0 = Nothing
      | otherwise =
          let s = if d < 0 then -1 else 1
              g = gcd n d
              g' = if g == 0 then 1 else g
           in Just (VPrim "__rat" [VLit (LitInt (s * n `div` g')), VLit (LitInt (s * d `div` g'))])
    asRat :: Value -> Maybe (Integer, Integer)
    asRat v = case v of
      VPrim "__rat" [VLit (LitInt n), VLit (LitInt d)] -> Just (n, d)
      _ -> Nothing
    asBoolV :: Value -> Maybe Bool
    asBoolV v = case v of
      VCtor g [] | g == prelTrue -> Just True
      VCtor g [] | g == prelFalse -> Just False
      _ -> Nothing
    -- walk a cons-list value to its i-th element (0-based); Nothing when
    -- the list runs out (out of bounds) so the application stays stuck
    indexList :: Value -> Integer -> Maybe Value
    indexList v i = case v of
      VCtor g [h, t]
        | g == prelCons, i <= 0 -> Just h
        | g == prelCons -> indexList t (i - 1)
      _ -> Nothing
    -- exact decode of a finite binary64 into a reduced ratio
    doubleToRatio :: Double -> (Integer, Integer)
    doubleToRatio d
      | isNaN d || isInfinite d = (0, 1)
      | otherwise =
          let r = toRational d
           in (numerator r, denominator r)
    bytes = Just . VLit . LitBytes
    bool b = Just (VCtor (prelBoolV b) [])
    listV = foldr (\x acc -> VCtor prelCons [x, acc]) (VCtor prelNil [])
    someV x = VCtor prelSome [x]
    noneV = VCtor prelNone []
    recV = VRecordV
    -- longest prefix of @bs@ that is valid UTF-8, plus the trailing bytes
    -- that are either an incomplete final sequence or the first invalid run
    splitValidUtf8Prefix :: BS.ByteString -> (BS.ByteString, BS.ByteString)
    splitValidUtf8Prefix bs = go (BS.length bs)
      where
        go n
          | n <= 0 = (BS.empty, bs)
          | otherwise =
              let pre = BS.take n bs
               in case TE.decodeUtf8' pre of
                    Right _ -> (pre, BS.drop n bs)
                    Left _ -> go (n - 1)
    -- does @bs@ contain a definitely-invalid byte (not merely an
    -- incomplete trailing sequence)?
    utf8HasInvalid :: BS.ByteString -> Bool
    utf8HasInvalid bs = case TE.decodeUtf8' bs of
      Right _ -> False
      Left _ -> not (isIncompleteUtf8Tail bs)
    -- a run is an incomplete tail when some proper extension makes it
    -- valid (i.e. it is a strict prefix of a valid encoding)
    isIncompleteUtf8Tail :: BS.ByteString -> Bool
    isIncompleteUtf8Tail bs =
      any (\sfx -> either (const False) (const True) (TE.decodeUtf8' (bs <> sfx)))
        [BS.pack ext | ext <- [[0x80], [0x80, 0x80], [0x80, 0x80, 0x80]]]
    clampNat n = if n < 0 then 0 else fromIntegral n
    -- decode a (possibly partly-evaluated) cons-list of Byte literals
    listOfBytes :: Value -> Maybe [Word8]
    listOfBytes v = case v of
      VCtor g [] | g == prelNil -> Just []
      VCtor g [VLit (LitByte w), t] | g == prelCons -> (w :) <$> listOfBytes t
      _ -> Nothing
    -- offset of the first occurrence of @sep@ in @bs@ (empty sep -> 0)
    bytesBreakIndex :: BS.ByteString -> BS.ByteString -> Maybe Int
    bytesBreakIndex sep bs
      | BS.null sep = Just 0
      | otherwise = go 0 bs
      where
        go off rest
          | BS.length rest < BS.length sep = Nothing
          | sep `BS.isPrefixOf` rest = Just off
          | otherwise = go (off + 1) (BS.drop 1 rest)
    pad2 s = if length s < 2 then replicate (2 - length s) '0' ++ s else s
    -- FNV-1a over one 64-bit lane; integers mix their 8 low-endian bytes
    fnvMixByte :: Integer -> Word8 -> Integer
    fnvMixByte s w =
      let s64 = fromIntegral s :: Word64
       in fromIntegral ((s64 `xor` fromIntegral w) * 1099511628211)
    fnvMixBytes = BS.foldl' fnvMixByte
    fnvMixInteger s v =
      foldl fnvMixByte s [fromIntegral ((v `div` (256 ^ i)) `mod` 256) :: Word8 | i <- [0 .. 7 :: Int]]
    identicalIEEE a b = (a == b && (1 / a == 1 / b)) || (a /= a && b /= b)

-- | Context-aware primitive reduction: the pure table first, then the
-- §18.1 algebraic-effect kernel (whose continuations are ordinary
-- closure values, so the driver needs application).
evalPrimCtx :: EvalCtx -> Text -> [Value] -> Maybe Value
-- Quotation represents a neutral 'CForceE' as the internal @force@ head.
-- Declaration-universe specialization quotes and re-evaluates closed values,
-- so this head must implement the same eliminator as the direct Core node or
-- partially applied polymorphic aliases change meaning during specialization.
evalPrimCtx ctx "force" [v] = Just (vforce ctx v)
evalPrimCtx ctx p args = case evalPurePrim p args of
  Just v -> Just v
  Nothing -> evalEffPrim ctx p args

-- | §29.6 std.debug runtime introspection. The primitives build the
-- std.debug 'DebugTree'\/'DebugEq' constructors by walking the runtime
-- value representation; representation that is hidden (sealed packages),
-- a function, a backend object, or stopped by the depth limit becomes
-- the corresponding 'OpaqueValue'\/'Unknown' reason (§29.6).
debugGN :: Text -> GName
debugGN = GName modDebug

debugListV :: [Value] -> Value
debugListV = foldr (\h t -> VCtor prelCons [h, t]) (VCtor prelNil [])

debugOptV :: Maybe Value -> Value
debugOptV = maybe (VCtor prelNone []) (\v -> VCtor prelSome [v])

-- literal rendering kept local to avoid a dependency on Kappa.Pretty
debugLitText :: Literal -> Text
debugLitText = \case
  LitInt n -> T.pack (show n)
  LitDouble d -> T.pack (show d)
  LitStr s -> s
  LitScalar c -> T.singleton c
  LitByte w -> T.pack (show w)
  LitBytes bs -> T.pack ("<" <> show (BS.length bs) <> " bytes>")
  LitGrapheme g -> g

-- | The reason a value is not transparently inspectable\/comparable, or
-- 'Nothing' when its representation is available structurally.
debugOpaqueReason :: Value -> Maybe Text
debugOpaqueReason = \case
  VLam {} -> Just "FunctionValue"
  VPrim {} -> Just "FunctionValue"
  VThunkV {} -> Just "FunctionValue"
  VLazyV {} -> Just "FunctionValue"
  VRef {} -> Just "ForeignValue"
  VArr {} -> Just "ForeignValue"
  VMVar {} -> Just "ForeignValue"
  VFiber {} -> Just "ForeignValue"
  VScope {} -> Just "ForeignValue"
  VFiberRef {} -> Just "ForeignValue"
  VTVar {} -> Just "ForeignValue"
  VIOAction {} -> Just "ForeignValue"
  VSealV {} -> Just "Opaque"
  VQuote {} -> Just "Unsupported"
  VRigid {} -> Just "Unsupported"
  VFlex {} -> Just "Unsupported"
  VGlobN {} -> Just "Unsupported"
  VMatchN {} -> Just "Unsupported"
  VProjN {} -> Just "Unsupported"
  _ -> Nothing

debugInspect :: EvalCtx -> Int -> Value -> Value
debugInspect ctx depth v0
  | depth <= 0 = VCtor (debugGN "OpaqueValue") [VCtor (debugGN "DepthLimit") []]
  | otherwise = case force ctx v0 of
      VLit l -> VCtor (debugGN "Scalar") [VLit (LitStr (debugLitText l))]
      VCtor g args -> node (gnameText g) [field Nothing a | a <- args]
      VInject tag w -> node tag [field Nothing w]
      VRecordV fs -> node "Record" [field (Just lbl) w | (lbl, w) <- fs]
      other -> case debugOpaqueReason other of
        Just r -> VCtor (debugGN "OpaqueValue") [VCtor (debugGN r) []]
        Nothing -> VCtor (debugGN "OpaqueValue") [VCtor (debugGN "Unsupported") []]
  where
    node tag fs = VCtor (debugGN "Node") [VLit (LitStr tag), debugListV fs]
    field mlabel w =
      VCtor (debugGN "DebugField")
        [debugOptV (VLit . LitStr <$> mlabel), debugInspect ctx (depth - 1) w]

debugRender :: EvalCtx -> Int -> Value -> Text
debugRender ctx depth v0
  | depth <= 0 = "<\x2026>"
  | otherwise = case force ctx v0 of
      VLit l -> debugLitText l
      VCtor g [] -> gnameText g
      VCtor g args -> gnameText g <> "(" <> T.intercalate " " (map (debugRender ctx (depth - 1)) args) <> ")"
      VInject tag w -> tag <> " " <> debugRender ctx (depth - 1) w
      VRecordV fs ->
        "(" <> T.intercalate ", " [lbl <> " = " <> debugRender ctx (depth - 1) w | (lbl, w) <- fs] <> ")"
      other -> case debugOpaqueReason other of
        Just r -> "<" <> r <> ">"
        Nothing -> "<opaque>"

debugCompare :: EvalCtx -> Value -> Value -> Value
debugCompare ctx x y =
  case orMaybe (debugOpaqueReason (force ctx x)) (debugOpaqueReason (force ctx y)) of
    Just r -> VCtor (debugGN "Unknown") [VCtor (debugGN r) []]
    Nothing ->
      if convertible ctx 0 x y
        then VCtor (debugGN "Equal") []
        else VCtor (debugGN "Different") []
  where
    orMaybe (Just a) _ = Just a
    orMaybe Nothing b = b

-- | The §30.2.2.7 effect kernel over the runtime 'Eff' tree
-- representation: @__EffPure v@ for a finished computation and
-- @__EffOp label op payload cont@ for a suspended operation, where
-- @cont@ is the captured continuation (a closure — re-entrant, so
-- multi-shot resumption per §32.2.14 is supported).
evalEffPrim :: EvalCtx -> Text -> [Value] -> Maybe Value
evalEffPrim ctx p args = case (p, args) of
  -- §29.1 representation equality for atomicCompareExchange (the
  -- interpreter's canonical value representation IS the atomic rep)
  ("__atomicRepEq", [x, y])
    | isCanonicalRt x && isCanonicalRt y ->
        Just
          ( VCtor
              (prelBoolV (convertible ctx 0 x y))
              []
          )
    where
      isCanonicalRt v = case force ctx v of
        VLit _ -> True
        VCtor _ _ -> True
        VRecordV _ -> True
        VInject _ _ -> True
        _ -> False
  -- §12.4.3 first-class borrowed views. At runtime a borrow IS its
  -- value (borrows carry no runtime witness), so `captureBorrow x`
  -- reifies the view as the value itself and `withBorrowView v k`
  -- eliminates it by reinstating the borrowed binder — i.e. applies
  -- the continuation to the viewed value. The forall (ρ, a, r) are
  -- erased and do not reach the primitive.
  ("captureBorrow", [x]) -> Just x
  ("withBorrowView", [v, k]) -> Just (vapp ctx k Expl v)
  -- §29.6 std.debug introspection: walk the runtime value into the
  -- std.debug DebugTree / DebugEq constructors (representation-only; no
  -- trait evidence is consulted).
  ("__debugInspect", [x]) -> Just (debugInspect ctx 64 x)
  ("__debugRender", [x]) -> Just (VLit (LitStr (debugRender ctx 64 x)))
  ("__debugCompare", [x, y]) -> Just (debugCompare ctx x y)
  -- runPure : Eff <[ ]> a -> a (§18.1.14)
  ("runPure", [comp]) -> case force ctx comp of
    VCtor g [v] | g == prelEffPure -> Just v
    _ -> Nothing
  -- monadic bind over the tree (Eff is a Monad, §18.1.14)
  ("__effBind", [m, f]) -> case force ctx m of
    VCtor g [v] | g == prelEffPure -> Just (vapp ctx f Expl v)
    VCtor g [l, op, a, cont] | g == prelEffOp ->
      -- Op l op a (\x -> __effBind (cont x) f)
      Just (VCtor g [l, op, a, VLamM Ordinary Expl QW "x" (Closure [f, cont] bindBody)])
    _ -> Nothing
  -- §18.7/§32.2.19 Eff-carrier do-scope / exit-action nodes (Stage 4a).
  -- `__effDoscope` delimits a do-scope; under `runPure` it is transparent (it adds
  -- no value, only an exit-action frame the native runtime drains).
  ("__effDoscope", [c]) -> Just (force ctx c)
  -- `__effDefer a` registers `a : Eff r Unit` as an exit action.  An EARLIER
  -- comment reduced this to `pure Unit`, discarding `a` on the premise that a pure
  -- Eff body has "no observable effect".  That premise is WRONG: handler-threaded
  -- state under a `runPure`-eliminated handler IS observable — a defer that
  -- performs `tell`/`get`/... into an enclosing handler this interpreter models
  -- (__handleEff) contributes to the handler's result.  Discarding the body made
  -- the interpreter an UNSOUND differential oracle (it disagreed with the native
  -- runtime, which runs the defer body).  Fix: run the body, yielding its Unit.
  -- Modelling-limitation note: this runs `a` at the REGISTRATION point rather than
  -- at masked-LIFO scope exit, so the interpreter does not reproduce defer ORDER
  -- (or the §32.2.20 not-yet-run-at-this-point timing).  For the carriers this
  -- oracle is used against — order-insensitive aggregations like a summing `Tell`
  -- handler, and single-defer cases — the observable VALUE matches the native
  -- runtime; faithful exit-time ordering is the IO do-kernel's job, not this pure
  -- Eff path.  (`a` is `Eff r Unit`, so sequencing it via the enclosing __effBind
  -- threads its perform/return effects and then continues with Unit.)
  ("__effDefer", [a]) -> Just (force ctx a)
  -- __handleEff deep label ret ops comp (HandleShallow plus the
  -- §18.1.22 deep recursive driver)
  ("__handleEff", [deepV, label, ret, ops, comp]) -> case force ctx comp of
    VCtor g [v] | g == prelEffPure -> Just (vapp ctx ret Expl v)
    VCtor g [l, opName, a, cont]
      | g == prelEffOp, sameLabel (force ctx l) (force ctx label) ->
          -- nearest matching handler intercepts (§18.1.18); a deep
          -- handler's k reinstalls itself around the resumption
          case (force ctx opName, force ctx ops) of
            (VLit (LitStr opn), VRecordV fs)
              | Just clause <- lookup opn fs ->
                  let k
                        | isTrueV (force ctx deepV) = reinstall cont
                        | otherwise = cont
                      runtimeClause = instantiateErasedClause clause
                   in Just (vapp ctx (vapp ctx runtimeClause Expl a) Expl k)
            _ -> Nothing
      | g == prelEffOp ->
          -- operations at other labels propagate outward unchanged,
          -- with this handler still installed inside the resumption
          Just (VCtor g [l, opName, a, reinstall cont])
    _ -> Nothing
    where
      reinstall cont = VLamM Ordinary Expl QW "x" (Closure [cont, ops, ret, label, deepV] handleBody)
  _ -> Nothing
  where
    effBindG = CGlob prelEffBind
    handleEffG = CGlob prelHandleEff
    appE = CApp Expl
    -- env [f, cont], binder x: __effBind (cont x) f
    bindBody = appE (appE effBindG (appE (CVar 2) (CVar 0))) (CVar 1)
    -- env [cont, ops, ret, label, deepV], binder x:
    -- __handleEff deepV label ret ops (cont x)
    handleBody =
      appE
        (appE (appE (appE (appE handleEffG (CVar 5)) (CVar 4)) (CVar 3)) (CVar 2))
        (appE (CVar 1) (CVar 0))
    sameLabel a b = case (a, b) of
      (VGlobN g1 [], VGlobN g2 []) -> g1 == g2
      (VCtor g1 [], VCtor g2 []) -> g1 == g2
      (VLit (LitStr label1), VLit (LitStr label2)) -> label1 == label2
      _ -> False
    isTrueV = \case
      VCtor g [] | g == prelTrue -> True
      _ -> False
    -- Operation-local `forall` parameters are represented by erased implicit
    -- lambdas in typed Core, but the OpCall runtime payload intentionally does
    -- not carry them. Native lowering erases those lambdas; the interpreter
    -- mirrors that boundary by instantiating only the authenticated Q0/Impl
    -- prefix with an inert value before applying payload and resumption.
    instantiateErasedClause clause = case force ctx clause of
      lambda@(VLamM _ Impl Q0 _ _) ->
        instantiateErasedClause (vapp ctx lambda Impl (VRecordV []))
      runtimeClause -> runtimeClause
