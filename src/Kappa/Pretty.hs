-- | Compact term rendering for diagnostics and variant member identity
-- tags (§31.3 canonical member rendering).
module Kappa.Pretty
  ( renderTerm
  , renderValueShallow
  ) where

import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Core

renderTerm :: Term -> Text
renderTerm = go 0
  where
    go :: Int -> Term -> Text
    go p = \case
      CVar i -> "@" <> tshow i
      CGlob g -> gnameText g
      CLam _ _ n b -> paren (p > 0) ("\\" <> n <> " -> " <> go 0 b)
      CPi ic q _ n a b ->
        paren (p > 0) $
          binder <> " -> " <> go 0 b
        where
          binder = case ic of
            Impl -> "(@" <> qtxt <> n <> " : " <> go 0 a <> ")"
            Expl
              | n == "_" && q == QW -> go 1 a
              | otherwise -> "(" <> qtxt <> n <> " : " <> go 0 a <> ")"
          qtxt = case q of
            QW -> ""
            Q0 -> "0 "
            Q1 -> "1 "
            QLe1 -> "<=1 "
            QGe1 -> ">=1 "
      CApp _ f a -> paren (p > 1) (go 1 f <> " " <> go 2 a)
      CSort 0 -> "Type"
      CSort n -> "Type" <> tshow n
      CLit l -> renderLit l
      CCtor g args
        | null args -> gnameText g
        | otherwise -> paren (p > 1) (T.unwords (gnameText g : map (go 2) args))
      CMatch s _ -> paren (p > 0) ("match " <> go 0 s <> " ...")
      -- §3.1.11 / §13.2.11: internal existential labels (`⟨wit_i⟩`,
      -- `⟨payload⟩`) are not source-addressable fields. They are hidden
      -- from user-facing renderings — a record carrying only such labels
      -- renders as the stable phrase `(an existential package)`.
      CRecordT fs ->
        case [(n, t) | (n, t) <- fs, not (isInternalLabel n)] of
          [] | not (null fs) -> "(an existential package)"
          fs' -> "(" <> T.intercalate ", " [n <> " : " <> go 0 t | (n, t) <- fs'] <> ")"
      CRecordV fs ->
        case [(n, t) | (n, t) <- fs, not (isInternalLabel n)] of
          [] | not (null fs) -> "(an existential package)"
          fs' -> "(" <> T.intercalate ", " [n <> " = " <> go 0 t | (n, t) <- fs'] <> ")"
      CProj e f
        | isInternalLabel f -> "(an opened existential witness)"
        | otherwise -> go 2 e <> "." <> f
      -- P0.4: render by name, identical to CProj (the index is backend-only).
      CProjAt e f _
        | isInternalLabel f -> "(an opened existential witness)"
        | otherwise -> go 2 e <> "." <> f
      CVariantT ms -> "(| " <> T.intercalate " | " (map (go 0) ms) <> " |)"
      CInject t e -> paren (p > 0) ("(| " <> go 0 e <> " : " <> t <> " |)")
      CLet _ n _ rhs body -> paren (p > 0) ("let " <> n <> " = " <> go 0 rhs <> " in " <> go 0 body)
      CLetRec _ n _ rhs body -> paren (p > 0) ("let rec " <> n <> " = " <> go 0 rhs <> " in " <> go 0 body)
      -- §3.1.11 internal-placeholder hygiene: an unsolved unification
      -- metavariable MUST NOT be shown as a raw solver id (`?m1238`).
      -- After zonking, any metavariable that survives is genuinely
      -- unknown, so it renders as the stable hole spelling `_`.
      CMeta _ -> "_"
      CDo _ _ -> "do ..."
      CSealE _ e -> paren (p > 1) ("seal " <> go 2 e)
      CSigT ls e ->
        case e of
          CRecordT fs ->
            "(" <> T.intercalate ", "
              [(if n `elem` ls then "opaque " else "") <> n <> " : " <> go 0 t | (n, t) <- fs]
              <> ")"
          _ -> go p e
      CThunkE e -> paren (p > 1) ("thunk " <> go 2 e)
      CLazyE e -> paren (p > 1) ("lazy " <> go 2 e)
      CForceE e -> paren (p > 1) ("force " <> go 2 e)
      CIf c t f -> paren (p > 0) ("if " <> go 0 c <> " then " <> go 0 t <> " else " <> go 0 f)
      CQuote _ slots -> "'{ ... }" <> (if null slots then "" else " [" <> tshow (length slots) <> " slots]")
    paren True t = "(" <> t <> ")"
    paren False t = t
    tshow :: Show a => a -> Text
    tshow = T.pack . show

-- | A §13.2.11 internal existential label (witness `⟨wit_i⟩` or the
-- anonymous payload `⟨payload⟩`): not a source-addressable field, so it
-- is suppressed in user-facing diagnostics (§3.1.11).
isInternalLabel :: Text -> Bool
isInternalLabel l = "⟨" `T.isPrefixOf` l

renderLit :: Literal -> Text
renderLit = \case
  LitInt n -> T.pack (show n)
  LitDouble d -> T.pack (show d)
  LitStr s -> T.pack (show s)
  LitScalar c -> T.pack (show c)
  LitByte w -> "b'\\x" <> T.pack (show w) <> "'"
  LitBytes bs -> "<" <> T.pack (show (BS.length bs)) <> " bytes>"
  LitGrapheme g -> "g'" <> g <> "'"

-- | Shallow value rendering for runtime messages.
renderValueShallow :: Value -> Text
renderValueShallow = \case
  VLit l -> renderLit l
  VCtor g args -> T.unwords (gnameText g : map (const "_") args)
  VRecordV fs -> "(" <> T.intercalate ", " (map fst fs) <> " = ...)"
  VLam {} -> "<function>"
  VInject t _ -> "(| _ : " <> t <> " |)"
  _ -> "<value>"
