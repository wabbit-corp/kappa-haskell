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
      CPi ic q n a b ->
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
      CRecordT fs -> "(" <> T.intercalate ", " [n <> " : " <> go 0 t | (n, t) <- fs] <> ")"
      CRecordV fs -> "(" <> T.intercalate ", " [n <> " = " <> go 0 t | (n, t) <- fs] <> ")"
      CProj e f -> go 2 e <> "." <> f
      CVariantT ms -> "(| " <> T.intercalate " | " (map (go 0) ms) <> " |)"
      CInject t e -> paren (p > 0) ("(| " <> go 0 e <> " : " <> t <> " |)")
      CLet _ n _ rhs body -> paren (p > 0) ("let " <> n <> " = " <> go 0 rhs <> " in " <> go 0 body)
      CLetRec _ n _ rhs body -> paren (p > 0) ("let rec " <> n <> " = " <> go 0 rhs <> " in " <> go 0 body)
      CMeta m -> "?m" <> tshow m
      CDo _ -> "do ..."
      CThunkE e -> paren (p > 1) ("thunk " <> go 2 e)
      CLazyE e -> paren (p > 1) ("lazy " <> go 2 e)
      CForceE e -> paren (p > 1) ("force " <> go 2 e)
      CIf c t f -> paren (p > 0) ("if " <> go 0 c <> " then " <> go 0 t <> " else " <> go 0 f)
    paren True t = "(" <> t <> ")"
    paren False t = t
    tshow :: Show a => a -> Text
    tshow = T.pack . show

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
