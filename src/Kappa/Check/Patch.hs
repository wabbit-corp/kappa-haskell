-- | Representation-independent source validation for record patches.
module Kappa.Check.Patch
  ( PatchSourceViolation (..)
  , patchSourceViolations
  ) where

import Data.List (isPrefixOf, nubBy)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Source (Span)
import Kappa.Syntax
  ( Name
  , PatchItem (..)
  , PatchValue (..)
  , nameSpan
  , nameText
  )

data PatchSourceViolation
  = DuplicateUpdatePath !Span !Text
  | DuplicateExtensionLabel !Span !Text
  | UpdatePrefixConflict !Span !Text
  | MixedPatchLabelConflict !Span !Text
  deriving stock (Eq, Show)

-- | Check the identity and prefix rules of Spec §13.2.5/§13.2.6 without
-- consulting a receiver type or runtime representation.
patchSourceViolations :: Span -> [PatchItem] -> [PatchSourceViolation]
patchSourceViolations fallbackSpan items =
  [ DuplicateUpdatePath (pathSpan path) (renderPath path)
  | path <- duplicateBy pathKey updatePaths
  ]
    ++ [ DuplicateExtensionLabel (nameSpan name) (nameText name)
       | name <- duplicateBy nameText extensionNames
       ]
    ++ [ UpdatePrefixConflict (pathSpan prefix) (renderPath prefix)
       | prefix <- strictPrefixes
       ]
    ++ [ MixedPatchLabelConflict (nameSpan name) (nameText name)
       | name <- mixedLabelConflicts
       ]
  where
    updatePaths =
      [ path
      | PatchUpdate path (PatchValue _) <- items
      , not (null path)
      ]
    extensionNames = [name | PatchExtend name _ <- items]
    pathKey = map (\(implicitField, name) -> (implicitField, nameText name))
    strictPrefixes =
      nubBy
        (\left right -> pathKey left == pathKey right)
        [ prefix
        | prefix <- updatePaths
        , longer <- updatePaths
        , pathKey prefix /= pathKey longer
        , pathKey prefix `isPrefixOf` pathKey longer
        ]
    updateRootLabels =
      [ nameText name
      | (_, name) : _ <- updatePaths
      ]
    mixedLabelConflicts =
      nubBy (\left right -> nameText left == nameText right)
        [ name
        | name <- extensionNames
        , nameText name `elem` updateRootLabels
        ]
    pathSpan ((_, name) : _) = nameSpan name
    pathSpan [] = fallbackSpan

duplicateBy :: Eq key => (value -> key) -> [value] -> [value]
duplicateBy key values =
  [ value
  | value <- nubBy (\left right -> key left == key right) values
  , length (filter (\other -> key other == key value) values) > 1
  ]

renderPath :: [(Bool, Name)] -> Text
renderPath =
  T.intercalate "."
    . map (\(implicitField, name) -> (if implicitField then "@" else "") <> nameText name)
