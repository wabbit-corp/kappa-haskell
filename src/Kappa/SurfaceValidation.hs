-- | Source-tree queries for diagnostics that must run independently of
-- elaboration demand. Keeping these total queries outside the checker makes
-- declaration validation reusable without extending the already monolithic
-- checker dependency cone.
module Kappa.SurfaceValidation
  ( quantityBorrowMarkerSpans
  ) where

import Kappa.Source (Span)
import Kappa.Syntax (Expr (..))
import Kappa.SyntaxOps (queryExprs)

-- | Every standalone @&@ retained by the parser as the dedicated §3.2.6
-- quantity/borrow-confusion node. Nested quotations are separate elaboration
-- scopes and are deliberately excluded by 'queryExprs'.
quantityBorrowMarkerSpans :: Expr -> [Span]
quantityBorrowMarkerSpans = queryExprs $ \case
  EQuantityBorrowMarker span' -> ([span'], False)
  _ -> ([], True)
