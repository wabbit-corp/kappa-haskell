-- | Host-level asynchronous exception delivery used only as a wake mechanism
-- by the reference interpreter.  Kappa's logical pending-interrupt state lives
-- in "Kappa.Interp"; this module controls whether the requesting fiber waits for
-- the target GHC thread to accept that wake.
module Kappa.AsyncException
  ( throwToAsync
  ) where

import Control.Concurrent (ThreadId, forkIO, throwTo)
import Control.Exception (Exception)
import Control.Monad (void)

-- | Request delivery to another host thread.
--
throwToAsync :: Exception e => ThreadId -> e -> IO ()
throwToAsync target exception =
  void (forkIO (throwTo target exception))
