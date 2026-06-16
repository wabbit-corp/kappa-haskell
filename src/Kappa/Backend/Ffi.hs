-- | Names of the foreign primitives implemented by the full FFI runtime
-- unit (@runtime/kappart_ffi.c@: POSIX sockets + sqlite3).  Kept in
-- lock-step with that file so the code generator only emits an FFI
-- primitive the linked runtime actually implements; anything else is a
-- compile-time @E_BACKEND_UNSUPPORTED@.  The no-FFI build links
-- @kappart_ffi_stub.c@ and uses the empty set.
--
-- See docs/NATIVE_BACKEND.md §6 for the FFI surface and the HTTP+sqlite
-- demo that drives it.
module Kappa.Backend.Ffi
  ( ffiPrimNames
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)

-- | The FFI primitive names provided by @kappart_ffi.c@.
ffiPrimNames :: Set Text
ffiPrimNames =
  Set.fromList
    [ -- POSIX TCP sockets (a minimal blocking HTTP-server surface)
      "__tcpListen" --  Int -> IO Listener       (bind+listen on a port)
    , "__tcpAccept" --  Listener -> IO Conn       (accept one connection)
    , "__connRead" --   Conn -> IO String         (read the request bytes)
    , "__connWrite" --  Conn -> String -> IO Unit (write the response)
    , "__connClose" --  Conn -> IO Unit
    , "__listenClose" -- Listener -> IO Unit
      -- sqlite3
    , "__sqliteOpen" --   String -> IO Db
    , "__sqliteExec" --   Db -> String -> IO Unit       (run a statement)
    , "__sqliteQueryInt" -- Db -> String -> IO Int      (first column of first row)
    , "__sqliteQueryText" -- Db -> String -> IO String  (first column of first row)
    , "__sqliteClose" --  Db -> IO Unit
    ]
