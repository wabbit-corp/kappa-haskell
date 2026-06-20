-- | Native backend runtime capability profile (§27.6) and the foreign-call
-- classification → capability requirement (§26.1.4).
--
-- §27.6 "Every backend profile MUST declare a runtime capability set." This
-- module is that declaration for the native (`zig`/`cc`) profile, plus the
-- rule that maps a raw foreign declaration's §26.1.4 classification to the
-- capabilities its invocation requires — so a binding that needs a capability
-- the profile does not advertise is rejected fail-closed (§26.1.4:26311,
-- §18.1.11:18683, §27.6:28186) rather than silently executed with weakened
-- semantics.
module Kappa.Backend.Capabilities
  ( nativeRuntimeCapabilities
  , ffiRequiredCapabilities
  ) where

import Data.Text (Text)
import Kappa.Build.Types (FfiClass (..))

-- | The runtime capabilities the native profile advertises (§27.6). The native
-- runtime is single-agent and synchronous: it realizes @rt-blocking@ as direct
-- execution on the sole agent (the agent IS the blocking lane, so a blocking
-- foreign call starves no concurrently-runnable fiber — §26.1.4:26304 holds
-- vacuously). It does NOT advertise @rt-blocking-cancel@ (no safe foreign-call
-- cancellation mechanism), so a @blocking-cancellable@ binding is rejected.
--
-- (This declares the binding-relevant capability subset; the full §27.6
-- obligations of @rt-core@'s concurrent scheduler are a separate runtime
-- concern tracked outside the native-binding path.)
nativeRuntimeCapabilities :: [Text]
nativeRuntimeCapabilities = ["rt-core", "rt-blocking", "rt-atomics"]

-- | The capabilities required to invoke a raw foreign declaration of the given
-- §26.1.4 classification. @nonblocking@ needs none (ordinary execution);
-- @blocking@ needs @rt-blocking@; @blocking-cancellable@ additionally needs a
-- safe-cancellation capability (@rt-blocking-cancel@) that the native profile
-- does not provide.
ffiRequiredCapabilities :: FfiClass -> [Text]
ffiRequiredCapabilities = \case
  FfiNonblocking -> []
  FfiBlocking -> ["rt-blocking"]
  FfiBlockingCancellable -> ["rt-blocking", "rt-blocking-cancel"]
