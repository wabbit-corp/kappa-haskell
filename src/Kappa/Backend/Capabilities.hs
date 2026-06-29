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

-- | The runtime capabilities the native profile advertises (§27.6). Classified
-- @blocking@ native calls are preserved into blocking @K_NATIVE@ actions and
-- routed through the runtime's off-worker blocking lane, so @rt-blocking@ is
-- part of the native profile. @blocking-cancellable@ remains unavailable until a
-- binding can name a safe cancellation mechanism and the runtime has a
-- cancellation-aware bridge.
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
