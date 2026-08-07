import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelRawPeriod
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelLocalSpectrum
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse

/-!
# Periodic-raw conductor attack umbrella

This module collects the exact reductions that replace the oversized zero-padded
raw torus by the natural square-sensitive CRT period on every primorial block
from `k = 2` onward, while preserving the historical corrected residual exactly.

The current layer also exposes the exact local `p^2` Fourier trichotomy and the
signed reduced-conductor response.  A raw shell that is proved constant can be
collapsed, before norms, to its exact additive-character/Ramanujan kernel while
retaining the smooth correction in the same signed packet.

No analytic estimate is claimed here.
-/
