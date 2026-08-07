import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelRawPeriod
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelLocalSpectrum
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse
import RHLean.Analysis.PrimeWheelRawUnitOrbit

/-!
# Periodic-raw conductor attack umbrella

This module collects the exact reductions that replace the oversized zero-padded
raw torus by the natural square-sensitive CRT period on every primorial block
from `k = 2` onward, while preserving the historical corrected residual exactly.

The current layer exposes the exact local `p^2` Fourier trichotomy, the signed
reduced-conductor response, and unit-orbit invariance of the actual periodic raw
spectrum.  A raw shell that is proved to be one unit orbit can therefore be
collapsed, before norms, to its exact additive-character/Ramanujan kernel while
retaining the smooth correction in the same signed packet.

No analytic estimate is claimed here.
-/
