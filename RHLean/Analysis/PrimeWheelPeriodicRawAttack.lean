import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelRawPeriod
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelLocalSpectrum
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse
import RHLean.Analysis.PrimeWheelRawUnitOrbit
import RHLean.Analysis.PrimeWheelRawShellConstancy

/-!
# Periodic-raw conductor attack umbrella

This module collects the exact reductions that replace the oversized zero-padded
raw torus by the natural square-sensitive CRT period on every primorial block
from `k = 2` onward, while preserving the historical corrected residual exactly.

The current layer exposes the exact local `p^2` Fourier trichotomy, the signed
reduced-conductor response, unit-orbit invariance of the actual periodic raw
spectrum, and the theorem that every reduced-conductor shell is one unit orbit.
Thus the shell-constancy hypothesis from the previous layer is discharged before
any norm is taken, while the smooth correction remains in the same signed
packet.

No analytic estimate is claimed here.
-/
