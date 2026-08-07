import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelRawPeriod
import RHLean.Analysis.PrimeWheelPeriodicRawBridge

/-!
# Periodic-raw conductor attack umbrella

This module collects the exact reductions that replace the oversized zero-padded
raw torus by the natural square-sensitive CRT period on every primorial block
from `k = 2` onward, while preserving the historical corrected residual exactly.

The next layer will add the explicit local Fourier trichotomy, conductor-shell
coefficients, and signed raw/smooth Ramanujan response.  No analytic estimate is
claimed here.
-/
