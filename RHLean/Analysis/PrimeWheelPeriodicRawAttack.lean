import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelRawPeriod
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelLocalSpectrum
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse
import RHLean.Analysis.PrimeWheelRawUnitOrbit
import RHLean.Analysis.PrimeWheelRawShellConstancy
import RHLean.Analysis.RamanujanDivisorBoundary
import RHLean.Analysis.PrimeWheelRamanujanIdentification
import RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction
import RHLean.Analysis.PrimeWheelRawConductorCoefficient
import RHLean.Analysis.PrimeWheelRawConductorWeight

/-!
# Periodic-raw conductor attack umbrella

This module collects the exact reductions that replace the oversized zero-padded
raw torus by the natural square-sensitive CRT period on every primorial block
from `k = 2` onward, while preserving the historical corrected residual exactly.

The current layer exposes the exact local `p^2` Fourier trichotomy, the signed
reduced-conductor response, unit-orbit invariance and shell constancy of the
actual periodic raw spectrum, and the identification of every occupied reduced-
conductor character kernel with the classical divisor-form Ramanujan sum.
For every conductor `q > 1`, both the raw interval and every shifted smooth
interval have their common bulk term cancelled exactly, leaving only finite
Möbius-weighted divisor-residue boundary defects.  The remaining common raw
shell Fourier coefficient is also eliminated: it is an exact finite arithmetic
divisor-tail sum indexed by the three local exponents `0,1,2`.

The normalized raw conductor coefficient now has an exact local product law.
First-power conductor coordinates cost at most `2/p`, square coordinates cost
exactly `1/p^2`, and the total absolute mass over all exponent-pattern
conductors is the finite Euler product `prod_p (1 + 1/p^2)`.  A marked
generating identity isolates the wheel primes not dividing the pinned
primorial lower endpoint.  Thus the remaining analytic target may be phrased as
a weighted conductor-average problem rather than a uniform unweighted pinned
estimate.

No analytic estimate is claimed here.
-/
