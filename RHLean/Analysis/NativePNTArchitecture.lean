import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionEndpoint
import RHLean.Arithmetic.SignedBuchstabRecursion

/-!
# Native prime number theorem architecture

This module is the entry point for an elementary prime-number-theorem proof
inside the finite arithmetic architecture of `RH_Lean`.

The proof route is intentionally firewalled from any theorem asserting the
prime number theorem.  It may use Mathlib's definitions of the von Mangoldt,
Chebyshev and prime-counting functions, together with generic real analysis,
but the asymptotic theorem itself must be derived from the finite divisor,
prime-extension, Buchstab and reciprocal-scale identities developed here.

The intended route is

* finite von-Mangoldt divisor identities;
* the log-weighted prime-extension and square-correction identities already
  present in this repository;
* an elementary Selberg symmetry identity in reciprocal coordinates;
* the Selberg--Erdos contraction of the normalized Chebyshev error;
* transfer from `psi(x) ~ x` to `theta(x) ~ x` and then to
  `pi(x) ~ x / log x` by the existing elementary Chebyshev interfaces.

No zeta zero-free region, Perron formula, spectral decomposition, or imported
PNT theorem belongs in this dependency chain.
-/

noncomputable section

open Filter
open scoped BigOperators Chebyshev Topology

namespace RHLean.Analysis

/-- The architecture-native Chebyshev error.  Keeping the subtraction explicit
is convenient for the finite reciprocal recurrences used by the Selberg step. -/
def nativePNTError (x : ℝ) : ℝ := Chebyshev.psi x - x

/-- `psi(x) = x + o(x)`, the natural terminal form of the elementary Selberg
argument before transferring to the ordinary prime-counting function. -/
def NativePsiPNTStatement : Prop :=
  nativePNTError =o[atTop] (fun x : ℝ => x)

/-- Ordinary prime-number-theorem statement in ratio form on the real cutoff.
The floor is harmless because `Nat.primeCounting` is a step function. -/
def NativePrimeCountingPNTStatement : Prop :=
  Tendsto
    (fun x : ℝ =>
      ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) * Real.log x / x)
    atTop (nhds 1)

@[simp] theorem nativePNTError_eq (x : ℝ) :
    nativePNTError x = Chebyshev.psi x - x := rfl

end RHLean.Analysis
