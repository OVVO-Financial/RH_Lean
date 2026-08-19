import Mathlib
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourFubini
import RHLean.Analysis.K2CenteredFinite

/-!
# Analytic interface for the centered K2 theorem

This file records the exact analytic statements which close the finite proof. They are theorem parameters here, not axioms. A fully machine-checked unconditional file must discharge them from a formal strong-PNT or sharp-Mertens library.

This separation is intentional: it prevents an unproved analytic estimate from being disguised as part of the finite algebra.
-/

noncomputable section
open Filter Finset Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

local notation "γE" => Real.eulerMascheroniConstant

/-- The analytic consequences actually needed by the finite argument. -/
structure K2ClassicalMomentInput : Prop where
  r_tendsto_zero : Tendsto k2r atTop (𝓝 0)
  r_mul_log_tendsto_zero :
    Tendsto (fun N : ℕ => k2r N * Real.log (N : ℝ)) atTop (𝓝 0)
  c3_tendsto : ∃ L : ℝ, Tendsto k2C3 atTop (𝓝 L)

/-- The desired centered boundedness statement. -/
def K2CenteredBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 3 ≤ N →
      |nativePNTSignedSecondSelbergKernelRecipMass N +
        2 * γE * Real.log (N : ℝ)| ≤ C

/-- Stronger asymptotic target, with the limiting constant left abstract. -/
def K2CenteredConverges : Prop :=
  ∃ L : ℝ,
    Tendsto
      (fun N : ℕ =>
        nativePNTSignedSecondSelbergKernelRecipMass N +
          2 * γE * Real.log (N : ℝ))
      atTop (𝓝 L)

/-!
The mathematical proof in `research/K2_CENTERED_CLASSICAL_PROOF_COMPLETE.md` proves:

* `K2ClassicalMomentInput` from the classical zero-free-region Mertens bound;
* `K2CenteredConverges` from `K2ClassicalMomentInput` by the two finite Abel identities plus the harmonic floor comparison;
* the limiting constant is `4 * γ^2 + 6 * γ₁`.

The public Lean ecosystem currently has a checked strong PNT for `psi` and the zeta near-one expansion, but the direct sharp-Mertens contour file publicly labels its final contour estimate as unfinished. Therefore this interface is kept assumption-explicit until that last analytic bridge is machine-checked.
-/

end RHLean.Analysis
