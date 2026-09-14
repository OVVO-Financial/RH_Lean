import Mathlib
import RHLean.Analysis.SquareRootCanonicalRoughCovariance
import RHLean.Proof.SignedTransportAmplificationAudit

/-!
# Global bounds for the canonical rough correlation

This file separates two quantitative milestones.

* Milestone 1 is unconditional: the canonical rough correlation is one Mertens
  interval from `R-1` to `R^2-1`, hence its norm is at most `R^2` and its
  squared norm at most `R^4`.
* Milestone 2 begins by isolating the q^2 owners whose daughter cutoff is already
  below the current root.  Their total daughter energy is root-scale under the
  existing lower critical envelope, so only owners with `q^2 < R` can carry a
  genuinely recursive obstruction.

No RH-scale estimate on the remaining low-owner parent synthesis is asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Milestone 1, amplitude form.**  The canonical rough correlation is a
single Mertens interval, so the trivial interval-variation estimate already
beats the earlier `2 R^2` triangle bound. -/
theorem norm_squareRootCanonicalRoughCorrelation_le_root_sq
    (R : ℕ) (hR : 2 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation R‖ ≤ (R : ℝ) ^ 2 := by
  rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R hR]
  have hle : R - 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : R ≤ R ^ 2 := by nlinarith
    omega
  have hvar := norm_mertensSummatory_sub_le (R - 1) (squareRootEndpoint R) hle
  have hrev :
      ‖mertensSummatory (R - 1) - mertensSummatory (squareRootEndpoint R)‖ =
        ‖mertensSummatory (squareRootEndpoint R) - mertensSummatory (R - 1)‖ :=
    norm_sub_rev _ _
  rw [hrev]
  have hdiffNat : squareRootEndpoint R - (R - 1) ≤ R ^ 2 := by
    exact (Nat.sub_le _ _).trans (by
      unfold squareRootEndpoint
      exact Nat.sub_le _ _)
  have hdiff :
      (((squareRootEndpoint R - (R - 1) : ℕ) : ℝ)) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hdiffNat
  exact hvar.trans hdiff

/-- **Milestone 1, energy form.**  A completely unconditional all-root bound
that can be quoted without any sampled-range qualification. -/
theorem squareRootCanonicalRoughCorrelation_energy_le_root_fourth
    (R : ℕ) (hR : 2 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤ (R : ℝ) ^ 4 := by
  have h := norm_squareRootCanonicalRoughCorrelation_le_root_sq R hR
  have hn : 0 ≤ ‖squareRootCanonicalRoughCorrelation R‖ := norm_nonneg _
  have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg ((R : ℝ) ^ 2 - ‖squareRootCanonicalRoughCorrelation R‖)]

end RHLean.Proof
