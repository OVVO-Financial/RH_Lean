import Mathlib
import RHLean.Proof.PostRootCovariancePowerEnvelope
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

/-- The exact scalar post-root Euler finite difference from the complete LCM
boundary, written as the falling-factorial Mertens field `M(M-1)`. -/
def postRootFallingEnergyFiniteDifference (W : ℕ) : ℝ :=
  (realMertensLength (W + 1) ^ 2 - realMertensLength (W + 1)) -
    ∑ p ∈ postRootPrimeFamilySet W,
      (realMertensLength (W / p + 1) ^ 2 -
        realMertensLength (W / p + 1))

/-- The scalar falling-energy finite difference is exactly twice the literal
post-root super-endpoint LCM-boundary mass. -/
theorem postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass
    (W : ℕ) :
    postRootFallingEnergyFiniteDifference W =
      2 * (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) := by
  unfold postRootFallingEnergyFiniteDifference
  exact (two_mul_sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_lengthFiniteDifference W).symm

/-- Positive power scale dominates one endpoint unit. -/
theorem endpoint_le_postRootPowerScale
    {ε : ℝ} (hε : 0 < ε) {W : ℕ} (hW : 2 ≤ W) :
    (W : ℝ) ≤ Real.rpow (W : ℝ) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast (show 1 ≤ W by omega)
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  simpa only [Real.rpow_one] using h

/-- Positive-power control of the exact scalar falling-energy finite difference.
This is the #597 boundary seam with the weaker exponent needed by #599. -/
def PostRootFallingEnergyFiniteDifferencePowerStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ W : ℕ, 2 ≤ W →
        postRootFallingEnergyFiniteDifference W ≤
          D * Real.rpow (W : ℝ) (1 + ε)

/-- A positive-power bound on the scalar falling-energy finite difference gives
the post-root covariance power remainder.  The only loss is one endpoint unit
from the already-packed complete-LCM interior. -/
theorem postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower
    (hfall : PostRootFallingEnergyFiniteDifferencePowerStatement) :
    PostRootCovariancePowerRemainderStatement := by
  intro ε hε
  rcases hfall ε hε with ⟨D, hD, hfallBound⟩
  refine ⟨D / 2 + 1, by positivity, ?_⟩
  intro W hW
  have hf := hfallBound W hW
  have hboundary :=
    postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass W
  have hinterior :=
    sum_postRootCovarianceRemainderInteriorLcmCarrier_le_endpoint W
  have hsplit :=
    postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
  have hscale := endpoint_le_postRootPowerScale hε hW
  have hpowNonneg : 0 ≤ Real.rpow (W : ℝ) (1 + ε) := by
    have hWpos : (0 : ℝ) < (W : ℝ) := by
      exact_mod_cast (show 0 < W by omega)
    exact (Real.rpow_pos_of_pos hWpos _).le
  nlinarith

/-- Conversely, the post-root covariance power remainder controls the scalar
falling-energy finite difference.  The lower complete-LCM interior bound costs
one endpoint unit, and the scalar boundary identity contributes the factor two. -/
theorem postRootFallingEnergyFiniteDifferencePower_of_powerRemainder
    (hpower : PostRootCovariancePowerRemainderStatement) :
    PostRootFallingEnergyFiniteDifferencePowerStatement := by
  intro ε hε
  rcases hpower ε hε with ⟨D, hD, hrem⟩
  refine ⟨2 * (D + 1), by positivity, ?_⟩
  intro W hW
  have hr := hrem W hW
  have hboundary :=
    postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass W
  have hinterior :=
    neg_endpoint_le_sum_postRootCovarianceRemainderInteriorLcmCarrier W
  have hsplit :=
    postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
  have hscale := endpoint_le_postRootPowerScale hε hW
  have hpowNonneg : 0 ≤ Real.rpow (W : ℝ) (1 + ε) := by
    have hWpos : (0 : ℝ) < (W : ℝ) := by
      exact_mod_cast (show 0 < W by omega)
    exact (Real.rpow_pos_of_pos hWpos _).le
  nlinarith

/-- **Exact scalar tether equivalence.**  Up to the already-proved linear
complete-LCM interior, the positive-power covariance seam and the falling-energy
Euler finite-difference seam are the same quantitative problem. -/
theorem postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder :
    PostRootFallingEnergyFiniteDifferencePowerStatement ↔
      PostRootCovariancePowerRemainderStatement :=
  ⟨postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower,
    postRootFallingEnergyFiniteDifferencePower_of_powerRemainder⟩

/-- The finite-horizon running envelope is uniformly bounded exactly when the
scalar falling-energy finite difference has the target positive-power bound. -/
theorem postRootCovariancePowerEnvelopeBounded_iff_fallingEnergyFiniteDifferencePower :
    PostRootCovariancePowerEnvelopeBoundedStatement ↔
      PostRootFallingEnergyFiniteDifferencePowerStatement := by
  rw [postRootCovariancePowerEnvelopeBounded_iff_powerRemainder,
    ← postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder]

/-- **Arrow/string endpoint.**  Bounded cumulative new-record excesses are
exactly equivalent to positive-power control of the explicit scalar
falling-energy finite difference.  Future inequalities may therefore tighten
the record-excess tail or the scalar finite difference interchangeably. -/
theorem postRootCovariancePowerRecordExcessBounded_iff_fallingEnergyFiniteDifferencePower :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      PostRootFallingEnergyFiniteDifferencePowerStatement := by
  rw [postRootCovariancePowerRecordExcessBounded_iff_powerRemainder,
    ← postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder]

/-- Positive-power control of the explicit falling-energy finite difference
therefore feeds the protected Mertens-energy criterion through #599. -/
theorem mertensEnergyBounded_of_postRootFallingEnergyFiniteDifferencePower
    (hfall : PostRootFallingEnergyFiniteDifferencePowerStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerRemainder
    (postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower hfall)

end RHLean.Proof
