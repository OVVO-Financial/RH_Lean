import Mathlib
import «research.VF_MID_919_OAI_PHASE_ALIGNED_OWNER_COMPENSATION»
import «research.GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT»

/-!
# #919: retain the actual owner-two signed clipped/returned cross term

The unramified local character compensation is already proved in the native
phase-aligned owner cells. Here the p=2 anchor is identified with the *exact*
Mertens clipped exit before ANY scalar estimate.

Do not replace this signed boundary by an interior bound: the interior is
already controlled, while the clipped exit is the terminal Mertens value.

The quantitative theorem below has *explicit* Mertens and returned-child
inputs. It is an arithmetic estimate transport, not an assertion that OpenAI's
7/8 nonvanishing already proves an RH-scale bound for this signed cross term.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- The signed clipped-returned interaction which survives the native full
first-owner telescope. No absolute values or ownerwise norming. -/
def vf919OwnerTwoSignedClippedReturnedBoundary (R : ℕ) : ℝ :=
  -2 * lowOwnerFirstOwnerClippedAmplitude R 2 ∅ *
    lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅

/-- The first owner's **actual** clipped mass is the entire top Mertens value.
Therefore the *remaining signed covariance* is a Mertens/returned-child
product, not a compensated-interior energy. -/
theorem vf919OwnerTwoSignedBoundary_eq_topMertens_times_returned
    {R : ℕ} (hR : 2 ≤ R) :
    vf919OwnerTwoSignedClippedReturnedBoundary R =
      -2 * ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ) *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅ := by
  unfold vf919OwnerTwoSignedClippedReturnedBoundary
  rw [lowOwnerFirstOwnerClippedAmplitude_two_eq_topMertens hR]

/-- The full owner-two signed Gram retains the literal clipped/returned
source. This is an identity, NOT a cancellation estimate. -/
theorem vf919OwnerTwoSignedGram_eq_interior_sub_branches_add_boundary
    (R : ℕ) :
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ =
      lowOwnerFirstOwnerCompensatedInteriorAmplitude R 2 ∅ ^ 2 -
      lowOwnerFirstOwnerAdmittedBaseAmplitude R 2 ∅ ^ 2 -
      lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅ ^ 2 +
      vf919OwnerTwoSignedClippedReturnedBoundary R := by
  rw [two_mul_lowOwnerFirstOwnerCellGram_eq_completeTelescope_sub_clippedCross
    Nat.prime_two]
  unfold lowOwnerFirstOwnerSignedCellTelescope
    vf919OwnerTwoSignedClippedReturnedBoundary
  ring

/-- Magnitude transfer with the **honest missing inputs** visible. Any
zero-free -> Mertens argument must also control the actual returned child
amplitude, or else use its signed correlation directly. -/
theorem vf919OwnerTwoSignedBoundary_abs_le_of_real_magnitudes
    {R : ℕ} {C J : ℝ}
    (hR : 2 ≤ R) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (hM : |((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)| ≤ C)
    (hreturned :
      |lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅| ≤ J) :
    |vf919OwnerTwoSignedClippedReturnedBoundary R| ≤ 2 * C * J := by
  rw [vf919OwnerTwoSignedBoundary_eq_topMertens_times_returned hR]
  have hprod :
      |((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)| *
        |lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅| ≤ C * J :=
    mul_le_mul hM hreturned (abs_nonneg _) hC
  rw [abs_mul, abs_mul, abs_neg]
  norm_num
  nlinarith

/-- A sign-aligned returned child makes the exact clipped boundary
nonpositive. The sign is a genuine **correlation** obligation, not a
consequence of a norm estimate. -/
theorem vf919OwnerTwoSignedBoundary_nonpos_of_aligned
    {R : ℕ} (hR : 2 ≤ R)
    (haligned :
      0 ≤ ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ) *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅) :
    vf919OwnerTwoSignedClippedReturnedBoundary R ≤ 0 := by
  rw [vf919OwnerTwoSignedBoundary_eq_topMertens_times_returned hR]
  nlinarith

/-- Conversely, opposite signs produce a positive boundary contribution;
an argument requiring this term to be nonpositive must exclude this case
through additional arithmetic information. -/
theorem vf919OwnerTwoSignedBoundary_nonneg_of_opposite
    {R : ℕ} (hR : 2 ≤ R)
    (hopposite :
      ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ) *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅ ≤ 0) :
    0 ≤ vf919OwnerTwoSignedClippedReturnedBoundary R := by
  rw [vf919OwnerTwoSignedBoundary_eq_topMertens_times_returned hR]
  nlinarith

end RHLean.Proof
