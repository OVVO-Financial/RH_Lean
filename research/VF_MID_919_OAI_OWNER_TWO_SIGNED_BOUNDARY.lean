import Mathlib
import «research.VF_MID_919_OAI_EXCLUDED_SIX_SIGNED_KERNEL»
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
    (hR : 2 ≤ R) (hC : 0 ≤ C)
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


/-! ## Exact original native p=2 physical site-weight dictionary

The following two functions are the LITERAL site coefficients in the
already-compiled AMP first-owner branch.  Their support is not chosen
by the Hecke representation.  In particular the returned-child site
is evaluated at 2*n, but its Mobius sign remains at the p-free parent
n; this is the native sign reversal.

The finite norm-grouped Hecke identification of these signed physical
sums and the sextic amplifier column identity are stated as distinct,
visible hypotheses below.  Nothing in this file bounds the resulting
signed cross matrix or claims the full historical Sector Six weld.
-/

/-- Native p=2 p-free parent weight, including the original exact
    AMP reciprocal daughters and root-tail cutoff. -/
def vf919OwnerTwoPhysicalParentSiteWeight (R n : ℕ) : ℝ :=
  if n ∈ lowOwnerFirstOwnerBaseFiber R 2 ∅ then
    lowOwnerZeroFrequencyMobiusWeight R n
  else 0

/-- Native p=2 returned-child parent weight.  The positive sign of
    the p-free parent Mobius is retained until the exact mixed Gram. -/
def vf919OwnerTwoPhysicalReturnedSiteWeight (R n : ℕ) : ℝ :=
  if n ∈ lowOwnerFirstOwnerAdmittedBaseFiber R 2 ∅ then
    lowOwnerZeroFrequencyMobiusWeight R (2 * n)
  else 0

/-- The actual complete p-free AMP branch is exactly its physical
    site-weighted Mobius sum. -/
theorem vf919OwnerTwoPhysicalParentSite_sum_eq_base (R : ℕ) :
    (∑ n ∈ lowOwnerFirstOwnerBaseFiber R 2 ∅,
        realMoebiusStep n * vf919OwnerTwoPhysicalParentSiteWeight R n) =
      lowOwnerFirstOwnerBaseAmplitude R 2 ∅ := by
  unfold lowOwnerFirstOwnerBaseAmplitude
  apply Finset.sum_congr rfl
  intro n hn
  simp [vf919OwnerTwoPhysicalParentSiteWeight, hn,
    lowOwnerZeroFrequencyMobiusSite, mul_comm]

/-- The actual returned p-child column is exactly its physical
    site-weighted p-free-parent Mobius sum. -/
theorem vf919OwnerTwoPhysicalReturnedSite_sum_eq_returned (R : ℕ) :
    (∑ n ∈ lowOwnerFirstOwnerAdmittedBaseFiber R 2 ∅,
        realMoebiusStep n * vf919OwnerTwoPhysicalReturnedSiteWeight R n) =
      lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅ := by
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
  apply Finset.sum_congr rfl
  intro n hn
  simp [vf919OwnerTwoPhysicalReturnedSiteWeight, hn, mul_comm]

/-- UNCONDITIONAL native signed source-product identity, with both
    original AMP site-weight functions exposed.  This is a real
    physical owner-two identity rather than a proxy Hecke Gram. -/
theorem vf919OwnerTwoSignedGram_eq_native_site_products (R : ℕ) :
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ =
      -2 *
        (∑ n ∈ lowOwnerFirstOwnerBaseFiber R 2 ∅,
          realMoebiusStep n * vf919OwnerTwoPhysicalParentSiteWeight R n) *
        (∑ n ∈ lowOwnerFirstOwnerAdmittedBaseFiber R 2 ∅,
          realMoebiusStep n * vf919OwnerTwoPhysicalReturnedSiteWeight R n) := by
  rw [lowOwnerFirstOwnerCellGram_eq_neg_basePlusClipped_mul_returned
    Nat.prime_two]
  rw [← lowOwnerFirstOwnerBaseAmplitude_eq_admittedBase_add_clipped R 2 ∅]
  rw [vf919OwnerTwoPhysicalParentSite_sum_eq_base,
    vf919OwnerTwoPhysicalReturnedSite_sum_eq_returned]
  ring

/-- Direct arithmetic inlet into the ACTUAL physical owner-two Gram.
    hparent/hreturned are the genuinely missing global ideal-norm
    identification for these precise native weights, not assumed
    consequences of the local formal norm Euler polynomial. -/
theorem vf919OwnerTwoSignedGram_eq_excludedSixHecke_of_identification
    (R : ℕ) (ms ds : Finset ℕ) (a chi : ℕ → ℝ)
    (hparent :
      vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalParentSiteWeight R) =
        lowOwnerFirstOwnerBaseAmplitude R 2 ∅)
    (hreturned :
      vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalReturnedSiteWeight R) =
        lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅) :
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ =
      -2 *
        vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalParentSiteWeight R) *
        vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalReturnedSiteWeight R) := by
  rw [lowOwnerFirstOwnerCellGram_eq_neg_basePlusClipped_mul_returned
    Nat.prime_two]
  rw [← lowOwnerFirstOwnerBaseAmplitude_eq_admittedBase_add_clipped R 2 ∅]
  rw [hparent, hreturned]
  ring

/-- The whole signed p=2 cross matrix enters the actual native cell
    under the two EXPLICIT coefficient-identification and amplifier
    hypotheses; no cross-divisor absolute square is taken.
    This is an arithmetic transfer, NOT a new uniform moment estimate. -/
theorem vf919OwnerTwoSignedGram_eq_amplified_signed_cross_of_identification
    {ι : Type*} (R : ℕ) (ms ds : Finset ℕ) (a chi : ℕ → ℝ)
    (amp : Finset ι) (c H J : ι → ℝ)
    (hparent :
      vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalParentSiteWeight R) =
        lowOwnerFirstOwnerBaseAmplitude R 2 ∅)
    (hreturned :
      vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalReturnedSiteWeight R) =
        lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅)
    (hAmpParent :
      vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalParentSiteWeight R) =
        ∑ d ∈ amp, c d * H d)
    (hAmpReturned :
      vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalReturnedSiteWeight R) =
        ∑ e ∈ amp, c e * J e) :
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ =
      ∑ d ∈ amp, ∑ e ∈ amp,
        -2 * c d * c e * H d * J e := by
  calc
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ =
      -2 *
        vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalParentSiteWeight R) *
        vf919FiniteSixExcludedHecke ms ds a chi
          (vf919OwnerTwoPhysicalReturnedSiteWeight R) :=
      vf919OwnerTwoSignedGram_eq_excludedSixHecke_of_identification
        R ms ds a chi hparent hreturned
    _ = -2 * (∑ d ∈ amp, c d * H d) *
          (∑ e ∈ amp, c e * J e) := by
      rw [hAmpParent, hAmpReturned]
    _ = ∑ d ∈ amp, ∑ e ∈ amp,
          -2 * c d * c e * H d * J e :=
      vf919PrincipalSignedSixthPowerCrossMatrix amp c H J

end RHLean.Proof
