import Mathlib
import «research.VF_MID_FIRST_BAD_AFFINE_OWNER_SPLICE»

/-!
# Terminal first-bad contradiction splice

This file imports the merged #888 affine/owner splice and attempts the terminal
composition directly, without introducing a new cancellation hypothesis.

The intended three inputs are kept in their native currencies:

1. the exact two-sector first-bad wall breach;
2. the first-bad prior-good wall on every genuinely descended child scale;
3. the #888 selection-stable reciprocal quarter contraction.

The child lemmas below make the second input literal for both the processed
low-owner sector and the live post-frozen sector.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A processed-owner child lies at a strict prior square-root scale. -/
theorem vfMidProcessedOwnerChild_sqrt_lt_anchor
    {A B R p m : ℕ}
    (hRB : R < B)
    (hBsq : B ^ 2 ≤ 3 * A ^ 2)
    (hp : p ∈ vfMidFrozenProcessedOwnerPrimes A R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    Nat.sqrt m < A := by
  exact (Nat.sqrt_lt').2
    (vfMidProcessedOwnerChild_lt_anchorSquare hRB hBsq hp hm)

/-- A processed-owner child is not a tiny exceptional scale: it is strictly
above the frozen anchor itself. -/
theorem vfMidProcessedOwnerChild_anchor_lt
    {A R p m : ℕ}
    (hAR : A ≤ R)
    (hp : p ∈ vfMidFrozenProcessedOwnerPrimes A R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    A < m := by
  rcases Finset.mem_filter.mp hp with ⟨_hpLate, hpA⟩
  rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
  rcases vfMidSquareBandCompositeOwner_mem hn with ⟨hnComp, _hmin⟩
  rcases Finset.mem_filter.mp hnComp with ⟨hnBand, _hnNotPrime⟩
  have hnLow : R ^ 2 < n := (Finset.mem_Ioo.mp hnBand).1
  have hmul : p * (n / p) = n :=
    vfMidSquareBandCompositeOwner_mul_div hn
  by_contra hnot
  have hmA : n / p ≤ A := Nat.le_of_not_gt hnot
  have hprod : p * (n / p) ≤ A * A :=
    Nat.mul_le_mul hpA hmA
  have hA2R2 : A ^ 2 ≤ R ^ 2 :=
    Nat.pow_le_pow_left hAR 2
  have hnLe : n ≤ R ^ 2 := by
    calc
      n = p * (n / p) := hmul.symm
      _ ≤ A * A := hprod
      _ = A ^ 2 := by ring
      _ ≤ R ^ 2 := hA2R2
  omega

/-- Therefore every processed-owner child is covered by the first-bad
prior-good wall at its native square-root scale. -/
theorem vfMidProcessedOwnerChild_prior_inside
    {K : ℝ} {A B R p m : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 4 ≤ A)
    (hABlt : A < B)
    (hR : R ∈ Finset.Ico A B)
    (hBsq : B ^ 2 ≤ 3 * A ^ 2)
    (hp : p ∈ vfMidFrozenProcessedOwnerPrimes A R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    |vfMidActualPrimeEndpointDefect (Nat.sqrt m)| ≤
      K * vfMidSyntheticRadialScale (Nat.sqrt m) := by
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hRB : R < B := (Finset.mem_Ico.mp hR).2
  have hAm := vfMidProcessedOwnerChild_anchor_lt (A := A) hAR hp hm
  have hm4 : 4 ≤ m := by omega
  have hs2 : 2 ≤ Nat.sqrt m := by
    exact (Nat.le_sqrt).2 hm4
  have hsA :=
    vfMidProcessedOwnerChild_sqrt_lt_anchor hRB hBsq hp hm
  have hsB : Nat.sqrt m < B := hsA.trans hABlt
  exact vfMidActualPrimeFirstBadAt_prior_inside hfirst hs2 hsB

/-- The post-frozen #887 prime children also lie in the first-bad prior-good
region. -/
theorem vfMidFrozenOwnerPrimeChild_prior_inside
    {K : ℝ} {A B R p q : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 4 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A)
    (hR : R ∈ Finset.Ico A B)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R)
    (hq : q ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    |vfMidActualPrimeEndpointDefect (Nat.sqrt q)| ≤
      K * vfMidSyntheticRadialScale (Nat.sqrt q) := by
  have hdata :=
    vfMidDyadicFrozenCompositeOwnerChild_prime_below_frozenSquare
      hA hABlt.le hBA hR hp hq
  rcases hdata with ⟨_hqPrime, _hqA2, hsA⟩
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hpA : A < p :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).2
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hR3 : 3 ≤ R := by omega
  have hrough : q ∈ vfMidSquareBandOwnerRoughChildren R p := by
    rw [← vfMidSquareBandCompositeOwnerChildren_eq_rough hR3 hpOwner]
    exact hq
  have hpq : p ≤ q :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hrough).1).1
  have hq4 : 4 ≤ q := by omega
  have hs2 : 2 ≤ Nat.sqrt q := by
    exact (Nat.le_sqrt).2 hq4
  have hsB : Nat.sqrt q < B := hsA.trans hABlt
  exact vfMidActualPrimeFirstBadAt_prior_inside hfirst hs2 hsB

/-- Exact reassembly of the #888 two-sector charge in endpoint-depth
currency.  This is the identity that must remain visible in the terminal
first-bad argument:
`T(A,B) = D_A - D_B`. -/
theorem vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub
    {A B : ℕ}
    (hA : 3 ≤ A)
    (hAB : A ≤ B)
    (hBA : B ≤ 2 * A) :
    vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B =
      vfMidActualPrimeEndpointDefect A -
        vfMidActualPrimeEndpointDefect B := by
  rw [← vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge
    hA hBA]
  rw [← vfMidDyadicVFTrackingDefect_eq_oddRunSeatMass
    (by omega : 2 ≤ A) hAB]
  rw [vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment
    (by omega : 2 ≤ A) (by omega : 2 ≤ B) hAB]
  unfold vfMidActualPrimeEndpointDefect
  ring

/-- A first-bad scale forces the exact two-sector charge to exceed the
**remaining global radial slack**, not merely the local radial gradient.

Equivalently:
`|T(A,B)| > K*rho(B) - |D_A|`.
The right side is
`K*(rho(B)-rho(A)) + (K*rho(A)-|D_A|)`, i.e. local gradient plus the
accumulated slack of the prior-good anchor. -/
theorem vfMidActualPrimeFirstBadAt_forces_depthAwareTwoSectorAbsTrigger
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A) :
    K * vfMidSyntheticRadialScale B -
        |vfMidActualPrimeEndpointDefect A| <
      |vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B| := by
  have hbad := hfirst.1
  unfold VFMidSyntheticBadAt at hbad
  have hT :=
    vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub
      hA hABlt.le hBA
  have hDB :
      vfMidActualPrimeEndpointDefect B =
        vfMidActualPrimeEndpointDefect A -
          (vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B) := by
    linarith
  have htri :
      |vfMidActualPrimeEndpointDefect B| ≤
        |vfMidActualPrimeEndpointDefect A| +
          |vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B| := by
    rw [hDB]
    simpa [sub_eq_add_neg] using
      (abs_add_le
        (vfMidActualPrimeEndpointDefect A)
        (-(vfMidDyadicFrozenSurvivorSeatCharge A B +
          vfMidDyadicProcessedOwnerSeatCharge A B)))
  linarith

/-- The anchor part of the depth-aware threshold is genuine nonnegative slack,
because every earlier scale of a first-bad trajectory is prior-good. -/
theorem vfMidActualPrimeFirstBadAt_anchorSlack_nonneg
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A)
    (hABlt : A < B) :
    0 ≤
      K * vfMidSyntheticRadialScale A -
        |vfMidActualPrimeEndpointDefect A| := by
  have hprior :=
    vfMidActualPrimeFirstBadAt_prior_inside
      hfirst (by omega : 2 ≤ A) hABlt
  linarith

/-- Pure algebra: the depth-aware threshold is exactly local radial growth plus
the accumulated slack at the anchor. -/
theorem vfMid_depthAwareThreshold_eq_gradient_add_anchorSlack
    (K : ℝ) (A B : ℕ) :
    K * vfMidSyntheticRadialScale B -
        |vfMidActualPrimeEndpointDefect A| =
      K * (vfMidSyntheticRadialScale B -
        vfMidSyntheticRadialScale A) +
      (K * vfMidSyntheticRadialScale A -
        |vfMidActualPrimeEndpointDefect A|) := by
  ring

/-- Algebraic terminal adapter only.

This theorem is intentionally **not** counted as the missing arithmetic result:
its `hceiling` hypothesis is exactly the depth-aware structural ceiling that
must be derived from the #887/#888 restricted reciprocal ledger and prior-good
children.  Once that ceiling is proved, the first-bad contradiction is
immediate. -/
theorem vfMidActualPrimeFirstBadAt_impossible_of_depthAwareCeiling
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A)
    (hceiling :
      |vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B| ≤
        K * vfMidSyntheticRadialScale B -
          |vfMidActualPrimeEndpointDefect A|) :
    False := by
  have hbreach :=
    vfMidActualPrimeFirstBadAt_forces_depthAwareTwoSectorAbsTrigger
      hfirst hA hABlt hBA
  linarith

end RHLean.Analysis
