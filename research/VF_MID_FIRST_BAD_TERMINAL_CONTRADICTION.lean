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
  have hs2 : 2 ≤ Nat.sqrt m := by
    apply (Nat.le_sqrt).2
    nlinarith
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
    apply (Nat.le_sqrt).2
    nlinarith
  have hsB : Nat.sqrt q < B := hsA.trans hABlt
  exact vfMidActualPrimeFirstBadAt_prior_inside hfirst hs2 hsB

/-- Direct terminal composition attempt.

No extra domination or packet-inheritance hypothesis is admitted here.
The proof deliberately instantiates exactly the three claimed inputs and asks
Lean to close the arithmetic contradiction. -/
theorem vfMidActualPrimeFirstBadAt_impossible_terminal
    {K : ℝ} {A B first : ℕ}
    (hfirstBad : VFMidActualPrimeFirstBadAt K B)
    (hA : 4 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A)
    (hBsq : B ^ 2 ≤ 3 * A ^ 2)
    (hfirstPrime : first.Prime)
    (parents : Finset (ℕ × ℕ))
    (coefficient : (ℕ × ℕ) → ℝ) :
    False := by
  have hbreach :=
    vfMidActualPrimeFirstBadAt_forces_twoSectorOwnerTrigger
      hfirstBad (by omega : 3 ≤ A) hABlt hBA
  have hprocessedPrior :
      ∀ R ∈ Finset.Ico A B,
        ∀ p ∈ vfMidFrozenProcessedOwnerPrimes A R,
          ∀ m ∈ vfMidSquareBandCompositeOwnerChildren R p,
            |vfMidActualPrimeEndpointDefect (Nat.sqrt m)| ≤
              K * vfMidSyntheticRadialScale (Nat.sqrt m) := by
    intro R hR p hp m hm
    exact
      vfMidProcessedOwnerChild_prior_inside
        hfirstBad hA hABlt hR hBsq hp hm
  have hquarter :=
    vfMidSelectedClippedOutgoingEnergy_le_quarter
      (R := B) hfirstPrime parents coefficient
  rcases hbreach with hpos | hneg
  · linarith
  · linarith

end RHLean.Analysis
