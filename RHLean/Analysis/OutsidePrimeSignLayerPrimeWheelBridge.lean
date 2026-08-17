import Mathlib
import RHLean.Analysis.LeastSquareCompleteSuperorbitRecombination
import RHLean.Analysis.PrimeWheelRecoveredMertensCriterion

/-!
# Coherent outside-prime sign layer and the square-root prime wheel

The least-owner deletion analysis leaves one coherent selected-CRT baseline.
This file identifies what that baseline is missing without introducing a new
estimate.

There are two exact levels of the same statement.

* Pointwise, the prime-wheel local factor is literally the product of the
  square-survival mask and the ordinary first-power sign factor.  Thus the raw
  seeded prime wheel already combines square deletion and ordinary prime sign
  flips in one local operator.
* On the one-prime degree-one CRT baseline, square deletion alone leaves the
  zero-free weight `p^2 - 6`.  The missing ordinary sign layer contributes
  exactly `-2 (p - 1)`, so the recombined weight is
  `p^2 - 2 p - 4`, exactly the nonzero weight-one Walsh baseline identified in
  `SelectedCRTBaseline`.

Finally, under square-root coverage, substituting the pointwise factorization
into the existing `raw - 2 * smooth` recovery theorem gives the actual Moebius
coefficient exactly.  No norm, independence hypothesis, or channelwise triangle
inequality appears here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Ordinary first-power sign supplied by one prime coordinate. -/
def ordinaryPrimeSignFactor (p n : ℕ) : ℤ :=
  if p ∣ n then -1 else 1

/-- Square-survival factor supplied by one prime coordinate. -/
def primeSquareSurvivalFactor (p n : ℕ) : ℤ :=
  if p ^ 2 ∣ n then 0 else 1

/-- **Exact local recombination.**  The prime-wheel local comb is square
survival times the ordinary prime sign.  A square hit kills the site, a
first-power hit flips it, and a miss leaves it unchanged. -/
theorem localPrimeComb_eq_squareSurvival_mul_ordinarySign
    (p n : ℕ) :
    localPrimeComb p n =
      primeSquareSurvivalFactor p n * ordinaryPrimeSignFactor p n := by
  by_cases hsq : p ^ 2 ∣ n
  · simp [localPrimeComb, primeSquareSurvivalFactor,
      ordinaryPrimeSignFactor, hsq]
  · by_cases hd : p ∣ n
    · simp [localPrimeComb, primeSquareSurvivalFactor,
        ordinaryPrimeSignFactor, hsq, hd]
    · simp [localPrimeComb, primeSquareSurvivalFactor,
        ordinaryPrimeSignFactor, hsq, hd]

/-- Product square-survival mask for a finite selected prime set. -/
def finitePrimeSquareSurvivalMask (P : Finset ℕ) (n : ℕ) : ℤ :=
  ∏ p ∈ P, primeSquareSurvivalFactor p n

/-- The selected sign field is exactly the product of the ordinary local sign
factors. -/
theorem selectedPrimeSign_eq_ordinaryPrimeSignProduct
    (P : Finset ℕ) (n : ℕ) :
    selectedPrimeSign P n =
      ∏ p ∈ P, ordinaryPrimeSignFactor p n := by
  rfl

/-- **Finite pointwise bridge.**  The seeded prime wheel is the selected
ordinary sign field multiplied by the complete selected square-survival mask,
with the repository's fixed seed orientation `-1`. -/
theorem seededPrimeComb_eq_neg_survival_mul_selectedPrimeSign
    (P : Finset ℕ) (n : ℕ) :
    seededPrimeComb P n =
      -(finitePrimeSquareSurvivalMask P n * selectedPrimeSign P n) := by
  classical
  unfold seededPrimeComb finitePrimeSquareSurvivalMask selectedPrimeSign
  have hprod :
      (∏ p ∈ P, localPrimeComb p n) =
        ∏ p ∈ P,
          (primeSquareSurvivalFactor p n * ordinaryPrimeSignFactor p n) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact localPrimeComb_eq_squareSurvival_mul_ordinarySign p n
  rw [hprod, Finset.prod_mul_distrib]
  rfl

/-- On a selected-square-zero-free site the survival mask is identically one. -/
theorem finitePrimeSquareSurvivalMask_eq_one_of_zeroFree
    (P : Finset ℕ) (n : ℕ)
    (hzero : ∀ p ∈ P, ¬ p ^ 2 ∣ n) :
    finitePrimeSquareSurvivalMask P n = 1 := by
  classical
  unfold finitePrimeSquareSurvivalMask
  apply Finset.prod_eq_one
  intro p hp
  simp [primeSquareSurvivalFactor, hzero p hp]

/-- Hence before any outside square is encountered, the raw seeded wheel is
exactly the negative selected sign field. -/
theorem seededPrimeComb_eq_neg_selectedPrimeSign_of_zeroFree
    (P : Finset ℕ) (n : ℕ)
    (hzero : ∀ p ∈ P, ¬ p ^ 2 ∣ n) :
    seededPrimeComb P n = -selectedPrimeSign P n := by
  rw [seededPrimeComb_eq_neg_survival_mul_selectedPrimeSign,
    finitePrimeSquareSurvivalMask_eq_one_of_zeroFree P n hzero]
  ring

/-- **Square-root wheel closure in selected-sign coordinates.**  Under the
existing square-root coverage hypothesis, the selected ordinary sign field,
the selected square-deletion mask, and the smooth-core correction recombine to
the actual Moebius coefficient exactly. -/
theorem selectedSign_squareDeletion_smooth_eq_moebius
    (P : Finset ℕ) {upper n : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hnpos : 0 < n) (hnupper : n ≤ upper) :
    -(finitePrimeSquareSurvivalMask P n * selectedPrimeSign P n) -
        2 * primeWheelSmoothCoreSite P upper n =
      μ n := by
  have hcorr :=
    correctedPrimeWheelSite_eq_moebius
      P hprime hcover hnpos hnupper
  rw [← seededPrimeComb_eq_neg_survival_mul_selectedPrimeSign P n]
  simpa [correctedPrimeWheelSite] using hcorr

/-! ## The same split on the complete one-prime CRT baseline -/

/-- Signed degree-one correction contributed by the ordinary first-power sign
layer after square-zero residues have already been deleted. -/
def onePrimeOrdinarySignCorrectionWeight (p : ℕ) : ℚ :=
  -2 * onePrimeSingleFlipWeight p

/-- The ordinary sign correction has the closed form `-2 (p - 1)`. -/
theorem onePrimeOrdinarySignCorrectionWeight_eq (p : ℕ) :
    onePrimeOrdinarySignCorrectionWeight p =
      -2 * ((p : ℚ) - 1) := by
  unfold onePrimeOrdinarySignCorrectionWeight onePrimeSingleFlipWeight
  ring

/-- **Exact deletion/sign recombination of the degree-one baseline.**  Deleting
the six square-zero residues leaves the zero-free weight; the one relevant
first-power sign-flip class then contributes `-2` times its class weight. -/
theorem onePrimeDegreeOneBaselineWeight_eq_zeroFree_add_signCorrection
    (p : ℕ) :
    onePrimeDegreeOneBaselineWeight p =
      onePrimeZeroFreeWeight p + onePrimeOrdinarySignCorrectionWeight p := by
  unfold onePrimeDegreeOneBaselineWeight onePrimeOrdinarySignCorrectionWeight
  rw [← onePrimeWeight_partition p]
  ring

/-- Closed recombination formula: starting from all `p^2` residues, the square
kill costs `6` and the ordinary sign layer costs `2 (p - 1)`. -/
theorem onePrimeDegreeOneBaselineWeight_eq_raw_sub_deletion_sub_sign
    (p : ℕ) :
    onePrimeDegreeOneBaselineWeight p =
      (p : ℚ) ^ 2 - 6 - 2 * ((p : ℚ) - 1) := by
  rw [onePrimeDegreeOneBaselineWeight_eq]
  ring

/-- Scalar stage form.  For any coherent incoming baseline `B`, square deletion
and the ordinary sign correction stay signed and recombine before any norm is
taken. -/
theorem onePrimeStageBaseline_recombination
    (p : ℕ) (B : ℚ) :
    onePrimeDegreeOneBaselineWeight p * B =
      onePrimeZeroFreeWeight p * B +
        onePrimeOrdinarySignCorrectionWeight p * B := by
  rw [onePrimeDegreeOneBaselineWeight_eq_zeroFree_add_signCorrection]
  ring

/-- For a generic prime, the same deletion-plus-sign quantity is exactly the
zero-free mass times the already-formalized weight-one Walsh multiplier. -/
theorem onePrimeDeletionAndSign_eq_zeroFree_mul_walsh
    {p : ℕ} (hp : 11 ≤ p) :
    onePrimeZeroFreeWeight p + onePrimeOrdinarySignCorrectionWeight p =
      onePrimeZeroFreeWeight p * onePrimeWalshFactor p 1 := by
  rw [← onePrimeDegreeOneBaselineWeight_eq_zeroFree_add_signCorrection]
  exact onePrimeDegreeOneBaselineWeight_eq_zeroFree_mul_walsh hp

/-- Adjoining a fresh prime to a finite coherent baseline performs exactly the
same signed deletion-plus-ordinary-sign recombination. -/
theorem finitePrimeDegreeOneBaselineWeight_insert_eq_deletion_add_sign
    {P : Finset ℕ} {q : ℕ} (hq : q ∉ P) :
    finitePrimeDegreeOneBaselineWeight (insert q P) =
      onePrimeZeroFreeWeight q * finitePrimeDegreeOneBaselineWeight P +
        onePrimeOrdinarySignCorrectionWeight q *
          finitePrimeDegreeOneBaselineWeight P := by
  classical
  unfold finitePrimeDegreeOneBaselineWeight
  rw [Finset.prod_insert hq]
  rw [onePrimeDegreeOneBaselineWeight_eq_zeroFree_add_signCorrection]
  ring

end RHLean.Analysis
