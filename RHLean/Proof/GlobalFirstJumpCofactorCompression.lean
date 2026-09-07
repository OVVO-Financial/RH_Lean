import Mathlib
import RHLean.Proof.FirstJumpPrimeSliceObstruction

/-!
# Global first-jump cofactor compression

The fixed-first-jump-prime norm estimate is too strong: the upper-half slice can
have prime-count size even when `R / p = 1`.  This file keeps the first-jump
prime cancellation intact and instead expands every completed predecessor
residual on one common low-cofactor carrier.

The arbitrary-prime cofactor-window transform from `TerminalAxiomAudit` permits
choosing the fresh coordinate `2`.  Thus every statewise first-jump residual is
written as a signed sum over `1 <= d <= sqrt R` before any norm is taken.  A
finite Fubini swap then produces global cofactor columns.

The quantitative seam isolated below is the column-packing estimate

`||G_R(d)|| <= R / d`.

Unlike the failed fixed-`p` estimate, each `G_R(d)` already contains the full
signed sum over all oriented states and all first-jump-prime coordinates.  If
this packing estimate holds, the desired `R (1 + log R)` bound follows
immediately from the harmonic sum, with constant `1`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Contribution of one low cofactor `d` to one oriented state's complete
first-jump residual.  The prime-dilate coordinate is fixed at `2`; no norm is
present in this definition. -/
noncomputable def firstJumpStateCofactorResponse
    (R d : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
      Nat.sqrt R < lowWheelCanonicalDowncrossPivot x then
    canonicalMoebiusWeight x.1 *
      (firstJumpHighPrimeCofactorResponse
          2 R (lowWheelCanonicalDowncrossPivot x - 1) (R / x.2) d -
        firstJumpHighPrimeCofactorResponse
          2 R (lowWheelCanonicalDowncrossPivot x - 1)
            (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2) d)
  else
    0

/-- Global signed column at low cofactor `d`, after every oriented state and
first-jump-prime coordinate has been summed. -/
noncomputable def signedFirstJumpCofactorColumnAggregate
    (R d : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    firstJumpStateCofactorResponse R d x

/-- **Statewise cofactor expansion.**  One complete first-jump state fibre is
exactly the signed sum of its low-cofactor responses on `d <= sqrt R`.
The proof uses the existing arbitrary-prime window transform at the fresh
coordinate `2`. -/
theorem lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_cofactorResponses
    (R : ℕ) (x : LowWheelCofactorQuotientState) :
    lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight d * firstJumpStateCofactorResponse R d x := by
  classical
  by_cases hstate :
      (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
        Nat.sqrt R < lowWheelCanonicalDowncrossPivot x
  · have hBR :
        lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2 ≤ R := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_left _ _).trans (Nat.div_le_self _ _)
    have hAB :
        R / x.2 ≤ lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2 := by
      rcases lowWheelCanonicalDowncrossChargingFaces_nonempty_of_oriented hstate.1 with
        ⟨t, ht⟩
      have hI := primeFaceProduct_mem_exactOwnershipInterval ht
      exact (Finset.mem_Ioc.mp hI).1.le
    have hJ :=
      sqrtFirstJumpResidual_cast_eq_cofactorWindowDifference
        (p := 2) (R := R) (q := lowWheelCanonicalDowncrossPivot x)
        (A := R / x.2)
        (B := lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2)
        Nat.prime_two hstate.2 hBR hAB
    unfold lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre
      firstJumpStateCofactorResponse
    rw [if_pos hstate, if_pos hstate, hJ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  · simp [lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre,
      firstJumpStateCofactorResponse, hstate]

/-- **Global cofactor Fubini.**  The live first-jump aggregate is a single
Möbius-weighted sum of global low-cofactor columns.  In particular, no norm is
taken after fixing the first-jump prime. -/
theorem signedLiveFirstJumpAggregate_eq_sum_cofactorColumns
    (R : ℕ) :
    signedLiveFirstJumpAggregate R =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight d *
          signedFirstJumpCofactorColumnAggregate R d := by
  classical
  unfold signedLiveFirstJumpAggregate
  calc
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
          canonicalMoebiusWeight d * firstJumpStateCofactorResponse R d x := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact
              lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_cofactorResponses
                R x
    _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
          canonicalMoebiusWeight d * firstJumpStateCofactorResponse R d x := by
            rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight d *
          signedFirstJumpCofactorColumnAggregate R d := by
            apply Finset.sum_congr rfl
            intro d _hd
            unfold signedFirstJumpCofactorColumnAggregate
            rw [Finset.mul_sum]

/-- The concrete global packing seam suggested by the cofactor Fubini
coordinate.  Every cancellation across first-jump primes and oriented owners
has already happened inside `G_R(d)` before its norm is taken. -/
def FirstJumpCofactorColumnPackingBound : Prop :=
  ∀ R d : ℕ, 3 ≤ R → d ∈ Finset.Icc 1 (Nat.sqrt R) →
    ‖signedFirstJumpCofactorColumnAggregate R d‖ ≤
      (R : ℝ) / (d : ℝ)

/-- **Column packing closes the desired global bound.**  If each fully signed
cofactor column costs at most its physical harmonic seat scale `R/d`, then the
whole live first-jump aggregate is bounded by `R (1 + log R)`. -/
theorem pntFiniteDifferenceLiveExposureBound_of_cofactorColumnPacking
    (hcol : FirstJumpCofactorColumnPackingBound) :
    PNTFiniteDifferenceLiveExposureBound := by
  refine ⟨1, by norm_num, ?_⟩
  intro R hR
  rw [signedLiveFirstJumpAggregate_eq_sum_cofactorColumns]
  have hsqrtR : Nat.sqrt R ≤ R := Nat.sqrt_le_self R
  have hsubset :
      Finset.Icc 1 (Nat.sqrt R) ⊆ Finset.Icc 1 R := by
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hds⟩
    exact Finset.mem_Icc.mpr ⟨hd1, hds.trans hsqrtR⟩
  have hsumSubset :
      (∑ d ∈ Finset.Icc 1 (Nat.sqrt R), (R : ℝ) / (d : ℝ)) ≤
        ∑ d ∈ Finset.Icc 1 R, (R : ℝ) / (d : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro d _hdR _hdOld
    positivity
  have hharm :
      (harmonic R : ℝ) =
        ∑ d ∈ Finset.Icc 1 R, (1 : ℝ) / (d : ℝ) := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div]
  have hsumHarm :
      (∑ d ∈ Finset.Icc 1 R, (R : ℝ) / (d : ℝ)) =
        (R : ℝ) * (harmonic R : ℝ) := by
    rw [hharm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  have hharmBound :
      (harmonic R : ℝ) ≤ 1 + Real.log (R : ℝ) := by
    simpa using harmonic_le_one_add_log R
  have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := by positivity
  calc
    ‖∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        canonicalMoebiusWeight d *
          signedFirstJumpCofactorColumnAggregate R d‖ ≤
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        ‖canonicalMoebiusWeight d *
          signedFirstJumpCofactorColumnAggregate R d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt R),
        (R : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hmu : ‖canonicalMoebiusWeight d‖ ≤ (1 : ℝ) := by
        rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;>
          simp [canonicalMoebiusWeight, h]
      have hc := hcol R d hR hd
      rw [norm_mul]
      have hmul := mul_le_mul hmu hc (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa using hmul
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (R : ℝ) / (d : ℝ) := hsumSubset
    _ = (R : ℝ) * (harmonic R : ℝ) := hsumHarm
    _ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) :=
      mul_le_mul_of_nonneg_left hharmBound hRnonneg
    _ = (1 : ℝ) * (R : ℝ) * (Real.log (R : ℝ) + 1) := by ring

end RHLean.Proof
