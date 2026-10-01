import Mathlib
import «research.VF_MID_PHI_OWNER_BRIDGE»

/-!
# VF-mid dyadic summation and Phi-owner transfer reduction

This file does two things.

1. It closes the routine local-to-global dyadic summation:
   a uniform bound on square-endpoint increments over A < B <= 2A implies
   the global square-endpoint von-Koch bound.

2. It sums the exact owner-level Phi identity from
   VF_MID_PHI_OWNER_BRIDGE over the full dyadic chronological owner census.
   Thus the physical signed late correction T-H is exactly the sum of
   a transformed-Li owner correction and a transformed actual-minus-Li
   displacement aggregate.

No quantitative estimate on either transformed aggregate is assumed or proved
in the exact identities of the second section.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Dyadic local-to-global summation -/

/-- The exact local increment estimate produced by the #843 signed late
correction consumer. -/
def VFMidDyadicIncrementBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ A B : ℕ, 2 ≤ A → A < B → B ≤ 2 * A →
      |vfMidPrimeError ((B : ℝ) ^ 2) -
          vfMidPrimeError ((A : ℝ) ^ 2)| ≤
        4 * (A : ℝ) + C * (A : ℝ) * Real.log A

/-- The signed late-correction statement immediately gives the local dyadic
increment statement. -/
theorem vfMidDyadicIncrementBounded_of_signedLateCorrection
    (hcor : VFMidDyadicSignedLateCorrectionStatement) :
    VFMidDyadicIncrementBoundedStatement :=
  abs_vfMidPrimeError_sq_sub_sq_le_of_signedLateCorrection hcor

/-- **Dyadic summation consumer.**
If every increment from A to B with A < B <= 2A is O(A log A), then the
square-endpoint error itself is O(R log R).

The induction uses A = ceil(R/2) = (R+1)/2.  For R >= 3,
3A <= 2R, so the induction has a genuine contraction and no explicit
log2 block bookkeeping is needed. -/
theorem vfMidSquareEndpointVonKochBounded_of_dyadicIncrement
    (hinc : VFMidDyadicIncrementBoundedStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  rcases hinc with ⟨C, hC0, hC⟩
  let ell : ℝ := Real.log 2
  have hell : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos (by norm_num)
  let E2 : ℝ := |vfMidPrimeError ((2 : ℝ) ^ 2)|
  have hE20 : 0 ≤ E2 := by
    dsimp [E2]
    exact abs_nonneg _
  let K : ℝ := E2 / (2 * ell) + 2 * C + 8 / ell
  have hbaseCoeff0 : 0 ≤ E2 / (2 * ell) := by
    exact div_nonneg hE20 (by positivity)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hKdom : 2 * C + 8 / ell ≤ K := by
    dsimp [K]
    linarith
  refine ⟨K, hK0, ?_⟩
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      intro hR2
      by_cases hRtwo : R = 2
      · subst R
        change E2 ≤ K * 2 * ell
        have hcoef : E2 / (2 * ell) ≤ K := by
          dsimp [K]
          linarith
        have hmul :=
          mul_le_mul_of_nonneg_right hcoef
            (show 0 ≤ 2 * ell by positivity)
        have hcancel :
            E2 / (2 * ell) * (2 * ell) = E2 := by
          field_simp [hell.ne']
        rw [hcancel] at hmul
        simpa [mul_assoc] using hmul
      · have hR3 : 3 ≤ R := by omega
        let A : ℕ := (R + 1) / 2
        have hA2 : 2 ≤ A := by
          dsimp [A]
          omega
        have hAlt : A < R := by
          dsimp [A]
          omega
        have hRle2A : R ≤ 2 * A := by
          dsimp [A]
          omega
        have h3A : 3 * A ≤ 2 * R := by
          dsimp [A]
          omega
        have hAleR : A ≤ R := hAlt.le
        have hAposR : (0 : ℝ) < (A : ℝ) := by
          exact_mod_cast (show 0 < A by omega)
        have hRposR : (0 : ℝ) < (R : ℝ) := by
          exact_mod_cast (show 0 < R by omega)
        have hAoneR : (1 : ℝ) ≤ (A : ℝ) := by
          exact_mod_cast (show 1 ≤ A by omega)
        have hRoneR : (1 : ℝ) ≤ (R : ℝ) := by
          exact_mod_cast (show 1 ≤ R by omega)
        have hlogA0 : 0 ≤ Real.log (A : ℝ) :=
          Real.log_nonneg hAoneR
        have hlogR0 : 0 ≤ Real.log (R : ℝ) :=
          Real.log_nonneg hRoneR
        have hlogAR : Real.log (A : ℝ) ≤ Real.log (R : ℝ) :=
          Real.log_le_log hAposR (by exact_mod_cast hAleR)
        have h3AR : 3 * (A : ℝ) ≤ 2 * (R : ℝ) := by
          exact_mod_cast h3A
        have hALog :
            3 * (A : ℝ) * Real.log (A : ℝ) ≤
              2 * (R : ℝ) * Real.log (R : ℝ) := by
          calc
            3 * (A : ℝ) * Real.log (A : ℝ) ≤
                2 * (R : ℝ) * Real.log (A : ℝ) :=
              mul_le_mul_of_nonneg_right h3AR hlogA0
            _ ≤ 2 * (R : ℝ) * Real.log (R : ℝ) :=
              mul_le_mul_of_nonneg_left hlogAR (by positivity)
        have hellR : ell ≤ Real.log (R : ℝ) := by
          dsimp [ell]
          exact Real.log_le_log (by norm_num)
            (by exact_mod_cast hR2)
        have hRlog0 :
            0 ≤ (R : ℝ) * Real.log (R : ℝ) :=
          mul_nonneg (by positivity) hlogR0
        have hfourScale :
            3 * (4 * (A : ℝ)) ≤
              (8 / ell) * (R : ℝ) * Real.log (R : ℝ) := by
          have hleft : 3 * (4 * (A : ℝ)) ≤ 8 * (R : ℝ) := by
            nlinarith [h3AR]
          have hcoef0 : 0 ≤ (8 / ell) * (R : ℝ) := by
            positivity
          have hlogmul :=
            mul_le_mul_of_nonneg_left hellR hcoef0
          have hrewrite :
              (8 / ell) * (R : ℝ) * ell = 8 * (R : ℝ) := by
            field_simp [hell.ne']
            ring
          rw [hrewrite] at hlogmul
          exact hleft.trans hlogmul
        have hInd := ih A hAlt hA2
        have hStep := hC A R hA2 hAlt hRle2A
        have htri :
            |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
              |vfMidPrimeError ((A : ℝ) ^ 2)| +
                |vfMidPrimeError ((R : ℝ) ^ 2) -
                  vfMidPrimeError ((A : ℝ) ^ 2)| := by
          calc
            |vfMidPrimeError ((R : ℝ) ^ 2)| =
                |vfMidPrimeError ((A : ℝ) ^ 2) +
                  (vfMidPrimeError ((R : ℝ) ^ 2) -
                    vfMidPrimeError ((A : ℝ) ^ 2))| := by
                      congr 1
                      ring
            _ ≤ _ := abs_add_le _ _
        have htotal :
            |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
              K * (A : ℝ) * Real.log (A : ℝ) +
                (4 * (A : ℝ) +
                  C * (A : ℝ) * Real.log (A : ℝ)) :=
          htri.trans (add_le_add hInd hStep)
        have hIndScale :
            3 * (K * (A : ℝ) * Real.log (A : ℝ)) ≤
              2 * K * (R : ℝ) * Real.log (R : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left hALog hK0
          nlinarith
        have hCScale :
            3 * (C * (A : ℝ) * Real.log (A : ℝ)) ≤
              2 * C * (R : ℝ) * Real.log (R : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left hALog hC0
          nlinarith
        have hcoeffScale :
            (2 * C + 8 / ell) *
                ((R : ℝ) * Real.log (R : ℝ)) ≤
              K * ((R : ℝ) * Real.log (R : ℝ)) :=
          mul_le_mul_of_nonneg_right hKdom hRlog0
        have htotal3 :=
          mul_le_mul_of_nonneg_left htotal (by norm_num : (0 : ℝ) ≤ 3)
        nlinarith [hIndScale, hCScale, hfourScale, hcoeffScale]

/-- The #843 signed late-correction theorem is therefore already the complete
arithmetic input needed for the global square-endpoint von-Koch bound. -/
theorem vfMidSquareEndpointVonKochBounded_of_signedLateCorrection
    (hcor : VFMidDyadicSignedLateCorrectionStatement) :
    VFMidSquareEndpointVonKochBoundedStatement :=
  vfMidSquareEndpointVonKochBounded_of_dyadicIncrement
    (vfMidDyadicIncrementBounded_of_signedLateCorrection hcor)

/-! ## Dyadic Phi-owner aggregates -/

/-- The transformed Li endpoint aggregate on the exact chronological owner
carrier. -/
def vfMidDyadicLiPhiOwnerAggregate
    (L : ℕ → ℕ → ℂ) (z A B : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ico A B,
    ∑ p ∈ vfMidSquareBandLateOwnerPrimes z r,
      (primeFrequencyCumulativeTransform L
          (((r + 1) ^ 2 - 1) / p) (p - 1) -
        primeFrequencyCumulativeTransform L
          (r ^ 2 / p) (p - 1))

/-- The transformed actual-minus-Li displacement aggregate on the same
chronological owner carrier. -/
def vfMidDyadicPhiDisplacementAggregate
    (Actual L : ℕ → ℕ → ℂ) (z A B : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ico A B,
    ∑ p ∈ vfMidSquareBandLateOwnerPrimes z r,
      (primeFrequencyCumulativeDisplacement Actual L
          (((r + 1) ^ 2 - 1) / p) (p - 1) -
        primeFrequencyCumulativeDisplacement Actual L
          (r ^ 2 / p) (p - 1))

/-- Summing the kernel-checked owner-fibre Phi decomposition gives an exact
identity for the entire chronological owner census. -/
theorem vfMidDyadicOwnerLateRemoval_cast_eq_liPhi_add_displacement
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    (z A B : ℕ) (hA : 3 ≤ A) :
    ((vfMidDyadicOwnerLateRemoval z A B : ℝ) : ℂ) =
      vfMidDyadicLiPhiOwnerAggregate L z A B +
        vfMidDyadicPhiDisplacementAggregate Actual L z A B := by
  unfold vfMidDyadicOwnerLateRemoval
    vfMidDyadicLiPhiOwnerAggregate
    vfMidDyadicPhiDisplacementAggregate
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
  have hr3 : 3 ≤ r := hA.trans hAr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpOwner :
      p ∈ vfMidSquareBandOwnerPrimes r :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  exact
    vfMidSquareBandCompositeOwner_card_eq_liPhi_add_displacement
      hActual hL hr3 hpOwner

/-- **Exact dyadic transfer identity.**
For A >= 3, the physical VF-centered late correction T-H is exactly the
transformed-Li owner correction plus the transformed actual-minus-Li
displacement aggregate.  This is the precise quantitative seam left to bound. -/
theorem vfMidDyadicLateCorrection_cast_eq_liPhiCorrection_add_displacement
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    (z A B : ℕ)
    (hA : 3 ≤ A) (hzA : z ≤ A) (hAB : A ≤ B) :
    ((vfMidDyadicLateRemoval z A B -
        vfMidDyadicLateReference z A B : ℝ) : ℂ) =
      (vfMidDyadicLiPhiOwnerAggregate L z A B -
        (vfMidDyadicLateReference z A B : ℂ)) +
      vfMidDyadicPhiDisplacementAggregate Actual L z A B := by
  have hT :=
    vfMidDyadicLateRemoval_eq_ownerCensus
      z A B (by omega : 2 ≤ A) hzA hAB
  have hOwner :=
    vfMidDyadicOwnerLateRemoval_cast_eq_liPhi_add_displacement
      hActual hL z A B hA
  rw [hT]
  push_cast
  rw [hOwner]
  ring

end RHLean.Analysis
