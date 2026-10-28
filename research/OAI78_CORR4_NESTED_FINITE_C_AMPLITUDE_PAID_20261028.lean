import Mathlib
import «research.OAI78_CORR4_NESTED_FINITE_C_PAID_20261028»
import «research.MERTENS_EXPONENT_ENVELOPES»

/-!
# Completely paid O(R) CORR4 -> nearest-square nested finite-C boundary

No PNT, no finite-C hypothesis and no new covariance assumption.
The only ingredients are the genuine original low q² owner set,
the existing 1/4 reciprocal-square and selected-root square budgets,
the already-certified R/4 midpoint-shell bound, and |M(n)| <= n.

The source quantity B is the ORIGINAL physical CORR4 remainder,
not a surrogate fractional or prime-cofactor model.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- The original weighted historical daughter column is paid at root scale.
    This is the actual q² owner set and actual nearest completed-square root. -/
theorem oai78_nested_historical_column_le_three_fourths_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖oai78NestedHistoricalColumn R‖ ≤
      (3 / 4 : ℝ) * (R : ℝ) := by
  let S : Finset ℕ := canonicalRoughLowQ2Owners R
  let A : ℝ := ∑ q ∈ S,
    ((1 : ℝ) / (q : ℝ)) * (oai78NestedDaughterRoot R q : ℝ)
  have hsub : S ⊆ (primesUpTo (R - 1)).erase 2 := by
    dsimp [S]
    exact Finset.sdiff_subset
  have hterm : ∀ q ∈ S,
      ‖(1 / (q : ℂ)) *
        mertensSummatory (oai78NestedDaughterRoot R q - 1)‖ ≤
        ((1 : ℝ) / (q : ℝ)) * (oai78NestedDaughterRoot R q : ℝ) := by
    intro q hq
    have hp : q.Prime :=
      (mem_primesUpTo.mp (Finset.mem_erase.mp (hsub hq)).2).1
    have hqp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hp.pos
    have hcoeff : ‖(1 / (q : ℂ))‖ = (1 : ℝ) / (q : ℝ) := by
      rw [norm_div, norm_one, Complex.norm_natCast]
    have hM :=
      RHLean.Analysis.MertensExponent.mertens_norm_le
        (oai78NestedDaughterRoot R q - 1)
    have hnat : (oai78NestedDaughterRoot R q - 1 : ℕ) ≤
        oai78NestedDaughterRoot R q := Nat.sub_le _ _
    have hreal :
        (((oai78NestedDaughterRoot R q - 1 : ℕ) : ℝ)) ≤
          (oai78NestedDaughterRoot R q : ℝ) := by
      exact_mod_cast hnat
    calc
      ‖(1 / (q : ℂ)) *
          mertensSummatory (oai78NestedDaughterRoot R q - 1)‖ =
        ((1 : ℝ) / (q : ℝ)) *
          ‖mertensSummatory (oai78NestedDaughterRoot R q - 1)‖ := by
            rw [norm_mul, hcoeff]
      _ ≤ ((1 : ℝ) / (q : ℝ)) *
          (oai78NestedDaughterRoot R q : ℝ) :=
        mul_le_mul_of_nonneg_left (hM.trans hreal)
          (by positivity)
  have htri : ‖oai78NestedHistoricalColumn R‖ ≤ A := by
    unfold oai78NestedHistoricalColumn
    dsimp [A, S]
    calc
      ‖∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) *
            mertensSummatory (oai78NestedDaughterRoot R q - 1)‖ ≤
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ‖(1 / (q : ℂ)) *
            mertensSummatory (oai78NestedDaughterRoot R q - 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) *
            (oai78NestedDaughterRoot R q : ℝ) :=
          Finset.sum_le_sum (by
            intro q hq
            exact hterm q hq)
  have hA0 : 0 ≤ A := by
    dsimp [A, S]
    apply Finset.sum_nonneg
    intro q hq
    have hp : q.Prime :=
      (mem_primesUpTo.mp (Finset.mem_erase.mp (hsub hq)).2).1
    have hqp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hp.pos
    positivity
  have hcs :
      A ^ 2 ≤
        (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) *
        (∑ q ∈ S, (oai78NestedDaughterRoot R q : ℝ) ^ 2) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq
      (R := ℝ) S
      (fun q => (1 : ℝ) / (q : ℝ))
      (fun q => (oai78NestedDaughterRoot R q : ℝ))
  have hcoeff :
      (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ 1 / 4 := by
    simpa [S, div_pow] using
      lowOwnerReciprocalSquareBudgetReal_le_quarter R
  have hroots :
      (∑ q ∈ S, (oai78NestedDaughterRoot R q : ℝ) ^ 2) ≤
        2 * (R : ℝ) ^ 2 := by
    simpa [S, oai78NestedDaughterRoot] using
      sum_lowOwnerQ2NearestSquareRoot_sq_le_two_root_sq R (by omega)
  have hcoeff0 :
      0 ≤ (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) := by positivity
  have hroots0 :
      0 ≤ (∑ q ∈ S, (oai78NestedDaughterRoot R q : ℝ) ^ 2) := by
    positivity
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hAbound : A ^ 2 ≤ (1 / 2 : ℝ) * (R : ℝ) ^ 2 := by
    calc
      A ^ 2 ≤
          (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) *
            (∑ q ∈ S, (oai78NestedDaughterRoot R q : ℝ) ^ 2) := hcs
      _ ≤ (1 / 4 : ℝ) * (2 * (R : ℝ) ^ 2) :=
        mul_le_mul hcoeff hroots hroots0 (by norm_num)
      _ = (1 / 2 : ℝ) * (R : ℝ) ^ 2 := by ring
  have hhistSq :
      ‖oai78NestedHistoricalColumn R‖ ^ 2 ≤
        (1 / 2 : ℝ) * (R : ℝ) ^ 2 := by
    exact ((sq_le_sq₀ (norm_nonneg _) hA0).2 htri).trans hAbound
  have hscaleSq :
      (1 / 2 : ℝ) * (R : ℝ) ^ 2 ≤
      ((3 / 4 : ℝ) * (R : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (R : ℝ)]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num) hR0)).1 (hhistSq.trans hscaleSq)

/-- Unconditional O(R) payment on the fully physical remainder relative
    to the nested finite-C parent plus children. No hidden RH hypothesis. -/
theorem oai78_nested_finiteC_physical_error_le_three_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowOwnerPhysicalAmplitudeRemainder R 0 -
       (oai78NestedFiniteC R + oai78NestedFiniteCColumn R)‖ ≤
      3 * (R : ℝ) := by
  have htri := oai78_corr4_nested_finiteC_error_triangle R hR
  have hhist :=
    oai78_nested_historical_column_le_three_fourths_root R hR
  have hshell :=
    norm_lowOwnerNearestSquareReciprocalShell_le_quarter_root R
  have hM :=
    RHLean.Analysis.MertensExponent.mertens_norm_le (R - 1)
  have hMle : ‖mertensSummatory (R - 1)‖ ≤ (R : ℝ) := by
    exact hM.trans (by exact_mod_cast (Nat.sub_le R 1))
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  calc
    ‖lowOwnerPhysicalAmplitudeRemainder R 0 -
       (oai78NestedFiniteC R + oai78NestedFiniteCColumn R)‖ ≤
       ‖mertensSummatory (R - 1)‖ +
       2 * ‖oai78NestedHistoricalColumn R‖ +
       ‖lowOwnerNearestSquareReciprocalShell R‖ := htri
    _ ≤ (R : ℝ) + 2 * ((3 / 4 : ℝ) * (R : ℝ)) +
       (R : ℝ) / 4 := by
      nlinarith
    _ ≤ 3 * (R : ℝ) := by nlinarith

#print axioms oai78_nested_historical_column_le_three_fourths_root
#print axioms oai78_nested_finiteC_physical_error_le_three_root

end RHLean.Proof
