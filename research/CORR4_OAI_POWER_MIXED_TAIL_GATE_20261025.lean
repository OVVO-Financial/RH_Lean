import Mathlib
import «research.CORR4_OAI_POWER_DETERMINISTIC_FRAME_20261025»
import «research.GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT»
import «research.GLOBAL_RETURNED_CORE_SIGNED_OWNER_TELESCOPE»
import «research.GLOBAL_RETURNED_CORE_DIAGONAL_BOUND»

/-!
# CORR-4: isolate the one unresolved signed mixed-tail power bill

Existing unconditional input:
  2*Gamma_R = 2*Gamma_prefix(R)+2*Gamma_mixed(R)
  2*Gamma_prefix(R) <= (1/4)*E_R
  0<=D_R<=3*R²

A NEW source-specific signed estimate
  2*Gamma_mixed(R) <= 2*E_R + A*R^(4*beta)
therefore gives
  2*Gamma_R <= (9/4)*E_R + (A+3)*R^(4*beta) - D_R,
and the completed CORR4 general-power biconditional gives MertensPowerBound
beta for beta>=1/2.

This does NOT prove the new mixed-tail estimate. No new unconditional
Mertens exponent or RH theorem is asserted.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- The genuinely new independent arithmetic estimate, on the existing
    full signed prefix/tail/mixed cell carrier, without absolute ownerwise
    domination or a substitute site weight. -/
def Corr4PowerMixedTailBill (A β : ℝ) : Prop :=
  ∀ R : ℕ, 56 ≤ R →
    2 * lowOwnerPrefixTailMixedRawCellMass R ≤
      2 * canonicalRoughLowQ2DaughterEnergy R +
        A * Real.rpow (R : ℝ) (4 * β)

/-- The native reciprocal prefix costs 1/4 E_R. The remaining mixed-tail
    bill costs 2 E_R, and the physical diagonal costs 3 R². Together,
    they give the CORR4 power Gram bill with precisely A+3. -/
theorem corr4PowerFirstOwnerGram_of_mixedTailBill
    {A β : ℝ} (hβ : (1 / 2 : ℝ) ≤ β)
    (hTail : Corr4PowerMixedTailBill A β) :
    Corr4PowerFirstOwnerGram (A + 3) β := by
  intro R hR
  have hSplit :
      2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerZeroFrequencyFirstOwnerGram R p) =
      2 * lowOwnerReciprocalPrefixRawCellMass R +
        2 * lowOwnerPrefixTailMixedRawCellMass R :=
    (two_mul_sum_lowOwnerZeroFrequencyFirstOwnerGram_eq_signedOwnerTelescope R).trans
      (sum_lowOwnerFirstOwnerSignedCellTelescope_eq_prefix_add_tailMixed R)
  have hPrefix :=
    two_mul_lowOwnerReciprocalPrefixRawCellMass_le_quarter_q2Energy R
  have hTailR := hTail R hR
  have hDiag := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  have hRone : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hRootPower :
      (R : ℝ) ^ 2 ≤ Real.rpow (R : ℝ) (4 * β) := by
    calc
      (R : ℝ) ^ 2 = Real.rpow (R : ℝ) (2 : ℝ) :=
        (Real.rpow_natCast (R : ℝ) 2).symm
      _ ≤ Real.rpow (R : ℝ) (4 * β) :=
        Real.rpow_le_rpow_of_exponent_le hRone (by linarith)
  change
    2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerZeroFrequencyFirstOwnerGram R p) ≤
      (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        (A + 3) * Real.rpow (R : ℝ) (4 * β) -
          lowOwnerZeroFrequencyMobiusDiagonal R
  nlinarith

/-- The newly isolated mixed-tail signed estimate, and NO Gram-side
    additional assumption, suffices for the Mertens power theorem. -/
theorem mertensPowerBound_of_corr4MixedTailBill
    {A β : ℝ} (hβ : (1 / 2 : ℝ) ≤ β) (hA : 0 ≤ A)
    (hTail : Corr4PowerMixedTailBill A β) :
    RHLean.Analysis.MertensExponent.MertensPowerBound β := by
  apply (corr4PowerFirstOwnerGram_iff_mertensPowerBound β hβ).mp
  refine ⟨A + 3, by linarith, ?_⟩
  exact corr4PowerFirstOwnerGram_of_mixedTailBill hβ hTail

/-- Exact exponent currency: any strictly positive saving in the full signed
    MIXED tail below R^(7/2) converts to the matching strict improvement
    below the Mertens x^(7/8) exponent. The independent signed estimate is
    displayed as a hypothesis, never inferred from OAI's 7/8 guidepost. -/
theorem mertensSevenEighthsImprovement_of_corr4MixedTailPowerSaving
    (η A : ℝ) (_hη : 0 < η) (hηmax : η ≤ 3 / 2) (hA : 0 ≤ A)
    (hMixed : ∀ R : ℕ, 56 ≤ R →
      2 * lowOwnerPrefixTailMixedRawCellMass R ≤
        2 * canonicalRoughLowQ2DaughterEnergy R +
          A * Real.rpow (R : ℝ) (7 / 2 - η)) :
    RHLean.Analysis.MertensExponent.MertensPowerBound
      (7 / 8 - η / 4) := by
  apply mertensPowerBound_of_corr4MixedTailBill
    (A := A) (β := 7 / 8 - η / 4) (by linarith) hA
  intro R hR
  convert hMixed R hR using 1
  congr 1
  ring

#print axioms corr4PowerFirstOwnerGram_of_mixedTailBill
#print axioms mertensPowerBound_of_corr4MixedTailBill
#print axioms mertensSevenEighthsImprovement_of_corr4MixedTailPowerSaving

end RHLean.Proof
