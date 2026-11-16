import «research.UNIVERSAL_ENVELOPE_LAWS»
import «research.EULER_SELF_DUAL_ENDPOINT_GATE_20261027»

/-!
# The same dictionary on the original frozen Möbius floor bilinear

This is the existing full self-dual floor source, with both mixed orientations
and all historical Möbius coefficients.  Its exact endpoint identity changes
the centered Mertens numerator only by a root-sized term, uniformly bounded
using the unit Möbius bound.  Every nonnegative-loss envelope absorbs that
term with one scale-independent constant.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open RHLean.Proof RHLean.Analysis.MertensExponent

/-- The dictionary displayed on the existing complete frozen floor source. -/
def FrozenQEnvelopeBound (lam eta : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ, 2 ≤ R →
    ‖eulerSelfDualBilinear R‖ ≤
      C * (R : ℝ) ^ (1 + eta + ε) * (squareRootHistoricalK R) ^ (lam / 2)

/-- The exact source identity supplies both norm comparisons at once. -/
theorem frozenQ_centered_norm_comparison (R : ℕ) (hR : 2 ≤ R) :
    ‖eulerSelfDualBilinear R‖ ≤ ‖mertensSummatory (squareRootEndpoint R) - 1‖ + 3 * (R : ℝ) ∧
    ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤ ‖eulerSelfDualBilinear R‖ + 3 * (R : ℝ) := by
  have hroot : ‖(2 : ℂ) * mertensSummatory (R - 1) - 1‖ ≤ 3 * (R : ℝ) := by
    have hM := mertens_norm_le (R - 1)
    have hpred : ((R - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast Nat.sub_le R 1
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
    calc
      ‖(2 : ℂ) * mertensSummatory (R - 1) - 1‖ ≤
          ‖(2 : ℂ) * mertensSummatory (R - 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 * ‖mertensSummatory (R - 1)‖ + 1 := by simp
      _ ≤ 3 * (R : ℝ) := by linarith
  have hsource := eulerSelfDualBilinear_eq_two_mertens_sub_endpoint R hR
  constructor
  · calc
      ‖eulerSelfDualBilinear R‖ =
          ‖((2 : ℂ) * mertensSummatory (R - 1) - 1) -
            (mertensSummatory (squareRootEndpoint R) - 1)‖ := by rw [hsource]; congr 1; ring
      _ ≤ ‖(2 : ℂ) * mertensSummatory (R - 1) - 1‖ +
          ‖mertensSummatory (squareRootEndpoint R) - 1‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  · calc
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ =
          ‖((2 : ℂ) * mertensSummatory (R - 1) - 1) - eulerSelfDualBilinear R‖ := by
        rw [hsource]
        congr 1
        ring
      _ ≤ ‖(2 : ℂ) * mertensSummatory (R - 1) - 1‖ + ‖eulerSelfDualBilinear R‖ := norm_sub_le _ _
      _ ≤ _ := by linarith

theorem root_le_envelope_scale {lam eta ε : ℝ}
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (hε : 0 ≤ ε) {R : ℕ} (hR : 2 ≤ R) :
    (R : ℝ) ≤ (R : ℝ) ^ (1 + eta + ε) * (squareRootHistoricalK R) ^ (lam / 2) := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
  have hp : (R : ℝ) ≤ (R : ℝ) ^ (1 + eta + ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR1 (show (1 : ℝ) ≤ 1 + eta + ε by linarith)
  have hK : 1 ≤ (squareRootHistoricalK R) ^ (lam / 2) :=
    Real.one_le_rpow (squareRootHistoricalK_one_le (by omega)) (by linarith)
  exact hp.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hK
      (Real.rpow_nonneg (Nat.cast_nonneg R) _))

/-- The frozen-floor and centered endpoint formulations have identical
exponents, with a harmless additive three in their quantified constants. -/
theorem frozenQEnvelope_iff_envelopeBound {lam eta : ℝ}
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta) :
    FrozenQEnvelopeBound lam eta ↔ EnvelopeBound lam eta := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C + 3, by linarith, ?_⟩
    intro R hR
    have hcomparison := (frozenQ_centered_norm_comparison R hR).2
    have hscale := root_le_envelope_scale hlam heta hε.le hR
    have hboundR := hbound R hR
    nlinarith only [hcomparison, hscale, hboundR]
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C + 3, by linarith, ?_⟩
    intro R hR
    have hcomparison := (frozenQ_centered_norm_comparison R hR).1
    have hscale := root_le_envelope_scale hlam heta hε.le hR
    have hboundR := hbound R hR
    nlinarith only [hcomparison, hscale, hboundR]

/-- ENV-5 on the complete original frozen source, not a relaxed kernel. -/
theorem frozenQEnvelope_iff_rightmost_le {lam eta : ℝ}
    (hlam : 0 ≤ lam) (hlam2 : lam < 2) (heta : 0 ≤ eta) :
    FrozenQEnvelopeBound lam eta ↔ zetaRightmostRealPart ≤ 1 / 2 + eta / (2 - lam) :=
  (frozenQEnvelope_iff_envelopeBound hlam heta).trans
    (envelopeBound_iff_rightmost_le hlam hlam2 heta)

/-- The complete floor bilinear has the universal historical exponent too. -/
theorem universal_frozenQ_envelope : FrozenQEnvelopeBound 2 0 :=
  (frozenQEnvelope_iff_envelopeBound (by norm_num) (by norm_num)).mpr universal_envelope_bound

end RHLean.Analysis.UniversalEnvelope

end
