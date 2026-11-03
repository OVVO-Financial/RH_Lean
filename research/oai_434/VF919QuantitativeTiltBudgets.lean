import «research.oai_434.VF919FiniteSlotReflectedGain»

/-!
# Enlarged physical tilt from the existing source inequalities

The old choice was e/48. The actual detector budget and finite-slot gap
permit e/2 while preserving the LOW Gram and large-tail conditions.
No improved zero-free region or cancellation bound is assumed here.
-/
namespace OAI
noncomputable section
namespace SevenEighths.RHLeanFiniteSlotGap

/-- A factor-24 enlargement of the physical tilt, chosen before characters
and the arbitrary LOW loss. The contour condition remains strict. -/
theorem enlarged_source_gain_budgets {Delta : ℝ} (D : Parameters.HighData Delta) :
    let delta := D.e / 2
    0 < delta ∧
      24 * delta < (7 / 8 : ℝ) * D.rmin ∧
      delta < 1 / 960 ∧
      24 * delta < D.t ∧
      ∀ beta : ℝ, 7 / 8 - delta ≤ beta → 7 / 8 < beta + D.e := by
  have hs := high_data_small_errors D
  have hepsilon : 576 * D.e < D.ε := by
    linarith only [D.detector_budget, D.kappa_pos, D.cost_pos]
  have hrt : D.rmin * D.t ≤ D.rmin := by
    have ht : D.t ≤ 1 := by linarith only [D.t_small]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht D.rmin_pos.le
  have her : 576 * D.e < D.rmin :=
    hepsilon.trans (D.epsilon_gap.trans_le hrt)
  dsimp only
  refine ⟨div_pos D.e_pos (by norm_num), ?_, ?_, ?_, ?_⟩
  · linarith only [her, D.rmin_pos]
  · linarith only [D.e_small]
  · linarith only [hs.2.1, D.t_pos]
  · intro beta hbeta
    linarith only [hbeta, D.e_pos]

/-- The stated enlargement is an exact identity, not an exponent heuristic. -/
theorem enlarged_tilt_eq_twenty_four_original
    {Delta : ℝ} (D : Parameters.HighData Delta) :
    D.e / 2 = 24 * (D.e / 48) := by ring

#print axioms enlarged_source_gain_budgets
#print axioms enlarged_tilt_eq_twenty_four_original
end SevenEighths.RHLeanFiniteSlotGap
end
end OAI
