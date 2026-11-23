import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.FinsumMemLeFinsumMem
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.Jensen
import RHLean.Analysis.AlpogeThin.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.RightOne

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Assemble.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Assemble.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

namespace PI.ZW

theorem rightChi : RightChi := rightChi_of jensenCount

theorem rightOne : RightOne := rightOne_of jensenCount

theorem zerosWindow_of_transfer (hT : Transfer) :
    PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow := by
  intro hL hZ hI
  obtain ⟨C₁, h₁⟩ := rightChi hL hI
  obtain ⟨C₂, h₂⟩ := rightOne hZ hI
  have hlog : ∀ (N : ℕ) [NeZero N] (t : ℝ), 0 ≤ Real.log (↑N * (|t| + 2)) := by
    intro N _ t
    apply Real.log_nonneg
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hN) (add_nonneg (abs_nonneg t) zero_le_two)]
  have h₁' : RightChiWith (max C₁ 1) := by
    unfold RightChiWith at h₁ ⊢
    intro N _ χ hχ t
    obtain ⟨hf, hs⟩ := h₁ N χ hχ t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog N t))⟩
  have h₂' : RightOneWith (max C₂ 1) := by
    unfold RightOneWith at h₂ ⊢
    intro N _ χ hχ t
    obtain ⟨hf, hs⟩ := h₂ N χ hχ t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog N t))⟩
  have hw := zerosWindowWith_of _ (rightHalf_of _ _ h₁' h₂') hT
  unfold PI.ZerosWindow
  exact ⟨_, mul_pos two_pos (lt_of_lt_of_le one_pos (le_trans (le_max_right C₁ 1) (le_max_left _ _))), hw⟩

end PI.ZW

end RHLean.Analysis.AlpogeThin
