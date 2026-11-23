import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoNegReLeNorm

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZeroFreeOf.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZeroFreeOf.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex

noncomputable section

namespace Formalism.ZF

theorem classicalZeroFreeRegionOfBounds : ZeroFreeOf := by
  intro h341 hLDR hG hI hSH hLL
  obtain ⟨t₀, -, ht₀⟩ := zfo_large h341 hLDR hG hI hLL
  obtain ⟨c₂, hc₂, hsmall⟩ := hSH t₀
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 200000) (c₂ * Real.log 2), lt_min (by norm_num) (mul_pos hc₂ hlog2), ?_⟩
  intro s hs1 hre
  have hL : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hLpos : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hlog2 hL
  rcases le_or_gt |s.im| t₀ with hT | hT
  · apply hsmall s hT _ hs1
    have hc : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ c₂ := by
      rw [div_le_iff₀ hLpos]
      calc min (1 / 200000) (c₂ * Real.log 2) ≤ c₂ * Real.log 2 := min_le_right _ _
        _ ≤ c₂ * Real.log (|s.im| + 2) := mul_le_mul_of_nonneg_left hL hc₂.le
    linarith
  · intro hz
    have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
    have hβ := ht₀ s.re s.im hT.le (by rw [← hs]; exact hz)
    have h2 : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ (1 / 200000) / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith

end Formalism.ZF

end

end RHLean.Analysis.AlpogeThin
