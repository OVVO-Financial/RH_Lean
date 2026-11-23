import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoGrowthBall

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LdrInvSubOneLe.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LdrInvSubOneLe.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma ldr_inv_sub_one_le {s : ℂ} (h : 1 ≤ |s.im|) : ‖1 / (s - 1)‖ ≤ 1 := by
  have h1 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, Complex.one_im, sub_zero] at h1
  rw [norm_div, norm_one, div_le_one (by linarith)]
  linarith

end Formalism.ZF

end

end RHLean.Analysis.AlpogeThin
