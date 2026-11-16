import «research.NATIVE_OWNER_PREFIX_MERTENS_20261021»
import «research.MERTENS_CONVERSE_IDENTIFICATION»

/-!
# Critical native-owner bounds and the Mertens half-exponent

The existing native-owner consumer proves that zero owner loss implies the
Mertens half-exponent.  This module supplies the reverse direction on the SAME
complete signed source.  The identity is `M(X_R)^2 = D_R + Gamma_R`, with the
original nonnegative prime-owner diagonal.  No individual signed interaction
is discarded before that identity is applied.

Consequently the zero-loss native-owner premise is equivalent to the
RH-strength Mertens growth statement.  These are equivalences of open
arithmetic propositions; none of their equivalent premises is asserted.
The reverse consumer is evaluated at the actual zero supremum, so no OpenAI
source or numerical sub-one Mertens seed is imported.

This does not identify every fixed positive owner-loss premise with its
consumer's zero boundary, and does not identify uniform finite amplification
with an every-positive-loss statement.
-/

noncomputable section

namespace RHLean.Analysis.OwnerPrefix

open RHLean.Analysis.MertensExponent

/-- RH-strength Mertens growth bounds the original complete signed owner
compensation with zero owner loss.  Each epsilon uses its own finite constant;
there is no epsilon-free bound or limit of constants. -/
theorem native_owner_zero_of_mertens_half
    (hgrowth : MertensGrowthAtMost (1 / 2 : ℝ)) :
    NativeOwnerBound 0 := by
  change OwnerBound nativeM nativeA 0
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hgrowth (ε / 4) (by linarith)
  refine ⟨C ^ 2 + 1, by positivity, ?_⟩
  intro R hR
  have hX1 : 1 ≤ endpoint R := by
    have hsq := Nat.pow_le_pow_left hR 2
    norm_num at hsq
    unfold endpoint
    omega
  have hX0 : 0 < (endpoint R : ℝ) := by
    exact_mod_cast (show 0 < endpoint R by omega)
  have hXle : (endpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    unfold endpoint
    exact_mod_cast Nat.sub_le (R ^ 2) 1
  have hpowSquare :
      ((endpoint R : ℝ) ^ ((1 : ℝ) / 2 + ε / 4)) ^ (2 : ℕ) =
        (endpoint R : ℝ) ^ (1 + ε / 2) := by
    rw [← Real.rpow_mul_natCast hX0.le ((1 : ℝ) / 2 + ε / 4) 2]
    congr 1
    ring
  have hMsquare :
      ‖mertensSummatory (endpoint R)‖ ^ 2 ≤
        C ^ 2 * (endpoint R : ℝ) ^ (1 + ε / 2) := by
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg hX0.le _))).mpr
        (hbound (endpoint R) hX1)
    simpa only [mul_pow, hpowSquare] using hs
  have hsmallPower : (endpoint R : ℝ) ^ (ε / 2) ≤ (R : ℝ) ^ ε := by
    calc
      (endpoint R : ℝ) ^ (ε / 2) ≤ ((R : ℝ) ^ 2) ^ (ε / 2) :=
        Real.rpow_le_rpow hX0.le hXle (by linarith)
      _ = (R : ℝ) ^ ε := by
        rw [← Real.rpow_natCast (R : ℝ) 2,
          ← Real.rpow_mul (Nat.cast_nonneg R)]
        congr 1
        ring
  have hsplit :
      (endpoint R : ℝ) ^ (1 + ε / 2) =
        (endpoint R : ℝ) * (endpoint R : ℝ) ^ (ε / 2) := by
    rw [Real.rpow_add hX0, Real.rpow_one]
  have hD0 : 0 ≤ diagonal nativeM R := diagonal_nonneg nativeM R
  have hcomplete := square_eq_diagonal_add_compensation nativeM nativeA
    (native_decomposition R hR)
  have hcomp : compensation nativeM nativeA R ≤ nativeM (endpoint R) ^ 2 := by
    linarith only [hcomplete, hD0]
  have hRp0 : 0 ≤ (R : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg R) ε
  calc
    compensation nativeM nativeA R ≤ nativeM (endpoint R) ^ 2 := hcomp
    _ = ‖mertensSummatory (endpoint R)‖ ^ 2 := by
      rw [← sq_abs, nativeM_abs_eq_norm]
    _ ≤ C ^ 2 * (endpoint R : ℝ) ^ (1 + ε / 2) := hMsquare
    _ = (C ^ 2 * (endpoint R : ℝ)) * (endpoint R : ℝ) ^ (ε / 2) := by
      rw [hsplit]
      ring
    _ ≤ (C ^ 2 * (endpoint R : ℝ)) * (R : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left hsmallPower (by positivity)
    _ = C ^ 2 * (R : ℝ) ^ ε * (endpoint R : ℝ) := by ring
    _ ≤ (C ^ 2 + 1) * (R : ℝ) ^ ε * (endpoint R : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hRp0) hX0.le
    _ ≤ (C ^ 2 + 1) * (R : ℝ) ^ ε *
        ((endpoint R : ℝ) + diagonal nativeM R) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hD0) (by positivity)
    _ = (C ^ 2 + 1) * (R : ℝ) ^ (0 + ε) *
        ((endpoint R : ℝ) + diagonal nativeM R) := by rw [zero_add]

/-- Evaluate the existing complete-source consumer at the independently
defined zero boundary.  If that boundary exceeded 1/2, zero owner loss would
force it strictly below itself.  No numerical Mertens seed is needed. -/
theorem mertens_half_of_native_owner_zero
    (howner : NativeOwnerBound 0) :
    MertensGrowthAtMost (1 / 2 : ℝ) := by
  apply (growthAtMost_iff_rightmost_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  by_contra hnot
  have hhalf : (1 / 2 : ℝ) < zetaRightmostRealPart := lt_of_not_ge hnot
  have hcurrent : MertensGrowthAtMost zetaRightmostRealPart :=
    growthAtMost_of_strip rightmost_nonneg strip_at_rightmost
  have hnext := native_growthAtMost_of_ownerBound
    (κ := 0) (θ := zetaRightmostRealPart) (by norm_num) hhalf.le howner hcurrent
  have hnext0 : 0 ≤ (1 + 2 * zetaRightmostRealPart + 0) / 4 := by
    linarith
  have hboundary := (growthAtMost_iff_rightmost_le hnext0).mp hnext
  linarith

/-- The reverse source bound and the existing complete-source consumer give
an equivalence, with neither open arithmetic premise assumed globally. -/
theorem native_owner_zero_iff_mertens_half :
    NativeOwnerBound 0 ↔ MertensGrowthAtMost (1 / 2 : ℝ) :=
  ⟨mertens_half_of_native_owner_zero, native_owner_zero_of_mertens_half⟩

/-- Critical-line formulation through the already proved analytic Mertens
identification.  The original owner source remains unchanged. -/
theorem native_owner_zero_iff_criticalZeros :
    NativeOwnerBound 0 ↔
      ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) :=
  native_owner_zero_iff_mertens_half.trans growthAtMost_half_iff_criticalZeros

end RHLean.Analysis.OwnerPrefix

end
