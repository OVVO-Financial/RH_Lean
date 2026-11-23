import Mathlib

/-!
# Exact homothety of the original elliptic period lattice

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean`.
The declaration cut is `IsHomothetic` through `IsHomothetic.G_eq`.
The final two invariant identities are the same direct lattice-sum
calculations as `LatticeDeterminedByInvariants.IsHomothetic.g₂_eq/g₃_eq`.
All periods and Weierstrass functions are the original analytic objects.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open Filter Complex PeriodPair
open scoped Topology

noncomputable section

namespace RHLean.Geometry.NativeCM.Weierstrass

variable (L : PeriodPair)

def IsHomothetic (c : ℂ) (L L' : PeriodPair) : Prop := ∀ x, c * x ∈ L'.lattice ↔ x ∈ L.lattice

def scalePeriods (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    refine LinearIndependent.pair_iff.1 L.indep s t (mul_left_cancel₀ hc ?_)
    simp only [real_smul] at h ⊢
    linear_combination h

theorem isHomothetic_scalePeriods (c : ℂ) (hc : c ≠ 0) :
    IsHomothetic c L (scalePeriods L c hc) := by
  intro x
  simp only [mem_lattice, scalePeriods]
  refine exists₂_congr fun m n => ⟨fun h => mul_left_cancel₀ hc ?_, fun h => ?_⟩
  · linear_combination h
  · linear_combination c * h

theorem isHomothetic_one_iff {L L' : PeriodPair} :
    IsHomothetic 1 L L' ↔ L'.lattice = L.lattice := by
  simp [IsHomothetic, SetLike.ext_iff]

namespace IsHomothetic

variable {L} {L' : PeriodPair} {c : ℂ}

theorem ne_zero (h : IsHomothetic c L L') : c ≠ 0 := by
  rintro rfl
  exact L.ω₁_div_two_notMem_lattice ((h _).1 (by simp))

def equiv (h : IsHomothetic c L L') : L.lattice ≃ L'.lattice where
  toFun x := ⟨c * x, (h _).2 x.2⟩
  invFun y := ⟨c⁻¹ * y, (h _).1 (by simp [h.ne_zero])⟩
  left_inv x := by simp [h.ne_zero]
  right_inv y := by simp [h.ne_zero]

@[simp] theorem coe_equiv (h : IsHomothetic c L L') (x : L.lattice) :
    (h.equiv x : ℂ) = c * x := rfl

theorem weierstrassP_mul (h : IsHomothetic c L L') (z : ℂ) :
    ℘[L'] (c * z) = (c ^ 2)⁻¹ * ℘[L] z := by
  simp only [weierstrassP]
  rw [← h.equiv.tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [coe_equiv, ← mul_sub, mul_pow, one_div, mul_inv]

theorem derivWeierstrassP_mul (h : IsHomothetic c L L') (z : ℂ) :
    ℘'[L'] (c * z) = (c ^ 3)⁻¹ * ℘'[L] z := by
  simp only [derivWeierstrassP]
  rw [← h.equiv.tsum_eq, mul_neg, ← tsum_mul_left]
  congr with l
  simp only [coe_equiv, ← mul_sub, mul_pow, div_eq_mul_inv, mul_inv]
  ring

theorem G_eq (h : IsHomothetic c L L') (n : ℕ) : L'.G n = (c ^ n)⁻¹ * L.G n := by
  simp only [PeriodPair.G]
  rw [← h.equiv.tsum_eq, ← tsum_mul_left]
  simp only [coe_equiv, mul_pow, mul_inv]

theorem g₂_eq (h : IsHomothetic c L L') : L'.g₂ = (c ^ 4)⁻¹ * L.g₂ := by
  rw [g₂, g₂, h.G_eq]
  ring

theorem g₃_eq (h : IsHomothetic c L L') : L'.g₃ = (c ^ 6)⁻¹ * L.g₃ := by
  rw [g₃, g₃, h.G_eq]
  ring

end IsHomothetic

end RHLean.Geometry.NativeCM.Weierstrass

end
