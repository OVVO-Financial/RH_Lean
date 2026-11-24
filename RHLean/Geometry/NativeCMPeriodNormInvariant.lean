import RHLean.Geometry.NativeCMWeierstrassPeriodScaling
import RHLean.Geometry.NativeCMWeierstrassLatticeCurve
import RHLean.Analysis.DistinguishedPrimeTransitionSupport

/-!
# The actual scale-invariant CM period expression

The expression covol(L)^6 times |Delta(L)| uses the original lattice,
Lebesgue covolume, and Weierstrass invariants. It is proved invariant under
actual lattice homotheties and complex conjugation, exactly as required
for the class/embedding double sum.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/
HasSumLocallyUniformlyWeierstrassZetaExcept.lean (the covolume determinant
and homothety declarations only), and
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
MeanLogCovolumeEqMeanClassGroup.lean (the norm-discriminant and conjugation
declarations only). The source archive states no license; attribution is
retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex NumberField
open scoped Classical BigOperators nonZeroDivisors ComplexConjugate

namespace RHLean.Geometry.NativeCM

namespace PeriodMean

def latticeArea (L : PeriodPair) : ℝ := ZLattice.covolume L.lattice

theorem latticeArea_pos (L : PeriodPair) : 0 < latticeArea L := ZLattice.covolume_pos _ _

theorem latticeArea_eq (L : PeriodPair) : latticeArea L = |(conj L.ω₁ * L.ω₂).im| := by
  rw [latticeArea, ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis
    Complex.orthonormalBasisOneI.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis,
    Complex.orthonormalBasisOneI.volume_parallelepiped]
  simp only [ENNReal.toReal_one, mul_one]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply]
  ring

theorem latticeArea_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    latticeArea L' = latticeArea L := by simp only [latticeArea, h]

theorem latticeArea_eq_abs_im_mul_conj (L : PeriodPair) :
    latticeArea L = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  rw [latticeArea_eq, ← abs_neg]
  congr 1
  simp
  ring


/-- Normalized area of the actual two period vectors in Phi coordinates.
This is the original Lebesgue covolume, not an assigned height. -/
def phiPeriodArea (L : PeriodPair) : ℝ :=
  |RHLean.Analysis.complexRealPairOrientedArea
    (RHLean.Analysis.complexRealPair L.ω₁) (RHLean.Analysis.complexRealPair L.ω₂)|

theorem phiPeriodArea_eq_latticeArea (L : PeriodPair) :
    phiPeriodArea L = latticeArea L := by
  rw [phiPeriodArea, RHLean.Analysis.complexRealPairOrientedArea_complexRealPair,
    latticeArea_eq_abs_im_mul_conj]

def latticeNormDisc (L : PeriodPair) : ℝ :=
  latticeArea L ^ 6 * ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖

theorem discriminant_ne_zero (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 :=
  Weierstrass.latticeCurve_Δ L ▸ Weierstrass.latticeCurve_Δ_ne_zero L

theorem latticeNormDisc_eq (L : PeriodPair) :
    latticeNormDisc L = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 *
      ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ := by
  rw [latticeNormDisc, latticeArea_eq_abs_im_mul_conj]

theorem latticeNormDisc_pos (L : PeriodPair) : 0 < latticeNormDisc L :=
  mul_pos (pow_pos (latticeArea_pos L) _) (norm_pos_iff.mpr (discriminant_ne_zero L))

end PeriodMean

namespace Weierstrass.IsHomothetic

open PeriodMean

theorem latticeArea_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeArea L' = ‖c‖ ^ 2 * latticeArea L := by
  have e : L'.lattice = (scalePeriods L c h.ne_zero).lattice := by
    ext x
    have h1 := h (c⁻¹ * x)
    have h2 := isHomothetic_scalePeriods L c h.ne_zero (c⁻¹ * x)
    rw [mul_inv_cancel_left₀ h.ne_zero] at h1 h2
    exact h1.trans h2.symm
  rw [latticeArea_congr e, ← phiPeriodArea_eq_latticeArea, ← phiPeriodArea_eq_latticeArea]
  unfold phiPeriodArea
  change |RHLean.Analysis.complexRealPairOrientedArea
    (RHLean.Analysis.complexRealPair (c * L.ω₁))
    (RHLean.Analysis.complexRealPair (c * L.ω₂))| = _
  rw [← RHLean.Analysis.complexRealPairMulHom_complexRealPair,
    ← RHLean.Analysis.complexRealPairMulHom_complexRealPair,
    RHLean.Analysis.complexRealPairOrientedArea_mulHom, abs_mul, abs_of_nonneg (sq_nonneg ‖c‖)]

theorem latticeNormDisc_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeNormDisc L' = latticeNormDisc L := by
  have hc : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr h.ne_zero
  have e : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h.g₂_eq, h.g₃_eq]
    ring
  rw [latticeNormDisc, latticeNormDisc, h.latticeArea_eq, e, norm_mul, norm_inv, norm_pow]
  field_simp

end Weierstrass.IsHomothetic

namespace PeriodMean

def conjPeriods (L : PeriodPair) : PeriodPair where
  ω₁ := starRingEnd ℂ L.ω₁
  ω₂ := starRingEnd ℂ L.ω₂
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have := congrArg (starRingEnd ℂ) h
    simpa using this

theorem mem_conjPeriods_lattice (L : PeriodPair) (z : ℂ) :
    z ∈ (conjPeriods L).lattice ↔ starRingEnd ℂ z ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, conjPeriods]
  refine exists₂_congr fun _ _ => ⟨fun h => ?_, fun h => ?_⟩
  · simpa using congrArg (starRingEnd ℂ) h
  · simpa using congrArg (starRingEnd ℂ) h

theorem G_conjPeriods (L : PeriodPair) (n : ℕ) :
    (conjPeriods L).G n = starRingEnd ℂ (L.G n) := by
  let e : L.lattice ≃ (conjPeriods L).lattice :=
    { toFun := fun x => ⟨starRingEnd ℂ x, (mem_conjPeriods_lattice L _).mpr (by simp)⟩
      invFun := fun y => ⟨starRingEnd ℂ y, (mem_conjPeriods_lattice L _).mp y.2⟩
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
  simp only [PeriodPair.G]
  rw [← e.tsum_eq, Complex.conj_tsum]
  simp [e]

theorem latticeNormDisc_conjPeriods (L : PeriodPair) :
    latticeNormDisc (conjPeriods L) = latticeNormDisc L := by
  have e : (conjPeriods L).g₂ ^ 3 - 27 * (conjPeriods L).g₃ ^ 2 =
      starRingEnd ℂ (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    simp only [PeriodPair.g₂, PeriodPair.g₃, G_conjPeriods, map_sub, map_mul, map_pow, map_ofNat]
  have a : latticeArea (conjPeriods L) = latticeArea L := by
    rw [latticeArea_eq, latticeArea_eq_abs_im_mul_conj]
    simp [conjPeriods]
  rw [latticeNormDisc, latticeNormDisc, e, a, Complex.norm_conj]

end PeriodMean

end RHLean.Geometry.NativeCM

end
