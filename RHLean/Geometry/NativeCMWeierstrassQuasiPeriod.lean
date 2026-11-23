import RHLean.Geometry.NativeCMWeierstrassZeta

/-!
# Exact quasi-period and covolume comparison

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean`.

The Legendre relation is derived from the actual Eisenstein series transform.
It identifies the conjugate-linear coefficient of the quasi-period with
pi divided by the existing native lattice covolume.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real

namespace RHLean.Geometry.NativeCM.Weierstrass

open RHLean.Geometry.NativeCM.PeriodMean

variable (L : PeriodPair)

namespace IsHomothetic

variable {L} {L' : PeriodPair} {c : ℂ}

theorem weierstrassZeta_mul (h : IsHomothetic c L L') (z : ℂ) :
    weierstrassZeta L' (c * z) = c⁻¹ * weierstrassZeta L z := by
  simp only [weierstrassZeta, zetaTerm_eq]
  rw [← h.equiv.tsum_eq, ← tsum_mul_left]
  congr with l
  have := h.ne_zero
  simp only [coe_equiv, ← mul_sub, mul_pow, div_eq_mul_inv, mul_inv]
  field_simp

theorem quasiPeriod_mul (h : IsHomothetic c L L') (w : ℂ) :
    quasiPeriod L' (c * w) = c⁻¹ * quasiPeriod L w := by
  have key : ∀ w ∈ L.lattice, quasiPeriod L' (c * w) = c⁻¹ * quasiPeriod L w := by
    intro w hw
    have hz := L.ω₁_div_two_notMem_lattice
    have h1 := weierstrassZeta_add L' ((h w).2 hw) ((h _).not.2 hz)
    rw [← mul_add, h.weierstrassZeta_mul, h.weierstrassZeta_mul, weierstrassZeta_add L hw hz] at h1
    linear_combination -h1
  have : (quasiPeriod L').comp (LinearMap.mulLeft ℝ c) =
      (LinearMap.mulLeft ℝ c⁻¹).comp (quasiPeriod L) := by
    refine L.basis.ext fun i => ?_
    fin_cases i
    · simpa using key _ L.ω₁_mem_lattice
    · simpa using key _ L.ω₂_mem_lattice
  exact LinearMap.congr_fun this w

end IsHomothetic

theorem weierstrassZeta_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    weierstrassZeta L' = weierstrassZeta L := by
  ext z; simpa using (isHomothetic_one_iff.2 h).weierstrassZeta_mul z

theorem quasiPeriod_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    quasiPeriod L' = quasiPeriod L :=
  LinearMap.ext fun z => by simpa using (isHomothetic_one_iff.2 h).quasiPeriod_mul z

open EisensteinSeries SummationFilter in

theorem quasiPeriod_ω₁_eq_eisenstein (τ : UpperHalfPlane) (hτ : (τ : ℂ) * L.ω₁ = L.ω₂) :
    quasiPeriod L L.ω₁ = L.ω₁⁻¹ * G2 τ := by
  have h0 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have h1 : quasiPeriod L L.ω₁ = weierstrassZeta L L.ω₁ := by
    rw [quasiPeriod_eq_weierstrassZetaExcept L L.ω₁_mem_lattice h0,
      ← weierstrassZetaExcept_add L L.ω₁_mem_lattice, zetaTerm_eq]
    simp only [sub_self, div_zero, zero_add]
    field_simp
    ring
  let e : ℤ × ℤ ≃ L.lattice :=
    ((Equiv.prodComm ℤ ℤ).trans L.latticeEquivProd.symm.toEquiv).trans (Equiv.neg _)
  have he : ∀ p : ℤ × ℤ, (e p : ℂ) = -(L.ω₁ * (p.1 * τ + p.2)) := by
    intro p
    have := L.latticeEquiv_symm_apply p.swap
    simp only [Prod.fst_swap, Prod.snd_swap] at this
    simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Equiv.neg_apply, NegMemClass.coe_neg,
      LinearEquiv.coe_toEquiv, this, ← hτ]
    ring
  have h2 := (e.hasSum_iff.2 (hasSum_weierstrassZeta L L.ω₁))
  have h3 : HasSum (fun m : ℤ => L.ω₁⁻¹ * e2Summand m τ) (weierstrassZeta L L.ω₁) := by
    refine h2.prod_fiberwise fun m => ?_
    have s1 := (e2Summand_summable m τ).hasSum
    have s2 := (summable_right_one_div_linear_sub_one_div_linear_succ τ m).hasSum
    rw [← tsum_eq_of_summable_unconditional (L := symmetricIco ℤ)
      (summable_right_one_div_linear_sub_one_div_linear_succ τ m),
      tsum_symmetricIco_linear_sub_linear_add_one_eq_zero] at s2
    convert (s1.sub s2).mul_left L.ω₁⁻¹ using 1
    · rfl
    · ext n
      simp only [Function.comp_apply, he, zetaTerm_eq, eisSummand, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [show L.ω₁ - -(L.ω₁ * (m * τ + n)) = L.ω₁ * (m * τ + n + 1) by ring]
      simp only [zpow_neg, zpow_ofNat, div_neg, inv_neg, neg_sq, mul_pow, div_eq_mul_inv, mul_inv, one_mul]
      generalize ((m : ℂ) * τ + n + 1)⁻¹ = a
      generalize (((m : ℂ) * τ + n) ^ 2)⁻¹ = b
      linear_combination (L.ω₁⁻¹ * b) * mul_inv_cancel₀ h0
    · rw [sub_zero, e2Summand]
  have h4 := h3.mul_left L.ω₁
  simp only [mul_inv_cancel_left₀ h0] at h4
  rw [h1, G2, tsum_eq_of_summable_unconditional h4.summable, h4.tsum_eq, inv_mul_cancel_left₀ h0]

def rotatePeriods : PeriodPair where
  ω₁ := L.ω₂
  ω₂ := -L.ω₁
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have := LinearIndependent.pair_iff.1 L.indep (-t) s (by
      simp only [real_smul, ofReal_neg] at h ⊢
      linear_combination h)
    exact ⟨this.2, by simpa using this.1⟩

theorem lattice_rotatePeriods : (rotatePeriods L).lattice = L.lattice := by
  ext x
  simp only [mem_lattice, rotatePeriods]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨-n, m, by push_cast; linear_combination h⟩
  · rintro ⟨m, n, h⟩
    exact ⟨n, -m, by push_cast; linear_combination h⟩

def swapPeriods : PeriodPair where
  ω₁ := L.ω₂
  ω₂ := L.ω₁
  indep := LinearIndependent.pair_symm_iff.1 L.indep

theorem lattice_swapPeriods : (swapPeriods L).lattice = L.lattice := by
  simp only [lattice, swapPeriods, Set.pair_comm]

theorem legendre_relation (h : 0 < (L.ω₂ / L.ω₁).im) :
    quasiPeriod L L.ω₁ * L.ω₂ - quasiPeriod L L.ω₂ * L.ω₁ = 2 * π * I := by
  have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have h2 : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1
  let τ : UpperHalfPlane := ⟨L.ω₂ / L.ω₁, h⟩
  have hτ : (τ : ℂ) = L.ω₂ / L.ω₁ := rfl
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -(L.ω₁ / L.ω₂) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [hτ]
  have e1 := quasiPeriod_ω₁_eq_eisenstein L τ (by rw [hτ]; field_simp)
  have e2 := quasiPeriod_ω₁_eq_eisenstein (rotatePeriods L) (ModularGroup.S • τ)
    (by rw [hS]; simp only [rotatePeriods]; field_simp)
  rw [quasiPeriod_congr (lattice_rotatePeriods L)] at e2
  simp only [rotatePeriods] at e2
  rw [e1, e2, EisensteinSeries.G2_S_transform τ, hτ]
  field_simp
  ring
def sTwo : ℂ := (quasiPeriod L 1 - I * quasiPeriod L I) / 2

theorem realLinear_eq_add_conj (f : ℂ →ₗ[ℝ] ℂ) (w : ℂ) :
    f w = (f 1 - I * f I) / 2 * w + (f 1 + I * f I) / 2 * conj w := by
  have : f w = w.re * f 1 + w.im * f I := by
    conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • I by simp]
    rw [map_add, map_smul, map_smul, real_smul, real_smul]
  rw [this]
  have h1 : conj w = w.re - w.im * I := by apply Complex.ext <;> simp
  rw [h1]
  conv_rhs => enter [1, 2]; rw [← re_add_im w]
  linear_combination (w.im * f I) * I_mul_I

theorem quasiPeriod_eq (w : ℂ) :
    quasiPeriod L w = sTwo L * w + (π / latticeArea L : ℝ) * conj w := by
  wlog h : 0 < (L.ω₂ / L.ω₁).im generalizing L
  · have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
    have h2 : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1
    have hA := latticeArea_pos L
    rw [latticeArea_eq, abs_pos] at hA
    have := this (swapPeriods L) (by
      simp only [swapPeriods]
      have n1 := normSq_pos.2 h1
      have n2 := normSq_pos.2 h2
      rw [div_im, ← sub_div] at h ⊢
      rw [not_lt, div_nonpos_iff] at h
      simp only [mul_im, conj_re, conj_im] at hA
      refine div_pos (lt_of_le_of_ne ?_ fun h' => hA ?_) n2
      · rcases h with h | h <;> nlinarith [h.1, h.2]
      · linarith)
    rwa [sTwo, quasiPeriod_congr (lattice_swapPeriods L),
      latticeArea_congr (lattice_swapPeriods L)] at this
  have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have hleg := legendre_relation L h
  have hA : latticeArea L = (conj L.ω₁ * L.ω₂).im := by
    rw [latticeArea_eq, abs_of_pos]
    rw [div_im, ← sub_div, div_pos_iff_of_pos_right (normSq_pos.2 h1)] at h
    simp only [mul_im, conj_re, conj_im]
    linarith
  have hA' : conj L.ω₁ * L.ω₂ - conj L.ω₂ * L.ω₁ = 2 * (latticeArea L : ℂ) * I := by
    rw [hA]; apply Complex.ext <;> simp <;> ring
  have hA0 : (latticeArea L : ℂ) ≠ 0 := by exact_mod_cast (latticeArea_pos L).ne'
  have hc : (quasiPeriod L 1 + I * quasiPeriod L I) / 2 = (π / latticeArea L : ℝ) := by
    rw [realLinear_eq_add_conj _ L.ω₁, realLinear_eq_add_conj _ L.ω₂] at hleg
    push_cast
    rw [eq_div_iff hA0]
    refine mul_right_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero) ?_
    linear_combination hleg - (quasiPeriod L 1 + I * quasiPeriod L I) / 2 * hA'
  rw [realLinear_eq_add_conj, hc, sTwo]

theorem sTwo_unique {s w : ℂ} (hw : w ≠ 0)
    (h : quasiPeriod L w = s * w + (π / latticeArea L : ℝ) * conj w) : s = sTwo L := by
  rw [quasiPeriod_eq] at h
  exact (mul_right_cancel₀ hw (add_right_cancel h)).symm

theorem quasiPeriod_mul_sub (a b : ℂ) : quasiPeriod L a * b - quasiPeriod L b * a =
    2 * π * I * ((conj a * b).im / latticeArea L : ℝ) := by
  have : conj a * b - conj b * a = 2 * ((conj a * b).im : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  rw [quasiPeriod_eq, quasiPeriod_eq]
  push_cast
  linear_combination (π / latticeArea L : ℂ) * this

theorem IsHomothetic.sTwo_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    sTwo L' = (c ^ 2)⁻¹ * sTwo L := by
  have hc := h.ne_zero
  refine (sTwo_unique L' hc ?_).symm
  have h1 := h.quasiPeriod_mul 1
  have hA0 : (latticeArea L : ℂ) ≠ 0 := by exact_mod_cast (latticeArea_pos L).ne'
  have hc' : conj c ≠ 0 := by simpa using hc
  rw [mul_one] at h1
  rw [h1, quasiPeriod_eq, h.latticeArea_eq]
  push_cast
  rw [← mul_conj']
  simp only [map_one]
  field_simp

theorem sTwo_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) : sTwo L' = sTwo L := by
  simp only [sTwo, quasiPeriod_congr h]

theorem sTwo_eq_eisenstein (τ : UpperHalfPlane) (h1 : L.ω₁ = 1) (h2 : L.ω₂ = τ) :
    sTwo L = EisensteinSeries.G2 τ - (π / τ.im : ℝ) := by
  have e := quasiPeriod_ω₁_eq_eisenstein L τ (by rw [h1, h2, mul_one])
  have hA : latticeArea L = τ.im := by
    rw [latticeArea_eq, h1, h2]; simp [abs_of_pos τ.im_pos]
  rw [quasiPeriod_eq, h1, hA] at e
  simp only [mul_one, map_one, inv_one, one_mul] at e
  linear_combination e

end RHLean.Geometry.NativeCM.Weierstrass
