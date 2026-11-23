import RHLean.Geometry.NativeCMWeierstrassSigma

/-!
# The origin theta section and its exact Hermitian automorphy

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean`.

The canonical sigma function has simple zeros exactly on the original
period lattice and derivative one at zero. Its automorphy is proved for
the explicit Hermitian form z*conj(w)/covol(L). This analytic construction
is the input for identifying the original integral origin line bundle.
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

def latticeForm (u v : ℂ) : ℂ := u * conj v / latticeArea L

theorem latticeForm_add_left (u u' v : ℂ) :
    latticeForm L (u + u') v = latticeForm L u v + latticeForm L u' v := by
  simp only [latticeForm]; ring

theorem latticeForm_add_right (u v v' : ℂ) :
    latticeForm L u (v + v') = latticeForm L u v + latticeForm L u v' := by
  simp only [latticeForm, map_add]; ring

theorem latticeForm_mul_left (a u v : ℂ) : latticeForm L (a * u) v = a * latticeForm L u v := by
  simp only [latticeForm]; ring

theorem latticeForm_mul_right (a u v : ℂ) :
    latticeForm L u (a * v) = conj a * latticeForm L u v := by
  simp only [latticeForm, map_mul]; ring

theorem latticeForm_eq_inner (u v : ℂ) : latticeForm L u v = inner ℂ v u / latticeArea L := by
  simp [latticeForm]

theorem conj_latticeForm (u v : ℂ) : conj (latticeForm L u v) = latticeForm L v u := by
  simp [latticeForm, mul_comm]

theorem latticeForm_self (u : ℂ) : latticeForm L u u = (‖u‖ ^ 2 / latticeArea L : ℝ) := by
  simp [latticeForm, mul_conj']

theorem im_latticeForm_int (m n m' n' : ℤ) :
    (latticeForm L (m * L.ω₁ + n * L.ω₂) (m' * L.ω₁ + n' * L.ω₂)).im =
      (n * m' - m * n' : ℤ) * (latticeForm L L.ω₂ L.ω₁).im := by
  simp only [latticeForm, div_ofReal_im]
  simp
  ring

theorem abs_im_latticeForm : |(latticeForm L L.ω₂ L.ω₁).im| = 1 := by
  rw [latticeForm, div_ofReal_im, abs_div, abs_of_pos (latticeArea_pos L), mul_comm,
    ← latticeArea_eq, div_self (latticeArea_pos L).ne']

theorem im_latticeForm_eq_one (h : 0 < (L.ω₂ / L.ω₁).im) : (latticeForm L L.ω₂ L.ω₁).im = 1 := by
  have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  rw [← abs_im_latticeForm L, abs_of_pos]
  rw [latticeForm, div_ofReal_im]
  refine div_pos ?_ (latticeArea_pos L)
  rw [div_im, ← sub_div, div_pos_iff_of_pos_right (normSq_pos.2 h1)] at h
  simp only [mul_im, conj_re, conj_im]
  linarith

theorem exists_int_im_latticeForm {a b : ℂ} (ha : a ∈ L.lattice) (hb : b ∈ L.lattice) :
    ∃ k : ℤ, (latticeForm L a b).im = k := by
  obtain ⟨m, n, rfl⟩ := mem_lattice.1 ha
  obtain ⟨m', n', rfl⟩ := mem_lattice.1 hb
  rw [im_latticeForm_int]
  rcases (abs_eq zero_le_one).1 (abs_im_latticeForm L) with h | h
  · exact ⟨n * m' - m * n', by rw [h, mul_one]⟩
  · exact ⟨-(n * m' - m * n'), by rw [h]; push_cast; ring⟩

theorem IsHomothetic.latticeForm_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (u v : ℂ) : latticeForm L' (c * u) (c * v) = latticeForm L u v := by
  have hc := h.ne_zero
  have hc' : conj c ≠ 0 := by simpa using hc
  rw [latticeForm, latticeForm, h.latticeArea_eq, map_mul]
  push_cast
  rw [← mul_conj']
  field_simp

theorem quasiPeriod_mul_eq (z w : ℂ) :
    quasiPeriod L w * z = sTwo L * w * z + π * latticeForm L z w := by
  rw [quasiPeriod_eq, latticeForm]; push_cast; ring

def canonicalSigma (z : ℂ) : ℂ := weierstrassSigma L z * cexp (-(sTwo L * z ^ 2 / 2))

@[fun_prop] theorem differentiable_canonicalSigma : Differentiable ℂ (canonicalSigma L) := by
  unfold canonicalSigma; fun_prop

@[simp] theorem canonicalSigma_neg (z : ℂ) : canonicalSigma L (-z) = -canonicalSigma L z := by
  simp [canonicalSigma]

@[simp] theorem canonicalSigma_zero : canonicalSigma L 0 = 0 := by simp [canonicalSigma]

theorem canonicalSigma_eq_zero_iff {z : ℂ} : canonicalSigma L z = 0 ↔ z ∈ L.lattice := by
  rw [canonicalSigma, mul_eq_zero, or_iff_left (exp_ne_zero _), weierstrassSigma_eq_zero_iff]

theorem hasDerivAt_canonicalSigma' (z : ℂ) : HasDerivAt (canonicalSigma L)
    ((deriv (weierstrassSigma L) z - sTwo L * z * weierstrassSigma L z) *
      cexp (-(sTwo L * z ^ 2 / 2))) z :=
  ((differentiable_weierstrassSigma L z).hasDerivAt.fun_mul
    ((((hasDerivAt_pow 2 z).const_mul (sTwo L)).div_const 2).fun_neg.cexp)).congr_deriv
    (by simp; ring)

theorem hasDerivAt_canonicalSigma_zero : HasDerivAt (canonicalSigma L) 1 0 := by
  simpa [(hasDerivAt_weierstrassSigma_zero L).deriv] using hasDerivAt_canonicalSigma' L 0

theorem hasDerivAt_canonicalSigma {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt (canonicalSigma L)
    ((weierstrassZeta L z - sTwo L * z) * canonicalSigma L z) z :=
  (hasDerivAt_canonicalSigma' L z).congr_deriv (by
    rw [(hasDerivAt_weierstrassSigma L hz).deriv, canonicalSigma]; ring)

theorem analyticOrderAt_canonicalSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    analyticOrderAt (canonicalSigma L) w = 1 := by
  refine ((differentiable_canonicalSigma L).analyticAt
    w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((canonicalSigma_eq_zero_iff L).2 hw) ?_
  rw [(hasDerivAt_canonicalSigma' L w).deriv, (weierstrassSigma_eq_zero_iff L).2 hw, mul_zero,
    sub_zero]
  exact mul_ne_zero (deriv_weierstrassSigma_ne_zero L hw) (exp_ne_zero _)

theorem IsHomothetic.canonicalSigma_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (z : ℂ) : canonicalSigma L' (c * z) = c * canonicalSigma L z := by
  have := h.ne_zero
  rw [canonicalSigma, h.weierstrassSigma_mul, h.sTwo_eq, canonicalSigma, mul_assoc]
  congr 3
  field_simp

theorem canonicalSigma_add {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    canonicalSigma L (z + w) = sigmaSign L w *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * canonicalSigma L z := by
  rw [canonicalSigma, canonicalSigma, weierstrassSigma_add L hw]
  have : cexp (quasiPeriod L w * (z + w / 2)) * cexp (-(sTwo L * (z + w) ^ 2 / 2)) =
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * cexp (-(sTwo L * z ^ 2 / 2)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination quasiPeriod_mul_eq L z w + quasiPeriod_mul_eq L w w / 2
  linear_combination sigmaSign L w * weierstrassSigma L z * this

theorem sigmaSign_add {a b : ℂ} (ha : a ∈ L.lattice) (hb : b ∈ L.lattice) :
    sigmaSign L (a + b) =
      sigmaSign L a * sigmaSign L b * cexp (π * I * (latticeForm L a b).im) := by
  set x := L.ω₁ / 2
  have hx : canonicalSigma L x ≠ 0 :=
    (canonicalSigma_eq_zero_iff L).not.2 L.ω₁_div_two_notMem_lattice
  have h1 := canonicalSigma_add L (add_mem ha hb) x
  rw [← add_assoc, canonicalSigma_add L hb, canonicalSigma_add L ha] at h1
  have h2 : cexp (π * latticeForm L (x + a) b + π * latticeForm L b b / 2) *
      cexp (π * latticeForm L x a + π * latticeForm L a a / 2) =
      cexp (π * I * (latticeForm L a b).im) *
      cexp (π * latticeForm L x (a + b) + π * latticeForm L (a + b) (a + b) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have h3 := sub_conj (latticeForm L a b)
    rw [conj_latticeForm] at h3
    push_cast at h3
    simp only [latticeForm, map_add] at h3 ⊢
    linear_combination (π / 2 : ℂ) * h3
  refine mul_right_cancel₀ (mul_ne_zero (exp_ne_zero
    (π * latticeForm L x (a + b) + π * latticeForm L (a + b) (a + b) / 2)) hx) ?_
  linear_combination sigmaSign L a * sigmaSign L b * canonicalSigma L x * h2 - h1

end RHLean.Geometry.NativeCM.Weierstrass
