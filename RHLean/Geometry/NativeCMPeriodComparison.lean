import RHLean.Geometry.NativeThetaAppellHumbert

/-!
# Exact period-volume and tangent-Gram comparison

The positive matrix and the integral alternating form are the original native
period data. Their perfect pairing forces the actual Lebesgue covolume times
the Hermitian determinant to be one. Every factor of pi and every change-of-
tangent-basis determinant is retained in the normalized comparison below.
This is an archimedean period comparison, not an algebraic model, arithmetic
CM degree, or Chowla--Selberg formula.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`VolumeFundamentalDomainStdRealBasis.lean`. The native image-lattice
specialization uses RHLean's constructed prescribed periods. No external
compiled artifact or terminal RH result is imported. The source archive
states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Matrix
open RHLean.Geometry.NativeGeometricPeriods
open scoped ComplexOrder

namespace RHLean.Geometry.NativeCMPeriodComparison.UnimodVol

def stdRealBasis (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

theorem volume_fundamentalDomain_stdRealBasis (g : ℕ) :
    volume (ZSpan.fundamentalDomain (stdRealBasis g)) = 1 := by
  have h : ZSpan.fundamentalDomain (stdRealBasis g) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, stdRealBasis, Pi.basis_repr, Sigma.forall, Fin.forall_fin_two]
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

theorem re_dotProduct_star {g : ℕ} (z w : Fin g → ℂ) :
    (z ⬝ᵥ star w).re = ∑ k, (stdRealBasis g).repr z k * (stdRealBasis g).repr w k := by
  simp [stdRealBasis, Pi.basis_repr, Fintype.sum_sigma, Fin.sum_univ_two, dotProduct]

theorem im_hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (hermForm Hm z w).im = (z ⬝ᵥ star ((Complex.I • Hm.map star) *ᵥ w)).re := by
  have : star ((Complex.I • Hm.map star) *ᵥ w) = (-Complex.I) • Hm *ᵥ star w := by
    ext k
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this, dotProduct_smul, hermForm]
  simp

theorem det_gram_im {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (v : (Σ _ : Fin g, Fin 2) → Fin g → ℂ) :
    (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im).det =
      ((stdRealBasis g).det v) ^ 2 * ‖Hm.det‖ ^ 2 := by
  set T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (Matrix.toLin' (Complex.I • Hm.map star)).restrictScalars ℝ with hT
  have h : (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im) =
      ((stdRealBasis g).toMatrix v)ᵀ * (stdRealBasis g).toMatrix (T ∘ v) := by
    ext i j
    rw [Matrix.of_apply, im_hermForm, re_dotProduct_star, Matrix.mul_apply]
    rfl
  have hd : LinearMap.det T = ‖Hm.det‖ ^ 2 := by
    have : (Hm.map star).det = star Hm.det := ((starRingEnd ℂ).map_det Hm).symm
    rw [hT, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, Matrix.det_smul, this]
    simp
  rw [h, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply, ← Module.Basis.det_apply,
    Module.Basis.det_comp, hd]
  ring

theorem posDef_of_hermForm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) : Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := hpos (star x) (by simpa using hx)
  have h2 := hH.im_star_dotProduct_mulVec_self x
  rw [hermForm, star_star] at h1
  exact Complex.pos_iff.2 ⟨h1, h2.symm⟩

theorem det_re_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    0 < Hm.det.re ∧ ‖Hm.det‖ = Hm.det.re := by
  have h := (posDef_of_hermForm hH hpos).det_pos
  exact ⟨(Complex.pos_iff.1 h).1, (Complex.re_eq_norm.2 h.le).symm⟩

end RHLean.Geometry.NativeCMPeriodComparison.UnimodVol

namespace RHLean.Geometry.NativeCMPeriodComparison

open UnimodVol

theorem volume_mul_det_eq_one_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) : (volume Fd).toReal * Hm.det.re = 1 := by
  have : IsZLattice ℝ Λ := ⟨hfull⟩
  let b₁ := Module.Free.chooseBasis ℤ Λ
  let b := b₁.reindex ((b₁.ofZLatticeBasis ℝ Λ).indexEquiv (stdRealBasis g))
  have hvol : (volume Fd).toReal = |(stdRealBasis g).det (Subtype.val ∘ b)| := by
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hFd
    rw [ZLattice.covolume_eq_det_mul_measureReal Λ volume b (stdRealBasis g), Measure.real,
      volume_fundamentalDomain_stdRealBasis] at h1
    simpa [Measure.real] using h1.symm
  have hu := LinearEquiv.isUnit_det (LinearEquiv.ofBijective Ef hbij) b b.dualBasis
  set M := LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective Ef hbij : Λ →ₗ[ℤ] Module.Dual ℤ Λ)
    with hM
  have hG : (Matrix.of fun i j => (hermForm Hm ((Subtype.val ∘ b) i) ((Subtype.val ∘ b) j)).im) =
      ((Int.castRingHom ℝ).mapMatrix M)ᵀ := by
    ext i j
    simp [hM, LinearMap.toMatrix_apply, hE]
  have hdet := det_gram_im Hm (Subtype.val ∘ b)
  rw [hG, Matrix.det_transpose, ← RingHom.map_det] at hdet
  obtain ⟨hp, hn⟩ := det_re_pos hH hpos
  have habs : |((M.det : ℤ) : ℝ)| = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
  rw [hn, eq_intCast] at hdet
  rw [hdet, ← mul_pow, abs_of_nonneg (sq_nonneg _), ← sq_abs, abs_mul, abs_of_pos hp,
    pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero] at habs
  rw [hvol, habs]

theorem det_gram_pi_hermForm {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)).det =
      (Real.pi : ℂ) ^ g * Hm.det * ((‖W.det‖ ^ 2 : ℝ) : ℂ) := by
  have h : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)) =
      (Real.pi : ℂ) • (W * (Hm * Wᴴ)) := by
    ext i j
    simp [hermForm, Matrix.mul_apply, dotProduct, mulVec]
  rw [h, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin,
    ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

theorem volume_div_eq_inv_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) (W : Matrix (Fin g) (Fin g) ℂ) (hW : W.det ≠ 0) :
    0 < Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 ∧
    (volume Fd).toReal / (Real.pi ^ g * ‖W.det‖ ^ 2) = (Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2)⁻¹ ∧
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)).det =
      ((Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 : ℝ) : ℂ) := by
  have h := volume_mul_det_eq_one_of_unimodular g Λ hfull Hm Ef Fd hH hpos hE hbij hFd
  have hp := (det_re_pos hH hpos).1
  have hW' : 0 < ‖W.det‖ := norm_pos_iff.2 hW
  have hπ := Real.pi_pos
  refine ⟨by positivity, ?_, ?_⟩
  · rw [eq_inv_of_mul_eq_one_left h]
    field_simp
  · have him : Hm.det = (Hm.det.re : ℂ) :=
      Complex.ext rfl (by simpa using (Complex.pos_iff.1 (posDef_of_hermForm hH hpos).det_pos).2.symm)
    rw [det_gram_pi_hermForm, him]
    push_cast
    simp

end RHLean.Geometry.NativeCMPeriodComparison

namespace RHLean.Geometry.NativeCMPeriodComparison

open NumberField NativeGeometricPeriods

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} (D : NativeGeometricDatum H) {g : ℕ}
    (P : D.La →+ (Fin g → ℂ))

/-- The actual image of the original period map, with no new lattice choice. -/
abbrev periodLattice : Submodule ℤ (Fin g → ℂ) := P.toIntLinearMap.range

/-- Carry the same perfect alternating form onto its actual period image. -/
def periodImageForm (hP : Function.Injective P) :
    LinearMap.BilinForm ℤ (periodLattice D P) :=
  let e := LinearEquiv.ofInjective P.toIntLinearMap hP
  D.EF.comp e.symm.toLinearMap e.symm.toLinearMap

theorem periodImageForm_bijective (hP : Function.Injective P) :
    Function.Bijective (periodImageForm D P hP) := by
  let e : D.La ≃ₗ[ℤ] periodLattice D P :=
    LinearEquiv.ofInjective P.toIntLinearMap hP
  constructor
  · intro x y h
    apply e.symm.injective
    apply D.unimod.1
    ext z
    have hz := congrArg (fun f : periodLattice D P →ₗ[ℤ] ℤ => f (e z)) h
    change D.EF (e.symm x) (e.symm (e z)) =
      D.EF (e.symm y) (e.symm (e z)) at hz
    simpa only [e.symm_apply_apply] using hz
  · intro f
    obtain ⟨x, hx⟩ := D.unimod.2 (f.comp e.toLinearMap)
    refine ⟨e x, ?_⟩
    ext y
    change D.EF (e.symm (e x)) (e.symm y) = f y
    rw [e.symm_apply_apply, hx]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem periodImageForm_eq_im (hP : Function.Injective P)
    (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (a b : periodLattice D P) :
    (periodImageForm D P hP a b : ℝ) = (hermForm Hm a b).im := by
  let e : D.La ≃ₗ[ℤ] periodLattice D P :=
    LinearEquiv.ofInjective P.toIntLinearMap hP
  have ha : P (e.symm a) = (a : Fin g → ℂ) :=
    congrArg Subtype.val (e.apply_symm_apply a)
  have hb : P (e.symm b) = (b : Fin g → ℂ) :=
    congrArg Subtype.val (e.apply_symm_apply b)
  change (D.EF (e.symm a) (e.symm b) : ℝ) = _
  rw [← ha, ← hb, hEF]

/-- Exact comparison on the native period image. The finite and infinite
normalizations use the very same perfect form; no measure scalar is supplied. -/
theorem isPeriod_volume_mul_det_eq_one
    {ty : Fin g → (E →+* ℂ)} (hP : IsPeriod D ty P)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (Fd : Set (Fin g → ℂ))
    (hFd : IsAddFundamentalDomain (periodLattice D P) Fd volume) :
    (volume Fd).toReal * Hm.det.re = 1 := by
  let : DiscreteTopology (periodLattice D P) := hP.2.2.1
  apply volume_mul_det_eq_one_of_unimodular g (periodLattice D P)
    hP.2.2.2.1 Hm (periodImageForm D P hP.2.1) Fd hH hpos
    (periodImageForm_eq_im D P hP.2.1 Hm hEF)
    (periodImageForm_bijective D P hP.2.1) hFd

/-- The exact normalized tangent determinant on the original native periods.
This retains the entire determinant of the tangent basis and all pi powers. -/
theorem isPeriod_volume_div_eq_inv
    {ty : Fin g → (E →+* ℂ)} (hP : IsPeriod D ty P)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (Fd : Set (Fin g → ℂ))
    (hFd : IsAddFundamentalDomain (periodLattice D P) Fd volume)
    (W : Matrix (Fin g) (Fin g) ℂ) (hW : W.det ≠ 0) :
    0 < Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 ∧
    (volume Fd).toReal / (Real.pi ^ g * ‖W.det‖ ^ 2) =
      (Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2)⁻¹ ∧
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)).det =
      ((Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 : ℝ) : ℂ) := by
  let : DiscreteTopology (periodLattice D P) := hP.2.2.1
  exact volume_div_eq_inv_of_unimodular g (periodLattice D P)
    hP.2.2.2.1 Hm (periodImageForm D P hP.2.1) Fd hH hpos
    (periodImageForm_eq_im D P hP.2.1 Hm hEF)
    (periodImageForm_bijective D P hP.2.1) hFd W hW

end RHLean.Geometry.NativeCMPeriodComparison

namespace RHLean.Geometry.NativeCMPeriodComparison

open NumberField NativeGeometricPeriods

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} (D : NativeGeometricDatum H) {g : ℕ}
    (P : D.La →+ (Fin g → ℂ))

/-- Canonical Lebesgue covolume of the actual period image. -/
theorem isPeriod_covolume_mul_det_eq_one
    {ty : Fin g → (E →+* ℂ)} (hP : IsPeriod D ty P)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) :
    ZLattice.covolume (periodLattice D P) * Hm.det.re = 1 := by
  classical
  let L := periodLattice D P
  let : DiscreteTopology L := hP.2.2.1
  let : IsZLattice ℝ L := ⟨hP.2.2.2.1⟩
  let b := Module.Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume
    (ZLattice.isAddFundamentalDomain b volume)]
  exact isPeriod_volume_mul_det_eq_one D P hP Hm hH hpos hEF _
    (ZLattice.isAddFundamentalDomain b volume)

end RHLean.Geometry.NativeCMPeriodComparison

namespace RHLean.Analysis.AlpogeThin

open NumberField
open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeGeometricPeriods
open RHLean.Geometry.NativeCMPeriodComparison
open NativeRawHostPolarization
open scoped Pointwise

/-- The exact covolume comparison for the SAME prescribed projective lattice,
period map, and principal polarization. No period matrix comparison is assumed. -/
theorem nativeDyadicPrescribedPeriod_exists_exact_covolume
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    let P := prescribedPeriodMap H.toHostRaw B hB k m j
    ∃ Hm : Matrix (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1)))
        (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1))) ℂ,
      Hm.IsHermitian ∧
      (∀ z, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) ∧
      ZLattice.covolume (periodLattice D P) * Hm.det.re = 1 := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
  let P := prescribedPeriodMap H.toHostRaw B hB k m j
  have hP := (nativeDyadicPrescribedGeometricDatum_isPeriod e q d he hH B hB k m j hk hj).2
  obtain ⟨Hm, hHerm, hpos, hEF⟩ := hP.2.2.2.2
  exact ⟨Hm, hHerm, hpos, hEF,
    isPeriod_covolume_mul_det_eq_one D P hP Hm hHerm hpos hEF⟩

end RHLean.Analysis.AlpogeThin

end
