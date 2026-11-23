import RHLean.Geometry.NativeCMQuadraticOrder
import RHLean.Geometry.NativeCMPeriodComparison
import RHLean.Geometry.NativeThetaPeriodFreeness

/-!
# The analytic polarized CM elliptic seed on the actual quadratic order

The period lattice is the image of the actual order `OK H = Z[H.w0]` under
an actual embedding of the native CM host. Its two periods are `1` and
`tau(H.w0)`, and its complex multiplication is literal multiplication by
that embedded order. No freely selected lattice or quadratic field is used.
The positive Hermitian metric is divided by the actual period parallelogram
area. Its imaginary part is a perfect integral alternating form, including
the orientation when the chosen embedding is in the lower half plane.

This constructs the analytic seed and its exact polarization/period data.
Algebraization to a polarized elliptic scheme over the integers of a number
field, its integral tangent generator, and the Chowla--Selberg comparison
of the mean logarithmic tangent norm are separate, unasserted obligations.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsCmEllipticCurveIntegersWithPeriod.lean`, `HermFormPrincipalDimOne.lean`
and `IsLieNormSqIffEqPiDivCovolume.lean`. The elementary construction below
uses the native quadratic order and periods directly; no external compiled
artifact or terminal RH theorem is imported. The source archive states no
license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField MeasureTheory
open scoped ComplexConjugate

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ)

/-- The actual second period, preserving the selected embedding's sign. -/
def omega : ℂ := embed H τ (wK H)

/-- The period map on the original quadratic order. -/
def period : OK H →+ ℂ := (embed H τ).toAddMonoidHom

theorem period_injective : Function.Injective (period H τ) := by
  intro x y h
  apply Subtype.ext
  apply RingOfIntegers.coe_injective
  exact τ.injective h

theorem two_mul_omega : 2 * omega H τ = 1 + τ (H.rt : E) := by
  have h := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root
  simpa only [map_mul, map_ofNat, map_add, map_one, RingHom.comp_apply,
    omega, embed_wK] using h

theorem root_im_ne_zero : (τ (H.rt : E)).im ≠ 0 := by
  intro hzero
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  have hsq : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by simpa using h
  have hre := congrArg Complex.re hsq
  simp [sq, hzero] at hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg (τ (H.rt : E)).re]

theorem root_re_eq_zero : (τ (H.rt : E)).re = 0 := by
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  have hsq : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by simpa using h
  have him := congrArg Complex.im hsq
  simp [sq] at him
  have hprod : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by nlinarith
  exact (mul_eq_zero.1 hprod).resolve_right (root_im_ne_zero H τ)

theorem omega_re : (omega H τ).re = 1 / 2 := by
  have h := congrArg Complex.re (two_mul_omega H τ)
  simp [root_re_eq_zero H τ] at h
  linarith

theorem omega_im_ne_zero : (omega H τ).im ≠ 0 := by
  intro hzero
  have h := congrArg Complex.im (two_mul_omega H τ)
  simp [hzero] at h
  exact root_im_ne_zero H τ h.symm

theorem omega_im_sq : 4 * (omega H τ).im ^ 2 = H.d := by
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  have hsq : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by simpa using h
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im (two_mul_omega H τ)
  simp [sq, root_re_eq_zero H τ] at hre him
  rw [← him] at hre
  nlinarith

theorem abs_omega_im : |(omega H τ).im| = Real.sqrt H.d / 2 := by
  have hd : (0 : ℝ) ≤ H.d := by positivity
  have hs := Real.sq_sqrt hd
  have h := omega_im_sq H τ
  have ha := sq_abs (omega H τ).im
  nlinarith [abs_nonneg (omega H τ).im, Real.sqrt_nonneg (H.d : ℝ)]

theorem omega_quadratic :
    omega H τ ^ 2 + (((1 + H.d) / 4 : ℕ) : ℂ) = omega H τ := by
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) (cm_generator_sq_quadratic_eq H)
  simpa [omega, embed_wK] using h

theorem period_coordinates (x : ℤ × ℤ) :
    period H τ (coordEquiv H x) = (x.1 : ℂ) + (x.2 : ℂ) * omega H τ := by
  rw [coordEquiv_apply]
  simp [period, omega]

/-- Real coordinates on the actual complex period plane. -/
def realCoordinates : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ where
  toFun x := (x 0 : ℂ) + (x 1 : ℂ) * omega H τ
  invFun z := ![z.re - (omega H τ).re * z.im / (omega H τ).im,
    z.im / (omega H τ).im]
  left_inv x := by
    ext i
    fin_cases i <;> simp
    · field_simp [omega_im_ne_zero H τ]
      ring
    · field_simp [omega_im_ne_zero H τ]
  right_inv z := by
    apply Complex.ext <;> simp
    · field_simp [omega_im_ne_zero H τ]
      ring
    · field_simp [omega_im_ne_zero H τ]
  map_add' x y := by
    apply Complex.ext <;> simp <;> ring
  map_smul' c x := by
    apply Complex.ext <;> simp <;> ring

/-- A real basis is constructed from the same two actual periods. -/
def periodBasis : Module.Basis (Fin 2) ℝ ℂ :=
  (Pi.basisFun ℝ (Fin 2)).map (realCoordinates H τ)

@[simp] theorem periodBasis_zero : periodBasis H τ 0 = 1 := by
  simp [periodBasis, realCoordinates]

@[simp] theorem periodBasis_one : periodBasis H τ 1 = omega H τ := by
  simp [periodBasis, realCoordinates]

/-- The same image lattice, retaining the original CM coefficient module. -/
abbrev lattice : Submodule ℤ ℂ := (period H τ).toIntLinearMap.range

theorem lattice_eq_span_periodBasis :
    lattice H τ = Submodule.span ℤ (Set.range (periodBasis H τ)) := by
  ext z
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨a, rfl⟩
    let x := (coordEquiv H).symm a
    refine ⟨![x.1, x.2], ?_⟩
    have hx := period_coordinates H τ x
    rw [(coordEquiv H).apply_symm_apply] at hx
    simp [Fin.sum_univ_two, zsmul_eq_mul, hx]
  · rintro ⟨n, hn⟩
    refine ⟨coordEquiv H (n 0, n 1), ?_⟩
    change period H τ (coordEquiv H (n 0, n 1)) = z
    rw [period_coordinates]
    simpa [Fin.sum_univ_two, zsmul_eq_mul] using hn

theorem lattice_discrete : DiscreteTopology (lattice H τ) := by
  rw [lattice_eq_span_periodBasis]
  infer_instance

theorem lattice_full : Submodule.span ℝ (lattice H τ : Set ℂ) = ⊤ := by
  rw [eq_top_iff, ← (periodBasis H τ).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  rw [lattice_eq_span_periodBasis]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The analytic CM elliptic torus is the quotient by this actual lattice. -/
abbrev Torus := ℂ ⧸ (period H τ).range

/-- Compactness follows from the actual full lattice, not from a new
geometric hypothesis. -/
theorem torus_compact : CompactSpace (Torus H τ) := by
  let L := lattice H τ
  let : DiscreteTopology L := lattice_discrete H τ
  let : IsZLattice ℝ L := ⟨lattice_full H τ⟩
  change CompactSpace (ℂ ⧸ L)
  refine ⟨?_⟩
  rw [← L.mkQ_surjective.range_eq]
  exact IsZLattice.isCompact_range_of_periodic L _
    L.isOpenQuotientMap_mkQ.continuous fun z w hw => by
      rw [map_add, Submodule.mkQ_apply L w,
        (Submodule.Quotient.mk_eq_zero L).2 hw, add_zero]

/-- Literal multiplication by the quadratic order on its analytic quotient. -/
def cmAction (a : OK H) : Torus H τ →+ Torus H τ :=
  QuotientAddGroup.map (period H τ).range (period H τ).range
    { toFun := fun z => embed H τ a * z
      map_zero' := mul_zero _
      map_add' := fun z w => mul_add _ _ _ } (by
        rintro _ ⟨x, rfl⟩
        exact ⟨a * x, map_mul (embed H τ) a x⟩)

@[simp] theorem cmAction_mk (a : OK H) (z : ℂ) :
    cmAction H τ a (QuotientAddGroup.mk' (period H τ).range z) =
      QuotientAddGroup.mk' (period H τ).range (embed H τ a * z) := rfl

theorem cmAction_one : cmAction H τ 1 = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (period H τ).range x
  change QuotientAddGroup.mk' (period H τ).range (embed H τ 1 * z) =
    QuotientAddGroup.mk' (period H τ).range z
  rw [map_one, one_mul]

theorem cmAction_mul (a b : OK H) :
    cmAction H τ (a * b) = (cmAction H τ a).comp (cmAction H τ b) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (period H τ).range x
  change QuotientAddGroup.mk' (period H τ).range (embed H τ (a * b) * z) =
    QuotientAddGroup.mk' (period H τ).range (embed H τ a * (embed H τ b * z))
  rw [map_mul (embed H τ) a b, mul_assoc]

theorem cmAction_add (a b : OK H) :
    cmAction H τ (a + b) = cmAction H τ a + cmAction H τ b := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (period H τ).range x
  change QuotientAddGroup.mk' (period H τ).range (embed H τ (a + b) * z) =
    QuotientAddGroup.mk' (period H τ).range (embed H τ a * z) +
      QuotientAddGroup.mk' (period H τ).range (embed H τ b * z)
  rw [map_add, add_mul, map_add]

theorem cmAction_zero : cmAction H τ 0 = 0 := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (period H τ).range x
  change QuotientAddGroup.mk' (period H τ).range (embed H τ 0 * z) = 0
  rw [map_zero, zero_mul, map_zero]

/-- The analytic elliptic points carry the genuine order module structure
required by the Serre tensor functor. -/
instance torusModule : Module (OK H) (Torus H τ) where
  smul a x := cmAction H τ a x
  one_smul x := DFunLike.congr_fun (cmAction_one H τ) x
  mul_smul a b x := DFunLike.congr_fun (cmAction_mul H τ a b) x
  smul_zero a := map_zero (cmAction H τ a)
  smul_add a x y := map_add (cmAction H τ a) x y
  add_smul a b x := DFunLike.congr_fun (cmAction_add H τ a b) x
  zero_smul x := DFunLike.congr_fun (cmAction_zero H τ) x

@[simp] theorem torus_smul_mk (a : OK H) (z : ℂ) :
    a • (QuotientAddGroup.mk' (period H τ).range z) =
      QuotientAddGroup.mk' (period H τ).range (embed H τ a * z) := rfl

/-- The genuine quadratic multiplication endomorphism satisfies the
original CM discriminant equation on the actual torus points. -/
theorem torus_cm_equation (x : Torus H τ) :
    wK H • (wK H • x) + (((1 + H.d) / 4 : ℕ) : OK H) • x = wK H • x := by
  have hw : wK H ^ 2 + (((1 + H.d) / 4 : ℕ) : OK H) = wK H :=
    Subtype.ext (cm_generator_sq_quadratic_eq H)
  simpa only [pow_two, add_smul, mul_smul] using congrArg (fun a : OK H => a • x) hw

/-- The squared tangent metric dictated by the actual period area. -/
def hermitian (z w : ℂ) : ℂ :=
  ((|(omega H τ).im|⁻¹ : ℝ) : ℂ) * z * conj w

theorem hermitian_self (z : ℂ) :
    (hermitian H τ z z).re = |(omega H τ).im|⁻¹ * ‖z‖ ^ 2 := by
  rw [hermitian, mul_assoc, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.normSq_eq_norm_sq]

theorem hermitian_pos {z : ℂ} (hz : z ≠ 0) : 0 < (hermitian H τ z z).re := by
  rw [hermitian_self]
  exact mul_pos (inv_pos.2 (abs_pos.2 (omega_im_ne_zero H τ)))
    (sq_pos_of_pos (norm_pos_iff.2 hz))

theorem hermitian_conj (z w : ℂ) :
    hermitian H τ z w = conj (hermitian H τ w z) := by
  simp [hermitian]
  ring

/-- Exact rank-one pi normalization, with the original discriminant. -/
theorem pi_hermitian_one :
    Real.pi * (hermitian H τ 1 1).re = 2 * Real.pi / Real.sqrt H.d := by
  rw [hermitian_self, norm_one, one_pow, mul_one, abs_omega_im, inv_div]
  ring

end RHLean.Geometry.NativeCM.EllipticSeed

end
