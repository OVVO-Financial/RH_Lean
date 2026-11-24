import RHLean.Geometry.NativeCMWeierstrassIntegralSchemeSeed

/-!
# The exact tangent scale of the actual Weierstrass uniformization

The original coordinate change has x = u^2 wp + r and
y = u^3 wp'/2 + u^2 s wp + t. Its origin-chart coordinates are -x/y
and -1/y. Removing the actual wp pole proves that these coordinates have
derivatives 1/u and 0 at the origin. Thus the direction z=u, and not z=1,
has the literal integral first jet [epsilon,-1,0].

The pole removal follows the formulas used in Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsConstOfSqMulTendstoZero.lean`, and uses Mathlib's proved
WeierstrassPExcept identities. The source archive states no license;
attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Filter PeriodPair AlgebraicGeometry CategoryTheory
open scoped Topology CategoryTheory.MonObj

namespace RHLean.Geometry.NativeCM.WeierstrassTangent

variable (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ)

def affineX (z : ℂ) : ℂ := (C.u : ℂ) ^ 2 * ℘[L] z + C.r

def affineY (z : ℂ) : ℂ :=
  (C.u : ℂ) ^ 3 * (℘'[L] z / 2) + (C.u : ℂ) ^ 2 * C.s * ℘[L] z + C.t

/-- The actual x coordinate after removing its double pole. -/
def regularX (z : ℂ) : ℂ :=
  (C.u : ℂ) ^ 2 * (z ^ 2 * ℘[L - (0 : ℂ)] z + 1) + C.r * z ^ 2

/-- The actual y coordinate after removing its triple pole. -/
def regularY (z : ℂ) : ℂ :=
  (C.u : ℂ) ^ 3 * (z ^ 3 * ℘'[L - (0 : ℂ)] z / 2 - 1) +
    (C.u : ℂ) ^ 2 * C.s * z * (z ^ 2 * ℘[L - (0 : ℂ)] z + 1) + C.t * z ^ 3

@[simp] theorem regularX_zero : regularX L C 0 = (C.u : ℂ) ^ 2 := by
  simp [regularX]

@[simp] theorem regularY_zero : regularY L C 0 = -(C.u : ℂ) ^ 3 := by
  simp [regularY]

theorem regularY_zero_ne : regularY L C 0 ≠ 0 := by
  rw [regularY_zero]
  exact neg_ne_zero.mpr (pow_ne_zero 3 (Units.ne_zero C.u))

theorem regularX_analytic : AnalyticAt ℂ (regularX L C) 0 := by
  have hP : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 :=
    L.analyticOnNhd_weierstrassPExcept 0 0 (by simp)
  unfold regularX
  fun_prop

theorem regularY_analytic : AnalyticAt ℂ (regularY L C) 0 := by
  have hP : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 :=
    L.analyticOnNhd_weierstrassPExcept 0 0 (by simp)
  have hD : AnalyticAt ℂ ℘'[L - (0 : ℂ)] 0 :=
    L.analyticOnNhd_derivWeierstrassPExcept 0 0 (by simp)
  unfold regularY
  fun_prop

theorem regularX_eq {z : ℂ} (hz : z ≠ 0) :
    regularX L C z = z ^ 2 * affineX L C z := by
  have h := L.weierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ z
  simp only [sub_zero, div_zero, zero_pow two_ne_zero] at h
  rw [regularX, affineX, h]
  field_simp
  ring

theorem regularY_eq {z : ℂ} (hz : z ≠ 0) :
    regularY L C z = z ^ 3 * affineY L C z := by
  have hP := L.weierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ z
  have hD := L.derivWeierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ z
  simp only [sub_zero, div_zero, zero_pow two_ne_zero] at hP
  simp only [sub_zero] at hD
  rw [regularY, affineY, hP, hD]
  field_simp
  ring

/-- A regular extension of the original projective origin coordinate -x/y. -/
def originZ (z : ℂ) : ℂ := z * (-regularX L C z / regularY L C z)

/-- A regular extension of the other origin coordinate -1/y. -/
def originW (z : ℂ) : ℂ := z ^ 3 * (-1 / regularY L C z)

@[simp] theorem originZ_zero : originZ L C 0 = 0 := by simp [originZ]

@[simp] theorem originW_zero : originW L C 0 = 0 := by simp [originW]

theorem originZ_eq {z : ℂ} (hz : z ≠ 0) (hy : affineY L C z ≠ 0) :
    originZ L C z = -affineX L C z / affineY L C z := by
  rw [originZ, regularX_eq L C hz, regularY_eq L C hz]
  field_simp

theorem originW_eq {z : ℂ} (hz : z ≠ 0) (hy : affineY L C z ≠ 0) :
    originW L C z = -1 / affineY L C z := by
  rw [originW, regularY_eq L C hz]
  field_simp

theorem originZ_hasDerivAt : HasDerivAt (originZ L C) (C.u : ℂ)⁻¹ 0 := by
  have hq : DifferentiableAt ℂ (fun z => -regularX L C z / regularY L C z) 0 :=
    (regularX_analytic L C).differentiableAt.neg.div
      (regularY_analytic L C).differentiableAt (regularY_zero_ne L C)
  refine HasDerivAt.congr_deriv (f := originZ L C)
    ((hasDerivAt_id (0 : ℂ)).mul hq.hasDerivAt) ?_
  simp only [id, one_mul, zero_mul, add_zero, regularX_zero, regularY_zero, neg_div_neg_eq]
  field_simp

theorem originW_hasDerivAt : HasDerivAt (originW L C) 0 0 := by
  have hq : DifferentiableAt ℂ (fun z => (-1 : ℂ) / regularY L C z) 0 :=
    (differentiableAt_const (-1 : ℂ)).div (regularY_analytic L C).differentiableAt
      (regularY_zero_ne L C)
  refine HasDerivAt.congr_deriv (f := originW L C)
    (((hasDerivAt_id (0 : ℂ)).pow 3).mul hq.hasDerivAt) ?_
  simp

/-- The direction given by the actual coordinate-change unit has origin
coordinate derivative one. -/
theorem scaled_originZ_hasDerivAt :
    HasDerivAt (fun z => originZ L C ((C.u : ℂ) * z)) 1 0 := by
  have hmul : HasDerivAt (fun z : ℂ => (C.u : ℂ) * z) (C.u : ℂ) 0 := by
    simpa using! (hasDerivAt_id (0 : ℂ)).const_mul (C.u : ℂ)
  have ho : HasDerivAt (originZ L C) (C.u : ℂ)⁻¹ ((C.u : ℂ) * 0) := by
    simpa only [mul_zero] using! originZ_hasDerivAt L C
  simpa only [Function.comp_def, inv_mul_cancel₀ (Units.ne_zero C.u)] using! ho.comp 0 hmul

theorem scaled_originW_hasDerivAt :
    HasDerivAt (fun z => originW L C ((C.u : ℂ) * z)) 0 0 := by
  have hmul : HasDerivAt (fun z : ℂ => (C.u : ℂ) * z) (C.u : ℂ) 0 := by
    simpa using! (hasDerivAt_id (0 : ℂ)).const_mul (C.u : ℂ)
  have ho : HasDerivAt (originW L C) 0 ((C.u : ℂ) * 0) := by
    simpa only [mul_zero] using! originW_hasDerivAt L C
  simpa only [Function.comp_def, zero_mul] using! ho.comp 0 hmul

/-- The actual first jet is exactly the specified integral Lie generator. -/
theorem scaled_origin_firstJet :
    (![TrivSqZeroExt.inr (deriv (fun z => originZ L C ((C.u : ℂ) * z)) 0), -1,
        TrivSqZeroExt.inr (deriv (fun z => originW L C ((C.u : ℂ) * z)) 0)] :
      Fin 3 → DualNumber ℂ) = ![DualNumber.eps, -1, 0] := by
  rw [(scaled_originZ_hasDerivAt L C).deriv, (scaled_originW_hasDerivAt L C).deriv,
    TrivSqZeroExt.inr_zero]
  rfl

open SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie

/-- Extension of scalars on the actual dual-number coordinates. -/
def dualMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) :
    DualNumber R →+* DualNumber S where
  toFun a := TrivSqZeroExt.inl (φ a.fst) + TrivSqZeroExt.inr (φ a.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

/-- The integral origin vector extends to the same literal epsilon point. -/
theorem integralVector_scalarExtension {R : Type} [CommRing R]
    (W : _root_.WeierstrassCurve R) (φ : R →+* ℂ) :
    ∃ h : IsUnimodularSol
        (W.map ((algebraMap ℂ (DualNumber ℂ)).comp φ)) ![DualNumber.eps, -1, 0],
      spMap (dualMap φ) ≫ (integralVector W).left =
        ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp φ) ![DualNumber.eps, -1, 0] h := by
  have hρ : (dualMap φ).comp (algebraMap R (DualNumber R)) =
      (algebraMap ℂ (DualNumber ℂ)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (dualMap φ ∘ ![DualNumber.eps, -1, 0]) =
      (![DualNumber.eps, -1, 0] : Fin 3 → DualNumber ℂ) := by
    ext1 j
    fin_cases j
    · ext <;> simp [dualMap]
    · simp
    · simp
  let h0 : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0] :=
    isUnimodularSol_origin (equation_inr W 1)
  have h := h0.map_comp (dualMap φ)
  rw [hρ, hP] at h
  refine ⟨h, ?_⟩
  change spMap (dualMap φ) ≫
    ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h0 = _
  exact (SpecMap_ptHom W _ _ h0 (dualMap φ)).trans
    (ptHom_congr W _ _ _ hρ hP _)

/-- The actual analytic first jet in direction u equals the extension of
the specified integral Lie generator, as a morphism of schemes. -/
theorem scaled_origin_firstJet_eq_integralVector {R : Type} [CommRing R]
    (W : _root_.WeierstrassCurve R) (φ : R →+* ℂ) :
    let P : Fin 3 → DualNumber ℂ :=
      ![TrivSqZeroExt.inr (deriv (fun z => originZ L C ((C.u : ℂ) * z)) 0), -1,
        TrivSqZeroExt.inr (deriv (fun z => originW L C ((C.u : ℂ) * z)) 0)]
    ∃ h : IsUnimodularSol (W.map ((algebraMap ℂ (DualNumber ℂ)).comp φ)) P,
      spMap (dualMap φ) ≫ (integralVector W).left =
        ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp φ) P h := by
  obtain ⟨h, hv⟩ := integralVector_scalarExtension W φ
  have hP := scaled_origin_firstJet L C
  refine ⟨hP.symm ▸ h, ?_⟩
  exact hv.trans (ptHom_congr W _ _ h rfl hP.symm _)

section ActualSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (W : _root_.WeierstrassCurve ℂ)
    (hC : C • W = Weierstrass.latticeCurve (EllipticSeed.periodPair G τ))

/-- Near the origin these regular coordinates are the coordinates of the
same actual elliptic exponential, with its original scale C. -/
theorem actual_exponential_origin_coordinates :
    ∀ᶠ z in 𝓝 (0 : ℂ), z = 0 ∨
      ∃ h : W.toAffine.Nonsingular
          (affineX (EllipticSeed.periodPair G τ) C z)
          (affineY (EllipticSeed.periodPair G τ) C z),
        EllipticSeed.equationExponential G τ W C hC z = .some _ _ h ∧
        originZ (EllipticSeed.periodPair G τ) C z =
          -affineX (EllipticSeed.periodPair G τ) C z /
            affineY (EllipticSeed.periodPair G τ) C z ∧
        originW (EllipticSeed.periodPair G τ) C z =
          -1 / affineY (EllipticSeed.periodPair G τ) C z := by
  let L := EllipticSeed.periodPair G τ
  filter_upwards [(regularY_analytic L C).continuousAt.eventually_ne (regularY_zero_ne L C),
    L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hy hz
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  have hzl : z ∉ L.lattice := by
    intro hm
    exact hz ⟨hm, hz0⟩
  have hzseed : z ∉ EllipticSeed.lattice G τ := by
    simpa only [L, EllipticSeed.periodPair_lattice] using! hzl
  have hy' : affineY L C z ≠ 0 := by
    intro hy0
    rw [regularY_eq L C hz0, hy0, mul_zero] at hy
    exact hy rfl
  obtain ⟨h, he⟩ := EllipticSeed.equationExponential_coordinates G τ W C hC hzseed
  exact Or.inr ⟨h, he, originZ_eq L C hz0 hy', originW_eq L C hz0 hy'⟩

end ActualSeed

/-- The same constructed integral group scheme has both the actual complex
exponential and the specified integral first jet. In particular, its
integral origin vector is the analytic direction `C.u`, with the original
discriminant scale and period kernel retained. -/
theorem exists_integral_group_scheme_seed_with_exact_tangent
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
      (W : _root_.WeierstrassCurve (𝓞 M)) (w : 𝓞 M)
      (C : _root_.WeierstrassCurve.VariableChange ℂ) (hΔ : W.Δ = 1),
      let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
      (∀ a : E, τ a ∈ M) ∧ ((w : M) : ℂ) = EllipticSeed.omega G τ ∧
      IsLieBasis ![integralVector W] ∧
      (C.u : ℂ) ^ 12 *
        (Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)).Δ = 1 ∧
      ∃ hC : C • W.baseChange ℂ =
          Weierstrass.latticeCurve (EllipticSeed.periodPair G τ),
        Function.Surjective (schemeExponential G τ W C hC) ∧
        (∀ z, schemeExponential G τ W C hC z = 0 ↔ z ∈ EllipticSeed.lattice G τ) ∧
        (∀ᶠ z in 𝓝 (0 : ℂ), z = 0 ∨
          ∃ h : (W.baseChange ℂ).toAffine.Nonsingular
              (affineX (EllipticSeed.periodPair G τ) C z)
              (affineY (EllipticSeed.periodPair G τ) C z),
            EllipticSeed.equationExponential G τ (W.baseChange ℂ) C hC z =
              .some _ _ h ∧
            originZ (EllipticSeed.periodPair G τ) C z =
              -affineX (EllipticSeed.periodPair G τ) C z /
                affineY (EllipticSeed.periodPair G τ) C z ∧
            originW (EllipticSeed.periodPair G τ) C z =
              -1 / affineY (EllipticSeed.periodPair G τ) C z) ∧
        let P : Fin 3 → DualNumber ℂ :=
          ![TrivSqZeroExt.inr (deriv (fun z =>
              originZ (EllipticSeed.periodPair G τ) C ((C.u : ℂ) * z)) 0), -1,
            TrivSqZeroExt.inr (deriv (fun z =>
              originW (EllipticSeed.periodPair G τ) C ((C.u : ℂ) * z)) 0)]
        ∃ h : IsUnimodularSol
            (W.map ((algebraMap ℂ (DualNumber ℂ)).comp (algebraMap (𝓞 M) ℂ))) P,
          spMap (dualMap (algebraMap (𝓞 M) ℂ)) ≫ (integralVector W).left =
            ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp (algebraMap (𝓞 M) ℂ)) P h := by
  obtain ⟨M, hM, W, w, C, hΔ, hhost, hw, -, -, -, -, hLie, -, hu,
    hC, hsurj, hker, -⟩ := exists_integral_group_scheme_seed G τ
  let _ : NumberField M := hM
  let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
  refine ⟨M, hM, W, w, C, hΔ, hhost, hw, hLie, hu, hC, hsurj, hker, ?_, ?_⟩
  · exact actual_exponential_origin_coordinates C G τ (W.baseChange ℂ) hC
  · exact scaled_origin_firstJet_eq_integralVector (EllipticSeed.periodPair G τ) C W
      (algebraMap (𝓞 M) ℂ)

end RHLean.Geometry.NativeCM.WeierstrassTangent

end
