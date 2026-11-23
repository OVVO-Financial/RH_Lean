import RHLean.Geometry.NativeCMWeierstrassAnalyticTangent
import RHLean.Geometry.NativeCMChowlaSelberg

/-!
# The actual integral tangent and its place-indexed analytic period profile

The same integral equation W with discriminant one is uniformized at every
infinite place. Each chosen lattice and coordinate change satisfies the
actual equation comparison. Its exponential has the exact lattice kernel,
and its origin coordinates identify the analytic direction u with the
scalar extension of the literal integral tangent vector [epsilon,-1,0].

The resulting positive profile is pi*|u|^2/covol(L). Its negative logarithm
is proved to be the actual lattice logarithmic period using u^12*Delta(L)=1.
The profile is indexed by places and pulled back to all complex embeddings,
which enforces the existing AllWt conjugation convention. No class-group
mean is assigned, and no arithmetic Serre Lie norm or polarizing line bundle
is claimed. Compatibility of the conjugate charts is a separate statement.

The equation and first-jet calculations use the reconstructed native
Weierstrass suppliers from Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/
WeierstrassCurvePointOfLatticeAddOfGeneric.lean and
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
ExistsConstOfSqMulTendstoZero.lean. The source archive states no license;
attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField Filter PeriodPair AlgebraicGeometry CategoryTheory
open scoped Classical Topology

namespace RHLean.Geometry.NativeCM.AllPlaceTangentPeriod

open WeierstrassTangent

section Uniformization

variable (L : PeriodPair) (W : WeierstrassCurve ℂ)
    (C : WeierstrassCurve.VariableChange ℂ) (hC : C • W = Weierstrass.latticeCurve L)

/-- The actual equation exponential for an arbitrary period lattice. -/
def exponential : ℂ →+ W.toAffine.Point :=
  (Weierstrass.variableChangePointEquiv C hC).toAddMonoidHom.comp
    (Weierstrass.latticePointHom L)

@[simp] theorem exponential_apply (z : ℂ) :
    exponential L W C hC z =
      Weierstrass.variableChangePoint C hC (Weierstrass.latticePoint L z) := rfl

theorem exponential_surjective : Function.Surjective (exponential L W C hC) :=
  (Weierstrass.variableChangePointEquiv C hC).surjective.comp
    (Weierstrass.latticePoint_surjective L)

theorem exponential_ker (z : ℂ) :
    exponential L W C hC z = 0 ↔ z ∈ L.lattice := by
  let e := Weierstrass.variableChangePointEquiv C hC
  change e (Weierstrass.latticePointHom L z) = 0 ↔ _
  have hz : e (Weierstrass.latticePointHom L z) = 0 ↔
      Weierstrass.latticePointHom L z = 0 :=
    ⟨fun h => e.injective (h.trans e.map_zero.symm), fun h => h ▸ e.map_zero⟩
  rw [hz, Weierstrass.latticePointHom_apply, Weierstrass.latticePoint_eq_zero_iff]

/-- These coordinates belong to the same exponential, not merely to a
formal expression with the same first-order behavior. -/
theorem exponential_coordinates {z : ℂ} (hz : z ∉ L.lattice) :
    ∃ h : W.toAffine.Nonsingular (affineX L C z) (affineY L C z),
      exponential L W C hC z = .some _ _ h := by
  refine ⟨(Weierstrass.nonsingular_variableChange_iff W C
    (L.weierstrassP z) (L.derivWeierstrassP z / 2)).mpr
      (hC ▸ Weierstrass.latticeCurve_nonsingular L hz), ?_⟩
  rw [exponential_apply, Weierstrass.latticePoint_of_notMem _ hz,
    Weierstrass.variableChangePoint_some]

/-- The generic near-origin comparison retains the actual equation and
its coordinate-change unit. -/
theorem exponential_origin_coordinates :
    ∀ᶠ z in 𝓝 (0 : ℂ), z = 0 ∨
      ∃ h : W.toAffine.Nonsingular (affineX L C z) (affineY L C z),
        exponential L W C hC z = .some _ _ h ∧
        originZ L C z = -affineX L C z / affineY L C z ∧
        originW L C z = -1 / affineY L C z := by
  filter_upwards [(regularY_analytic L C).continuousAt.eventually_ne (regularY_zero_ne L C),
    L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hy hz
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  have hzl : z ∉ L.lattice := by
    intro hm
    exact hz ⟨hm, hz0⟩
  have hy' : affineY L C z ≠ 0 := by
    intro hy0
    rw [regularY_eq L C hz0, hy0, mul_zero] at hy
    exact hy rfl
  obtain ⟨h, he⟩ := exponential_coordinates L W C hC hzl
  exact Or.inr ⟨h, he, originZ_eq L C hz0 hy', originW_eq L C hz0 hy'⟩

end Uniformization

section Profile

variable {F : Type} [Field F] (W : WeierstrassCurve (𝓞 F))

/-- The coefficient embedding at the actual infinite-place representative. -/
def placeMap (v : InfinitePlace F) : 𝓞 F →+* ℂ :=
  v.embedding.comp (algebraMap (𝓞 F) F)

/-- The same integral equation after the specified complex base change. -/
def complexEquation (v : InfinitePlace F) : WeierstrassCurve ℂ :=
  W.map (placeMap v)

theorem complexEquation_discriminant (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    (complexEquation W v).Δ = 1 := by
  rw [complexEquation, WeierstrassCurve.map_Δ, hΔ, map_one]

/-- Both the lattice and its comparison are constructed from the actual
complex equation, rather than supplied as an unrelated period family. -/
def placeUniformization (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    Σ L : PeriodPair, {C : WeierstrassCurve.VariableChange ℂ //
      C • complexEquation W v = Weierstrass.latticeCurve L} :=
  Classical.choice (by
    have : (complexEquation W v).IsElliptic :=
      ⟨(complexEquation_discriminant W hΔ v).symm ▸ isUnit_one⟩
    obtain ⟨L, C, hC⟩ := Weierstrass.exists_variableChange_eq_latticeCurve
      (complexEquation W v)
    exact ⟨⟨L, C, hC⟩⟩)

def lattice (hΔ : W.Δ = 1) (v : InfinitePlace F) : PeriodPair :=
  (placeUniformization W hΔ v).1

def coordinateChange (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    WeierstrassCurve.VariableChange ℂ := (placeUniformization W hΔ v).2.1

theorem comparison (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    coordinateChange W hΔ v • complexEquation W v =
      Weierstrass.latticeCurve (lattice W hΔ v) :=
  (placeUniformization W hΔ v).2.property

theorem discriminant_scale (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    ((coordinateChange W hΔ v).u : ℂ) ^ 12 *
      (Weierstrass.latticeCurve (lattice W hΔ v)).Δ = 1 := by
  rw [← comparison W hΔ v, WeierstrassCurve.variableChange_Δ,
    ← mul_assoc, ← mul_pow]
  simp [complexEquation_discriminant W hΔ v]

/-- Each place uses the uniformization of that same integral equation. -/
def placeExponential (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    ℂ →+ (complexEquation W v).toAffine.Point :=
  exponential (lattice W hΔ v) (complexEquation W v)
    (coordinateChange W hΔ v) (comparison W hΔ v)

theorem placeExponential_surjective (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    Function.Surjective (placeExponential W hΔ v) :=
  exponential_surjective _ _ _ _

theorem placeExponential_ker (hΔ : W.Δ = 1) (v : InfinitePlace F) (z : ℂ) :
    placeExponential W hΔ v z = 0 ↔ z ∈ (lattice W hΔ v).lattice :=
  exponential_ker _ _ _ _ z

open SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie

/-- At each place the actual equation coordinates and their u-scaled first
jet are joined to the scalar extension of the same integral Lie vector. -/
theorem placeExponential_exact_tangent (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    let L := lattice W hΔ v
    let C := coordinateChange W hΔ v
    (∀ᶠ z in 𝓝 (0 : ℂ), z = 0 ∨
      ∃ h : (complexEquation W v).toAffine.Nonsingular (affineX L C z) (affineY L C z),
        placeExponential W hΔ v z = .some _ _ h ∧
        originZ L C z = -affineX L C z / affineY L C z ∧
        originW L C z = -1 / affineY L C z) ∧
    (let P : Fin 3 → DualNumber ℂ :=
      ![TrivSqZeroExt.inr (deriv (fun z => originZ L C ((C.u : ℂ) * z)) 0), -1,
        TrivSqZeroExt.inr (deriv (fun z => originW L C ((C.u : ℂ) * z)) 0)]
     ∃ h : IsUnimodularSol
         (W.map ((algebraMap ℂ (DualNumber ℂ)).comp (placeMap v))) P,
       spMap (dualMap (placeMap v)) ≫ (integralVector W).left =
         ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp (placeMap v)) P h) := by
  constructor
  · exact exponential_origin_coordinates _ _ _ (comparison W hΔ v)
  · exact scaled_origin_firstJet_eq_integralVector
      (lattice W hΔ v) (coordinateChange W hΔ v) W (placeMap v)

/-- The square norm of the actual analytic tangent direction u, in the
source pi-normalization of the elliptic lattice metric. -/
def placeProfile (hΔ : W.Δ = 1) (v : InfinitePlace F) : ℝ :=
  Real.pi * ‖((coordinateChange W hΔ v).u : ℂ)‖ ^ 2 /
    ZLattice.covolume (lattice W hΔ v).lattice

theorem placeProfile_pos (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    0 < placeProfile W hΔ v := by
  exact div_pos
    (mul_pos Real.pi_pos (sq_pos_of_ne_zero
      (norm_ne_zero_iff.mpr (coordinateChange W hΔ v).u.ne_zero)))
    (ZLattice.covolume_pos (lattice W hΔ v).lattice _)

/-- The logarithmic comparison is derived from the exact discriminant
scale; it is not a prescribed value of the metric. -/
theorem neg_log_placeProfile (hΔ : W.Δ = 1) (v : InfinitePlace F) :
    -Real.log (placeProfile W hΔ v) =
      PeriodArithmetic.latticeLogPeriod (lattice W hΔ v) := by
  have hc : ZLattice.covolume (lattice W hΔ v).lattice ≠ 0 :=
    (ZLattice.covolume_pos (lattice W hΔ v).lattice _).ne'
  have hu : ‖((coordinateChange W hΔ v).u : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (coordinateChange W hΔ v).u.ne_zero
  have hd : ‖(Weierstrass.latticeCurve (lattice W hΔ v)).Δ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Weierstrass.latticeCurve_Δ_ne_zero _)
  have hlog := congrArg (fun z : ℂ => Real.log ‖z‖) (discriminant_scale W hΔ v)
  simp only [norm_mul, norm_pow, norm_one, Real.log_one,
    Real.log_mul (pow_ne_zero 12 hu) hd, Real.log_pow] at hlog
  rw [placeProfile, PeriodArithmetic.latticeLogPeriod, ← Weierstrass.latticeCurve_Δ,
    Real.log_div (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hu)) hc,
    Real.log_mul Real.pi_ne_zero (pow_ne_zero 2 hu), Real.log_pow,
    Real.log_div hc Real.pi_ne_zero]
  norm_num at hlog ⊢
  linarith

/-- Pullback of the actual place-indexed profile to all complex embeddings. -/
def embeddingProfile (hΔ : W.Δ = 1) (σ : F →+* ℂ) : ℝ :=
  placeProfile W hΔ (InfinitePlace.mk σ)

theorem embeddingProfile_pos (hΔ : W.Δ = 1) (σ : F →+* ℂ) :
    0 < embeddingProfile W hΔ σ := placeProfile_pos W hΔ _

theorem embeddingProfile_conjugate (hΔ : W.Δ = 1) (σ : F →+* ℂ) :
    embeddingProfile W hΔ ((starRingEnd ℂ).comp σ) = embeddingProfile W hΔ σ := by
  change placeProfile W hΔ (InfinitePlace.mk (ComplexEmbedding.conjugate σ)) = _
  rw [InfinitePlace.mk_conjugate_eq]

theorem neg_log_embeddingProfile (hΔ : W.Δ = 1) (σ : F →+* ℂ) :
    -Real.log (embeddingProfile W hΔ σ) =
      PeriodArithmetic.latticeLogPeriod (lattice W hΔ (InfinitePlace.mk σ)) :=
  neg_log_placeProfile W hΔ _

end Profile

end RHLean.Geometry.NativeCM.AllPlaceTangentPeriod

end
