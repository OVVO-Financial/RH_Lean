import RHLean.Geometry.NativeCMWeierstrassSeedComparison
import RHLean.Geometry.NativeCMWeierstrassPointUniformization

/-!
# The native CM seed as actual Weierstrass curve points

The analytic seed quotient is identified with Mathlib's additive group of
points on the same integral Weierstrass equation after complex base change.
The map is given by the actual Weierstrass functions followed by the already
constructed coordinate change; its exact original period kernel is proved.
The original quadratic-order module action is transported through this
equivalence, so this is also an actual coefficient module for Serre tensoring.

This construction concerns algebraic-curve points and their explicit analytic
uniformization. Representing the transported CM point action by a scheme
morphism, the origin line bundle, and the integral tangent comparison remain
separate obligations.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/`
`WeierstrassCurvePointOfLatticeAddOfGeneric.lean`, `latticePointEquiv`, and
`ExistsLineOfAddAddEqZero.lean`, `variableChangePointEquiv`.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ)

theorem period_range_eq_pair :
    (period H τ).range = (periodPair H τ).lattice.toAddSubgroup := by
  rw [periodPair_lattice]
  rfl

/-- The same analytic torus is the actual Weierstrass lattice-curve point group. -/
def torusPointEquiv :
    Torus H τ ≃+ (Weierstrass.latticeCurve (periodPair H τ)).toAffine.Point :=
  (QuotientAddGroup.quotientAddEquivOfEq (period_range_eq_pair H τ)).trans
    (Weierstrass.latticePointEquiv (periodPair H τ))

@[simp] theorem torusPointEquiv_mk (z : ℂ) :
    torusPointEquiv H τ (QuotientAddGroup.mk' (period H τ).range z) =
      Weierstrass.latticePoint (periodPair H τ) z := rfl

variable (W : WeierstrassCurve ℂ) (C : WeierstrassCurve.VariableChange ℂ)
    (hC : C • W = Weierstrass.latticeCurve (periodPair H τ))

/-- Apply the actual coordinate change to the lattice-curve point group. -/
def equationPointEquiv : Torus H τ ≃+ W.toAffine.Point :=
  (torusPointEquiv H τ).trans (Weierstrass.variableChangePointEquiv C hC)

/-- The order module structure on the actual curve points, transported from
the proved CM action on the exact same quotient. -/
@[instance_reducible]
def equationModule : Module (OK H) W.toAffine.Point :=
  let e := equationPointEquiv H τ W C hC
  { smul a P := e (a • e.symm P)
    one_smul P := by
      change e ((1 : OK H) • e.symm P) = P
      rw [one_smul, AddEquiv.apply_symm_apply]
    mul_smul a b P := by
      change e ((a * b) • e.symm P) = e (a • e.symm (e (b • e.symm P)))
      rw [AddEquiv.symm_apply_apply, mul_smul]
    smul_zero a := by
      change e (a • e.symm 0) = 0
      rw [map_zero, smul_zero, map_zero]
    smul_add a P Q := by
      change e (a • e.symm (P + Q)) = e (a • e.symm P) + e (a • e.symm Q)
      rw [map_add, smul_add, map_add]
    add_smul a b P := by
      change e ((a + b) • e.symm P) = e (a • e.symm P) + e (b • e.symm P)
      rw [add_smul, map_add]
    zero_smul P := by
      change e ((0 : OK H) • e.symm P) = 0
      have hzero : (0 : OK H) • e.symm P = 0 :=
        DFunLike.congr_fun (cmAction_zero H τ) (e.symm P)
      exact (congrArg e hzero).trans e.map_zero }

/-- The equivalence is linear for this actual transported order action. -/
def equationPointLinearEquiv :
    let _ : Module (OK H) W.toAffine.Point := equationModule H τ W C hC
    Torus H τ ≃ₗ[OK H] W.toAffine.Point := by
  let _ : Module (OK H) W.toAffine.Point := equationModule H τ W C hC
  refine { equationPointEquiv H τ W C hC with map_smul' := ?_ }
  intro a x
  change equationPointEquiv H τ W C hC (a • x) =
    equationPointEquiv H τ W C hC
      (a • (equationPointEquiv H τ W C hC).symm (equationPointEquiv H τ W C hC x))
  rw [AddEquiv.symm_apply_apply]

/-- The actual Weierstrass-function point uniformization. -/
def equationExponential : ℂ →+ W.toAffine.Point :=
  (equationPointEquiv H τ W C hC).toAddMonoidHom.comp
    (QuotientAddGroup.mk' (period H τ).range)

@[simp] theorem equationExponential_apply (z : ℂ) :
    equationExponential H τ W C hC z =
      Weierstrass.variableChangePoint C hC (Weierstrass.latticePoint (periodPair H τ) z) := rfl

theorem equationExponential_surjective :
    Function.Surjective (equationExponential H τ W C hC) :=
  (equationPointEquiv H τ W C hC).surjective.comp
    (QuotientAddGroup.mk'_surjective (period H τ).range)

theorem equationExponential_ker (z : ℂ) :
    equationExponential H τ W C hC z = 0 ↔ z ∈ lattice H τ := by
  let e := equationPointEquiv H τ W C hC
  change e (QuotientAddGroup.mk' (period H τ).range z) = 0 ↔ z ∈ lattice H τ
  have hz : e (QuotientAddGroup.mk' (period H τ).range z) = 0 ↔
      QuotientAddGroup.mk' (period H τ).range z = 0 :=
    ⟨fun h => e.injective (h.trans e.map_zero.symm), fun h => h ▸ e.map_zero⟩
  rw [hz]
  change (z : ℂ ⧸ (period H τ).range) = 0 ↔ z ∈ (period H τ).range
  exact QuotientAddGroup.eq_zero_iff (N := (period H τ).range) z

theorem equationExponential_coordinates {z : ℂ} (hz : z ∉ lattice H τ) :
    ∃ h : W.toAffine.Nonsingular
        ((C.u : ℂ) ^ 2 * (periodPair H τ).weierstrassP z + C.r)
        ((C.u : ℂ) ^ 3 * ((periodPair H τ).derivWeierstrassP z / 2) +
          (C.u : ℂ) ^ 2 * C.s * (periodPair H τ).weierstrassP z + C.t),
      equationExponential H τ W C hC z =
        .some _ _ h := by
  have hz' : z ∉ (periodPair H τ).lattice := by
    simpa only [periodPair_lattice] using hz
  refine ⟨(Weierstrass.nonsingular_variableChange_iff W C
    ((periodPair H τ).weierstrassP z)
    ((periodPair H τ).derivWeierstrassP z / 2)).mpr
      (hC ▸ Weierstrass.latticeCurve_nonsingular (periodPair H τ) hz'), ?_⟩
  rw [equationExponential_apply, Weierstrass.latticePoint_of_notMem _ hz',
    Weierstrass.variableChangePoint_some]

/-- Literal CM point action, expressed as an additive endomorphism. -/
def equationCMAction (a : OK H) : W.toAffine.Point →+ W.toAffine.Point :=
  let e := equationPointEquiv H τ W C hC
  { toFun P := e (a • e.symm P)
    map_zero' := by simp
    map_add' P Q := by simp [smul_add] }

theorem equationCMAction_exponential (a : OK H) (z : ℂ) :
    equationCMAction H τ W C hC a (equationExponential H τ W C hC z) =
      equationExponential H τ W C hC (embed H τ a * z) := by
  change equationPointEquiv H τ W C hC
    (a • (equationPointEquiv H τ W C hC).symm
      (equationPointEquiv H τ W C hC (QuotientAddGroup.mk' (period H τ).range z))) =
    equationPointEquiv H τ W C hC
      (QuotientAddGroup.mk' (period H τ).range (embed H τ a * z))
  rw [AddEquiv.symm_apply_apply, torus_smul_mk]

theorem equationCMAction_quadratic (P : W.toAffine.Point) :
    equationCMAction H τ W C hC (wK H)
        (equationCMAction H τ W C hC (wK H) P) +
      equationCMAction H τ W C hC (((1 + H.d) / 4 : ℕ) : OK H) P =
      equationCMAction H τ W C hC (wK H) P := by
  let e := equationPointEquiv H τ W C hC
  change e (wK H • e.symm (e (wK H • e.symm P))) +
    e ((((1 + H.d) / 4 : ℕ) : OK H) • e.symm P) = e (wK H • e.symm P)
  rw [AddEquiv.symm_apply_apply, ← map_add]
  exact congrArg e (torus_cm_equation H τ (e.symm P))

end RHLean.Geometry.NativeCM.EllipticSeed

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed

/-- A genuine integral equation, its exact complex point uniformization,
and the actual CM action on its points are constructed from the native seed.
The discriminant scale is retained alongside the exact original period kernel. -/
theorem exists_integral_point_uniformization
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
      (W : WeierstrassCurve (𝓞 M)) (w : 𝓞 M)
      (C : WeierstrassCurve.VariableChange ℂ),
      let φ : 𝓞 M →+* ℂ :=
        (M.val : M →+* ℂ).comp (algebraMap (𝓞 M) M)
      (∀ a : E, τ a ∈ M) ∧ ((w : M) : ℂ) = omega H τ ∧ W.Δ = 1 ∧
      (C.u : ℂ) ^ 12 * (latticeCurve (periodPair H τ)).Δ = 1 ∧
      ∃ hC : C • W.map φ = latticeCurve (periodPair H τ),
        Function.Surjective (equationExponential H τ (W.map φ) C hC) ∧
        (∀ z, equationExponential H τ (W.map φ) C hC z = 0 ↔ z ∈ lattice H τ) ∧
        (∀ a z, equationCMAction H τ (W.map φ) C hC a
            (equationExponential H τ (W.map φ) C hC z) =
          equationExponential H τ (W.map φ) C hC (embed H τ a * z)) ∧
        (let _ : Module (OK H) (W.map φ).toAffine.Point :=
          equationModule H τ (W.map φ) C hC
         Nonempty (Torus H τ ≃ₗ[OK H] (W.map φ).toAffine.Point)) := by
  obtain ⟨M, hM, W, w, C, hΔ, hhost, hw, -, hC, -, -, h12, -, -⟩ :=
    exists_integral_equation_with_exact_period_invariants H τ
  let _ : NumberField M := hM
  exact ⟨M, hM, W, w, C, hhost, hw, hΔ, h12, hC,
    equationExponential_surjective H τ _ C hC,
    equationExponential_ker H τ _ C hC,
    equationCMAction_exponential H τ _ C hC,
    ⟨equationPointLinearEquiv H τ _ C hC⟩⟩

end RHLean.Geometry.NativeCM.Weierstrass

end
