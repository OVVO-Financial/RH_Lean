import RHLean.Geometry.NativeCMSerreMixedPeriods
import RHLean.Geometry.NativeCMWeierstrassSeedPoints

/-!
# The same projective Serre module on actual integral-equation points

The proved elliptic point uniformization is tensored with the unchanged
native projective module. Its existing trace-Hermitian retraction is kept,
and the mixed exponential is carried to the two actual Weierstrass point
groups. The original period kernel and full O_E action survive exactly.
Both coordinate changes and their nontrivial discriminant scales remain
in the native joint-existence statement.

This is a construction on actual elliptic curve point groups. It does not
assert that the transported CM point action has been represented by a
scheme morphism, or identify an arithmetic Lie lattice or tangent metric.

Source interfaces: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/`
`PowObjGeometricallyConnected.lean`, `IsTensor.ofRetract` and
`IsTensor.ofIso`; and the explicit Weierstrass point equivalences already
reconstructed in `NativeCMWeierstrassSeedPoints`.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical TensorProduct Pointwise

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (W : WeierstrassCurve ℂ) (C : WeierstrassCurve.VariableChange ℂ)
    (hC : C • W = Weierstrass.latticeCurve (periodPair G τ))
    (M : Type) [AddCommGroup M] [Module (𝓞 E) M]

/-- The original coefficient module is tensored with the actual curve
point equivalence, including its constructed coordinate change. -/
def equationTensorEquiv :
    let _ : Module (OK G) W.toAffine.Point := equationModule G τ W C hC
    M ⊗[OK G] Torus G τ ≃ₗ[OK G] M ⊗[OK G] W.toAffine.Point := by
  let _ : Module (OK G) W.toAffine.Point := equationModule G τ W C hC
  exact (equationPointLinearEquiv G τ W C hC).lTensor M

theorem equationTensorEquiv_tmul (x : M) (z : ℂ) :
    let _ : Module (OK G) W.toAffine.Point := equationModule G τ W C hC
    equationTensorEquiv G τ W C hC M
        (x ⊗ₜ[OK G] QuotientAddGroup.mk' (period G τ).range z) =
      x ⊗ₜ[OK G] equationExponential G τ W C hC z := by
  let _ : Module (OK G) W.toAffine.Point := equationModule G τ W C hC
  change (equationPointLinearEquiv G τ W C hC).lTensor M
    (x ⊗ₜ[OK G] QuotientAddGroup.mk' (period G τ).range z) = _
  rw [LinearEquiv.lTensor_tmul]
  rfl

theorem equationTensorEquiv_smul (a : 𝓞 E) (t : M ⊗[OK G] Torus G τ) :
    let _ : Module (OK G) W.toAffine.Point := equationModule G τ W C hC
    equationTensorEquiv G τ W C hC M (a • t) =
      a • equationTensorEquiv G τ W C hC M t := by
  let _ : Module (OK G) W.toAffine.Point := equationModule G τ W C hC
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [smul_add, map_add, ht, hu]
  | tmul x z =>
    -- Same explicit scalar transport as `conjugateTensor_smul`: move the
    -- scalar onto the coefficient factor, apply the actual point
    -- equivalence to the torus factor, and move the scalar back.
    calc
      _ = equationTensorEquiv G τ W C hC M ((a • x) ⊗ₜ[OK G] z) := rfl
      _ = (a • x) ⊗ₜ[OK G] equationPointLinearEquiv G τ W C hC z := by rfl
      _ = _ := TensorProduct.smul_tmul' a x _

/-- The same trace-Hermitian frame presents the actual equation-point
tensor as the fixed module of its original integral idempotent. -/
def equationTensorFixedEquiv {D : TraceLattice G} {ε : ℤˣ} (F : TraceFrame D ε) :
    let _ : Module (OK G) W.toAffine.Point := equationModule G τ W C hC
    D.La ⊗[OK G] W.toAffine.Point ≃ₗ[OK G] F.tensorFixed W.toAffine.Point := by
  let _ : Module (OK G) W.toAffine.Point := equationModule G τ W C hC
  exact F.tensorEquivFixed W.toAffine.Point

end RHLean.Geometry.NativeCM.EllipticSeed

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]

/-- The literal B^-1 and its original trace-Hermitian frame are presented
on the actual equation point module, with no free replacement of B^-1. -/
def coefficientEquationFixedEquiv (G : NativeGeometricHost H.E)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (ε : ℤˣ) (τ : H.E →+* ℂ) (W : WeierstrassCurve ℂ)
    (C : WeierstrassCurve.VariableChange ℂ)
    (hC : C • W = Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)) :
    let _ : Module (OK G) W.toAffine.Point := EllipticSeed.equationModule G τ W C hC
    coefficientIdeal H B ⊗[OK G] W.toAffine.Point ≃ₗ[OK G]
      (coefficientSerreFrame H G hbar B hB ε).tensorFixed W.toAffine.Point :=
  EllipticSeed.equationTensorFixedEquiv G τ W C hC
    (coefficientSerreFrame H G hbar B hB ε)

variable (G : NativeGeometricHost H.E) (B : Ideal (𝓞 H.E)) (p q : ℕ)
    (τ₀ : cmTypeFinset H)
    (WP WQ : WeierstrassCurve ℂ)
    (CP CQ : WeierstrassCurve.VariableChange ℂ)
    (hP : CP • WP = Weierstrass.latticeCurve (EllipticSeed.periodPair G (τ₀ : H.E →+* ℂ)))
    (hQ : CQ • WQ = Weierstrass.latticeCurve
      (EllipticSeed.periodPair G (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ))))

/-- Both actual equations are retained, one for each elliptic orientation. -/
abbrev mixedEquationPoints :=
  let _ : Module (OK G) WP.toAffine.Point :=
    EllipticSeed.equationModule G (τ₀ : H.E →+* ℂ) WP CP hP
  let _ : Module (OK G) WQ.toAffine.Point :=
    EllipticSeed.equationModule G (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ)) WQ CQ hQ
  (twistedLattice H B p ⊗[OK G] WP.toAffine.Point) ×
    (twistedLattice H B q ⊗[OK G] WQ.toAffine.Point)

def mixedEquationEquiv :
    mixedSerrePoints H G B p q τ₀ ≃ₗ[OK G]
      mixedEquationPoints H G B p q τ₀ WP WQ CP CQ hP hQ := by
  let _ : Module (OK G) WP.toAffine.Point :=
    EllipticSeed.equationModule G (τ₀ : H.E →+* ℂ) WP CP hP
  let _ : Module (OK G) WQ.toAffine.Point :=
    EllipticSeed.equationModule G (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ)) WQ CQ hQ
  exact LinearEquiv.prodCongr
    (EllipticSeed.equationTensorEquiv G (τ₀ : H.E →+* ℂ) WP CP hP (twistedLattice H B p))
    (EllipticSeed.equationTensorEquiv G (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ))
      WQ CQ hQ (twistedLattice H B q))

theorem mixedEquationEquiv_smul (a : 𝓞 H.E) (t : mixedSerrePoints H G B p q τ₀) :
    mixedEquationEquiv H G B p q τ₀ WP WQ CP CQ hP hQ (a • t) =
      a • mixedEquationEquiv H G B p q τ₀ WP WQ CP CQ hP hQ t := by
  apply Prod.ext
  · exact EllipticSeed.equationTensorEquiv_smul G (τ₀ : H.E →+* ℂ)
      WP CP hP (twistedLattice H B p) a t.1
  · exact EllipticSeed.equationTensorEquiv_smul G
      (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ))
      WQ CQ hQ (twistedLattice H B q) a t.2

/-- An exact mixed period exponential is transported to the actual
equation points without altering either kernel or coefficient action. -/
theorem exists_prescribedEquationExponential
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    [Algebra (OK G) ℂ]
    (hcompat : ∀ τ : cmTypeFinset H,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    ∃ ex : (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ) →+
        mixedEquationPoints H G B (k + j - 1) (m - j) τ₀ WP WQ CP CQ hP hQ,
      Function.Surjective ex ∧
      (∀ v, ex v = 0 ↔ v ∈ (prescribedPeriodMap H B hB k m j).range) ∧
      ∀ (a : 𝓞 H.E) v, ex (fun s => prescribedPeriodType H k m j s (a : H.E) * v s) =
        a • ex v := by
  obtain ⟨ex, hs, hkern, hact⟩ :=
    exists_prescribedMixedSerreExponential H G hcompat B hB k m j hk hj τ₀
  let f := mixedEquationEquiv H G B (k + j - 1) (m - j) τ₀ WP WQ CP CQ hP hQ
  refine ⟨f.toAddEquiv.toAddMonoidHom.comp ex, f.surjective.comp hs, ?_, ?_⟩
  · intro v
    change f (ex v) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff, hkern]
  · intro a v
    change f (ex (fun s => prescribedPeriodType H k m j s (a : H.E) * v s)) = _
    rw [hact]
    exact mixedEquationEquiv_smul H G B (k + j - 1) (m - j) τ₀ WP WQ CP CQ hP hQ a (ex v)

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM
open NativeRawHostPolarization

/-- One actual half-different and two actual integral seed equations are
chosen before all ranks and signatures. Their original coordinate scales
are retained, while the existing mixed period kernel and full coefficient
action are realized on the literal projective tensors of their point groups. -/
theorem nativeDyadicHost_exists_serreEquationPoints
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ τ₀ : cmTypeFinset H.toHostRaw,
        ∃ (FP : IntermediateField ℚ ℂ) (_ : NumberField FP)
          (WP : WeierstrassCurve (𝓞 FP)) (wP : 𝓞 FP) (CP : WeierstrassCurve.VariableChange ℂ)
          (FQ : IntermediateField ℚ ℂ) (_ : NumberField FQ)
          (WQ : WeierstrassCurve (𝓞 FQ)) (wQ : 𝓞 FQ) (CQ : WeierstrassCurve.VariableChange ℂ),
          let φP : 𝓞 FP →+* ℂ := (FP.val : FP →+* ℂ).comp (algebraMap (𝓞 FP) FP)
          let φQ : 𝓞 FQ →+* ℂ := (FQ.val : FQ →+* ℂ).comp (algebraMap (𝓞 FQ) FQ)
          (∀ a : H.E, (τ₀ : H.E →+* ℂ) a ∈ FP) ∧
          (∀ a : H.E, ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ) a ∈ FQ) ∧
          ((wP : FP) : ℂ) = EllipticSeed.omega G (τ₀ : H.E →+* ℂ) ∧
          ((wQ : FQ) : ℂ) = EllipticSeed.omega G
            (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ)) ∧
          WP.Δ = 1 ∧ WQ.Δ = 1 ∧
          (CP.u : ℂ) ^ 12 * (Weierstrass.latticeCurve
            (EllipticSeed.periodPair G (τ₀ : H.E →+* ℂ))).Δ = 1 ∧
          (CQ.u : ℂ) ^ 12 * (Weierstrass.latticeCurve
            (EllipticSeed.periodPair G (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ)))).Δ = 1 ∧
          ∃ (hP : CP • WP.map φP = Weierstrass.latticeCurve
              (EllipticSeed.periodPair G (τ₀ : H.E →+* ℂ)))
            (hQ : CQ • WQ.map φQ = Weierstrass.latticeCurve
              (EllipticSeed.periodPair G (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ)))),
            ∀ (k m j : ℕ), m + 3 ≤ k → j ≤ m →
              ∃ ex : (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1)) → ℂ) →+
                  mixedEquationPoints H.toHostRaw G B (k + j - 1) (m - j) τ₀
                    (WP.map φP) (WQ.map φQ) CP CQ hP hQ,
                Function.Surjective ex ∧
                (∀ v, ex v = 0 ↔ v ∈ (prescribedPeriodMap H.toHostRaw B hB k m j).range) ∧
                ∀ (a : 𝓞 H.E) v,
                  ex (fun s => prescribedPeriodType H.toHostRaw k m j s (a : H.E) * v s) =
                    a • ex v := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro τ₀
  obtain ⟨FP, hFP, WP, wP, CP, hEP, hwP, hΔP, huP, hP, -⟩ :=
    Weierstrass.exists_integral_point_uniformization G (τ₀ : H.E →+* ℂ)
  let _ : NumberField FP := hFP
  obtain ⟨FQ, hFQ, WQ, wQ, CQ, hEQ, hwQ, hΔQ, huQ, hQ, -⟩ :=
    Weierstrass.exists_integral_point_uniformization G
      (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ))
  let _ : NumberField FQ := hFQ
  refine ⟨FP, hFP, WP, wP, CP, FQ, hFQ, WQ, wQ, CQ,
    hEP, hEQ, hwP, hwQ, hΔP, hΔQ, huP, huQ, hP, hQ, ?_⟩
  intro k m j hk hj
  let _ : Algebra (OK G) ℂ := (embed G (τ₀ : H.E →+* ℂ)).toAlgebra
  have hcompat : ∀ τ : cmTypeFinset H.toHostRaw,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ := by
    intro τ
    exact nativeDyadic_quadraticEmbeddings_eq e q d he hH τ τ₀
  exact exists_prescribedEquationExponential H.toHostRaw G B τ₀
    _ _ CP CQ hP hQ hB hcompat k m j hk hj

end RHLean.Analysis.AlpogeThin

end
