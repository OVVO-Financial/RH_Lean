import RHLean.Geometry.NativeCMSerreSigmaMetric
import RHLean.Geometry.NativeCMSerreSchemeLie
import RHLean.Geometry.NativeCMWeierstrassCMOrderTangent

/-!
# The constructed generic CM action, intrinsic Lie module and sigma Gram

The actual finite-field CM action supplies its integral order embedding and
its proved action on the specified epsilon vector. Those conclusions give
the intrinsic Lie module of the same trace-frame equalizer. Its projection
derivatives are the original Hermitian dual coordinates. In the original
period parameter their complex directions acquire the actual factor u;
the sigma product metric therefore has the exact factor pi*|u|²/covol.

This is native glue between the represented projective tensor, the actual
CM scheme action and the regular-section derivative comparison. The module
is the original D.La throughout; the final coefficient specialization uses
the literal B^-1. No action over the ring of integers is assumed, and no
generic Lie module is declared to be an integral arithmetic Lie lattice.
The remaining extension, cubical/Rosati and principal-polarization steps
are separate geometric obligations.

The underlying source constructions are Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`TensorLieBasisExists.lean` and `TwoMulDegreeEigenLatticeTensorRankOne.lean`,
already reconstructed in the imported native modules. No new source
closure or external compiled object is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical TensorProduct BigOperators ComplexConjugate Real

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.TraceFrame

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie
open SerreScheme Weierstrass

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {G : NativeGeometricHost E} {D : TraceLattice G} {ε : ℤˣ}
    (P : TraceFrame D ε)
    {F : Type} [Field F] [Algebra (OK G) F]

/-- The actual integral dual-frame coordinate, extended only to the
generic field. This does not replace the original projective module. -/
def fieldCoefficient (i : Fin P.n) : F ⊗[OK G] D.La →ₗ[F] F :=
  LinearMap.liftBaseChange F ((Algebra.linearMap (OK G) F).comp (P.coefficient i))

theorem fieldCoefficient_tmul (i : Fin P.n) (c : F) (m : D.La) :
    P.fieldCoefficient i (c ⊗ₜ[OK G] m) =
      c * algebraMap (OK G) F (kLin D ε m (P.y i)) := rfl

variable (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (a : OAct (OK G) (schemeOver V))
    (ha : ∀ c, IsLieComb ![algebraMap (OK G) F c] ![integralVector V]
      (integralVector V ≫ a.act c))

/-- The target uses its intrinsic dual-number Lie operations. -/
def genericLieEquiv : F ⊗[OK G] D.La ≃ₗ[F] Lie (P.schemeObj a) :=
  (LieTensor.exists_lie_equiv F (schemeOver V) (OK G) D.La
    (P.schemeObj a) a (P.schemeAct a) (P.schemeIsTensor a)
    (integralVector V) (integralVector_isLieBasis V) ha).choose

theorem genericLieEquiv_one (m : D.La) :
    Lie.hom (P.genericLieEquiv V a ha (1 ⊗ₜ[OK G] m)) =
      integralVector V ≫ (P.schemeIsTensor a).tmul m :=
  (LieTensor.exists_lie_equiv F (schemeOver V) (OK G) D.La
    (P.schemeObj a) a (P.schemeAct a) (P.schemeIsTensor a)
    (integralVector V) (integralVector_isLieBasis V) ha).choose_spec.1 m

/-- Every coefficient endomorphism acts on the original module factor. -/
theorem genericLieEquiv_coefficient (c : 𝓞 E) (t : F ⊗[OK G] D.La) :
    Lie.hom (P.genericLieEquiv V a ha ((moduleScalar D c).baseChange F t)) =
      Lie.hom (P.genericLieEquiv V a ha t) ≫ (P.schemeCoefficientAct a).act c :=
  (LieTensor.exists_lie_equiv F (schemeOver V) (OK G) D.La
    (P.schemeObj a) a (P.schemeAct a) (P.schemeIsTensor a)
    (integralVector V) (integralVector_isLieBasis V) ha).choose_spec.2
      (moduleScalar D c) t

/-- Actual differentials of the actual represented projection morphisms. -/
theorem genericLieEquiv_projection (i : Fin P.n) (t : F ⊗[OK G] D.La) :
    Lie.hom (P.genericLieEquiv V a ha t) ≫ P.schemeCoordinate a i =
      epsScale (P.fieldCoefficient i t) ≫ integralVector V := by
  have hd (c : OK G) : integralVector V ≫ a.act c =
      epsScale (algebraMap (OK G) F c) ≫ integralVector V :=
    (LieTensor.isLieComb_one_iff _ _ _).mp (ha c)
  induction t using TensorProduct.inductionOn with
  | tmul c m =>
    have ht : c ⊗ₜ[OK G] m = c • (1 ⊗ₜ[OK G] m) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [fieldCoefficient_tmul, ht, map_smul, Lie.hom_smul, genericLieEquiv_one]
    change (epsScale c ≫ integralVector V ≫ (P.schemeIsTensor a).tmul m) ≫
      P.schemeCoordinate a i = _
    rw [Category.assoc, Category.assoc, tmul_schemeCoordinate, hd, epsScale_mul_assoc]
  | add t u ht hu =>
    rw [map_add, Lie.hom_add, MonObj.mul_comp, ht, hu, map_add]
    exact (epsScale_add_comp _ _ (integralVector_isTangent V)).symm

section ComplexDirections

variable [Algebra F ℂ] [Algebra (OK G) ℂ]
    (τ : E →+* ℂ) (hemb : algebraMap (OK G) ℂ = embed G τ)
    (hκ : ∀ c : OK G, algebraMap F ℂ (algebraMap (OK G) F c) = embed G τ c)

/-- The scalar map is linear for the actual, proved derivative embedding. -/
def genericComplexScalar : F →ₗ[OK G] ℂ where
  toFun := algebraMap F ℂ
  map_add' := map_add _
  map_smul' c r := by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hκ, hemb]

variable (C : _root_.WeierstrassCurve.VariableChange ℂ)

/-- In the original period parameter, the normalized epsilon vector has
direction u. Scalar extension is on the field factor only. -/
def genericLieDirection (t : F ⊗[OK G] D.La) : ℂ ⊗[OK G] D.La :=
  (C.u : ℂ) • (genericComplexScalar τ hemb hκ).rTensor D.La t

theorem genericLieDirection_tmul (r : F) (m : D.La) :
    genericLieDirection (D := D) τ hemb hκ C (r ⊗ₜ[OK G] m) =
      ((C.u : ℂ) * algebraMap F ℂ r) ⊗ₜ[OK G] m := by
  rw [genericLieDirection, LinearMap.rTensor_tmul, TensorProduct.smul_tmul']
  rfl

/-- Projection directions agree with the actual Lie coordinates, including
the inverse scale in the actual normalized equation exponential. -/
theorem genericLieDirection_coordinate (i : Fin P.n) (t : F ⊗[OK G] D.La) :
    P.complexCoefficient i (genericLieDirection (D := D) τ hemb hκ C t) =
      (C.u : ℂ) * algebraMap F ℂ (P.fieldCoefficient i t) := by
  induction t using TensorProduct.inductionOn with
  | tmul r m =>
    rw [genericLieDirection_tmul, complexCoefficient_tmul P τ hemb,
      fieldCoefficient_tmul, map_mul, hκ]
    ring
  | add t u ht hu =>
    simp only [genericLieDirection, map_add, smul_add] at ht hu ⊢
    rw [ht, hu, mul_add]

theorem genericLieDirection_scaled_coordinate (i : Fin P.n) (t : F ⊗[OK G] D.La) :
    (C.u : ℂ)⁻¹ * P.complexCoefficient i (genericLieDirection (D := D) τ hemb hκ C t) =
      algebraMap F ℂ (P.fieldCoefficient i t) := by
  rw [genericLieDirection_coordinate, inv_mul_cancel_left₀ C.u.ne_zero]

/-- The projected analytic curve is the actual normalized equation point
with parameter z times its algebraic Lie coordinate. Both factors u and
u^-1 are retained until this equality is proved. -/
theorem genericLieDirection_exponential_coordinate
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
    (hact : ∀ b : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
          a.act b =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ b * z))))
    (i : Fin P.n) (t : F ⊗[OK G] D.La) (z : ℂ) :
    Pts.hom (P.genericExponential τ V C hVC a hact hemb
        (z • genericLieDirection (D := D) τ hemb hκ C t)) ≫ P.schemeCoordinate a i =
      ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C)
        (z * algebraMap F ℂ (P.fieldCoefficient i t)))) := by
  rw [genericExponential_coordinate, map_smul, genericLieDirection_coordinate,
    genericSeedExponential_apply]
  congr 3
  change (C.u : ℂ)⁻¹ * (z * ((C.u : ℂ) * _)) = _
  rw [mul_left_comm z, ← mul_assoc, inv_mul_cancel₀ C.u.ne_zero, _root_.one_mul]

/-- This is the Gaussian form of the actual signed sigma metric evaluated
in the directions determined by the actual projection derivatives. -/
theorem sigmaGram_genericLieDirection (t s : F ⊗[OK G] D.La) :
    (Real.pi : ℂ) * P.sigmaGram τ C
        (genericLieDirection (D := D) τ hemb hκ C t) (genericLieDirection (D := D) τ hemb hκ C s) =
      (Real.pi * ‖(C.u : ℂ)‖ ^ 2 / ZLattice.covolume (periodPair G τ).lattice : ℝ) *
        ∑ k : Fin P.n × Fin P.n,
          embed G τ (kLin D ε (P.x k.1) (P.x k.2)) *
            algebraMap F ℂ (P.fieldCoefficient k.1 t) *
              conj (algebraMap F ℂ (P.fieldCoefficient k.2 s)) := by
  have hu : (C.u : ℂ) * conj (C.u : ℂ) = (‖(C.u : ℂ)‖ ^ 2 : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hterm (k : Fin P.n × Fin P.n) :
      embed G τ (kLin D ε (P.x k.1) (P.x k.2)) *
          ((C.u : ℂ) * algebraMap F ℂ (P.fieldCoefficient k.1 t)) *
            conj ((C.u : ℂ) * algebraMap F ℂ (P.fieldCoefficient k.2 s)) =
        (‖(C.u : ℂ)‖ ^ 2 : ℝ) *
          (embed G τ (kLin D ε (P.x k.1) (P.x k.2)) *
            algebraMap F ℂ (P.fieldCoefficient k.1 t) *
              conj (algebraMap F ℂ (P.fieldCoefficient k.2 s))) := by
    rw [map_mul, ← hu]
    ring
  rw [sigmaGram_eq]
  simp_rw [genericLieDirection_coordinate, hterm]
  rw [← Finset.mul_sum]
  simp only [PeriodMean.latticeArea, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow]
  ring

end ComplexDirections

end RHLean.Geometry.NativeCM.TraceFrame

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM EllipticSeed SerreScheme SchemeTheory
open SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie Weierstrass

/-- The genuine seed constructor supplies the derivative compatibility;
the same literal B^-1 then gives its intrinsic generic Lie module and the
exact signed sigma Gram. No integral-model extension is a premise. -/
theorem coefficient_exists_genericSerreLieMetric
    {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (τ : H.E →+* ℂ) (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : _root_.WeierstrassCurve (𝓞 M)) [W.IsElliptic] (w : 𝓞 M)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ))
    (hw : ((w : M) : ℂ) = omega G τ) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (V : _root_.WeierstrassCurve F) (_ : V.IsElliptic)
      (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
      (a : OAct (OK G) (schemeOver V)) (κ : OK G →+* 𝓞 F),
      let _ : Algebra (OK G) F := ((algebraMap (𝓞 F) F).comp κ).toAlgebra
      let _ : Algebra (OK G) ℂ := (embed G τ).toAlgebra
      let P := coefficientSerreFrame H G hbar B hB 1
      V = shortModel ((W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom) ∧
      ∃ hpoint : ∀ b z, ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) z)) ≫ a.act b =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ b * z))),
      ∃ hκ : ∀ c : OK G, algebraMap F ℂ (algebraMap (OK G) F c) = embed G τ c,
        ∃ e : F ⊗[OK G] (coefficientIdeal H B : Submodule (𝓞 H.E) H.E) ≃ₗ[F]
            Lie (coefficientSerreScheme H G hbar B hB 1 a),
          (∀ m, Lie.hom (e (1 ⊗ₜ[OK G] m)) =
            integralVector V ≫ (P.schemeIsTensor a).tmul m) ∧
          (∀ c t, Lie.hom (e ((TraceFrame.moduleScalar
              (coefficientTraceLattice H G hbar B hB) c).baseChange F t)) =
            Lie.hom (e t) ≫ (P.schemeCoefficientAct a).act c) ∧
          (∀ i t, Lie.hom (e t) ≫ P.schemeCoordinate a i =
            epsScale (P.fieldCoefficient i t) ≫ integralVector V) ∧
          (∀ i t z, Pts.hom (P.genericExponential τ V C hVC a hpoint rfl
              (z • TraceFrame.genericLieDirection
                (D := coefficientTraceLattice H G hbar B hB) τ rfl hκ C t)) ≫
                P.schemeCoordinate a i =
            ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C)
              (z * algebraMap F ℂ (P.fieldCoefficient i t))))) ∧
          ∀ t s, (Real.pi : ℂ) * P.sigmaGram τ C
              (TraceFrame.genericLieDirection
                (D := coefficientTraceLattice H G hbar B hB) τ rfl hκ C t)
              (TraceFrame.genericLieDirection
                (D := coefficientTraceLattice H G hbar B hB) τ rfl hκ C s) =
            (Real.pi * ‖(C.u : ℂ)‖ ^ 2 / ZLattice.covolume (periodPair G τ).lattice : ℝ) *
              ∑ k : Fin P.n × Fin P.n,
                embed G τ (kLin (coefficientTraceLattice H G hbar B hB) 1
                  (P.x k.1) (P.x k.2)) *
                  algebraMap F ℂ (P.fieldCoefficient k.1 t) *
                    conj (algebraMap F ℂ (P.fieldCoefficient k.2 s)) := by
  obtain ⟨F, hF, hMF, V, hV, hVC, a, κ, hnorm, hpoint, hκ, -, hlie⟩ :=
    exists_cm_scheme_order_action_with_tangent G τ C M W w hC hw
  let _ : NumberField F := hF
  let _ : V.IsElliptic := hV
  let _ : Algebra (OK G) F := ((algebraMap (𝓞 F) F).comp κ).toAlgebra
  let _ : Algebra (OK G) ℂ := (embed G τ).toAlgebra
  let P := coefficientSerreFrame H G hbar B hB 1
  refine ⟨F, hF, hMF, V, hV, hVC, a, κ, hnorm, hpoint, hκ,
    P.genericLieEquiv V a hlie, ?_, ?_, ?_, ?_, ?_⟩
  · exact P.genericLieEquiv_one V a hlie
  · exact P.genericLieEquiv_coefficient V a hlie
  · exact P.genericLieEquiv_projection V a hlie
  · exact P.genericLieDirection_exponential_coordinate V a τ rfl hκ C hVC hpoint
  · exact P.sigmaGram_genericLieDirection τ rfl hκ C

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
