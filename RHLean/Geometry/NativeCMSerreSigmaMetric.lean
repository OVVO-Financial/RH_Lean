import RHLean.Geometry.NativeCMSerreGenericCoordinates
import RHLean.Geometry.NativeCMLineBundleSigmaMetric
import RHLean.Geometry.NativeCMSerreBundleGram

/-!
# The actual sigma product metric of the trace-frame Serre bundle

The four signed factors are the original scheme morphisms. Their complex
coordinates are proved from the actual point tensor, and their metrics
are the literal signed products of the original seed chart metrics. The
result respects the actual algebraic transition functions and original
integral tensor periods. Its Gaussian term is then calculated as the
trace-Hermitian Gram on that same projective module.

The rescaled generic equation has period lattice u⁻¹Λ and point parameter
u⁻¹z. Their homothety factors cancel in the form on the original period
space. This does not set the original integral tangent scale u to one,
nor does it extend the quadratic-order scheme action over the integers.
All proofs are native joins of the attributed constructions above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical TensorProduct BigOperators ComplexConjugate Real

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve WeierstrassTheta

theorem exponential_one_eq (W : _root_.WeierstrassCurve ℂ) (L : PeriodPair)
    (h : W = latticeCurve L) (z : ℂ) :
    AllPlaceTangentPeriod.exponential L W 1 ((one_smul _ W).trans h) z =
      (pointCongr h).symm (latticePoint L z) := by
  rw [AllPlaceTangentPeriod.exponential_apply]
  generalize latticePoint L z = p
  cases p with
  | zero => rw [map_zero, map_zero]
  | some x y hp =>
    rw [variableChangePoint_some, pointCongr_symm_some,
      _root_.WeierstrassCurve.Affine.Point.some.injEq]
    change ((1 : ℂ) ^ 2 * x + 0 = x) ∧
      ((1 : ℂ) ^ 3 * y + (1 : ℂ) ^ 2 * 0 * x + 0 = y)
    constructor <;> ring

theorem latticeForm_homothetic {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (z w : ℂ) : latticeForm L' (c * z) (c * w) = latticeForm L z w := by
  have hc : (‖c‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr h.ne_zero)
  have hm : c * conj c = (‖c‖ ^ 2 : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hn : c * z * conj (c * w) = (‖c‖ ^ 2 : ℝ) * (z * conj w) := by
    rw [map_mul, ← hm]
    ring
  rw [latticeForm, latticeForm, h.latticeArea_eq, hn, Complex.ofReal_mul,
    mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hc)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    {F : Type} [Field F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))

theorem genericSeedExponential_analyticPoint (z : ℂ) :
    Additive.toMul (genericSeedExponential G τ V C hVC z) =
      analyticPoint V (rescaledPeriods G τ C) 1 ((one_smul _ _).trans hVC)
        ((C.u : ℂ)⁻¹ * z) := by
  rw [genericSeedExponential_apply, analyticPoint,
    exponential_one_eq (V.baseChange ℂ) (rescaledPeriods G τ C) hVC]

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.TraceFrame

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.SectionPoints
open SerreScheme Weierstrass WeierstrassTheta

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {G : NativeGeometricHost E} {D : TraceLattice G} {ε : ℤˣ}
    (P : TraceFrame D ε) [Algebra (OK G) ℂ]
    (τ : E →+* ℂ) (hemb : algebraMap (OK G) ℂ = embed G τ)
    {F : Type} [Field F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
    (a : OAct (OK G) (schemeOver V))
    (hact : ∀ c : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
          a.act c =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ c * z))))

def genericSchemePoint (t : ℂ ⊗[OK G] D.La) : Sp ℂ ⟶ (P.schemeObj a).left :=
  (Pts.hom (P.genericExponential τ V C hVC a hact hemb t)).left

def scaledBundleMap (k : (Fin P.n × Fin P.n) × Fin 4) : ℂ ⊗[OK G] D.La →ₗ[ℂ] ℂ :=
  (C.u : ℂ)⁻¹ • P.complexBundleMap τ k

theorem genericSchemePoint_bundleMap (k : (Fin P.n × Fin P.n) × Fin 4)
    (t : ℂ ⊗[OK G] D.La) :
    P.genericSchemePoint τ hemb V C hVC a hact t ≫ (P.schemeBundleMap a k).left =
      (analyticPoint V (rescaledPeriods G τ C) 1 ((one_smul _ _).trans hVC)
        (P.scaledBundleMap τ C k t)).left := by
  have h := P.genericExponential_bundleMap τ hemb V C hVC a hact k t
  rw [genericSeedExponential_analyticPoint] at h
  exact congrArg Over.Hom.left h

/-- The original bundle's metric is the signed product of its actual
seed pullback metrics, on its literal LinComb chart indices. -/
def schemeSigmaNormSq (j : (P.schemeBundle a (originLB V)).ι)
    (t : ℂ ⊗[OK G] D.La) (c : ℂ) : ℝ :=
  signedChartNormSq V (rescaledPeriods G τ C) 1
    (fun k s => P.scaledBundleMap τ C k s) P.schemeBundleExponent j t c

theorem schemeSigmaNormSq_pos (j : (P.schemeBundle a (originLB V)).ι)
    (t : ℂ ⊗[OK G] D.La) {c : ℂ}
    (h : ⊤ ≤ P.genericSchemePoint τ hemb V C hVC a hact t ⁻¹ᵁ
      (P.schemeBundle a (originLB V)).U j) (hc : c ≠ 0) :
    0 < P.schemeSigmaNormSq τ V C a j t c :=
  signedChartNormSq_pos V (rescaledPeriods G τ C) 1
    (fun k s => P.scaledBundleMap τ C k s) P.schemeBundleExponent
    ((one_smul _ _).trans hVC) (fun k => (P.schemeBundleMap a k).left)
    (P.genericSchemePoint τ hemb V C hVC a hact)
    (P.genericSchemePoint_bundleMap τ hemb V C hVC a hact) j t h hc

/-- The metric descends through the actual tensor-bundle transition units. -/
theorem schemeSigmaNormSq_transition (i j : (P.schemeBundle a (originLB V)).ι)
    (t : ℂ ⊗[OK G] D.La) (c : ℂ)
    (h : ⊤ ≤ P.genericSchemePoint τ hemb V C hVC a hact t ⁻¹ᵁ
      ((P.schemeBundle a (originLB V)).U i ⊓ (P.schemeBundle a (originLB V)).U j)) :
    P.schemeSigmaNormSq τ V C a i t
      (evalPt (P.genericSchemePoint τ hemb V C hVC a hact t) _ h
        ((P.schemeBundle a (originLB V)).g i j : Γ((P.schemeObj a).left, _)) * c) =
      P.schemeSigmaNormSq τ V C a j t c :=
  signedChartNormSq_transition V (rescaledPeriods G τ C) 1
    (fun k s => P.scaledBundleMap τ C k s) P.schemeBundleExponent
    ((one_smul _ _).trans hVC) (fun k => (P.schemeBundleMap a k).left)
    (P.genericSchemePoint τ hemb V C hVC a hact)
    (P.genericSchemePoint_bundleMap τ hemb V C hVC a hact) i j t c h

/-- The metric has exactly the original integral tensor periods. -/
include hemb hact in
theorem schemeSigmaNormSq_period (j : (P.schemeBundle a (originLB V)).ι)
    (t : ℂ ⊗[OK G] D.La) (m : D.La) (c : ℂ) :
    P.schemeSigmaNormSq τ V C a j (t + 1 ⊗ₜ[OK G] m) c =
      P.schemeSigmaNormSq τ V C a j t c := by
  apply signedChartNormSq_period V (rescaledPeriods G τ C) 1
    (fun k s => P.scaledBundleMap τ C k s) P.schemeBundleExponent j t
    (t + 1 ⊗ₜ[OK G] m) (fun k => P.scaledBundleMap τ C k (1 ⊗ₜ[OK G] m))
  · intro k
    exact P.scaled_complexBundleMap_period τ hemb V C hVC a hact k m
  · intro k
    exact map_add (P.scaledBundleMap τ C k) t (1 ⊗ₜ[OK G] m)

/-- This form is the quadratic exponent derived from the actual product
metric. It retains every signed pullback and its original complex map. -/
def sigmaGram (t u : ℂ ⊗[OK G] D.La) : ℂ :=
  ∑ k : (Fin P.n × Fin P.n) × Fin 4, (P.schemeBundleExponent k : ℂ) *
    latticeForm (rescaledPeriods G τ C)
      (P.scaledBundleMap τ C k t) (P.scaledBundleMap τ C k u)

/-- The exact signed Gram is the original trace pairing, with factor one. -/
theorem sigmaGram_eq (t u : ℂ ⊗[OK G] D.La) :
    P.sigmaGram τ C t u =
      (1 / PeriodMean.latticeArea (periodPair G τ) : ℂ) *
        ∑ k : Fin P.n × Fin P.n,
          embed G τ (kLin D ε (P.x k.1) (P.x k.2)) *
            P.complexCoefficient k.1 t * conj (P.complexCoefficient k.2 u) := by
  have hh := isHomothetic_scalePeriods (periodPair G τ) (C.u : ℂ)⁻¹
    (inv_ne_zero C.u.ne_zero)
  have hs (z w : ℂ) :
      latticeForm (rescaledPeriods G τ C) ((C.u : ℂ)⁻¹ * z) ((C.u : ℂ)⁻¹ * w) =
        latticeForm (periodPair G τ) z w := latticeForm_homothetic hh z w
  have hω : embed G τ (wK G) + conj (embed G τ (wK G)) = 1 := by
    rw [← EllipticSeed.embed_bar, ← map_add, wK_add_barOK, map_one]
  have h4 (ij : Fin P.n × Fin P.n) :
      (∑ j : Fin 4, (P.schemeBundleExponent (ij, j) : ℂ) *
        latticeForm (periodPair G τ)
          (P.complexBundleMap τ (ij, j) t) (P.complexBundleMap τ (ij, j) u)) =
      SerreGram.squareGram (1 / PeriodMean.latticeArea (periodPair G τ))
        (embed G τ (kLin D ε (P.x ij.1) (P.x ij.2)) * P.complexCoefficient ij.1 t)
        (embed G τ (wK G) * P.complexCoefficient ij.2 t)
        (embed G τ (kLin D ε (P.x ij.1) (P.x ij.2)) * P.complexCoefficient ij.1 u)
        (embed G τ (wK G) * P.complexCoefficient ij.2 u) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, complexBundleMap,
      schemeBundleExponent, Matrix.cons_val_zero, Matrix.cons_val_succ,
      complexBundleFirst, complexBundleSecond, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, smul_eq_mul, Int.cast_one, Int.cast_neg,
      latticeForm, SerreGram.squareGram]
    ring
  change (∑ k : (Fin P.n × Fin P.n) × Fin 4, (P.schemeBundleExponent k : ℂ) *
    latticeForm (rescaledPeriods G τ C)
      ((C.u : ℂ)⁻¹ * P.complexBundleMap τ k t)
      ((C.u : ℂ)⁻¹ * P.complexBundleMap τ k u)) = _
  simp_rw [hs]
  rw [Fintype.sum_prod_type]
  simp_rw [h4]
  exact SerreGram.sum_squareGram _ _ hω _
    (fun _ _ => by rw [kLin_barOK, EllipticSeed.embed_bar]) _ _

/-- Gaussian expression of the actual metric, using its proved signed
trace Gram and actual product of seed sigma frames. -/
theorem schemeSigmaNormSq_gaussian (j : (P.schemeBundle a (originLB V)).ι)
    (t : ℂ ⊗[OK G] D.La) (c : ℂ) :
    P.schemeSigmaNormSq τ V C a j t c =
      ‖c / signedFrame V (rescaledPeriods G τ C) 1
        (fun k s => P.scaledBundleMap τ C k s) P.schemeBundleExponent j t‖ ^ 2 *
          Real.exp (-Real.pi * (P.sigmaGram τ C t t).re) := by
  rw [schemeSigmaNormSq, signedChartNormSq_gaussian]
  congr 2
  simp [sigmaGram, Complex.mul_re]

end RHLean.Geometry.NativeCM.TraceFrame

end
