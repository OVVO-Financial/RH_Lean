import RHLean.Geometry.NativeCMSerreSchemeBundle
import RHLean.Geometry.NativeCMSerreSchemeEigenline
import RHLean.Geometry.NativeCMSerreBundleGram
import RHLean.Geometry.NativeCMWeierstrassThetaMetric
import RHLean.Analysis.DistinguishedPrimeTransitionSupport

/-!
# Actual Serre projection derivatives and the same integral eigenline norm

The projection coordinates are differentiated on the intrinsic scheme Lie
module, using the original integral vector of the original equation. The
four signed pullback derivatives then give the computed trace Gram. Its
restriction to the actual identity-character eigenmodule is exactly the
lineNorm already used in the finite-index-preserving degree calculation.
The scale is the same canonical-sigma automorphy form at the actual
coordinate-change direction u.

This file joins native constructions, without new external source imports.
The genuine CM seed action and its derivative compatibility remain explicit.
Global analytic descent of the theta frames and identification with the
tensor bundle's polarizing curvature are not asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField Complex
open scoped Classical BigOperators Pointwise nonZeroDivisors TensorProduct ComplexConjugate

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM SerreScheme SchemeTheory
open SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie
open RHLean.Geometry.NativeCM.LineDegree RHLean.Geometry.NativeCM.AllPlaceTangentPeriod

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E)
    (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (F : Type) [Field F] [Algebra H.E F]
    (W : WeierstrassCurve (𝓞 F)) [W.IsElliptic]
    (a : OAct (OK G) (schemeOver W))
    (ha : ∀ c, IsLieComb ![algebraMap (OK G) (𝓞 F) c] ![integralVector W]
      (integralVector W ≫ a.act c))

/-- The actual derivative of each represented projection is the original
integral trace-pairing coordinate, with no rational saturation. -/
theorem coefficientLieProjection
    (i : Fin (coefficientSerreFrame H G hbar B hB 1).n)
    (t : IntegralTensor H G F B) :
    Lie.hom (coefficientLieEquiv H G hbar B hB F W a ha t) ≫
        (coefficientSerreFrame H G hbar B hB 1).schemeCoordinate a i =
      epsScale (integralPairing H G F hbar B hB i t) ≫ integralVector W := by
  let fr := coefficientSerreFrame H G hbar B hB 1
  have hd (c : OK G) : integralVector W ≫ a.act c =
      epsScale (algebraMap (OK G) (𝓞 F) c) ≫ integralVector W :=
    (LieTensor.isLieComb_one_iff _ _ _).mp (ha c)
  induction t using TensorProduct.inductionOn with
  | tmul c m =>
    have ht : c ⊗ₜ[OK G] m = c • (1 ⊗ₜ[OK G] m) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [integralPairing_tmul, ht, map_smul, Lie.hom_smul,
      coefficientLieEquiv_one]
    change (epsScale c ≫ integralVector W ≫ (fr.schemeIsTensor a).tmul m) ≫
      fr.schemeCoordinate a i = _
    rw [Category.assoc, Category.assoc, TraceFrame.tmul_schemeCoordinate, hd,
      epsScale_mul_assoc]
  | add t u ht hu =>
    rw [map_add, Lie.hom_add, MonObj.mul_comp, ht, hu, map_add]
    exact (epsScale_add_comp _ _ (integralVector_isTangent W)).symm

/-- Integral derivatives of the four actual bundle maps in their signed order. -/
def integralBundleDerivative
    (k : (Fin (coefficientSerreFrame H G hbar B hB 1).n ×
      Fin (coefficientSerreFrame H G hbar B hB 1).n) × Fin 4)
    (t : IntegralTensor H G F B) : 𝓞 F :=
  let fr := coefficientSerreFrame H G hbar B hB 1
  let c := integralPairing H G F hbar B hB k.1.1 t *
    algebraMap (OK G) (𝓞 F)
      (kLin (coefficientTraceLattice H G hbar B hB) 1 (fr.x k.1.1) (fr.x k.1.2))
  let d := integralPairing H G F hbar B hB k.1.2 t *
    algebraMap (OK G) (𝓞 F) (wK G)
  ![c + d, c, d, 0] k.2

theorem coefficientLieBundleMap
    (k : (Fin (coefficientSerreFrame H G hbar B hB 1).n ×
      Fin (coefficientSerreFrame H G hbar B hB 1).n) × Fin 4)
    (t : IntegralTensor H G F B) :
    Lie.hom (coefficientLieEquiv H G hbar B hB F W a ha t) ≫
        (coefficientSerreFrame H G hbar B hB 1).schemeBundleMap a k =
      epsScale (integralBundleDerivative H G hbar B hB F k t) ≫ integralVector W := by
  let fr := coefficientSerreFrame H G hbar B hB 1
  have hd (c : OK G) : integralVector W ≫ a.act c =
      epsScale (algebraMap (OK G) (𝓞 F) c) ≫ integralVector W :=
    (LieTensor.isLieComb_one_iff _ _ _).mp (ha c)
  have hfirst (ij : Fin fr.n × Fin fr.n) :
      Lie.hom (coefficientLieEquiv H G hbar B hB F W a ha t) ≫
        fr.schemeBundleFirst a ij =
      epsScale (integralPairing H G F hbar B hB ij.1 t *
        algebraMap (OK G) (𝓞 F)
          (kLin (coefficientTraceLattice H G hbar B hB) 1 (fr.x ij.1) (fr.x ij.2))) ≫
            integralVector W := by
    rw [TraceFrame.schemeBundleFirst, ← Category.assoc, coefficientLieProjection,
      Category.assoc, hd, epsScale_mul_assoc]
  have hsecond (ij : Fin fr.n × Fin fr.n) :
      Lie.hom (coefficientLieEquiv H G hbar B hB F W a ha t) ≫
        fr.schemeBundleSecond a ij =
      epsScale (integralPairing H G F hbar B hB ij.2 t *
        algebraMap (OK G) (𝓞 F) (wK G)) ≫ integralVector W := by
    rw [TraceFrame.schemeBundleSecond,
      (fr.isLinearHom_schemeCoordinate a ij.2).comm,
      ← Category.assoc, coefficientLieProjection, Category.assoc, hd, epsScale_mul_assoc]
  rcases k with ⟨ij, k⟩
  fin_cases k
  · change _ ≫ (fr.schemeBundleFirst a ij * fr.schemeBundleSecond a ij) = _
    rw [MonObj.comp_mul, hfirst, hsecond, ← epsScale_add_comp _ _ (integralVector_isTangent W)]
    rfl
  · exact hfirst ij
  · exact hsecond ij
  · change _ ≫ (1 : fr.schemeObj a ⟶ schemeOver W) = epsScale 0 ≫ integralVector W
    rw [MonObj.comp_one, epsScale_zero_comp (integralVector_isTangent W)]

/-- The signed pullback Gram is computed on derivatives of actual scheme
morphisms. The parameter n is specialized below to the proved sigma scale. -/
def coefficientSchemeBundleGram (σ : F →+* ℂ) (n : ℝ)
    (t u : IntegralTensor H G F B) : ℂ :=
  let fr := coefficientSerreFrame H G hbar B hB 1
  ∑ k : (Fin fr.n × Fin fr.n) × Fin 4,
    (fr.schemeBundleExponent k : ℂ) * n *
      σ (algebraMap (𝓞 F) F (integralBundleDerivative H G hbar B hB F k t)) *
      conj (σ (algebraMap (𝓞 F) F (integralBundleDerivative H G hbar B hB F k u)))

theorem coefficientSchemeBundleGram_eq (σ : F →+* ℂ) (n : ℝ)
    (t u : IntegralTensor H G F B) :
    coefficientSchemeBundleGram H G hbar B hB F σ n t u =
      tensorOriginGram H G F hbar B hB σ n t u := by
  unfold coefficientSchemeBundleGram tensorOriginGram
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, integralBundleDerivative,
    TraceFrame.schemeBundleExponent, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, map_mul, map_zero,
    Int.cast_one, Int.cast_neg, map_neg, SerreGram.squareGram,
    embeddedCoefficient, embeddedPairing]
  ring

/-- On the actual integral Lie eigenmodule, the signed Gram is precisely
the line metric used by the existing finite-index-preserving AllWt degree. -/
theorem coefficientLieEigen_signedGram_norm
    (hroot : (G.rt : H.E) = H.sqd) (n : (F →+* ℂ) → ℝ)
    (hn : ∀ σ, 0 < n σ) (σ : F →+* ℂ)
    (v : coefficientLieEigenmodule H G hbar B hB F W a) :
    (coefficientSchemeBundleGram H G hbar B hB F σ (n σ)
      ((coefficientLieEigenEquiv H G hbar B hB F W a ha).symm v)
      ((coefficientLieEigenEquiv H G hbar B hB F W a ha).symm v)).re =
        lineNorm n σ (coefficientLieEigenCoordinate H G hbar B hB F W a ha v) ^ 2 := by
  rw [coefficientSchemeBundleGram_eq, tensorOriginGram_eigen H G F hbar hroot]
  change ((n σ : ℂ) * σ (coefficientLieEigenCoordinate H G hbar B hB F W a ha v) *
    conj (σ (coefficientLieEigenCoordinate H G hbar B hB F W a ha v))).re = _
  rw [mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, lineNorm, mul_pow, Real.sq_sqrt (hn σ).le]

variable [NumberField F]

/-- The form is evaluated in the actual tangent direction u of the same
equation and canonical-sigma automorphy, rather than assigned a target mean. -/
theorem coefficientLieEigen_actualSigma_norm
    (hroot : (G.rt : H.E) = H.sqd) (hΔ : W.Δ = 1) (σ : F →+* ℂ)
    (v : coefficientLieEigenmodule H G hbar B hB F W a) :
    (coefficientSchemeBundleGram H G hbar B hB F σ
      (Real.pi * (Weierstrass.latticeForm (lattice W hΔ (InfinitePlace.mk σ))
        ((coordinateChange W hΔ (InfinitePlace.mk σ)).u : ℂ)
        ((coordinateChange W hΔ (InfinitePlace.mk σ)).u : ℂ)).re)
      ((coefficientLieEigenEquiv H G hbar B hB F W a ha).symm v)
      ((coefficientLieEigenEquiv H G hbar B hB F W a ha).symm v)).re =
      lineNorm (embeddingProfile W hΔ) σ
        (coefficientLieEigenCoordinate H G hbar B hB F W a ha v) ^ 2 := by
  rw [WeierstrassTheta.automorphy_tangent_eq_placeProfile]
  exact coefficientLieEigen_signedGram_norm H G hbar B hB F W a ha hroot
    (embeddingProfile W hΔ) (embeddingProfile_pos W hΔ) σ v


/-- The actual Serre scheme Gram in the native real-pair coordinates.
The actual sigma metric, the integral eigenvector and its evaluation are
unchanged. This is a direct transport of the existing geometric norm
identity, not a new geometric witness or a replacement rank. -/
theorem coefficientLieEigen_actualSigma_phi_norm
    (hroot : (G.rt : H.E) = H.sqd) (hΔ : W.Δ = 1) (σ : F →+* ℂ)
    (v : coefficientLieEigenmodule H G hbar B hB F W a) :
    (coefficientSchemeBundleGram H G hbar B hB F σ
      (Real.pi * (Weierstrass.latticeForm (lattice W hΔ (InfinitePlace.mk σ))
        ((coordinateChange W hΔ (InfinitePlace.mk σ)).u : ℂ)
        ((coordinateChange W hΔ (InfinitePlace.mk σ)).u : ℂ)).re)
      ((coefficientLieEigenEquiv H G hbar B hB F W a ha).symm v)
      ((coefficientLieEigenEquiv H G hbar B hB F W a ha).symm v)).re =
      embeddingProfile W hΔ σ *
        RHLean.Analysis.complexRealPairNormSq (RHLean.Analysis.complexRealPair
          (σ (coefficientLieEigenCoordinate H G hbar B hB F W a ha v))) := by
  rw [coefficientLieEigen_actualSigma_norm H G hbar B hB F W a ha hroot hΔ,
    lineNorm, mul_pow, Real.sq_sqrt (embeddingProfile_pos W hΔ σ).le,
    RHLean.Analysis.complexRealPairNormSq_complexRealPair]

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
