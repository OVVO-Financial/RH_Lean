import RHLean.Geometry.NativeThetaCuspFlagDomain

/-!
# The precise Hermitian Gram identities for the flag action

These declaration cuts provide exactly the canonical CM conjugation and
Gram-matrix identities used to prove the principal congruence action free.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsIntegralCc.lean,
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean,
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DetSubUpper.lean.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open NumberField Complex Matrix
open scoped ComplexConjugate

namespace RHLean.Geometry.NativeTheta.Cusp.FlagDomain

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by
  rw [cc]
  exact IsCMField.complexEmbedding_complexConj E τ x

theorem hermC_conj (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (u v : Fin r → ℂ) : conj (hermC τ G u v) = hermC τ G v u := by
  unfold hermC
  simp only [map_sum, map_mul, Complex.conj_conj]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← emb_cc, hG]
  ring

theorem gram_isHermitian (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (M : Matrix (Fin r) (Fin r) ℂ) : (gram τ G M).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [gram, Matrix.of_apply]
  exact hermC_conj τ hG _ _

namespace FrameDegreeData

omit [NumberField E] [IsCMField E] in
lemma gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [NumberField E] [IsCMField E] in
lemma gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]


end FrameDegreeData

end RHLean.Geometry.NativeTheta.Cusp.FlagDomain
