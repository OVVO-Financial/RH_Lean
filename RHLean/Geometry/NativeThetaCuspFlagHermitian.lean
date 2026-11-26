import RHLean.Geometry.NativeThetaCuspFlagGram

/-!
# Elementary Hermitian operations for varying flag periods

These are the exact first-linear/conjugate-second-linear operations used
in the source's local flag-period formula. No positivity or analytic
transformation premise is introduced.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open NumberField Matrix
open scoped Classical ComplexConjugate

namespace RHLean.Geometry.NativeTheta.Cusp.FlagDomain

section Operations
variable {E : Type} [Field E] {r : ℕ}

theorem hermC_add_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  unfold hermC
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hermC_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (c • u) v = c * hermC τ G u v := by
  unfold hermC
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hermC_sub_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  unfold hermC
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem hermC_zero_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → ℂ) :
    hermC τ G 0 v = 0 := by
  unfold hermC
  simp

theorem hermC_add_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  unfold hermC
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hermC_smul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (c • v) = conj c * hermC τ G u v := by
  unfold hermC
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hermC_sub_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  unfold hermC
  simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem hermC_zero_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ) :
    hermC τ G u 0 = 0 := by
  unfold hermC
  simp

theorem hermC_sum_left {ι : Type} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ G (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact hermC_zero_left τ G v
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_left, ih]

theorem hermC_sum_right {ι : Type} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (u : Fin r → ℂ) (f : ι → Fin r → ℂ) :
    hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact hermC_zero_right τ G u
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_right, ih]

end Operations

namespace Data
variable {r : ℕ}

theorem mulVec_eq_sum_col (P : Matrix (Fin r) (Fin r) ℂ) (c : Fin r → ℂ) :
    P *ᵥ c = ∑ i, c i • col P i := by
  ext k
  simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]

end Data

theorem hermC_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    hermC τ G (Data.emb τ u) (Data.emb τ v) = τ (herm G u v) := by
  unfold hermC herm Data.emb
  simp only [map_sum, map_mul, emb_cc]

end RHLean.Geometry.NativeTheta.Cusp.FlagDomain
