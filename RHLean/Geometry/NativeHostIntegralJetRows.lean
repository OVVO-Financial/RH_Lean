import RHLean.Geometry.NativePrescribedPolarizationLattice
import RHLean.Geometry.NativeThetaFiniteFamily
import RHLean.Geometry.NativeThetaLatticeNormalization

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial
open scoped BigOperators

namespace RHLean.Geometry.NativeTheta.Paired

variable {E K : Type} [Field E] [NumberField E] [IsCMField E] [Field K] [NumberField K]
    {T J σ : Type} [Fintype J] {p q n : ℕ}

/-- Substitute polynomial linear combinations of genuine Hermitian lattice
directions in each of the two sorts of rows. A constant parameter permits
translation before taking a coefficient. -/
def hermitianJetPoint (τ : T → E →+* K)
    (w : T → (Fin p ⊕ Fin q) → J → Fin n → E)
    (g : J → MvPolynomial σ (𝓞 K)) :
    Var T p q (Fin n) → MvPolynomial σ K :=
  fun k => ∑ s, C (τ k.1 (match k.2.1 with
    | .inl a => IsCMField.complexConj E (w k.1 (.inl a) s k.2.2)
    | .inr b => w k.1 (.inr b) s k.2.2)) *
    MvPolynomial.map (algebraMap (𝓞 K) K) (g s)

private theorem contract_jet_row {κ : Type} [Fintype κ]
    (v : κ → K) (w : J → κ → K) (g : J → MvPolynomial σ K) :
    (∑ k, C (v k) * ∑ s, C (w s k) * g s) =
      ∑ s, C (∑ k, v k * w s k) * g s := by
  classical
  calc
    _ = ∑ k, ∑ s, (C (v k) * C (w s k)) * g s := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ s, ∑ k, (C (v k) * C (w s k)) * g s := Finset.sum_comm
    _ = _ := by simp only [map_sum, map_mul, Finset.sum_mul]

/-- On the native integral harmonic generators, a Hermitian-lattice
substitution has every coefficient in the original ring of integers.
This includes affine polynomial parameterizations of any number of rows. -/
theorem latticePolynomials_hermitianJet_integral
    (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (w : T → (Fin p ⊕ Fin q) → J → Fin n → E)
    (hw : ∀ t r s, w t r s ∈ Λ) (g : J → MvPolynomial σ (𝓞 K))
    {P : Poly K T p q (Fin n)} (hP : P ∈ latticePolynomials τ Λ) :
    ∃ Q : MvPolynomial σ (𝓞 K), MvPolynomial.map (algebraMap (𝓞 K) K) Q =
      aeval (hermitianJetPoint τ w g) P := by
  classical
  let emb := algebraMap (𝓞 K) K
  have lift_row (t : T) (h : J → E) (hh : ∀ s, IsIntegral ℤ (h s)) :
      ∃ Q : MvPolynomial σ (𝓞 K), MvPolynomial.map emb Q =
        ∑ s, C (τ t (h s)) * MvPolynomial.map emb (g s) := by
    let z : J → 𝓞 K := fun s => ⟨τ t (h s), (hh s).map (τ t).toIntAlgHom⟩
    refine ⟨∑ s, C (z s) * g s, ?_⟩
    simp only [map_sum, map_mul, MvPolynomial.map_C] <;> rfl
  unfold latticePolynomials at hP
  induction hP using Algebra.adjoin_induction with
  | mem u hu =>
    rcases hu with ⟨t, a, v, hv, rfl⟩ | ⟨t, b, v, hv, rfl⟩
    · have heval :
          aeval (hermitianJetPoint τ w g) (xForm t a (fun k => τ t (v k))) =
            ∑ s, C (τ t (hermPairing E n v (w t (.inl a) s))) *
              MvPolynomial.map emb (g s) := by
        simp only [xForm_apply, map_sum, map_mul, aeval_C, aeval_X,
          MvPolynomial.algebraMap_eq, hermitianJetPoint, xVar]
        rw [contract_jet_row]
        simp only [hermPairing_apply, map_sum, map_mul] <;> rfl
      rw [heval]
      exact lift_row t _ (fun s => hint _ hv _ (hw t (.inl a) s))
    · have heval :
          aeval (hermitianJetPoint τ w g)
              (yForm t b (fun k => τ t (IsCMField.complexConj E (v k)))) =
            ∑ s, C (τ t (hermPairing E n (w t (.inr b) s) v)) *
              MvPolynomial.map emb (g s) := by
        simp only [yForm_apply, map_sum, map_mul, aeval_C, aeval_X,
          MvPolynomial.algebraMap_eq, hermitianJetPoint, yVar]
        rw [contract_jet_row]
        refine Finset.sum_congr rfl fun s _ => ?_
        have hcoeff :
            (∑ k, τ t (IsCMField.complexConj E (v k)) * τ t (w t (.inr b) s k)) =
              τ t (hermPairing E n (w t (.inr b) s) v) := by
          simp only [hermPairing_apply, map_sum, map_mul]
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
        rw [hcoeff]
      rw [heval]
      exact lift_row t _ (fun s => hint _ (hw t (.inr b) s) _ hv)
  | algebraMap r =>
    refine ⟨C r, ?_⟩
    rw [MvPolynomial.map_C]
    change C (algebraMap (𝓞 K) K r) =
      aeval _ (C (algebraMap (𝓞 K) K r))
    rw [aeval_C, MvPolynomial.algebraMap_eq]
  | add P Q _ _ hP hQ =>
    obtain ⟨P₀, hP₀⟩ := hP
    obtain ⟨Q₀, hQ₀⟩ := hQ
    exact ⟨P₀ + Q₀, by rw [map_add, map_add, hP₀, hQ₀]⟩
  | mul P Q _ _ hP hQ =>
    obtain ⟨P₀, hP₀⟩ := hP
    obtain ⟨Q₀, hQ₀⟩ := hQ
    exact ⟨P₀ * Q₀, by rw [map_mul, map_mul, hP₀, hQ₀]⟩

theorem isIntegral_coeff_hermitianJet
    (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (w : T → (Fin p ⊕ Fin q) → J → Fin n → E)
    (hw : ∀ t r s, w t r s ∈ Λ) (g : J → MvPolynomial σ (𝓞 K))
    {P : Poly K T p q (Fin n)} (hP : P ∈ latticePolynomials τ Λ)
    (α : σ →₀ ℕ) :
    IsIntegral ℤ ((aeval (hermitianJetPoint τ w g) P).coeff α) := by
  obtain ⟨Q, hQ⟩ := latticePolynomials_hermitianJet_integral τ Λ hint w hw g hP
  rw [← hQ, coeff_map]
  exact (Q.coeff α).isIntegral_coe

/-- Apply the test with the original self-duality assumption of the evaluated
finite theta family. -/
theorem isIntegral_coeff_hermitianJet_of_unimodular
    (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E)) (hU : Lattice.Unimodular Λ)
    (w : T → (Fin p ⊕ Fin q) → J → Fin n → E)
    (hw : ∀ t r s, w t r s ∈ Λ) (g : J → MvPolynomial σ (𝓞 K))
    {P : Poly K T p q (Fin n)} (hP : P ∈ latticePolynomials τ Λ)
    (α : σ →₀ ℕ) :
    IsIntegral ℤ ((aeval (hermitianJetPoint τ w g) P).coeff α) :=
  isIntegral_coeff_hermitianJet τ Λ (fun x hx => ((Lattice.unimodular_iff Λ).mp hU x).mp hx)
    w hw g hP α

end RHLean.Geometry.NativeTheta.Paired

end

noncomputable section
open NumberField Matrix
open scoped Pointwise nonZeroDivisors BigOperators

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits

/-- A row on the actual prescribed lattice is integral exactly when each entry
belongs to the half-different ideal. The test uses the original inverse-ideal
coordinates of the host. -/
theorem prescribedLattice_row_integral_iff {φ : Frame} (H : HostRaw φ)
    (B : Ideal (𝓞 H.E)) (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m : ℕ) (c : Fin (k + m - 1) → H.E) :
    (∀ x ∈ prescribedLattice H B k m, (∑ i, c i * x i) ∈ (algebraMap (𝓞 H.E) H.E).range) ↔
      ∀ i, c i ∈ (B : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  classical
  have hn : coefficientIdeal H B ≠ 0 := inv_ne_zero (halfDifferent_ne_zero H B hB).1
  have hdual (z : H.E) : z ∈ (B : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∀ y ∈ coefficientIdeal H B, z * y ∈ (algebraMap (𝓞 H.E) H.E).range := by
    have h := FractionalIdeal.mem_inv_iff (x := z) hn
    rw [show (coefficientIdeal H B)⁻¹ = (B : FractionalIdeal (𝓞 H.E)⁰ H.E) from inv_inv _] at h
    exact h.trans ⟨fun hz y hy => (FractionalIdeal.mem_one_iff _).mp (hz y hy),
      fun hz y hy => (FractionalIdeal.mem_one_iff _).mpr (hz y hy)⟩
  constructor
  · intro h i
    apply (hdual _).mpr
    intro y hy
    have hx : Pi.single i y ∈ prescribedLattice H B k m := by
      apply (mem_twistedLattice H B _ _).mpr
      intro j
      by_cases hj : j = i
      · subst j
        simpa only [Pi.single_eq_same] using hy
      · rw [Pi.single_eq_of_ne hj]
        exact (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).zero_mem
    have ht := h (Pi.single i y) hx
    rw [show (∑ j, c j * Pi.single i y j) = c i * y from dotProduct_single c y i] at ht
    exact ht
  · intro h x hx
    apply (algebraMap (𝓞 H.E) H.E).range.sum_mem
    intro i _
    exact ((hdual _).mp (h i)) (x i) ((mem_twistedLattice H B _ _).mp hx i)

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization
end
