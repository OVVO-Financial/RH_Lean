import Mathlib

/-!
# Exact finite-grid interpolation for the native theta family

A polynomial map has the same linear span on the displayed integral grid as
on its entire coefficient domain, once the grid exceeds each variable degree.
This is proved by polynomial interpolation and linear duality. It assumes no
spanning family or geometric theta-density assertion.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/`
`EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean`, the Vanishing and Span sections.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace RHLean.Geometry.NativeTheta.GridInterpolation

open MvPolynomial

section Vanishing

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]

theorem eq_zero_of_eval_box_eq_zero (d : σ → ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d i)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d i) → eval (fun i => (x i : R)) P = 0) : P = 0 := by
  classical
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun i => (Finset.range (d i + 1)).image (Nat.cast : ℕ → R)) (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (hdeg i)
  · choose n hn hnx using fun i => Finset.mem_image.1 (hx i)
    have : x = fun i => (n i : R) := funext fun i => (hnx i).symm
    rw [this]
    exact hP n fun i => Nat.lt_succ_iff.1 (Finset.mem_range.1 (hn i))

theorem eq_zero_of_eval_grid_eq_zero (d : ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → eval (fun i => (x i : R)) P = 0) : P = 0 :=
  eq_zero_of_eval_box_eq_zero (fun _ => d) P hdeg hP

end Vanishing

section Span

variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]

theorem mem_of_grid_mem (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P)
    (U : Submodule K V)
    (hU : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → Φ (fun i => (x i : A)) ∈ U) (y : σ → A) :
    Φ y ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
  intro l hl
  obtain ⟨P, hdeg, hP⟩ := hΦ l
  have h0 : P = 0 := by
    refine eq_zero_of_eval_grid_eq_zero d P hdeg fun x hx => ?_
    have := (Submodule.mem_dualAnnihilator l).1 hl _ (hU x hx)
    rw [hP] at this
    simpa using this
  rw [hP, h0, map_zero]

theorem span_grid_eq_span_range (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine mem_of_grid_mem d Φ hΦ _ (fun x hx => ?_) y
    apply Submodule.subset_span
    exact ⟨x, hx, rfl⟩

omit [Finite σ] [CharZero K] in

theorem exists_poly_dual_sum_monomial_smul (d : ℕ) (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V)
    (hs : ∀ a ∈ s, ∀ i, a i ≤ d) (l : Module.Dual K V) :
    ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧ ∀ x : σ → A,
      l (∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) =
        eval (fun i => algebraMap A K (x i)) P := by
  classical
  refine ⟨∑ a ∈ s, monomial a (l (v a)), fun i => ?_, fun x => ?_⟩
  · rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨a, ha, hma⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have := Finset.mem_singleton.1 (support_monomial_subset hma)
    rw [this]
    exact hs a ha i
  · simp only [map_sum, map_smul, eval_monomial, smul_eq_mul, mul_comm]

theorem span_grid_eq_span_range_of_eq_sum (d : ℕ) (Φ : (σ → A) → V)
    (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V) (hs : ∀ a ∈ s, ∀ i, a i ≤ d)
    (hΦ : ∀ x, Φ x = ∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  refine span_grid_eq_span_range d Φ fun l => ?_
  simp only [hΦ]
  exact exists_poly_dual_sum_monomial_smul d s v hs l

theorem span_grid_eval_eq_span_range {B : Type*} [CommRing B] [Algebra K B] (d : ℕ)
    (F : MvPolynomial σ B) (hF : ∀ i, F.degreeOf i ≤ d) :
    Submodule.span K ((fun x : σ → ℕ => eval (fun i => (x i : B)) F) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range fun x : σ → A =>
        eval (fun i => algebraMap K B (algebraMap A K (x i))) F) := by
  have h := span_grid_eq_span_range_of_eq_sum (K := K) d
    (fun x : σ → A => eval (fun i => algebraMap K B (algebraMap A K (x i))) F)
    F.support (fun a => F.coeff a) (fun a ha i => (degreeOf_le_iff.1 (hF i)) a ha)
    (fun x => by
      rw [eval_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Algebra.smul_def, Finsupp.prod, map_prod, mul_comm]
      simp only [map_pow])
  simpa only [map_natCast] using h

end Span

end RHLean.Geometry.NativeTheta.GridInterpolation

end
