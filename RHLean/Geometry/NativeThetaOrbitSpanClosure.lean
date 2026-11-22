import RHLean.Geometry.NativeThetaGridParametrization
import RHLean.Geometry.NativeThetaPerpendicularOrbit
import RHLean.Geometry.NativeThetaOrbitGeneration

/-!
# The actual parameter image spans the full harmonic space

Distinct field embeddings and a rational spanning lattice family allow
independent coefficient interpolation in every positive and conjugate row.
The actual perpendicular construction therefore reaches every column orbit.
The proved highest-weight theorem identifies this orbit span with the entire
prescribed harmonic row space.

The input is rational spanning of the original lattice vectors and literal
independence of its coefficient embeddings, not a harmonic-span premise.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`SpanGridPerpVecEqOrbitSpanOfLe.lean`, `span_range_coordProd`,
`exists_sum_mul_embedding_eq` and the first step of its CM specialization.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MvPolynomial Matrix NumberField

namespace RHLean.Geometry.NativeTheta.Paired

/-- The same adjugate projection fixes a perpendicular vector up to its
actual pairing determinant. -/
theorem perpVec_of_pairing_eq_zero
    {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {p : ℕ}
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V)
    (hg : ∀ a, h g (e a) = 0) :
    perpVec h e e' g = (hMat h e e').det • g := by
  simp [perpVec, hg]

section Field

variable {K : Type} [Field K] {T : Type*} [Fintype T]
  {ι : Type} [Fintype ι] {p q n : ℕ}

theorem coordProd_mem_orbitSpan (hpq : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → K) :
    coordProd c c' w w' x ∈ orbitSpan K hpq c c' :=
  minorProd_mem_orbitSpan hpq c c' fun _ a _ => by
    rw [dotProduct_comm]; exact perpVec_apply_eq_zero (dotPairing K n) _ _ _ a

theorem span_range_coordProd (hpq : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K)
    (hw : ∀ y y' : T → Fin n → K, ∃ x : ι → K,
      (∀ t k, ∑ i, x i * w t i k = y t k) ∧ ∀ t k, ∑ i, x i * w' t i k = y' t k) :
    Submodule.span K (Set.range (coordProd c c' w w')) = orbitSpan K hpq c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact coordProd_mem_orbitSpan hpq c c' w w' x
  rw [orbitSpan_eq_span_linearIndependent]
  refine Submodule.span_mono ?_
  rintro _ ⟨ε, φ, hε, -, hperp, rfl⟩
  choose ε' hε' using fun t a => surjective_mulVecLin_of (hε t) (Pi.single a 1)
  choose x₁ _ hx₁ using fun a => hw 0 fun t => ε t a
  choose x₂ hx₂ _ using fun a => hw (fun t => ε' t a) 0
  choose x₃ hx₃ _ using fun b => hw (fun t => φ t b) 0
  refine ⟨fun j => Sum.elim x₁ (Sum.elim x₂ x₃) j.1 j.2, ?_⟩
  simp only [coordProd, Sum.elim_inl, Sum.elim_inr, hx₁, hx₂, hx₃]
  congr 1
  funext t b
  have hM : hMat (dotPairing K n) (ε t) (ε' t) = 1 := by
    ext a' a
    have := congrFun (hε' t a') a
    rw [one_eq_pi_single, ← this]
    exact dotProduct_comm (ε' t a') (ε t a)
  have := perpVec_of_pairing_eq_zero (dotPairing K n) (ε t) (ε' t) (φ t b) fun a => by
    rw [dotPairing_apply, dotProduct_comm]; exact hperp t a b
  rw [hM, det_one, one_smul] at this
  exact this

end Field

section Embeddings

theorem exists_sum_mul_embedding_eq {E K J κ ι : Type*} [Field E] [CharZero E] [Field K]
    [Finite J] [Finite κ] [Fintype ι] (σ : J → E →+* K) (hσ : Function.Injective σ)
    (v : ι → κ → E) (hv : Submodule.span ℚ (Set.range v) = ⊤) (y : J → κ → K) :
    ∃ x : ι → K, ∀ j k, ∑ i, x i * σ j (v i k) = y j k := by
  classical
  have := Fintype.ofFinite J
  have := Fintype.ofFinite κ
  let u : (κ → E) → J × κ → K := fun z s => σ s.1 (z s.2)
  let U : Submodule K (J × κ → K) := Submodule.span K (Set.range fun i => u (v i))
  have hU (z : κ → E) : u z ∈ U := by
    have hz : z ∈ Submodule.span ℚ (Set.range v) := hv ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => convert U.zero_mem; ext s; simp [u]
    | add z z' _ _ h h' => convert U.add_mem h h'; ext s; simp [u]
    | smul r z _ h => convert U.smul_mem (r : K) h; ext s; simp [u, Rat.smul_def]
  have hind : LinearIndependent K fun j => (σ j : E → K) :=
    (linearIndependent_monoidHom E K).comp (fun j => (σ j : E →* K)) fun j j' e =>
      hσ (RingHom.ext fun a => DFunLike.congr_fun e a)
  have hy : (fun s : J × κ => y s.1 s.2) ∈ U := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
    intro l hl
    have h0 (j k) : l (Pi.single (j, k) 1) = 0 := by
      refine Fintype.linearIndependent_iff.1 hind (fun j => l (Pi.single (j, k) 1)) ?_ j
      funext a
      have h1 := (Submodule.mem_dualAnnihilator l).1 hl _ (hU (Pi.single k a))
      have h2 : u (Pi.single k a) = ∑ j, σ j a • Pi.single (j, k) 1 := by
        ext ⟨j', k'⟩
        by_cases hk : k' = k <;> simp [u, Finset.sum_apply, Pi.single_apply, hk]
      rw [h2, map_sum] at h1
      simpa [mul_comm] using h1
    rw [← Finset.univ_sum_single (fun s : J × κ => y s.1 s.2), map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← mul_one (y s.1 s.2), ← smul_eq_mul, Pi.single_smul', map_smul, h0, smul_zero]
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
  exact ⟨x, fun j k => by simpa [u] using congrFun hx (j, k)⟩

end Embeddings

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {K : Type} [Field K] [CharZero K] {T : Type} [Fintype T]
  {ι : Type} [Fintype ι] {p q n : ℕ}

/-- Full generation for the literal parameter orientation returned by the
finite integral family: x-rows use v and y-rows use conjugate v. -/
theorem span_range_coordProd_eq_rowHighest
    (τ : T → E →+* K)
    (hτ : Function.Injective fun s : T × Bool => fun x : E =>
      τ s.1 (if s.2 then IsCMField.complexConj E x else x))
    (hpq : p + q ≤ n) (v : ι → Fin n → E)
    (hv : Submodule.span ℚ (Set.range v) = ⊤)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    Submodule.span K (Set.range (coordProd c c'
      (fun t i k => τ t (IsCMField.complexConj E (v i k)))
      (fun t i k => τ t (v i k)))) = rowHighest K c c' := by
  let γ : E →+* E := (IsCMField.complexConj E : E ≃ₐ[_] E)
  let σ : T × Bool → E →+* K := fun s => if s.2 then (τ s.1).comp γ else τ s.1
  have hσ : Function.Injective σ := fun s s' e => hτ (funext fun x => by
    have h := DFunLike.congr_fun e x
    obtain ⟨t, _ | _⟩ := s <;> obtain ⟨t', _ | _⟩ := s' <;> exact h)
  calc
    _ = orbitSpan K hpq c c' := span_range_coordProd hpq c c' _ _ fun y y' => by
      obtain ⟨x, hx⟩ := exists_sum_mul_embedding_eq σ hσ v hv
        fun s => if s.2 then y s.1 else y' s.1
      exact ⟨x, fun t => hx (t, true), fun t => hx (t, false)⟩
    _ = rowHighest K c c' := (rowHighest_eq_orbitSpan hpq c c' K).symm

end CM

end RHLean.Geometry.NativeTheta.Paired

end
