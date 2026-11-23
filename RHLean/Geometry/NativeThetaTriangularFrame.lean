import RHLean.Geometry.NativeThetaHarmonicPolynomials

/-!
# Triangular frame covariance of the actual native harmonic polynomials

The existing RowInv and RowDeg conditions imply their exact transformation
under invertible lower-triangular row changes over any coefficient algebra.
The proof extends elementary row invariance from the infinite coefficient
field, constructs the unipotent block substitution, and retains every
individual diagonal weight. No cusp-space, section, or frame-covariance
conclusion is assumed.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`InvariantOperatorValueTriangularChange.lean`, `RowTriangular`, section Poly.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.RowTriangular

open MvPolynomial

variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k T : Type} [Field k] [CommRing T]

theorem eval₂_shift [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k} (hP : RowInv r n k P)
    (σ : Ty) (i i' : Fin (r σ)) (hi : i' < i) (t : T) (y y' : Letter Ty r n → T)
    (h₁ : ∀ b, y' ⟨σ, i, b⟩ = y ⟨σ, i, b⟩ + t * y ⟨σ, i', b⟩)
    (h₂ : ∀ ℓ, (¬ ∃ b, ℓ = ⟨σ, i, b⟩) → y' ℓ = y ℓ) :
    eval₂Hom φ y' P = eval₂Hom φ y P := by
  classical
  let _ : Algebra k T := φ.toAlgebra
  let G : Letter Ty r n → MvPolynomial (Option (Letter Ty r n)) k := fun ℓ =>
    if ∃ b, ℓ = ⟨σ, (i, b)⟩ then X (some ℓ) + X none * X (some ⟨σ, (i', ℓ.snd.2)⟩) else X (some ℓ)
  have hQ : aeval G P = rename some P := by
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (aeval (x ∘ some)) (hP σ i i' hi (x none))
    unfold rowShift at h1
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h1
    change aeval x (aeval G P) = aeval x (rename some P)
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_rename, ← h1]
    congr 2
    funext ℓ
    by_cases hℓ : ∃ b, ℓ = ⟨σ, (i, b)⟩
    · simp [G, hℓ]
    · simp [G, hℓ]
  let g : Option (Letter Ty r n) → T := fun o => o.elim t y
  have e1 : (fun ℓ => aeval g (G ℓ)) = y' := by
    funext ℓ
    by_cases hℓ : ∃ b, ℓ = ⟨σ, (i, b)⟩
    · obtain ⟨b, rfl⟩ := hℓ
      simp only [G, ite_eq_left (show ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ from ⟨b, rfl⟩)]
      simp [g, h₁]
    · simp only [G, ite_eq_right hℓ]
      simp [g, h₂ ℓ hℓ]
  have e2 := congrArg (aeval g) hQ
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_rename, e1] at e2
  exact e2

private theorem eval₂Hom_unipotent_substitution_eq [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (σ : Ty) (i : Fin (r σ))
    [DecidablePred fun ℓ : Letter Ty r n => ∃ b, ℓ = ⟨σ, (i, b)⟩] (N : Fin (r σ) → T) (hN : ∀ j, i ≤ j → N j = 0)
    (y : Letter Ty r n → T) [DecidableEq (Fin (r σ))] (S : Finset (Fin (r σ))) :
    eval₂Hom φ (fun ℓ : Letter Ty r n =>
      if ∃ b, ℓ = ⟨σ, (i, b)⟩ then y ℓ + ∑ j ∈ S, N j * y ⟨σ, (j, ℓ.2.2)⟩ else y ℓ) P = eval₂Hom φ y P := by
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro j S hj ih
    rw [← ih]
    by_cases hji : j < i
    · refine eval₂_shift φ hP σ i j hji (N j) _ _ ?_ ?_
      · intro b
        have hb : ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := ⟨b, rfl⟩
        have hb' : ¬ ∃ b', (⟨σ, (j, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := by
          rintro ⟨b', h⟩
          simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
          exact hji.ne h.1
        simp only [ite_eq_left hb, ite_eq_right hb', Finset.sum_insert hj]
        ring
      · intro ℓ hℓ
        simp only [ite_eq_right hℓ]
    · have h0 : N j = 0 := hN j (not_lt.1 hji)
      refine congrArg (fun g => eval₂Hom φ g P) (funext fun ℓ => ?_)
      split_ifs <;> simp [Finset.sum_insert hj, h0]

private theorem eval₂Hom_unipotent_block_substitution_eq [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (N : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hN : ∀ σ i j, i ≤ j → N σ i j = 0)
    [DecidableEq (Σ σ : Ty, Fin (r σ))] (R : Finset (Σ σ : Ty, Fin (r σ))) :
    ∀ y : Letter Ty r n → T, eval₂Hom φ (fun ℓ : Letter Ty r n => y ℓ +
      if (⟨ℓ.1, ℓ.2.1⟩ : Σ σ : Ty, Fin (r σ)) ∈ R then ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, (j, ℓ.2.2)⟩ else 0) P =
      eval₂Hom φ y P := by
  refine Finset.induction_on_max_value (fun p : (Σ σ : Ty, Fin (r σ)) => (p.2 : ℕ)) R ?_ ?_
  · intro y
    simp
  · intro p R hp hmax ih y
    obtain ⟨σ, i⟩ := p
    classical
    have hA := eval₂Hom_unipotent_substitution_eq φ hP σ i (N σ i) (hN σ i) y Finset.univ
    refine Eq.trans ?_ ((ih _).trans hA)
    refine congrArg (fun g => eval₂Hom φ g P) (funext fun ℓ => ?_)
    rcases ℓ with ⟨σ', i', b⟩
    by_cases hrow : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) = ⟨σ, i⟩
    · cases hrow
      dsimp only
      rw [ite_eq_left (Finset.mem_insert_self _ _), ite_eq_right hp,
        ite_eq_left (show ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ from ⟨b, rfl⟩), add_zero]
    · have hne : ∀ j : Fin (r σ'), (⟨σ', j⟩ : Σ σ : Ty, Fin (r σ)) ≠ ⟨σ, i⟩ →
          ¬ ∃ b', (⟨σ', (j, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := by
        rintro j hj ⟨b', h⟩
        apply hj
        cases h
        rfl
      dsimp only
      rw [ite_eq_right (hne i' hrow)]
      by_cases hR : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) ∈ R
      · rw [ite_eq_left (Finset.mem_insert_of_mem hR), ite_eq_left hR]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : i' ≤ j
        · rw [hN σ' i' j hj, zero_mul, zero_mul]
        · rw [ite_eq_right (hne j ?_)]
          intro hji
          cases hji
          exact hj (Fin.le_iff_val_le_val.2 (hmax _ hR))
      · have hI : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) ∉ insert ⟨σ, i⟩ R := by
          rw [Finset.mem_insert]
          rintro (h | h)
          exacts [hrow h, hR h]
        rw [ite_eq_right hI, ite_eq_right hR]

theorem eval₂_unip [Infinite k] [Fintype Ty] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (N : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hN : ∀ σ i j, i ≤ j → N σ i j = 0)
    (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => y ℓ + ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) P = eval₂Hom φ y P := by
  classical
  have h := eval₂Hom_unipotent_block_substitution_eq φ hP N hN Finset.univ y
  simpa only [Finset.mem_univ, ↓reduceIte] using h

theorem eval₂_diag [Fintype Ty] (φ : k →+* T) {a : Ty → ℕ → ℕ} {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowDeg r n k a P) (c : ∀ σ, Fin (r σ) → T) (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => c ℓ.1 ℓ.2.1 * y ℓ) P =
      (∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 ^ a p.1 p.2) * eval₂Hom φ y P := by
  classical
  simp only [coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ ℓ : Letter Ty r n, c ℓ.1 ℓ.2.1 ^ m ℓ = ∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 ^ a p.1 p.2 := by
    rw [Fintype.prod_sigma, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hP m hm σ i]
  rw [hc]
  ring

theorem eval₂_triangular [Infinite k] [Fintype Ty] (φ : k →+* T) {a : Ty → ℕ → ℕ}
    {P : MvPolynomial (Letter Ty r n) k} (hI : RowInv r n k P) (hD : RowDeg r n k a P)
    (c : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hc : ∀ σ i j, i < j → c σ i j = 0) (hu : ∀ σ i, IsUnit (c σ i i))
    (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => ∑ j, c ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) P =
      (∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 p.2 ^ a p.1 p.2) * eval₂Hom φ y P := by
  classical
  let N : ∀ σ, Fin (r σ) → Fin (r σ) → T := fun σ i j => if j < i then ↑(hu σ i).unit⁻¹ * c σ i j else 0
  have hN : ∀ σ i j, i ≤ j → N σ i j = 0 := fun σ i j h => by simp [N, not_lt.2 h]
  have hfun : (fun ℓ : Letter Ty r n => ∑ j, c ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) =
      fun ℓ => c ℓ.1 ℓ.2.1 ℓ.2.1 * (y ℓ + ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) := by
    funext ℓ
    rcases ℓ with ⟨σ, i, b⟩
    have e : ∀ j, c σ i j * y ⟨σ, j, b⟩ =
        (if j = i then c σ i i * y ⟨σ, i, b⟩ else 0) + c σ i i * (N σ i j * y ⟨σ, j, b⟩) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · simp only [N, ite_eq_left h, ite_eq_right h.ne, zero_add]
        rw [← _root_.mul_assoc, ← _root_.mul_assoc, (hu σ i).mul_val_inv, _root_.one_mul]
      · subst h
        simp [N]
      · simp [N, h.ne', not_lt.2 h.le, hc σ i j h]
    dsimp only
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ _), mul_add, Finset.mul_sum]
  have h1 := eval₂_diag φ hD (fun σ i => c σ i i) (fun ℓ => y ℓ + ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩)
  have h2 := eval₂_unip φ hI N hN y
  rw [hfun]
  exact h1.trans (by rw [h2])


/-- The native HHa family satisfies both hypotheses used by triangular
covariance. Harmonicity is retained in the source family and need not be
replaced by an independent transformation premise. -/
theorem eval₂_triangular_of_mem_HHa [Infinite k] [Fintype Ty]
    (φ : k →+* T) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) k) (hP : P ∈ HHa r n k cc isX a)
    (c : ∀ σ, Fin (r σ) → Fin (r σ) → T)
    (hc : ∀ σ i j, i < j → c σ i j = 0) (hu : ∀ σ i, IsUnit (c σ i i))
    (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => ∑ j, c ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) P =
      (∏ p : (Σ σ : Ty, Fin (r σ)), c p.1 p.2 p.2 ^ a p.1 p.2) * eval₂Hom φ y P :=
  eval₂_triangular φ hP.2.1 hP.2.2 c hc hu y

end RHLean.Geometry.NativeTheta.RowTriangular

end
