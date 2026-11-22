import RHLean.Geometry.NativePolarizationComplexCoordinates

/-!
# Explicit complex coordinates and their exact embedding multiplicities

Conjugating exactly the negative coordinates converts the already constructed
diagonal real complex structure i*sgn to ordinary multiplication by i.
Positive coordinates retain their CM embedding; negative coordinates acquire
its complex conjugate. The finite equivalences below prove the exact fiber
cardinalities after the SAME reindexing to Fin(card(Psi)*N).

This is the explicit diagonal specialization of the coordinate conclusion in
Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/ToricGeometry/
ExistsEquivOfSumEq.lean, exists_diag_real. The source signature and type
predicate come from IsHolPeriods.lean, IsTypeFn, and the original negative
tail in src/Formalism/LocalRingCardinality/SpanPowerMembership/
BaseFormAnisotropicOrthogonalSingle.lean.
No diagonalization, multiplicity or spectral premise is introduced. The
source mirror states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical ComplexConjugate

namespace RHLean.Geometry.NativePeriodCoordinates

open NativePrescribedHermitian NativePolarizationComplexCoordinates

/-- Real-linear conjugation precisely in a negative coordinate. -/
def conjIf : Bool → ℂ ≃ₗ[ℝ] ℂ
  | false => LinearEquiv.refl ℝ ℂ
  | true => Complex.conjAe.toLinearEquiv

theorem conjIf_involutive (b : Bool) : Function.Involutive (conjIf b) := by
  cases b <;> intro z <;> simp [conjIf]

theorem conjIf_diagonalJ (b : Bool) (z : ℂ) :
    conjIf b (Complex.I * sgn b * z) = Complex.I * conjIf b z := by
  cases b <;> simp [conjIf, sgn]

variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))

/-- The one finite enumeration used by both coordinates and coefficient type. -/
def indexEquiv (N : ℕ) : (Ψ × Fin N) ≃ Fin (Ψ.card * N) :=
  (Fintype.equivFin (Ψ × Fin N)).trans
    (finCongr (by simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]))

/-- Negative-coordinate conjugation followed by the actual finite enumeration. -/
def coordinates (N q : ℕ) :
    (Ψ → Fin N → ℂ) ≃ₗ[ℝ] (Fin (Ψ.card * N) → ℂ) where
  toFun u s :=
    conjIf (negTail N q ((indexEquiv Ψ N).symm s).2)
      (u ((indexEquiv Ψ N).symm s).1 ((indexEquiv Ψ N).symm s).2)
  invFun v τ i := conjIf (negTail N q i) (v (indexEquiv Ψ N (τ, i)))
  left_inv u := by
    funext τ i
    simp only [Equiv.symm_apply_apply]
    exact conjIf_involutive _ _
  right_inv v := by
    funext s
    calc
      _ = v (indexEquiv Ψ N ((indexEquiv Ψ N).symm s)) :=
        conjIf_involutive _ _
      _ = v s := congrArg v ((indexEquiv Ψ N).apply_symm_apply s)
  map_add' u v := by
    funext s
    exact map_add (conjIf _) _ _
  map_smul' c u := by
    funext s
    exact (conjIf _).map_smul c _

theorem coordinates_apply (N q : ℕ) (u : Ψ → Fin N → ℂ)
    (s : Fin (Ψ.card * N)) :
    coordinates Ψ N q u s =
      conjIf (negTail N q ((indexEquiv Ψ N).symm s).2)
        (u ((indexEquiv Ψ N).symm s).1 ((indexEquiv Ψ N).symm s).2) := rfl

/-- The literal embedding on a signed row before finite reindexing. -/
def rawType (N q : ℕ) (s : Ψ × Fin N) : E →+* ℂ :=
  if N - q ≤ (s.2 : ℕ) then ComplexEmbedding.conjugate s.1.1 else s.1.1

def typeFn (N q : ℕ) (s : Fin (Ψ.card * N)) : E →+* ℂ :=
  rawType Ψ N q ((indexEquiv Ψ N).symm s)

/-- The actual diagonal coefficient action acquires the same embedding type
as the explicit coordinates, including every conjugated negative row. -/
theorem coordinates_mul (N q : ℕ) (a : E) (u : Ψ → Fin N → ℂ)
    (s : Fin (Ψ.card * N)) :
    coordinates Ψ N q (fun τ i => (τ : E →+* ℂ) a * u τ i) s =
      typeFn Ψ N q s a * coordinates Ψ N q u s := by
  let v := (indexEquiv Ψ N).symm s
  change conjIf (negTail N q v.2) ((v.1 : E →+* ℂ) a * u v.1 v.2) =
    (if N - q ≤ (v.2 : ℕ) then ComplexEmbedding.conjugate v.1.1 else v.1.1) a *
      conjIf (negTail N q v.2) (u v.1 v.2)
  by_cases hi : N - q ≤ (v.2 : ℕ)
  · rw [ite_eq_left hi, negTail_true N q v.2 hi]
    exact map_mul (starRingEnd ℂ) _ _
  · rw [ite_eq_right hi, negTail_false N q v.2 (lt_of_not_ge hi)]
    rfl

theorem coordinates_diagonalJ (N q : ℕ) (u : Ψ → Fin N → ℂ) :
    coordinates Ψ N q (blk (fun _ : Ψ => diagonalJ (negTail N q)) u) =
      Complex.I • coordinates Ψ N q u := by
  funext s
  simp only [coordinates_apply, blk_apply, diagonalJ_apply, Pi.smul_apply, smul_eq_mul]
  exact conjIf_diagonalJ _ _

section Fibers

variable (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)

include hΨ in
theorem rawType_eq_of_mem (N q : ℕ) (τ : E →+* ℂ) (hτ : τ ∈ Ψ)
    (s : Ψ × Fin N) :
    rawType Ψ N q s = τ ↔ s.1.1 = τ ∧ (s.2 : ℕ) < N - q := by
  by_cases hi : N - q ≤ (s.2 : ℕ)
  · rw [rawType, ite_eq_left hi]
    constructor
    · intro h
      exact False.elim (((hΨ s.1.1).mp s.1.2) (h.symm ▸ hτ))
    · rintro ⟨_, hl⟩
      exact False.elim ((not_lt_of_ge hi) hl)
  · rw [rawType, ite_eq_right hi]
    exact ⟨fun h => ⟨h, lt_of_not_ge hi⟩, And.left⟩

theorem rawType_eq_of_not_mem (N q : ℕ) (τ : E →+* ℂ) (hτ : τ ∉ Ψ)
    (s : Ψ × Fin N) :
    rawType Ψ N q s = τ ↔
      s.1.1 = ComplexEmbedding.conjugate τ ∧ N - q ≤ (s.2 : ℕ) := by
  by_cases hi : N - q ≤ (s.2 : ℕ)
  · rw [rawType, ite_eq_left hi]
    constructor
    · intro h
      exact ⟨by simpa using congrArg ComplexEmbedding.conjugate h, hi⟩
    · rintro ⟨h, _⟩
      rw [h]
      exact ComplexEmbedding.involutive_conjugate E τ
  · rw [rawType, ite_eq_right hi]
    constructor
    · intro h
      exact False.elim (hτ (h ▸ s.1.2))
    · rintro ⟨_, hl⟩
      exact False.elim (hi hl)

/-- A positive embedding's fiber is exactly the original positive prefix. -/
def positiveFiberEquiv (N q : ℕ) (τ : E →+* ℂ) (hτ : τ ∈ Ψ) :
    {s : Ψ × Fin N // rawType Ψ N q s = τ} ≃ Fin (N - q) where
  toFun s := ⟨s.1.2, ((rawType_eq_of_mem Ψ hΨ N q τ hτ s.1).mp s.2).2⟩
  invFun i := ⟨(⟨τ, hτ⟩, ⟨i, lt_of_lt_of_le i.2 (Nat.sub_le N q)⟩),
    (rawType_eq_of_mem Ψ hΨ N q τ hτ _).mpr ⟨rfl, i.2⟩⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext ((rawType_eq_of_mem Ψ hΨ N q τ hτ s.1).mp s.2).1.symm
    · apply Fin.ext
      rfl
  right_inv i := by
    apply Fin.ext
    rfl

/-- A negative embedding's fiber is exactly the original negative tail. -/
def negativeFiberEquiv (N q : ℕ) (hq : q ≤ N)
    (τ : E →+* ℂ) (hτ : τ ∉ Ψ) :
    {s : Ψ × Fin N // rawType Ψ N q s = τ} ≃ Fin q := by
  have hc : ComplexEmbedding.conjugate τ ∈ Ψ := by
    by_contra hn
    exact hτ ((hΨ τ).mpr hn)
  exact
    { toFun := fun s =>
        ⟨(s.1.2 : ℕ) - (N - q), by
          have h1 := ((rawType_eq_of_not_mem Ψ N q τ hτ s.1).mp s.2).2
          have h2 := s.1.2.2
          omega⟩
      invFun := fun i =>
        ⟨(⟨ComplexEmbedding.conjugate τ, hc⟩, ⟨N - q + i, by omega⟩),
          (rawType_eq_of_not_mem Ψ N q τ hτ _).mpr ⟨rfl, by
            change N - q ≤ N - q + (i : ℕ)
            omega⟩⟩
      left_inv := fun s => by
        apply Subtype.ext
        apply Prod.ext
        · exact Subtype.ext ((rawType_eq_of_not_mem Ψ N q τ hτ s.1).mp s.2).1.symm
        · apply Fin.ext
          change N - q + ((s.1.2 : ℕ) - (N - q)) = (s.1.2 : ℕ)
          have h1 := ((rawType_eq_of_not_mem Ψ N q τ hτ s.1).mp s.2).2
          exact Nat.add_sub_of_le h1
      right_inv := fun i => by
        apply Fin.ext
        change N - q + (i : ℕ) - (N - q) = (i : ℕ)
        exact Nat.add_sub_cancel_left _ _ }

include hΨ in
theorem typeFn_card_of_mem (N q : ℕ) (τ : E →+* ℂ) (hτ : τ ∈ Ψ) :
    Nat.card {i // typeFn Ψ N q i = τ} = N - q := by
  let e := (indexEquiv Ψ N).symm.subtypeEquivOfSubtype
    (p := fun s : Ψ × Fin N => rawType Ψ N q s = τ)
  exact (Nat.card_congr (e.trans (positiveFiberEquiv Ψ hΨ N q τ hτ))).trans
    (Nat.card_fin (N - q))

include hΨ in
theorem typeFn_card_of_not_mem (N q : ℕ) (hq : q ≤ N)
    (τ : E →+* ℂ) (hτ : τ ∉ Ψ) :
    Nat.card {i // typeFn Ψ N q i = τ} = q := by
  let e := (indexEquiv Ψ N).symm.subtypeEquivOfSubtype
    (p := fun s : Ψ × Fin N => rawType Ψ N q s = τ)
  exact (Nat.card_congr (e.trans (negativeFiberEquiv Ψ hΨ N q hq τ hτ))).trans
    (Nat.card_fin q)

end Fibers
end RHLean.Geometry.NativePeriodCoordinates

end
