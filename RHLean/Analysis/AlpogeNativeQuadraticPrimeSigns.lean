import RHLean.Analysis.AlpogeNativeRootOfUnityInertia

/-!
# Actual residue signs and dyadic splitting for a quadratic root

These elementary prime-local proofs use the actual root in the given number
field. The odd Frobenius sign is Euler's criterion in the residue ring. At
2, the integral half-root and stability of the prime rule out the negative
sign when the radicand is 1 modulo 8.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean`,
`odd_frob_sgn` and its used helpers; `CentralOrderTwo/DecompositionSubgroupIndex.lean`,
`stab_fix`, with its actual proof from
`src/Lemmata/GeneralBFactRightTerForm/Imports.lean`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open NumberField Ideal
open scoped Pointwise

noncomputable section

namespace RHLean.Analysis.NativeQuadraticPrimeSigns

open Classical in
def sgn {L : Type*} [Field L] [Algebra ℚ L] (σ : L ≃ₐ[ℚ] L) (x : L) : ℤˣ :=
  if σ x = x then 1 else -1

theorem odd_card_under {L : Type} [Field L] [NumberField L] (p : ℕ)
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.over_def P (span {(p : ℤ)}), Int.card_ideal_quot]

theorem odd_coe_smul {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (X : 𝓞 L) :
    ((σ • X : 𝓞 L) : L) = σ (X : L) := rfl

theorem odd_sgn_spec {L : Type} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) (c : ℤ)
    (hx : x ^ 2 = (c : L)) : σ x = (((sgn σ x : ℤˣ) : ℤ) : L) * x := by
  unfold sgn
  split_ifs with h
  · simp [h]
  · have h2 : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
    have : (σ x - x) * (σ x + x) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') h
    · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      linear_combination h'

theorem odd_lift {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ) (hx : x ^ 2 = (c : L)) :
    ∃ X : 𝓞 L, (X : L) = x ∧ X ^ 2 = (c : 𝓞 L) := by
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx, ← eq_intCast (algebraMap ℤ L)]
    exact isIntegral_algebraMap
  refine ⟨⟨x, hint⟩, rfl, ?_⟩
  apply RingOfIntegers.coe_injective
  simp only [map_intCast]
  exact hx

theorem odd_smul_lift {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (x : L) (c : ℤ)
    (hx : x ^ 2 = (c : L)) (X : 𝓞 L) (hX : (X : L) = x) :
    σ • X = (((sgn σ x : ℤˣ) : ℤ) : 𝓞 L) * X := by
  apply RingOfIntegers.coe_injective
  show ((σ • X : 𝓞 L) : L) = ((((sgn σ x : ℤˣ) : ℤ) : 𝓞 L) * X : 𝓞 L)
  rw [odd_coe_smul, hX, odd_sgn_spec σ x c hx]
  simp [hX]

theorem odd_frob_sgn {L : Type} [Field L] [NumberField L] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(L/ℚ))
    (H : IsArithFrobAt ℤ σ P) (x : L) (c : ℤ) (hx : x ^ 2 = (c : L)) (hpc : ¬ (p : ℤ) ∣ c) :
    ((sgn σ x : ℤˣ) : ℤ) = jacobiSym c p := by
  have hp : p.Prime := Fact.out
  have hmem := NativeRootOfUnityInertia.intCast_mem_iff p P
  have hF : ∀ y : 𝓞 L, σ • y - y ^ p ∈ P := by
    intro y
    have := H y
    rw [odd_card_under p P] at this
    exact this
  obtain ⟨A, hAcoe, hA2⟩ := odd_lift x c hx
  have hσA := odd_smul_lift σ x c hx A hAcoe
  have hAnot : A ∉ P := by
    intro hA
    apply hpc
    rw [← hmem, ← hA2]
    exact P.pow_mem_of_mem hA 2 (by norm_num)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hpow : A ^ p = A * (c : 𝓞 L) ^ (p / 2) := by
    rw [← hA2, ← pow_mul, ← pow_succ']
    congr 1
    omega
  have hE : (p : ℤ) ∣ c ^ (p / 2) - legendreSym p c := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, legendreSym.eq_pow]
    push_cast
    rfl
  have hE' : (c : 𝓞 L) ^ (p / 2) - ((legendreSym p c : ℤ) : 𝓞 L) ∈ P := by
    have := (hmem _).mpr hE
    push_cast at this
    exact this
  have hprod : ((((sgn σ x : ℤˣ) : ℤ) - legendreSym p c : ℤ) : 𝓞 L) * A ∈ P := by
    have heq : ((((sgn σ x : ℤˣ) : ℤ) - legendreSym p c : ℤ) : 𝓞 L) * A =
        (σ • A - A ^ p) + A * ((c : 𝓞 L) ^ (p / 2) - ((legendreSym p c : ℤ) : 𝓞 L)) := by
      rw [hσA, hpow]
      push_cast
      ring
    rw [heq]
    exact P.add_mem (hF A) (P.mul_mem_left A hE')
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hbad : ∀ n : ℤ, (n = 2 ∨ n = -2) → ¬ (p : ℤ) ∣ n := by
    rintro n (rfl | rfl) h
    · have := Int.le_of_dvd (by norm_num) h
      have := hp.two_le
      omega
    · have := Int.le_of_dvd (by norm_num) (dvd_neg.mpr h)
      have := hp.two_le
      omega
  rcases (inferInstance : P.IsPrime).mem_or_mem hprod with h | h
  · rw [hmem] at h
    have hL := legendreSym.eq_one_or_neg_one p (a := c)
      (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpc)
    rcases Int.units_eq_one_or (sgn σ x) with h1 | h1 <;>
      simp only [h1, Units.val_one, Units.val_neg] at h ⊢ <;>
      rcases hL with h2 | h2 <;> rw [h2] at h ⊢ <;>
      exact absurd h (hbad _ (by norm_num))
  · exact absurd h hAnot

theorem stab_fix {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * (2 * c) + 1 : ℤ) : L))
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (σ : L ≃ₐ[ℚ] L) (hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) P) : σ x = x := by
  have hsq : (σ x) ^ 2 = x ^ 2 := by
    rw [← map_pow, hx, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  exfalso
  have hx' : x ^ 2 = 8 * (c : L) + 1 := by rw [hx]; push_cast; ring
  have hint : IsIntegral ℤ ((1 + x) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C (2 * c), ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      simp only [eq_intCast, Int.cast_mul, Int.cast_ofNat]
      linear_combination hx' / 4
  let y : NumberField.RingOfIntegers L := ⟨(1 + x) / 2, hint⟩
  have hy : algebraMap (NumberField.RingOfIntegers L) L y = (1 + x) / 2 := rfl
  have h2 : (2 : NumberField.RingOfIntegers L) ∈ P := by
    have h0 := (Ideal.mem_of_liesOver P (Ideal.span {(2 : ℤ)}) (2 : ℤ)).mp
      (Ideal.subset_span rfl)
    simpa using h0
  have hprod : y * (y - 1) = 2 * (c : NumberField.RingOfIntegers L) := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (NumberField.RingOfIntegers L) L (y * (y - 1)) =
      algebraMap (NumberField.RingOfIntegers L) L (2 * (c : NumberField.RingOfIntegers L))
    rw [map_mul, map_sub, map_one, map_mul, map_ofNat, map_intCast, hy]
    linear_combination hx' / 4
  have hmem : y * (y - 1) ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ h2
  have hσP : Ideal.map (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (NumberField.RingOfIntegers L) σ) P
      = P := hσ
  have key : ∀ a ∈ P, σ • a ∈ P := fun a ha => by
    have h3 := Ideal.mem_map_of_mem
      (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (NumberField.RingOfIntegers L) σ) ha
    rw [hσP] at h3
    exact h3
  have hσy : σ • y = 1 - y := by
    apply NumberField.RingOfIntegers.ext
    change σ (algebraMap (NumberField.RingOfIntegers L) L y) =
      algebraMap (NumberField.RingOfIntegers L) L (1 - y)
    rw [map_sub, map_one, hy, map_div₀, map_add, map_one, h, map_ofNat]
    ring
  have h1 : (1 : NumberField.RingOfIntegers L) ∈ P := by
    rcases hP.mem_or_mem hmem with h' | h'
    · have h4 := key y h'
      rw [hσy] at h4
      have e : (1 : NumberField.RingOfIntegers L) = (1 - y) + y := by ring
      rw [e]
      exact P.add_mem h4 h'
    · have h4 := key _ h'
      rw [smul_sub, hσy, smul_one] at h4
      have e : (1 : NumberField.RingOfIntegers L) = -((1 - y - 1) + (y - 1)) := by ring
      rw [e]
      exact P.neg_mem (P.add_mem h4 h')
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

end RHLean.Analysis.NativeQuadraticPrimeSigns

end
