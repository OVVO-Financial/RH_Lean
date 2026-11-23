import Mathlib

/-!
# Roots of unity and actual prime inertia

The primitive-root product makes the rational prime lie in a high power
of the prime ideal; the actual ideal multiplicity therefore bounds the
root order. A two-element inertia image bounds the ramification index.
These are the finite algebraic ingredients of the original norm-mu proof.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/MuCardLeTwo.lean`,
`Mu.{mu_le_ram,mu_mem_pow,mu_card_le_two}`;
`src/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean`,
`{odd_intCast_mem_iff,odd_card}`; and
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/KcEqOfPowEqOne.lean`, `kc_eq_of_pow_eq_one`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open NumberField IntermediateField Ideal

noncomputable section

namespace RHLean.Analysis.NativeRootOfUnityInertia

variable {L : Type} [Field L] [NumberField L]

theorem mu_le_ram (p : ℕ) [hp : Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (k : ℕ) (hk : ((p : ℤ) : 𝓞 L) ∈ Q ^ k) :
    k ≤ Q.ramificationIdx ℤ := by
  have hmap : Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) = span {((p : ℤ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, algebraMap_int_eq, eq_intCast]
  have hne0 : ((p : ℤ) : 𝓞 L) ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap (𝓞 L) L) h0
    have h2 : (p : L) = 0 := by simpa using h1
    exact hp.out.ne_zero (by exact_mod_cast h2)
  have hne : Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hne0
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (span {(p : ℤ)}) Q hne]
  have hdvd : Q ^ k ∣ Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) := by
    rw [Ideal.dvd_iff_le, hmap, Ideal.span_singleton_le_iff_mem]
    exact hk
  have hQ : ¬ IsUnit Q := by
    rw [Ideal.isUnit_iff]
    exact Ideal.IsPrime.ne_top ‹_›
  exact (FiniteMultiplicity.of_not_isUnit hQ hne).le_multiplicity_of_pow_dvd hdvd

omit [NumberField L] in
theorem mu_mem_pow (p : ℕ) [hp : Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (η : L) (hη : IsPrimitiveRoot η p) :
    ((p : ℤ) : 𝓞 L) ∈ Q ^ (p - 1) := by
  have hp0 : 0 < p := hp.out.pos
  have hint : IsIntegral ℤ η := hη.isIntegral hp0
  let η' : 𝓞 L := ⟨η, hint⟩
  have hmapη : algebraMap (𝓞 L) L η' = η := rfl
  have hinj : Function.Injective (algebraMap (𝓞 L) L) :=
    FaithfulSMul.algebraMap_injective (𝓞 L) L
  have hη' : IsPrimitiveRoot η' p := by
    refine ⟨hinj ?_, fun l hl => hη.dvd_of_pow_eq_one l ?_⟩
    · rw [map_pow, hmapη, map_one]
      exact hη.pow_eq_one
    · rw [← hmapη, ← map_pow, hl, map_one]
  have hprod : ((p : ℤ) : 𝓞 L) = ∏ μ ∈ primitiveRoots p (𝓞 L), (1 - μ) := by
    have h1 := Polynomial.eval_one_cyclotomic_prime (R := 𝓞 L) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hη', Polynomial.eval_prod] at h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
    rw [Int.cast_natCast, ← h1]
  have hmemQ : ((p : ℤ) : 𝓞 L) ∈ Q := by
    have hover : span {(p : ℤ)} = Ideal.under ℤ Q := Ideal.LiesOver.over
    have h1 : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [← hover]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap, algebraMap_int_eq, eq_intCast] at h1
    exact h1
  rw [hprod] at hmemQ
  obtain ⟨μ0, hμ0mem, hμ0Q⟩ : ∃ μ ∈ primitiveRoots p (𝓞 L), 1 - μ ∈ Q :=
    Ideal.IsPrime.prod_mem_iff.mp hmemQ
  have hall : ∀ μ ∈ primitiveRoots p (𝓞 L), 1 - μ ∈ Q := by
    intro μ hμ
    have hμ0p : IsPrimitiveRoot μ0 p := (mem_primitiveRoots hp0).mp hμ0mem
    have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp0).mp hμ
    have : NeZero p := ⟨hp.out.ne_zero⟩
    obtain ⟨i, -, hi⟩ := hμ0p.eq_pow_of_pow_eq_one hμp.pow_eq_one
    rw [← hi]
    have hd : 1 - μ0 ∣ 1 - μ0 ^ i := by simpa [one_pow] using sub_dvd_pow_sub_pow 1 μ0 i
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    exact Ideal.mul_mem_right c Q hμ0Q
  rw [hprod]
  have h2 := Ideal.prod_mem_prod (I := fun _ => Q) hall
  rw [Finset.prod_const, IsPrimitiveRoot.card_primitiveRoots hη', Nat.totient_prime hp.out] at h2
  exact h2

theorem mu_card_le_two {G : Type*} [One G] (f : Gal(L/ℚ) → G) (hinj : Function.Injective f)
    (t : G) (H : Subgroup Gal(L/ℚ)) (hH : ∀ ρ ∈ H, f ρ = 1 ∨ f ρ = t) : Nat.card H ≤ 2 := by
  classical
  let g : H → ({1, t} : Set G) := fun ρ => ⟨f ρ, by rcases hH ρ ρ.2 with h | h <;> simp [h]⟩
  have hg : Function.Injective g := fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))
  calc Nat.card H ≤ Nat.card ({1, t} : Set G) := Nat.card_le_card_of_injective g hg
    _ = ({1, t} : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ 2 := (Set.ncard_insert_le 1 {t}).trans (by simp)

omit [NumberField L] in
theorem intCast_mem_iff (p : ℕ) (P : Ideal (𝓞 L))
    [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 L) ∈ P ↔ (p : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}),
    Ideal.under_def, Ideal.mem_comap, eq_intCast]

theorem card_inertia [IsGalois ℚ L] (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (P.inertia (L ≃ₐ[ℚ] L)) = P.ramificationIdx ℤ := by
  have : IsGaloisGroup (L ≃ₐ[ℚ] L) ℤ (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(p : ℤ)} : Ideal ℤ).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  rw [card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (span {(p : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P (L ≃ₐ[ℚ] L)]

theorem eq_of_pow_eq_one {S : Type*} [CommRing S] [IsDomain S]
    (P : Ideal S) [hP : P.IsPrime] {m : ℕ} (hm : (m : S) ∉ P)
    {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y m
  rw [hx, hy, sub_self, mul_eq_zero, sub_eq_zero] at h1
  have h2 := congrArg (Ideal.Quotient.mk P) (h1.resolve_right hne)
  have h3 : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.mpr hxy
  rw [RingHom.map_geom_sum₂, h3, geom_sum₂_self, map_zero, ← map_pow,
    ← map_natCast (Ideal.Quotient.mk P), ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
  rcases hP.mem_or_mem h2 with h4 | h4
  · exact hm h4
  · have h5 : y ∈ P := hP.mem_of_pow_mem _ h4
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have h6 := P.pow_mem_of_mem h5 m (Nat.pos_of_ne_zero hm0)
    rw [hy] at h6
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h6)

end RHLean.Analysis.NativeRootOfUnityInertia

end
