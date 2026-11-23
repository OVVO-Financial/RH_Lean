import RHLean.Analysis.AlpogeNativeHostPrimes

/-!
# Actual decomposition groups of the native cyclotomic host

The stabilizer of a prime acts on its finite residue field by powers of
arithmetic Frobenius. The remaining factor acts trivially on the residue
field, so the already constructed native inertia theorem identifies it
with an actual modular unit. This gives the original decomposition
congruence on the SAME fixed field, also at conductor primes.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean`,
`Decomp.{frob_pow_mk,stab_frob_pow,stab_eq_inertia_mul}`, and
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/RootEqOfSubMem.lean`, `Der.decomp`.
The source archive/mirror states no license; this notice retains attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.NativePrimeDecomposition

theorem frob_pow_mk {M : Type} [Field M] [NumberField M] (p : ℕ)
    (Q : Ideal (𝓞 M)) [Q.LiesOver (span {(p : ℤ)})] (F : M ≃ₐ[ℚ] M)
    (hF : IsArithFrobAt ℤ F Q) (k : ℕ) (x : 𝓞 M) :
    Ideal.Quotient.mk Q ((F ^ k) • x) = (Ideal.Quotient.mk Q x) ^ (p ^ k) := by
  have hn : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ),
      Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have key : ∀ y : 𝓞 M, Ideal.Quotient.mk Q (F • y) = Ideal.Quotient.mk Q y ^ p := by
    intro y
    rw [← map_pow, Ideal.Quotient.eq, ← hn]
    exact hF y
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ' F k, mul_smul, key, ih, ← pow_mul, ← pow_succ p k]

/-- A decomposition automorphism induces an actual Frobenius power on the
finite residue field; no decomposition-group identification is assumed. -/
theorem stab_frob_pow {M : Type} [Field M] [NumberField M] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (F σ : M ≃ₐ[ℚ] M) (hF : IsArithFrobAt ℤ F Q)
    (hσ : σ ∈ MulAction.stabilizer (M ≃ₐ[ℚ] M) Q) :
    ∃ k : ℕ, ∀ x : 𝓞 M, σ • x - (F ^ k) • x ∈ Q := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hund : span {(p : ℤ)} = Q.under ℤ := Ideal.LiesOver.over
  have hQ0 : Q ≠ ⊥ := by
    intro hQ
    have h1 : (p : ℤ) ∈ Q.under ℤ := by
      rw [← hund]
      exact Ideal.mem_span_singleton_self _
    have h2 := Ideal.mem_comap.mp h1
    rw [hQ, Ideal.mem_bot] at h2
    exact hp.ne_zero (by simpa using h2)
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  let : Field (𝓞 M ⧸ Q) := Ideal.Quotient.field Q
  have : Finite (𝓞 M ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  have : CharP (𝓞 M ⧸ Q) p := by
    refine ⟨fun n => ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk Q) n, Ideal.Quotient.eq_zero_iff_mem]
    have e1 : (n : 𝓞 M) ∈ Q ↔ (n : ℤ) ∈ Q.under ℤ :=
      ⟨fun h => Ideal.mem_comap.mpr (by rwa [map_natCast]),
        fun h => by simpa using Ideal.mem_comap.mp h⟩
    rw [e1, ← hund, Ideal.mem_span_singleton]
    norm_cast
  let : Algebra (ZMod p) (𝓞 M ⧸ Q) := ZMod.algebra _ p
  have hσQ : Q ≤ Q.comap (MulSemiringAction.toRingHom _ (𝓞 M) σ) := by
    intro y hy
    rw [Ideal.mem_comap, MulSemiringAction.toRingHom_apply]
    have hσ' : σ • Q = Q := MulAction.mem_stabilizer_iff.mp hσ
    rw [← hσ', Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
    exact hy
  let sb : (𝓞 M ⧸ Q) →+* (𝓞 M ⧸ Q) :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ (𝓞 M) σ) hσQ
  let sa : (𝓞 M ⧸ Q) →ₐ[ZMod p] (𝓞 M ⧸ Q) :=
    { sb with
      commutes' := fun c => by
        change sb (algebraMap (ZMod p) _ c) = algebraMap (ZMod p) _ c
        rw [← ZMod.natCast_zmod_val c, map_natCast, map_natCast] }
  obtain ⟨⟨n, _⟩, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (𝓞 M ⧸ Q)).2 sa
  have hn' : FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ n = sa := hn
  have key : ∀ m : ℕ, ∀ y : 𝓞 M ⧸ Q,
      (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q) ^ m) y = y ^ (p ^ m) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        rw [pow_succ' (FiniteField.frobeniusAlgHom (ZMod p) (𝓞 M ⧸ Q)) m,
          AlgHom.mul_apply, ih, FiniteField.frobeniusAlgHom_apply, ZMod.card,
          ← pow_mul, ← pow_succ p m]
  refine ⟨n, fun x => ?_⟩
  rw [← Ideal.Quotient.eq]
  have h1 : sa (Ideal.Quotient.mk Q x) = Ideal.Quotient.mk Q (σ • x) := rfl
  rw [← h1, ← hn', key, frob_pow_mk p Q F hF n x]

theorem stab_eq_inertia_mul {M : Type} [Field M] [NumberField M]
    (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 M)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (F σ : M ≃ₐ[ℚ] M)
    (hF : IsArithFrobAt ℤ F Q) (hσ : σ ∈ MulAction.stabilizer (M ≃ₐ[ℚ] M) Q) :
    ∃ k : ℕ, ∃ ρ : M ≃ₐ[ℚ] M, (∀ x : 𝓞 M, ρ • x - x ∈ Q) ∧ σ = ρ * F ^ k := by
  obtain ⟨k, hk⟩ := stab_frob_pow p Q F σ hF hσ
  refine ⟨k, σ * (F ^ k)⁻¹, fun x => ?_, by simp⟩
  have hx := hk ((F ^ k)⁻¹ • x)
  rwa [smul_inv_smul, ← mul_smul] at hx

end RHLean.Analysis.NativePrimeDecomposition

namespace RHLean.Analysis

open NativeCyclotomicResidue NativePrimeDecomposition

/-- Actual prime-ideal decomposition is exactly the original residue-power
condition on the same native conductor and reciprocity map. -/
theorem alpogeNativeHostField_decomp_iff
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (l : ℕ) [Fact l.Prime]
    (P : Ideal (𝓞 (alpogeNativeHostField e q d)))
    [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    σ ∈ MulAction.stabilizer _ P ↔
      ∃ (u : (ZMod (alpogeNativeHostN e q d))ˣ) (k : ℕ),
        (u : ZMod (alpogeNativeHostN e q d)).val ≡
          l ^ k [MOD ordCompl[l] (alpogeNativeHostN e q d)] ∧
        alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ = alpogeNativeRecMap e q d u := by
  let w := alpogeNativeFrobUnit (alpogeNativeHostN e q d) l
  let F := (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
    (alpogeNativeRecMap e q d w)
  have hF : IsArithFrobAt ℤ F P :=
    alpogeNativeHostField_hostData_frob e q d hq2 hd2 hqd l P
  have hw : (w : ZMod (alpogeNativeHostN e q d)).val ≡
      l [MOD ordCompl[l] (alpogeNativeHostN e q d)] :=
    (alpogeNativeFrobUnit_modEq (Fact.out : l.Prime)).1
  have hFw : alpogeNativeHostGalEquiv e q d hq2 hd2 hqd F = alpogeNativeRecMap e q d w :=
    (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).apply_symm_apply _
  have hM := Nat.ordCompl_dvd (alpogeNativeHostN e q d) l
  rw [val_modEq_iff hM] at hw
  constructor
  · intro hσ
    obtain ⟨k, ρ, hρ, rfl⟩ := stab_eq_inertia_mul l P F σ hF hσ
    obtain ⟨u, hu, h1⟩ :=
      (alpogeNativeHostField_inertia_iff e q d hq2 hd2 hqd l P ρ).mp hρ
    refine ⟨u * w ^ k, k, ?_, ?_⟩
    · rw [val_modEq_one_iff hM] at hu
      rw [val_modEq_iff hM, map_mul, hu, one_mul, map_pow,
        Units.val_pow_eq_pow_val, hw, Nat.cast_pow]
    · rw [map_mul, map_mul, map_pow, map_pow, h1, hFw]
  · rintro ⟨u, k, hu, h1⟩
    have h2 : ∀ x : 𝓞 (alpogeNativeHostField e q d),
        (σ * (F ^ k)⁻¹) • x - x ∈ P := by
      rw [alpogeNativeHostField_inertia_iff e q d hq2 hd2 hqd l P]
      refine ⟨u * (w ^ k)⁻¹, ?_, ?_⟩
      · rw [val_modEq_iff hM] at hu
        have h3 : ZMod.unitsMap hM u = ZMod.unitsMap hM (w ^ k) :=
          Units.ext (by rw [hu, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow])
        rw [val_modEq_one_iff hM, map_mul, map_inv, h3, mul_inv_cancel]
      · rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, h1, hFw]
    have h4 := Subgroup.mul_mem _
      (NativePrimeLift.mem_stabilizer_of _ P
        (NativePrimeLift.smul_mem_of_inertia _ P h2))
      (Subgroup.pow_mem _ hF.mem_stabilizer k)
    rwa [inv_mul_cancel_right] at h4

end RHLean.Analysis

end
