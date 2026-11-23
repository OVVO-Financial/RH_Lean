import RHLean.Analysis.AlpogeNativeDifferentPairing
import RHLean.Analysis.AlpogeThin.NativeRawHostDifferent
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRamifiedPrimes

/-!
# Construct the original conjugate half of the native relative different

The base field is the literal `HostRaw.K = ℚ(sqrt(-d))` inside the same
constructed native field. Actual inertia proves the relative different is
supported above the dyadic-and-q conductor. Actual type-I decomposition
then separates the contractions of a prime and its conjugate. The original
normalized-factor pairing constructs an ideal whose conjugate gives the
complementary different factors, with coprime support and the required
quadratic-subfield invariance. Its inverse has the original trace duality.

No `HostDer`, different-support premise, prime partition, half-ideal witness,
or trace-duality premise is assumed for the native host.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/KcBase.lean`, the K-fixing lemmas; `KcDiff.lean`,
`Der.{kc_below_smul,diffSupport,kc_below_ne,principal}`; and
`KcDiffSmulMem.lean`, `Der.unimodular`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

namespace NativeRawHostDifferent

variable {φ : Frame} (H : HostRaw φ)

theorem sqd_mem_K : H.sqd ∈ H.K := by
  unfold HostRaw.K
  exact IntermediateField.mem_adjoin_simple_self ℚ H.sqd

theorem restrict_mem_Psi (σ : H.E ≃ₐ[H.K] H.E) :
    H.gal (σ.restrictScalars ℚ) ∈ φ.Psi := by
  rw [NativeRawHostCore.gal_mem_Psi_iff]
  exact σ.commutes ⟨H.sqd, sqd_mem_K H⟩

theorem fix_K (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ ∈ φ.Psi) (x : H.K) :
    σ (x : H.E) = x := by
  have hs : H.sqd ∈
      IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf => hf
  have hle : H.K ≤
      IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) := by
    unfold HostRaw.K
    exact IntermediateField.adjoin_simple_le_iff.mpr hs
  have hx := hle x.2
  rw [IntermediateField.mem_fixedField_iff] at hx
  exact hx σ ((NativeRawHostCore.gal_mem_Psi_iff H σ).mp hσ)

theorem cc_not_mem_Psi : φ.cc ∉ φ.Psi := by
  simp only [Frame.Psi, MonoidHom.mem_ker, Frame.chD, Frame.cc, c0,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]
  decide

theorem iod_not_mem_Psi : φ.iod ∉ φ.Psi := by
  simp only [Frame.Psi, MonoidHom.mem_ker, Frame.chD, Frame.iod,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]
  decide

theorem gal_conj : H.gal H.conj = φ.cc := H.gal.apply_symm_apply _

theorem conj_sq : H.conj * H.conj = 1 := by
  apply H.gal.injective
  rw [map_mul, gal_conj, map_one]
  ext <;> simp [Frame.cc, c0]

abbrev below (P : Ideal (𝓞 H.E)) : Ideal (𝓞 H.K) :=
  P.comap (algebraMap (𝓞 H.K) (𝓞 H.E))

theorem below_smul (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ ∈ φ.Psi)
    (P : Ideal (𝓞 H.E)) : below H (σ • P) = below H P := by
  ext a
  simp only [below, Ideal.mem_comap]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hσ' : H.gal σ⁻¹ ∈ φ.Psi := by
    rw [map_inv]
    exact inv_mem hσ
  have heq : σ⁻¹ • algebraMap (𝓞 H.K) (𝓞 H.E) a =
      algebraMap (𝓞 H.K) (𝓞 H.E) a := by
    apply RingOfIntegers.ext
    show σ⁻¹ ((a : H.K) : H.E) = ((a : H.K) : H.E)
    exact fix_K H σ⁻¹ hσ' (a : H.K)
  rw [heq]

end NativeRawHostDifferent

private theorem nativePrime_liesOver_dvd_of_mem
    {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [P.IsPrime]
    (a : ℕ) (ha : a ≠ 0) (hm : (a : 𝓞 M) ∈ P) :
    ∃ l : ℕ, l.Prime ∧ l ∣ a ∧ P.LiesOver (span {(l : ℤ)}) := by
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact ha (by simpa only [Ideal.mem_bot, Nat.cast_eq_zero] using hm)
  obtain ⟨l, hl, hlo⟩ := NativePrimeLift.exists_prime_liesOver P hP0
  have hcast : (a : ℤ) ∈ P.under ℤ := by
    change algebraMap ℤ (𝓞 M) (a : ℤ) ∈ P
    simpa only [map_intCast, Int.cast_natCast] using hm
  rw [← hlo.over, Ideal.mem_span_singleton] at hcast
  exact ⟨l, hl, by exact_mod_cast hcast, hlo⟩

/-- The original relative different over the actual quadratic subfield has
support only above the dyadic-and-q factor. -/
theorem nativeDyadicHostRaw_diffSupport
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ P : Ideal (𝓞 H.E), P.IsPrime →
      P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) → ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P := by
  intro H P hP hdvd
  let : P.IsPrime := hP
  let : IsGalois ℚ H.E := H.galois
  let : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  by_contra hnot
  refine NativeDifferentPairing.not_dvd_different_of_trivial_inertia H.K H.E P ?_ hdvd
  intro hP0 σ hσ
  obtain ⟨l, hl, hlo⟩ := NativePrimeLift.exists_prime_liesOver P hP0
  let : Fact l.Prime := ⟨hl⟩
  let : P.LiesOver (span {(l : ℤ)}) := hlo
  have hlP : (l : 𝓞 H.E) ∈ P := by
    have h1 : (l : ℤ) ∈ P.under ℤ := by
      rw [← hlo.over]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
  have hlq : ¬ l ∣ H.QS * H.q := by
    rintro ⟨m, hm⟩
    apply hnot
    rw [hm, Nat.cast_mul]
    exact P.mul_mem_right _ hlP
  obtain ⟨u, hu, hgal⟩ :=
    (nativeDyadicHostRaw_inertia e q d he hH l P (σ.restrictScalars ℚ)).mp fun x => hσ x
  have hmod : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] :=
    hu.of_dvd (Nat.dvd_ordCompl_of_dvd_not_dvd (dvd_mul_right (H.QS * H.q) H.d) hlq)
  rcases H.art_d u hmod with h1 | h1
  · have h2 : σ.restrictScalars ℚ = 1 := H.gal.injective (by rw [hgal, h1, map_one])
    ext x
    exact congrArg (fun τ : H.E ≃ₐ[ℚ] H.E => τ x) h2
  · exfalso
    have hpsi := NativeRawHostDifferent.restrict_mem_Psi H σ
    rw [hgal, h1] at hpsi
    exact NativeRawHostDifferent.iod_not_mem_Psi hpsi

/-- Prime contractions to the original quadratic subfield separate each
different-support prime from its actual complex conjugate. -/
theorem nativeDyadicHostRaw_below_ne_conj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime],
      ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P →
        NativeRawHostDifferent.below H P ≠ NativeRawHostDifferent.below H (H.conj • P) := by
  intro H P hP hm heq
  let : P.IsPrime := hP
  let : IsGalois ℚ H.E := H.galois
  let : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  have hA0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' H.hyp.1.ne_zero
  obtain ⟨l, hl, hlA, hlo⟩ := nativePrime_liesOver_dvd_of_mem P (H.QS * H.q) hA0 hm
  let : P.LiesOver (span {(l : ℤ)}) := hlo
  let : P.LiesOver (NativeRawHostDifferent.below H P) := ⟨rfl⟩
  let : (H.conj • P).LiesOver (NativeRawHostDifferent.below H P) := ⟨heq⟩
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isGaloisGroup
    (NativeRawHostDifferent.below H P) P (H.conj • P) (H.E ≃ₐ[H.K] H.E)
  have hτ' : (τ.restrictScalars ℚ) • P = H.conj • P := hτ
  have hst : (τ.restrictScalars ℚ)⁻¹ * H.conj ∈
      MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hτ', inv_smul_smul]
  have hpsi := nativeDyadicHostRaw_decomp_typeI e q d he hH l hl hlA P _ hst
  rw [map_mul, map_inv,
    Subgroup.mul_mem_cancel_left _ (inv_mem (NativeRawHostDifferent.restrict_mem_Psi H τ)),
    NativeRawHostDifferent.gal_conj] at hpsi
  exact NativeRawHostDifferent.cc_not_mem_Psi hpsi

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Construct the actual conjugate half of the relative different, including
coprimality and invariance under the original CM-type subgroup. -/
theorem nativeDyadicHostRaw_principal
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ B : Ideal (𝓞 H.E),
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B) ∧
      B ⊔ H.conj • B = ⊤ ∧
      ∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B := by
  let H := nativeDyadicHostRaw e q d he hH
  let : IsGalois ℚ H.E := H.galois
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, f I = H.conj • I :=
    ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) H.conj).toMulEquiv, fun _ => rfl⟩
  have hD0 : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hfD : f (differentIdeal (𝓞 H.K) (𝓞 H.E)) = differentIdeal (𝓞 H.K) (𝓞 H.E) := by
    rw [hf]
    exact NativeRawHostDifferent.kc_diff_smul_eq H H.conj
  have hcc : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I := fun I => by
    rw [← mul_smul, NativeRawHostDifferent.conj_sq, one_smul]
  let part : Ideal (𝓞 H.E) → Prop := fun P =>
    WellOrderingRel (NativeRawHostDifferent.below H P)
      (NativeRawHostDifferent.below H (H.conj • P))
  have hpart : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
      (differentIdeal (𝓞 H.K) (𝓞 H.E)), (part (f P) ↔ ¬ part P) := by
    intro P hP
    have hPp : P.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    let : P.IsPrime := hPp
    have hPd : P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hne := nativeDyadicHostRaw_below_ne_conj e q d he hH P
      (nativeDyadicHostRaw_diffSupport e q d he hH P hPp hPd)
    show WellOrderingRel (NativeRawHostDifferent.below H (f P))
      (NativeRawHostDifferent.below H (H.conj • f P)) ↔
      ¬ WellOrderingRel (NativeRawHostDifferent.below H P)
        (NativeRawHostDifferent.below H (H.conj • P))
    rw [hf, hcc]
    constructor
    · intro h1 h2
      exact asymm h1 h2
    · intro h1
      rcases trichotomous_of WellOrderingRel (NativeRawHostDifferent.below H P)
          (NativeRawHostDifferent.below H (H.conj • P)) with h | h | h
      · exact absurd h h1
      · exact absurd h hne
      · exact h
  obtain ⟨B, hB, _, hBtop, hinv, _⟩ :=
    NativeDifferentPairing.pairing _ hD0 f hfD part hpart
  refine ⟨B, ?_, ?_, fun σ hσ => ?_⟩
  · rw [← hf]
    exact hB
  · rw [← hf]
    exact hBtop
  · obtain ⟨g, hg⟩ : ∃ g : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E), ∀ I, g I = σ • I :=
      ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) σ).toMulEquiv, fun _ => rfl⟩
    rw [← hg]
    refine hinv g (by rw [hg]; exact NativeRawHostDifferent.kc_diff_smul_eq H σ) fun P _ => ?_
    have hn : H.gal (H.conj * σ * H.conj⁻¹) ∈ (nativeDyadicFrame e).Psi := by
      have hσ' : (nativeDyadicFrame e).chD (H.gal σ) = 1 := hσ
      show (nativeDyadicFrame e).chD (H.gal (H.conj * σ * H.conj⁻¹)) = 1
      simp only [map_mul, map_inv, hσ', mul_one, mul_inv_cancel]
    have heq : (H.conj * σ * H.conj⁻¹) • H.conj • P = H.conj • σ • P := by
      rw [← mul_smul, inv_mul_cancel_right, mul_smul]
    show WellOrderingRel (NativeRawHostDifferent.below H (g P))
      (NativeRawHostDifferent.below H (H.conj • g P)) ↔
      WellOrderingRel (NativeRawHostDifferent.below H P)
        (NativeRawHostDifferent.below H (H.conj • P))
    rw [hg, NativeRawHostDifferent.below_smul H σ hσ P, ← heq,
      NativeRawHostDifferent.below_smul H _ hn]

/-- The original trace-duality clause, for any factorization witness on this
actual field; the preceding theorem constructs such a witness. -/
theorem nativeDyadicHostRaw_unimodular
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ B : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B) →
      ∀ x : H.E, x ∈ ((B : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
        ∀ y ∈ ((B : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
          Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range :=
  NativeRawHostDifferent.unimodular (nativeDyadicHostRaw e q d he hH)

/-- One actual ideal simultaneously supplies the different factorization,
coprimality, type-subgroup invariance and original trace duality. -/
theorem nativeDyadicHostRaw_exists_traceSelfDualIdeal
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ B : Ideal (𝓞 H.E),
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B) ∧
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ x : H.E, x ∈ ((B : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
        ∀ y ∈ ((B : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
          Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range := by
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  exact ⟨B, hB, hcop, hinv, nativeDyadicHostRaw_unimodular e q d he hH B hB⟩

end RHLean.Analysis.AlpogeThin

end
