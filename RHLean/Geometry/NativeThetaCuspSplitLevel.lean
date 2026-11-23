import RHLean.Analysis.AlpogeNativePrimeDecomposition
import RHLean.Analysis.AlpogeThin.NativeDyadicFixedAuxiliaryLevel
import RHLean.Analysis.AlpogeThin.NativeDyadicHostDifferent
import RHLean.Analysis.AlpogeThin.NativeDyadicHostFrobenius
import RHLean.Geometry.NativeThetaFullLevelCost

/-!
# A conjugate half of the fixed five-level on the actual native host

The arithmetic level required by the finite theta construction is an ideal
coprime to its conjugate. The rational ideal `(5)` itself is therefore not
that level. We prove that no prime above 5 is fixed by complex conjugation,
then construct a complementary pair of ideals whose product is exactly
`(5)`. The chosen half is proper, nonzero, and coprime to `(2)`.

The exclusion uses the actual Frobenius at 5: its dyadic coordinate is the
original class-of-five generator of order `2^e`. A power equal to complex
conjugation would have even exponent, contradicting either sign coordinate.
Trivial native inertia identifies the entire decomposition group with these
Frobenius powers. No splitting or prime-pairing premise is assumed.

The factor-pairing proof is the already native reconstruction of Levent
Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/KcPair.lean`, `pairing`. The immediate consumer is the
ideal part of `SW.Level` in
`src/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IsSystem.lean`.
The integral generator lifts use `card_levGrp_and_span` from
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardLevGrpAndSpan.lean`.
The present fixed-five specialization retains the exact rational product
and does not identify this level with a geometric moduli-level datum.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Ideal
open scoped Pointwise BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.SplitLevel

open RHLean.Analysis RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

/-- A prime above the fixed auxiliary prime is never fixed by the actual
complex conjugation of the native dyadic host. -/
theorem five_prime_ne_conj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(5 : ℤ)})],
      P ≠ H.conj • P := by
  intro H P _ _ hfix
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5N : ¬ 5 ∣ H.condN :=
    nativeDyadicFixedLevelFive_not_dvd_conductor e q d hH
  obtain ⟨⟨F, hF⟩, _, hfrob, hinertia⟩ :=
    nativeDyadicHostRaw_frob e q d he hH 5 h5N P
  have hstab : H.conj ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P := by
    rw [MulAction.mem_stabilizer_iff]
    exact hfix.symm
  obtain ⟨k, ρ, hρ, hconj⟩ :=
    NativePrimeDecomposition.stab_eq_inertia_mul 5 P F H.conj hF hstab
  rw [(hinertia ρ).mp hρ, one_mul] at hconj
  have hgal : (H.gal F) ^ k = (nativeDyadicFrame e).cc := by
    rw [← map_pow, ← hconj, NativeRawHostDifferent.gal_conj]
  obtain ⟨v, hv, hd⟩ := (hfrob F hF).2.2
  have hv5 : v = u5 (e + 2) := by
    apply Units.ext
    exact hv.trans (ZMod.coe_unitOfCoprime _ _).symm
  rw [hv5] at hd
  have hpow : (hcl e (u5 (e + 2))) ^ k = 1 := by
    have hh := congrArg (fun a : (nativeDyadicFrame e).GG =>
      (nativeDyadicFrame e).hH a.2) hgal
    simpa only [Prod.snd_pow, map_pow, hd, Frame.cc, map_one] using hh
  have hord : orderOf (hcl e (u5 (e + 2))) = 2 ^ e :=
    nativeDyadicGenerator_order e
  have hdiv : 2 ^ e ∣ k := hord ▸ orderOf_dvd_of_pow_eq_one hpow
  have hEven : Even k := even_iff_two_dvd.mpr
    ((dvd_pow_self 2 (by omega : e ≠ 0)).trans hdiv)
  have hsign : (((H.gal F).1.2 : ℤˣ) : ℤ) ^ k = -1 := by
    have hs := congrArg (fun a : (nativeDyadicFrame e).GG =>
      ((a.1.2 : ℤˣ) : ℤ)) hgal
    simpa only [Prod.fst_pow, Prod.snd_pow, Units.val_pow_eq_pow_val,
      Frame.cc, c0, Units.val_neg, Units.val_one] using hs
  rcases Int.units_eq_one_or (H.gal F).1.2 with hs | hs
  · simp [hs] at hsign
  · simp [hs, hEven.neg_one_pow] at hsign

private theorem liesOver_five_of_dvd
    {M : Type} [Field M] [NumberField M]
    (P : Ideal (𝓞 M)) [P.IsPrime]
    (hP : P ∣ span {(5 : 𝓞 M)}) : P.LiesOver (span {(5 : ℤ)}) := by
  have h5 : (5 : 𝓞 M) ∈ P :=
    (Ideal.dvd_iff_le.mp hP) (Ideal.mem_span_singleton_self _)
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    norm_num at h5
  obtain ⟨l, hl, hlo⟩ := NativePrimeLift.exists_prime_liesOver P hP0
  have hcast : (5 : ℤ) ∈ P.under ℤ := by
    change algebraMap ℤ (𝓞 M) (5 : ℤ) ∈ P
    simpa only [map_ofNat] using h5
  rw [← hlo.over, Ideal.mem_span_singleton] at hcast
  have hdiv : l ∣ 5 := by exact_mod_cast hcast
  have hl5 : l = 5 := (Nat.prime_dvd_prime_iff_eq hl (by norm_num)).mp hdiv
  subst l
  exact hlo

private theorem five_span_ne_top (M : Type) [Field M] [NumberField M] :
    span {(5 : 𝓞 M)} ≠ ⊤ := by
  intro htop
  have h1 := congrArg Ideal.absNorm htop
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top,
    ← map_natCast (algebraMap ℤ (𝓞 M)) 5,
    Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h1
  rcases Nat.pow_eq_one.mp h1 with h | h
  · norm_num at h
  · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 M)).ne' h

/-- Construct a genuine conjugate half of the original fixed five-level.
Its product with its conjugate is the same rational ideal `(5)`, preserving
the level scale used by the native finite-congruence calculation. -/
theorem exists_five_split_level
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ m : Ideal (𝓞 H.E),
      m ≠ ⊤ ∧ m ≠ ⊥ ∧ IsCoprime m (H.conj • m) ∧
      IsCoprime m (span {(2 : 𝓞 H.E)}) ∧
      m * (H.conj • m) = span {(5 : 𝓞 H.E)} := by
  intro H
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 H.E) ≃* Ideal (𝓞 H.E),
      ∀ I, f I = H.conj • I :=
    ⟨(MulSemiringAction.toRingEquiv _ (Ideal (𝓞 H.E)) H.conj).toMulEquiv,
      fun _ => rfl⟩
  have hD0 : span {(5 : 𝓞 H.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  have hfD : f (span {(5 : 𝓞 H.E)}) = span {(5 : 𝓞 H.E)} := by
    rw [hf, Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton, map_ofNat]
  have hcc : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I := fun I => by
    rw [← mul_smul, NativeRawHostDifferent.conj_sq, one_smul]
  let part : Ideal (𝓞 H.E) → Prop := fun P => WellOrderingRel P (H.conj • P)
  have hpart : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
      (span {(5 : 𝓞 H.E)}), part (f P) ↔ ¬ part P := by
    intro P hP
    let : P.IsPrime := Ideal.isPrime_of_prime
      (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    let : P.LiesOver (span {(5 : ℤ)}) := liesOver_five_of_dvd P
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
    have hne := five_prime_ne_conj e q d he hH P
    change WellOrderingRel (f P) (H.conj • f P) ↔
      ¬ WellOrderingRel P (H.conj • P)
    rw [hf, hcc]
    constructor
    · intro h1 h2
      exact asymm h1 h2
    · intro h1
      rcases trichotomous_of WellOrderingRel P (H.conj • P) with h | h | h
      · exact absurd h h1
      · exact absurd h hne
      · exact h
  obtain ⟨m, hprod, _, hcop, _, _⟩ :=
    NativeDifferentPairing.pairing _ hD0 f hfD part hpart
  rw [hf] at hprod hcop
  have hm0 : m ≠ ⊥ := by
    intro hm
    apply hD0
    rw [hprod, hm, Ideal.bot_mul]
  have hmtop : m ≠ ⊤ := by
    intro hm
    apply five_span_ne_top H.E
    rw [hprod, hm]
    change (1 : Ideal (𝓞 H.E)) * (H.conj • (1 : Ideal (𝓞 H.E))) = 1
    rw [smul_one, mul_one]
  have h5m : (5 : 𝓞 H.E) ∈ m := by
    apply (show span {(5 : 𝓞 H.E)} ≤ m from by
      rw [hprod]
      exact Ideal.mul_le_left)
    exact Ideal.mem_span_singleton_self _
  have hmodd : IsCoprime m (span {(2 : 𝓞 H.E)}) := by
    rw [Ideal.isCoprime_iff_exists]
    refine ⟨5, h5m, -4, ?_, by norm_num⟩
    rw [Ideal.mem_span_singleton]
    exact ⟨-2, by norm_num⟩
  exact ⟨m, hmtop, hm0, Ideal.isCoprime_iff_sup_eq.mpr hcop, hmodd, hprod.symm⟩

/-- Lift a basis of the actual finite projective quotient to integral
generators. No basis of the original projective module is required. -/
theorem exists_generators_mod (O M : Type) [CommRing O] [IsDomain O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)]
    (r : ℕ) (hr : Module.finrank O M = r) :
    ∃ β : Fin r → M,
      Submodule.span O (Set.range β) ⊔ (I • ⊤ : Submodule O M) = ⊤ := by
  classical
  obtain ⟨e1⟩ := NativeThetaFullLevelCost.nonempty_equiv_mod O M I r hr
  choose β hβ using fun i =>
    Submodule.Quotient.mk_surjective _ (e1.symm (Pi.single i 1))
  refine ⟨β, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, eq_top_iff]
  intro z _
  choose c hc using fun i => Ideal.Quotient.mk_surjective (e1 z i)
  refine ⟨∑ i, c i • β i, Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), e1.injective ?_⟩
  simp only [map_sum, map_smul, Submodule.mkQ_apply, hβ, LinearEquiv.apply_symm_apply]
  ext j
  rw [Finset.sum_apply,
    Finset.sum_eq_single j (fun i _ hi => by simp [hi.symm]) (by simp), ← hc]
  simp [Algebra.smul_def]

/-- The same original inverse-half-different lattice has integral
generators modulo the constructed conjugate half of `(5)`. Both the ideal
and the generators are constructed; the full projective lattice is retained. -/
theorem exists_five_split_level_generators
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (B : Ideal (𝓞 H.E))
      (_hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ),
      ∃ m : Ideal (𝓞 H.E),
        m ≠ ⊤ ∧ m ≠ ⊥ ∧ IsCoprime m (H.conj • m) ∧
        IsCoprime m (span {(2 : 𝓞 H.E)}) ∧
        m * (H.conj • m) = span {(5 : 𝓞 H.E)} ∧
        ∃ β : Fin N → NativeRawHostPolarization.twistedLattice H B N,
          Submodule.span (𝓞 H.E) (Set.range β) ⊔
            (m • ⊤ : Submodule (𝓞 H.E)
              (NativeRawHostPolarization.twistedLattice H B N)) = ⊤ := by
  intro H B hB N
  obtain ⟨m, hmtop, hm0, hcop, hodd, hprod⟩ := exists_five_split_level e q d he hH
  let := NativeRawHostPolarization.twistedLattice_finite H B N
  let := NativeRawHostPolarization.twistedLattice_projective H B N
  let : Finite (𝓞 H.E ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot _ hm0
  exact ⟨m, hmtop, hm0, hcop, hodd, hprod,
    exists_generators_mod (𝓞 H.E) (NativeRawHostPolarization.twistedLattice H B N)
      m N (NativeRawHostPolarization.twistedLattice_rank H B hB N)⟩

end RHLean.Geometry.NativeTheta.Cusp.SplitLevel
