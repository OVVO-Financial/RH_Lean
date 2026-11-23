import RHLean.Analysis.AlpogeThin.NativeRayIdealCounts

/-!
# Complete prime-power mass for the actual ray ideal source

For any number field, the total ideal von Mangoldt mass at a fixed integer
norm is at most the field degree times the ordinary von Mangoldt weight.
The proof retains every prime-power exponent and every residue degree.
It uses no unramified or splitting assumption: distinct prime radicals
are coprime and their product divides the rational prime ideal.

The same bound then applies to the disjoint actual ray-class fibres.
For the constructed degree-two field this supplies the original 2*Lambda(n)
budget, including ramified primes and all prime powers.

Source guide: Levent Alpöge's archive, inspected mirror pin
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4;
`Proofs/IwasawaDecomposition/ExistsPrimeMemHeightOneSpectrum.lean` and
`Proofs/GlobalInterpolation/SumLamIdealLe.lean` beneath
`src/Development/AbelianVarietyTheory/`. The proof is reconstructed in the
native namespace and generalized from degree two to every number-field degree.
No terminal theorem, count bound, or external compiled object is imported.
The inspected mirror states no license; attribution assigns none.
-/

noncomputable section
open NumberField ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt BigOperators Classical

namespace RHLean.Analysis.AlpogeThin.NativeRay.PrimePowerMass

theorem exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using hmem))
    have hpr : Nat.Prime n.minFac := Nat.minFac_prime h1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hmul : ((n.minFac : R) * (m : R)) ∈ P := by
      rw [← Nat.cast_mul, ← hm]; exact hmem
    rcases hP.mem_or_mem hmul with h | h
    · exact ⟨_, hpr, h⟩
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
      have hlt : m < n := by
        rw [hm]
        have := hpr.two_le
        calc m = 1 * m := (one_mul m).symm
          _ < n.minFac * m := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
      exact ih m hlt hm0 h

theorem exists_prime_mem_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  haveI := v.isPrime
  exact exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)

variable {K : Type} [Field K] [NumberField K]

theorem pow_prime_norm {P : Ideal (𝓞 K)} {k : ℕ} (hP : P.IsPrime) (h0 : P ≠ ⊥)
    (hk : 1 ≤ k) : IsPrimePow (Ideal.absNorm (P ^ k)) ∧
      P ∣ Ideal.span {((Ideal.absNorm (P ^ k)).minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm P := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hP, h0⟩
  obtain ⟨p, hp, hm⟩ := exists_prime_mem_heightOneSpectrum v
  have hd : P ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_span_singleton.2 hm
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have h1 : 1 < Ideal.absNorm P := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 : Ideal.absNorm P ∣ p ^ Module.finrank ℚ K := hN ▸ map_dvd _ hd
  obtain ⟨i, -, he⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hi : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    exact absurd he h1.ne'
  have hik : i * k ≠ 0 := mul_ne_zero hi (by omega)
  rw [map_pow, he, ← pow_mul, hp.pow_minFac hik]
  exact ⟨(isPrimePow_nat_iff _).2 ⟨p, i * k, hp, Nat.pos_of_ne_zero hik, rfl⟩, hd, he ▸ h1⟩

theorem finite_mass_le (n : ℕ) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ I ∈ S, Ideal.absNorm I = n) : ∑ I ∈ S, lamIdeal I ≤ (Module.finrank ℚ K : ℝ) * Λ n := by
  set T := S.filter (fun I => ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) with hT
  have e : ∑ I ∈ S, lamIdeal I = ∑ I ∈ T, Real.log (Ideal.absNorm I.radical) := by
    rw [hT, Finset.sum_filter]
    rfl
  rw [e]
  rcases T.eq_empty_or_nonempty with h | ⟨I₀, hI₀⟩
  · rw [h, Finset.sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg
  have key : ∀ I ∈ T, IsPrimePow n ∧ I.radical.IsPrime ∧ I.radical ≠ ⊥ ∧
      I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm I.radical ∧ ∃ k, I = I.radical ^ k := by
    intro I hI
    obtain ⟨hIS, P, k, hP, h0, hk, rfl⟩ := Finset.mem_filter.1 hI
    have h := pow_prime_norm hP h0 hk
    rw [hS _ hIS] at h
    rw [Ideal.radical_pow _ (by omega), hP.radical]
    exact ⟨h.1, hP, h0, h.2.1, h.2.2, k, rfl⟩
  have hn := (key I₀ hI₀).1
  have hp : n.minFac.Prime := Nat.minFac_prime hn.ne_one
  have hdvd : ∏ I ∈ T, I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime (fun I hI J hJ hIJ => ?_) (fun I hI => (key I hI).2.2.2.1)
    obtain ⟨-, a1, a2, -, a3, k, a4⟩ := key I hI
    obtain ⟨-, b1, b2, -, -, l, b4⟩ := key J hJ
    refine Ideal.isCoprime_iff_sup_eq.2 ((a1.isMaximal a2).coprime_of_ne (b1.isMaximal b2) fun h => hIJ ?_)
    have c1 := hS I (Finset.mem_filter.1 hI).1
    have c2 := hS J (Finset.mem_filter.1 hJ).1
    rw [a4, map_pow] at c1
    rw [b4, map_pow, ← h] at c2
    have := Nat.pow_right_injective a3 (c1.trans c2.symm)
    rw [a4, b4, ← h, this]
  have h2 : ∏ I ∈ T, Ideal.absNorm I.radical ∣ n.minFac ^ Module.finrank ℚ K := by
    have := map_dvd Ideal.absNorm hdvd
    rwa [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at this
  have h3 : ((∏ I ∈ T, Ideal.absNorm I.radical : ℕ) : ℝ) ≤ (n.minFac ^ Module.finrank ℚ K : ℕ) :=
    Nat.cast_le.2 (Nat.le_of_dvd (pow_pos hp.pos _) h2)
  have hpos : ∀ I ∈ T, (0 : ℝ) < Ideal.absNorm I.radical := fun I hI =>
    Nat.cast_pos.2 (lt_trans one_pos (key I hI).2.2.2.2.1)
  push_cast at h3
  rw [← Real.log_prod (fun I hI => (hpos I hI).ne'), vonMangoldt_apply, ite_eq_left hn]
  have h4 := Real.log_le_log (Finset.prod_pos hpos) h3
  rw [Real.log_pow] at h4
  exact_mod_cast h4

/-- The original ray ideal fibres are disjoint, so summing every ray class
adds no multiplicity beyond the actual number-field degree. -/
theorem ray_mass_le
    {M : ℕ} (D : RayData K M) (n : ℕ) :
    ∑ g : D.G, lamRay D g n ≤ (Module.finrank ℚ K : ℝ) * Λ n := by
  have e : ∀ g, lamRay D g n =
      ∑ I ∈ (RayCount.idealsIn_finite D g n).toFinset, lamIdeal I :=
    fun g => RayCount.lamRay_eq_sum D g n
  simp only [e]
  rw [← Finset.sum_biUnion]
  · refine finite_mass_le n _ fun I hI => ?_
    obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp hI
    exact ((Set.Finite.mem_toFinset _).mp hg).2.2.1
  · intro g _ g' _ hgg
    refine Finset.disjoint_left.mpr fun I h1 h2 => hgg ?_
    exact ((Set.Finite.mem_toFinset _).mp h1).2.2.2.symm.trans
      ((Set.Finite.mem_toFinset _).mp h2).2.2.2

/-- Full original quadratic-field Lambda payment, with no omitted ramified
or higher-order return. This is unconditional on the actual ray datum. -/
theorem quadratic_ray_mass_le
    (hK : Module.finrank ℚ K = 2) {M : ℕ} (D : RayData K M) (n : ℕ) :
    ∑ g : D.G, lamRay D g n ≤ 2 * Λ n := by
  simpa only [hK, Nat.cast_ofNat] using ray_mass_le D n

end RHLean.Analysis.AlpogeThin.NativeRay.PrimePowerMass

end
