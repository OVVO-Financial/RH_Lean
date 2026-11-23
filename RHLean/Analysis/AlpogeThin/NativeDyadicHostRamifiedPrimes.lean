import RHLean.Analysis.AlpogeThin.NativeDyadicHostDecomposition

/-!
# Ramified prime geometry of the actual native dyadic host

The actual inertia and decomposition descriptions are specialized to the
original conductor `2^(e+2) * q * d`. The d-inertia group is precisely the
original two-element group. At the other conductor primes, the decomposition
group preserves the original CM type. Complex conjugation is outside every
decomposition group above a conductor prime.

All statements concern the already constructed fixed field, with the same
q,d signs and dyadic quotient. No derived-host record, decomposition premise,
or replacement field is supplied.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/CycGrp.lean`, `Der.{exists_unit_crt,exists_art_iod,
inertia_d,decomp_typeI,decompConj}`. The type-I proof here uses the actual
dyadic conductor and the already proved residue-power theorem directly.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits NativeCyclotomicResidue

private theorem nativeRamifiedUnits_crt {A B : ℕ} [NeZero (A * B)]
    (hAB : A.Coprime B) (x y : ℕ) (hx : x.Coprime A) (hy : y.Coprime B) :
    ∃ u : (ZMod (A * B))ˣ,
      (u : ZMod (A * B)).val ≡ x [MOD A] ∧
      (u : ZMod (A * B)).val ≡ y [MOD B] := by
  let z := Nat.chineseRemainder hAB x y
  have hzA : (z : ℕ) ≡ x [MOD A] := z.2.1
  have hzB : (z : ℕ) ≡ y [MOD B] := z.2.2
  have hcA : Nat.Coprime z A := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hzA]
    exact hx
  have hcB : Nat.Coprime z B := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hzB]
    exact hy
  refine ⟨ZMod.unitOfCoprime z (Nat.Coprime.mul_right hcA hcB), ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq z (A * B)).of_mul_right B).trans hzA
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq z (A * B)).of_mul_left A).trans hzB

private theorem nativeRamifiedLegU_of_modEq
    {N p a : ℕ} [NeZero N] [Fact p.Prime] (hp : p ∣ N)
    (u : (ZMod N)ˣ) (hu : (u : ZMod N).val ≡ a [MOD p]) :
    ((alpogeNativeLegU N p hp u : ℤˣ) : ℤ) = jacobiSym (a : ℤ) p := by
  rw [NativeQuadraticRoot.legU_val,
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu,
    ← jacobiSym.legendreSym.to_jacobiSym]
  simp only [legendreSym, Int.cast_natCast]

private theorem nativeRamifiedCoprime
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hd2 : d ≠ 2) (hqd : q ≠ d) : (2 ^ (e + 2) * q).Coprime d := by
  have h2d : (2 ^ (e + 2)).Coprime d :=
    ((Nat.coprime_primes Nat.prime_two (Fact.out : d.Prime)).mpr hd2.symm).pow_left _
  exact h2d.mul_left ((Nat.coprime_primes (Fact.out : q.Prime)
    (Fact.out : d.Prime)).mpr hqd)

/-- The d-prime part of the actual conductor is exactly d. -/
theorem nativeDyadicOrdCompl_d
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hd2 : d ≠ 2) (hqd : q ≠ d) :
    ordCompl[d] (alpogeNativeHostN e q d) = 2 ^ (e + 2) * q := by
  have hd : d.Prime := Fact.out
  have hc := nativeRamifiedCoprime e q d hd2 hqd
  have hnd : ¬ d ∣ 2 ^ (e + 2) * q :=
    fun h => hd.one_lt.ne' (hc.symm.eq_one_of_dvd h)
  change ordCompl[d] (2 ^ (e + 2) * q * d) = _
  rw [show 2 ^ (e + 2) * q * d = d ^ 1 * (2 ^ (e + 2) * q) by ring]
  exact Nat.ordCompl_pow_mul_of_not_dvd 1 hd hnd

/-- An actual CRT unit realizes the original d-involution and is trivial
on the full dyadic-and-q conductor. -/
theorem nativeDyadicArt_exists_iod
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hd2 : d ≠ 2) (hqd : q ≠ d) (hd4 : d % 4 = 3) :
    ∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
      (u : ZMod (alpogeNativeHostN e q d)).val ≡ 1 [MOD 2 ^ (e + 2) * q] ∧
      nativeDyadicArt e q d u = (nativeDyadicFrame e).iod := by
  have hd : d.Prime := Fact.out
  have hd1 : 1 ≤ d := hd.one_lt.le
  have hcop : (d - 1).Coprime d :=
    ((Nat.Prime.coprime_iff_not_dvd hd).mpr
      (Nat.not_dvd_of_pos_of_lt (by have := hd.two_le; omega) (by omega))).symm
  obtain ⟨u, hu1, hu2⟩ :
      ∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
        (u : ZMod (alpogeNativeHostN e q d)).val ≡ 1 [MOD 2 ^ (e + 2) * q] ∧
        (u : ZMod (alpogeNativeHostN e q d)).val ≡ d - 1 [MOD d] :=
    nativeRamifiedUnits_crt
      (nativeRamifiedCoprime e q d hd2 hqd) 1 (d - 1) (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hval : (((u : ZMod (alpogeNativeHostN e q d)).val : ℕ) : ZMod d) = -1 := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hu2, Nat.cast_sub hd1]
    simp
  have hJ : ((alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u : ℤˣ) : ℤ) = -1 := by
    rw [NativeQuadraticRoot.legU_val, hval,
      quadraticChar_neg_one (by simpa only [ZMod.ringChar_zmod_n] using hd2),
      ZMod.card, ZMod.χ₄_nat_three_mod_four hd4]
  rcases nativeDyadicArt_d e q d u hu1 with h | h
  · have hs := congrArg (fun g : (nativeDyadicFrame e).GG => ((g.1.2 : ℤˣ) : ℤ)) h
    rw [nativeDyadicArt_apply] at hs
    change ((alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u : ℤˣ) : ℤ) = 1 at hs
    rw [hJ] at hs
    norm_num at hs
  · exact h

/-- The literal original d-inertia field, now proved on the actual native host. -/
theorem nativeDyadicHostRaw_inertia_d
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.d : ℤ)})]
      (σ : H.E ≃ₐ[ℚ] H.E),
      (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
        (H.gal σ = 1 ∨ H.gal σ = (nativeDyadicFrame e).iod) := by
  dsimp only
  simp only [nativeDyadicHostRaw_d]
  intro P hP hPl σ
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hd4 : d % 4 = 3 := by omega
  have hmod := nativeDyadicOrdCompl_d e q d hd2 hqd
  rw [@nativeDyadicHostRaw_inertia e q d _ _ he hH d inferInstance P hP hPl σ]
  change (∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
    (u : ZMod (alpogeNativeHostN e q d)).val ≡ 1
      [MOD ordCompl[d] (alpogeNativeHostN e q d)] ∧
      (nativeDyadicHostRaw e q d he hH).gal σ = nativeDyadicArt e q d u) ↔ _
  constructor
  · rintro ⟨u, hu, hσ⟩
    rw [hmod] at hu
    rw [hσ]
    exact nativeDyadicArt_d e q d u hu
  · rintro (hσ | hσ)
    · refine ⟨1, ?_, hσ.trans (map_one _).symm⟩
      exact (val_modEq_one_iff (Nat.ordCompl_dvd (alpogeNativeHostN e q d) d) 1).mpr
        (map_one _)
    · obtain ⟨u, hu, hiod⟩ := nativeDyadicArt_exists_iod e q d hd2 hqd hd4
      refine ⟨u, ?_, hσ.trans hiod.symm⟩
      rw [hmod]
      exact hu

private theorem nativeRamifiedJacobi_d_q
    {q d : ℕ} (hH : HostHyp q d) : jacobiSym (d : ℤ) q = -1 := by
  have hqmod := hH.2.2.1
  have hq4 : q % 4 = 3 := by omega
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hs := hH.2.2.2.2
  rw [jacobiSym.neg _ hqodd, ZMod.χ₄_nat_three_mod_four hq4, neg_one_mul] at hs
  linarith

private theorem nativeRamifiedJacobi_typeI
    {e q d l : ℕ} (hH : HostHyp q d) (hl : l.Prime)
    (hlA : l ∣ 2 ^ (e + 2) * q) : jacobiSym (l : ℤ) d = 1 := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hd8 : d % 8 = 7 := by omega
  rcases hl.dvd_mul.mp hlA with hl2 | hlq
  · have hl2' : l = 2 :=
      (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow hl2)
    subst l
    rw [Nat.cast_ofNat, jacobiSym.at_two (b := d) (Nat.odd_iff.mpr (by omega)),
      ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num [hd8]
    omega
  · have hlq' : l = q := (Nat.prime_dvd_prime_iff_eq hl hH.1).mp hlq
    subst l
    rw [jacobiSym.quadratic_reciprocity_three_mod_four hq4 hd4,
      nativeRamifiedJacobi_d_q hH]
    norm_num

/-- At 2 and q, every actual decomposition automorphism preserves the
original d-character CM type. -/
theorem nativeDyadicHostRaw_decomp_typeI
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (l : ℕ), l.Prime → l ∣ H.QS * H.q →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
        (σ : H.E ≃ₐ[ℚ] H.E),
        σ ∈ MulAction.stabilizer _ P → H.gal σ ∈ (nativeDyadicFrame e).Psi := by
  dsimp only
  intro l hl hlA P _ _ σ hσ
  let : Fact l.Prime := ⟨hl⟩
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hc := nativeRamifiedCoprime e q d hd2 hqd
  have hlnd : ¬ l ∣ d := fun h =>
    hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hlA hc) h)
  have hdM : d ∣ ordCompl[l] (alpogeNativeHostN e q d) :=
    Nat.dvd_ordCompl_of_dvd_not_dvd (alpogeNativeD_dvd_hostN e q d) hlnd
  obtain ⟨u, k, hu, hσu⟩ :
      ∃ (u : (ZMod (alpogeNativeHostN e q d))ˣ) (k : ℕ),
        (u : ZMod (alpogeNativeHostN e q d)).val ≡ l ^ k
          [MOD ordCompl[l] (alpogeNativeHostN e q d)] ∧
        (nativeDyadicHostRaw e q d he hH).gal σ = nativeDyadicArt e q d u :=
    (nativeDyadicHostRaw_decomp e q d he hH l P σ).mp hσ
  show ((nativeDyadicHostRaw e q d he hH).gal σ).1.2 = 1
  rw [hσu, nativeDyadicArt_apply]
  apply Units.ext
  change ((alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u : ℤˣ) : ℤ) = 1
  rw [nativeRamifiedLegU_of_modEq _ u (hu.of_dvd hdM), Nat.cast_pow,
    jacobiSym.pow_left, nativeRamifiedJacobi_typeI hH hl hlA, one_pow]

/-- Complex conjugation does not stabilize any prime above the original
conductor. The d-prime case uses the literal mod-16 class of d, together
with its q-character; no replacement decomposition data are introduced. -/
theorem nativeDyadicHostRaw_decompConj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (l : ℕ), l.Prime → l ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})],
        H.conj ∉ MulAction.stabilizer _ P := by
  dsimp only
  intro l hl hlN P _ _ hσ
  let H := nativeDyadicHostRaw e q d he hH
  have hgal : H.gal H.conj = (nativeDyadicFrame e).cc := H.gal.apply_symm_apply _
  by_cases hlA : l ∣ 2 ^ (e + 2) * q
  · have ht := nativeDyadicHostRaw_decomp_typeI e q d he hH l hl hlA P H.conj hσ
    change (H.gal H.conj).1.2 = 1 at ht
    rw [hgal] at ht
    have hbad : (-1 : ℤˣ) = 1 := ht
    exact absurd (congrArg Units.val hbad) (by norm_num)
  have hld : l = d := by
    change l ∣ 2 ^ (e + 2) * q * d at hlN
    rcases hl.dvd_mul.mp hlN with h | h
    · exact False.elim (hlA h)
    · exact (Nat.prime_dvd_prime_iff_eq hl hH.2.1).mp h
  subst l
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  obtain ⟨u, k, hu, hσu⟩ :
      ∃ (u : (ZMod (alpogeNativeHostN e q d))ˣ) (k : ℕ),
        (u : ZMod (alpogeNativeHostN e q d)).val ≡ d ^ k
          [MOD ordCompl[d] (alpogeNativeHostN e q d)] ∧
        H.gal H.conj = nativeDyadicArt e q d u :=
    (nativeDyadicHostRaw_decomp e q d he hH d P H.conj).mp hσ
  rw [nativeDyadicOrdCompl_d e q d hd2 hqd] at hu
  have hcc : nativeDyadicArt e q d u = (nativeDyadicFrame e).cc :=
    hσu.symm.trans hgal
  have hps : (((nativeDyadicArt e q d u).1.1 : ℤˣ) : ℤ) = (-1 : ℤ) ^ k := by
    rw [nativeDyadicArt_apply]
    change ((alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) u : ℤˣ) : ℤ) = _
    rw [nativeRamifiedLegU_of_modEq _ u (hu.of_dvd (dvd_mul_left q _)),
      Nat.cast_pow, jacobiSym.pow_left, nativeRamifiedJacobi_d_q hH]
  have hqpow : (-1 : ℤ) ^ k = -1 := by
    rw [← hps, hcc]
    rfl
  let v := ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u
  have hv : (v : ZMod (2 ^ (e + 2))) =
      (((u : ZMod (alpogeNativeHostN e q d)).val : ℕ) : ZMod (2 ^ (e + 2))) := by
    dsimp only [v]
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
  have hvk : hcl e v = 1 := by
    have hh := nativeDyadicArt_h e q d u v hv
    rw [hcc] at hh
    exact hh.symm.trans (map_one _)
  obtain ⟨n, hn⟩ :=
    Subgroup.mem_zpowers_iff.mp ((QuotientGroup.eq_one_iff v).mp hvk)
  have h16 : 16 ∣ 2 ^ (e + 2) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  have hred : (((u : ZMod (alpogeNativeHostN e q d)).val : ℕ) : ZMod 16) =
      ((d ^ k : ℕ) : ZMod 16) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (hu.of_dvd (h16.trans (dvd_mul_right (2 ^ (e + 2)) q)))
  have hfv : ZMod.castHom h16 (ZMod 16) (v : ZMod (2 ^ (e + 2))) =
      (7 : ZMod 16) ^ k := by
    rw [hv, map_natCast, hred, Nat.cast_pow, ← ZMod.natCast_mod d 16, hdmod]
    rfl
  have hpm : (7 : ZMod 16) ^ k = 1 ∨ (7 : ZMod 16) ^ k = -1 := by
    have h0 := congrArg (fun x : (ZMod (2 ^ (e + 2)))ˣ =>
      ZMod.castHom h16 (ZMod 16) (x : ZMod (2 ^ (e + 2)))) hn
    rw [hfv] at h0
    rcases Int.even_or_odd n with hnEven | hnOdd
    · left
      rw [hnEven.neg_one_zpow, Units.val_one, map_one] at h0
      exact h0.symm
    · right
      rw [hnOdd.neg_one_zpow, Units.val_neg, Units.val_one, map_neg, map_one] at h0
      exact h0.symm
  rcases Nat.even_or_odd k with hkEven | ⟨j, hj⟩
  · rw [hkEven.neg_one_pow] at hqpow
    norm_num at hqpow
  · have h7 : (7 : ZMod 16) ^ k = 7 := by
      rw [hj, pow_succ, pow_mul, (by decide : (7 : ZMod 16) ^ 2 = 1), one_pow, one_mul]
    rw [h7] at hpm
    revert hpm
    decide

end RHLean.Analysis.AlpogeThin

end
