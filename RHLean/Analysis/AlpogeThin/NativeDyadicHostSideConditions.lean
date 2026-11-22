import RHLean.Analysis.AlpogeThin.NativeDyadicHostRaw

/-!
# Elementary raw-host conditions on the actual native conductor

The raw host has `QS = 2^(e+2)`, so its small conductor is coprime to fifteen.
Its first Artin coordinate is the actual q-Jacobi character on the same
residue unit. For exactness, the displayed unit is `1 + N/2`, where
`N = 2^(e+2) * q * d`. It is one modulo `N/2`, while its dyadic class is
neither `1` nor `-1`.

The predicates are the original `HostRaw.{CoprimeFifteen,PsQ,Exact}` from
Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`ConjEMemHostFIff.lean`. This proof supplies their concrete arithmetic
witnesses; it does not assume a ramification or Artin-nontriviality premise.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Analysis.AlpogeThin

open Formalism.FrobeniusOrbits Formalism.HC

theorem nativeDyadicHostRaw_coprimeFifteen
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).CoprimeFifteen := by
  change Nat.Coprime (2 ^ (e + 2)) 15
  exact (show Nat.Coprime 2 15 by decide).pow_left (e + 2)

/-- The first source sign is the Jacobi symbol of the literal residue. -/
theorem nativeDyadicHostRaw_psQ
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).PsQ := by
  intro u
  change (((nativeDyadicArt e q d u).1.1 : ℤˣ) : ℤ) =
    jacobiSym (((u : ZMod (alpogeNativeHostN e q d)).val : ℕ) : ℤ) q
  rw [nativeDyadicArt_apply, NativeQuadraticRoot.legU_val,
    ← jacobiSym.legendreSym.to_jacobiSym]
  simp only [legendreSym, Int.cast_natCast]

/-- The unit `1 + N/2` supplies the nontrivial dyadic inertia class directly.
Its unit property and both exclusions from the `±1` kernel are proved here. -/
theorem nativeDyadicArt_halfConductor_nontrivial
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    ∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
      (u : ZMod (alpogeNativeHostN e q d)).val ≡ 1
        [MOD alpogeNativeHostN e q d / 2] ∧
      nativeDyadicArt e q d u ≠ 1 := by
  let s : ℕ := 2 ^ (e + 1)
  let n : ℕ := s * (q * d)
  have hs4 : 4 ≤ s := by
    change (2 : ℕ) ^ 2 ≤ 2 ^ (e + 1)
    exact pow_le_pow_right₀ (by decide) (by omega)
  have hspos : 0 < s := lt_of_lt_of_le (by decide : 0 < 4) hs4
  have hqdpos : 0 < q * d := Nat.mul_pos hH.1.pos hH.2.1.pos
  have hn4 : 4 ≤ n := hs4.trans (by
    change s ≤ s * (q * d)
    simpa only [mul_one] using Nat.mul_le_mul_left s hqdpos)
  have hm : 2 ^ (e + 2) = s * 2 := by
    dsimp only [s]
    rw [show e + 2 = (e + 1) + 1 by omega, pow_succ]
  have hN : alpogeNativeHostN e q d = 2 * n := by
    unfold alpogeNativeHostN
    rw [hm]
    dsimp only [n]
    ring
  have hNdiv : alpogeNativeHostN e q d / 2 = n := by
    rw [hN, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  have hsEven : 2 ∣ s := by
    refine ⟨2 ^ e, ?_⟩
    dsimp only [s]
    rw [pow_succ, mul_comm]
  have hnEven : 2 ∣ n := dvd_mul_of_dvd_left hsEven (q * d)
  have ha2 : (n + 1).Coprime 2 := by
    rw [Nat.coprime_two_right, Nat.odd_iff]
    have hnmod := Nat.mod_eq_zero_of_dvd hnEven
    omega
  have han : (n + 1).Coprime n := by simp
  have haN : (n + 1).Coprime (alpogeNativeHostN e q d) := by
    rw [hN]
    exact ha2.mul_right han
  have ha_lt : n + 1 < alpogeNativeHostN e q d := by
    rw [hN]
    omega
  have hqodd : q % 2 = 1 := by
    have hqmod := hH.2.2.1
    omega
  have hdodd : d % 2 = 1 := by
    have hdmod := hH.2.2.2.1
    omega
  have hqdodd : (q * d) % 2 = 1 := by
    rw [Nat.mul_mod, hqodd, hdodd]
  refine ⟨ZMod.unitOfCoprime (n + 1) haN, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt, hNdiv]
    simp [Nat.ModEq]
  · intro hArt
    change nativeDyadicFullHostEquiv e
      (alpogeNativeRecMap e q d (ZMod.unitOfCoprime (n + 1) haN)) = 1 at hArt
    have hRec := (nativeDyadicFullHostEquiv e).map_eq_one_iff.mp hArt
    have hclass := ((nativeDyadicRecMap_unitOfCoprime_eq_one_iff e q d (n + 1) haN).mp hRec).1
    rcases hclass with hpos | hneg
    · have hdiv : 2 ^ (e + 2) ∣ n :=
        Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 1 hpos)
      rw [hm] at hdiv
      change s * 2 ∣ s * (q * d) at hdiv
      have htwo : 2 ∣ q * d := (Nat.mul_dvd_mul_iff_left hspos).mp hdiv
      have hzero := Nat.mod_eq_zero_of_dvd htwo
      omega
    · have hdiv : 2 ^ (e + 2) ∣ n + 2 := by
        simpa only [Nat.add_assoc] using Nat.modEq_zero_iff_dvd.mp hneg
      have hsmod : s ∣ 2 ^ (e + 2) := by
        rw [hm]
        exact dvd_mul_right s 2
      have hsn : s ∣ n := dvd_mul_right s (q * d)
      have hstwo : s ∣ 2 := by
        simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub (hsmod.trans hdiv) hsn
      have hsle : s ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hstwo
      omega

/-- Every prime of the actual small conductor has a nontrivial Artin witness
with the exact source congruence; the only such prime is two. -/
theorem nativeDyadicHostRaw_exact
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).Exact := by
  change ∀ l : ℕ, l.Prime → l ∣ 2 ^ (e + 2) →
    ∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
      (u : ZMod (alpogeNativeHostN e q d)).val ≡ 1 [MOD alpogeNativeHostN e q d / l] ∧
      nativeDyadicArt e q d u ≠ 1
  intro l hl hlQS
  have hl2 : l = 2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
    (hl.dvd_of_dvd_pow hlQS)
  subst l
  exact nativeDyadicArt_halfConductor_nontrivial e q d he hH

end RHLean.Analysis.AlpogeThin

end
