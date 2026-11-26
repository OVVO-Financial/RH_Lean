import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimePowerWeights
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

/-!
# The selected pair removes small inert primes

The pair used for a complete window forces every small odd prime to divide
d+1. Its Jacobi symbol at -d is therefore positive. On that same outer window,
the remaining prime powers have exponent bounded in terms of epsilon alone.
-/

set_option autoImplicit false

namespace RHLean.Analysis.AlpogeThin

/-- The complete unramified inert census contains no primes up to the
    selected pair's prescribed small-prime threshold, for every host exponent
    and every integer cutoff. -/
theorem nativeDyadicInertPrime_gt_winPair {eps Y : ℝ} {q d : ℕ}
    (hpair : UpperTheory.Top.WinPair eps Y q d) (e N p : ℕ)
    (hp : p ∈ nativeDyadicInertPrimes e q d N) : Y ^ (eps / 5) < (p : ℝ) := by
  change p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter
    (fun r => ¬ r ∣ alpogeNativeHostN e q d ∧ jacobiSym (-(d : ℤ)) r = -1) at hp
  obtain ⟨hpB, hpN, hsign⟩ := Finset.mem_filter.mp hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hpB).2
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN ((dvd_pow_self 2 (by omega : e + 2 ≠ 0)).trans (alpogeNativeTwo_dvd_hostN e q d))
  by_contra! hle
  have hd := hpair.d_small p hpPrime hp2 hle
  have hd' : (p : ℤ) ∣ (d : ℤ) + 1 := by exact_mod_cast hd
  have hmod : -(d : ℤ) ≡ 1 [ZMOD (p : ℤ)] :=
    Int.modEq_iff_dvd.mpr (by simpa only [sub_neg_eq_add, add_comm (1 : ℤ) (d : ℤ)] using hd')
  have hone : jacobiSym (-(d : ℤ)) p = 1 :=
    (jacobiSym.mod_left' hmod).trans (jacobiSym.one_left p)
  omega

/-- All positive powers of selected inert primes lying below the *outer*
    square-window endpoint have a uniform exponent quota across the window. -/
theorem nativeDyadicInertPrime_exponent_lt_of_winPair {eps Y : ℝ} {q d : ℕ}
    (hpair : UpperTheory.Top.WinPair eps Y q d) (heps : 0 < eps) (hY : 1 < Y)
    (e N p i : ℕ) (hp : p ∈ nativeDyadicInertPrimes e q d N) (hi : 0 < i)
    (hcap : ((p ^ i : ℕ) : ℝ) ≤ Y ^ (2 : ℝ)) : (i : ℝ) < 10 / eps := by
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hgap := nativeDyadicInertPrime_gt_winPair hpair e N p hp
  have hip : (0 : ℝ) < i := by exact_mod_cast hi
  have hpow : Y ^ ((eps / 5) * (i : ℝ)) < Y ^ (2 : ℝ) := by
    calc
      _ = (Y ^ (eps / 5)) ^ (i : ℝ) := Real.rpow_mul hY0.le _ _
      _ < (p : ℝ) ^ (i : ℝ) := Real.rpow_lt_rpow (Real.rpow_nonneg hY0.le _) hgap hip
      _ = (p : ℝ) ^ i := Real.rpow_natCast _ _
      _ ≤ Y ^ (2 : ℝ) := by simpa only [Nat.cast_pow] using hcap
  have hb := (Real.rpow_lt_rpow_left_iff hY).mp hpow
  apply (lt_div_iff₀ heps).mpr
  nlinarith

open scoped Classical in
/-- For one actual inert prime, the original exponent cutoff and any further
    mask select at most ceil (5 / eps) odd powers below the outer endpoint. -/
theorem nativeDyadicInertPrime_odd_mask_card_le {eps Y X : ℝ} {q d : ℕ}
    (hpair : UpperTheory.Top.WinPair eps Y q d) (heps : 0 < eps) (hY : 1 < Y)
    (e N p : ℕ) (hp : p ∈ nativeDyadicInertPrimes e q d N)
    (hX : X ≤ Y ^ (2 : ℝ)) (mask : ℕ → Prop) :
    ((Finset.Icc 1 N).filter (fun i => Odd i ∧ ((p ^ i : ℕ) : ℝ) ≤ X ∧ mask i)).card ≤
      ⌈5 / eps⌉₊ := by
  let S := (Finset.Icc 1 N).filter (fun i => Odd i ∧ ((p ^ i : ℕ) : ℝ) ≤ X ∧ mask i)
  have hmap (i : ℕ) (hi : i ∈ S) : i / 2 ∈ Finset.range ⌈5 / eps⌉₊ := by
    obtain ⟨hI, ho, hcap, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨j, hj⟩ := ho
    have hbound := nativeDyadicInertPrime_exponent_lt_of_winPair hpair heps hY e N p i hp
      (Finset.mem_Icc.mp hI).1 (hcap.trans hX)
    have hnat : i = 2 * j + 1 := by omega
    have hreal : (i : ℝ) = 2 * (j : ℝ) + 1 := by exact_mod_cast hnat
    rw [Finset.mem_range, show i / 2 = j by omega, Nat.lt_ceil]
    have hscale : 10 / eps = 2 * (5 / eps) := by ring
    linarith only [hbound, hreal, hscale]
  have hinj : Set.InjOn (fun i : ℕ => i / 2) (S : Set ℕ) := by
    intro i hi k hk hik
    change i / 2 = k / 2 at hik
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2.1
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hk).2.1
    omega
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn (fun i : ℕ => i / 2) hmap hinj

end RHLean.Analysis.AlpogeThin
