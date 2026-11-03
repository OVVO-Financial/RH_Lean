import «research.oai_434.VF919ActualSlotMinRetighten»
import «research.NATIVE_OWNER_PREFIX_MERTENS_20261021»

/-!
# Source-faithful owner bootstrap: exact quantitative ledger

This module does not assume any new Moebius cancellation. It distinguishes:

* unconditional positive initial exponent gap from the fixed physical slots;
* conditionally proved original-owner transfer and its true hypotheses;
* precise exponent transfer under iteration.

The arithmetic hypothesis NativeOwnerBound is never silently discharged.
In particular a positive initial gap alone is NOT an owner contraction.
-/

noncomputable section

namespace RHLean.Analysis.OwnerPrefix

open RHLean.Analysis.MertensExponent
open OAI.SevenEighths
open OAI.SevenEighths.RHLeanActualSlotMin
open RHLean.Proof.NativeOwnerSwapRenewal

/-- Iterate the already-compiled original-owner exponent exchange rate. -/
def ownerExponentIterate (κ θ : ℝ) : ℕ → ℝ
  | 0 => θ
  | n + 1 => (1 + 2 * ownerExponentIterate κ θ n + κ) / 4

/-- With nonnegative owner loss, the iteration does not cross below 1/2. -/
theorem ownerExponentIterate_half_le (κ θ : ℝ)
    (hκ : 0 ≤ κ) (hθ : (1 / 2 : ℝ) ≤ θ) (n : ℕ) :
    (1 / 2 : ℝ) ≤ ownerExponentIterate κ θ n := by
  induction n with
  | zero =>
      simpa only [ownerExponentIterate] using hθ
  | succ n ih =>
      change (1 / 2 : ℝ) ≤
        (1 + 2 * ownerExponentIterate κ θ n + κ) / 4
      linarith only [hκ, ih]

/-- Closed-form exponent orbit: the unique fixed point is (1+κ)/2. -/
theorem ownerExponentIterate_closed (κ θ : ℝ) (n : ℕ) :
    ownerExponentIterate κ θ n =
      (1 + κ) / 2 + (θ - (1 + κ) / 2) / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      simp only [ownerExponentIterate, pow_zero, div_one]
      ring
  | succ n ih =>
      change (1 + 2 * ownerExponentIterate κ θ n + κ) / 4 =
        (1 + κ) / 2 + (θ - (1 + κ) / 2) / (2 : ℝ) ^ (n + 1)
      rw [ih, pow_succ]
      have hz : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hz]
      ring

/-- The original-owner recurrence may be iterated at every integer level.
Its only arithmetic hypothesis is the SAME complete signed owner bound. -/
theorem native_owner_iterated_growth
    (κ θ : ℝ) (hκ : 0 ≤ κ) (hθ : (1 / 2 : ℝ) ≤ θ)
    (howner : NativeOwnerBound κ)
    (hgrowth : MertensGrowthAtMost θ) :
    ∀ n : ℕ, MertensGrowthAtMost (ownerExponentIterate κ θ n) := by
  intro n
  induction n with
  | zero =>
      simpa only [ownerExponentIterate] using hgrowth
  | succ n ih =>
      exact native_growthAtMost_of_ownerBound hκ
        (ownerExponentIterate_half_le κ θ hκ hθ n) howner ih

/-- A strict owner improvement requires κ < 2θ-1. This is the exact
noncircular threshold for the already-proved exponent consumer. -/
theorem native_owner_single_strict_gain
    (κ θ : ℝ) (hκ : 0 ≤ κ) (hθ : (1 / 2 : ℝ) ≤ θ)
    (hstrict : κ < 2 * θ - 1)
    (howner : NativeOwnerBound κ)
    (hgrowth : MertensGrowthAtMost θ) :
    ∃ gain : ℝ, 0 < gain ∧ MertensGrowthAtMost (θ - gain) := by
  let gain : ℝ := (2 * θ - 1 - κ) / 4
  have hgain : 0 < gain := by dsimp [gain]; linarith only [hstrict]
  refine ⟨gain, hgain, ?_⟩
  have hs := native_growthAtMost_of_ownerBound hκ hθ howner hgrowth
  have hexp : (1 + 2 * θ + κ) / 4 = θ - gain := by
    dsimp [gain]
    ring
  rw [← hexp]
  exact hs

/-- Feed the already-proved actual minimum-slot gain into ANY genuine
uniform owner hypothesis. No extra source assumptions enter the seed. -/
theorem native_slot_seed_owner_iterates
    (κ : ℝ) (hκ : 0 ≤ κ) (howner : NativeOwnerBound κ) :
    ∃ θ : ℝ, (1 / 2 : ℝ) ≤ θ ∧ θ < 7 / 8 ∧
      ∀ n : ℕ, MertensGrowthAtMost (ownerExponentIterate κ θ n) := by
  obtain ⟨D, hpositive, hbeta⟩ :=
    native_beta_le_true_physical_slot_minimum
  let θ : ℝ := 7 / 8 - actualSlotMinimum D / 24
  have hθ : (1 / 2 : ℝ) ≤ θ := by
    dsimp [θ]
    linarith only [hbeta, HeckeZeroSupremum.half_le_beta]
  have hstrict : θ < (7 / 8 : ℝ) := by
    dsimp [θ]
    linarith only [hpositive]
  have hgrowth : MertensGrowthAtMost θ := by
    exact growthAtMost_mono hbeta native_mertens_growth_at_hecke_beta
  exact ⟨θ, hθ, hstrict,
    native_owner_iterated_growth κ θ hκ hθ howner hgrowth⟩

/-- The zero-owner case has exactly the geometric RH-limiting orbit;
this is a conditional ledger identity, NOT an unconditional RH proof. -/
theorem native_slot_seed_zero_owner_orbit
    (howner : NativeOwnerBound 0) :
    ∃ θ : ℝ, (1 / 2 : ℝ) ≤ θ ∧ θ < 7 / 8 ∧
      ∀ n : ℕ, MertensGrowthAtMost
        ((1 / 2 : ℝ) + (θ - 1 / 2) / (2 : ℝ) ^ n) := by
  obtain ⟨θ, hθ, hθ7, hgrowth⟩ :=
    native_slot_seed_owner_iterates 0 (by norm_num) howner
  refine ⟨θ, hθ, hθ7, ?_⟩
  intro n
  have h := hgrowth n
  rw [ownerExponentIterate_closed] at h
  norm_num at h ⊢
  exact h

/-- Elementary domination: the geometric dyadic scale outgrows its index. -/
theorem nat_cast_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      push_cast
      have hp : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      nlinarith only [ih, hp]

/-- If the complete ORIGINAL signed owner loss is zero, the fixed positive
slot seed and the compiled recurrence really do prove Mertens at exponent
1/2. No limit at a boundary is assumed: each epsilon uses a finite n. -/
theorem native_zero_owner_bootstrap_to_half
    (howner : NativeOwnerBound 0) :
    MertensGrowthAtMost (1 / 2) := by
  obtain ⟨θ, hθ, _hθ7, hall⟩ :=
    native_slot_seed_zero_owner_orbit howner
  intro ε hε
  let A : ℝ := θ - 1 / 2
  let u : ℝ := ε / 2
  have hu : 0 < u := by dsimp [u]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (A / u)
  have hnA : A < (n : ℝ) * u := (div_lt_iff₀ hu).mp hn
  have hn2 : (n : ℝ) ≤ (2 : ℝ) ^ n := nat_cast_le_two_pow n
  have hnA2 : A < (2 : ℝ) ^ n * u := by
    have hm := mul_le_mul_of_nonneg_right hn2 hu.le
    linarith only [hnA, hm]
  have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hsmall : A / (2 : ℝ) ^ n < u :=
    (div_lt_iff₀ hpow).mpr (by nlinarith only [hnA2])
  have hp := hall n u hu
  have heq : (1 / 2 + (θ - 1 / 2) / (2 : ℝ) ^ n) + u ≤
      (1 / 2 : ℝ) + ε := by
    dsimp [A, u] at hsmall
    dsimp [u]
    linarith only [hsmall]
  exact powerBound_mono heq hp

/-- Original-owner zero loss is RH-strength, given the existing finite-slot
source. This is CONDITIONAL on the unproved signed owner hypothesis. -/
theorem native_zero_owner_implies_critical_zeros
    (howner : NativeOwnerBound 0) :
    ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) := by
  exact growthAtMost_half_iff_criticalZeros.mp
    (native_zero_owner_bootstrap_to_half howner)

#print axioms ownerExponentIterate_closed
#print axioms native_owner_iterated_growth
#print axioms native_owner_single_strict_gain
#print axioms native_slot_seed_owner_iterates
#print axioms native_slot_seed_zero_owner_orbit
#print axioms native_zero_owner_bootstrap_to_half
#print axioms native_zero_owner_implies_critical_zeros

end RHLean.Analysis.OwnerPrefix
end
