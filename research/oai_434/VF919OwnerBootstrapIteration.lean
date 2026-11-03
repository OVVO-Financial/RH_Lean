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

#print axioms ownerExponentIterate_closed
#print axioms native_owner_iterated_growth
#print axioms native_owner_single_strict_gain
#print axioms native_slot_seed_owner_iterates
#print axioms native_slot_seed_zero_owner_orbit

end RHLean.Analysis.OwnerPrefix
end
