import Mathlib
import «research.CANONICAL_ROUGH_GLOBAL_BOUNDS»
import RHLean.Proof.FarSurvivorRenewal_is_LowerMertens

/-!
# Global q^2 tail reduction for the canonical rough bound

For an odd owner `q`, the literal daughter cutoff is

  Y_q = floor((R^2-1)/q^2).

If `q^2 >= R`, then `Y_q < R`.  Such a daughter is already inside the lower
critical envelope at the parent root and is therefore not a genuinely recursive
obstruction.  This file proves that the entire `q^2 >= R` owner tail costs only
`3 R^2 K` in the native raw daughter energy.

Consequently any fixed-coefficient global parent estimate only needs new
arithmetic input on the low-owner sector `q^2 < R`; the complementary owner tail
is an admissible root-scale boundary.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Odd q^2 owners whose daughter cutoff is already below the parent root. -/
def canonicalRoughHighQ2Owners (R : ℕ) : Finset ℕ :=
  ((primesUpTo (R - 1)).erase 2).filter fun q => R ≤ q * q

/-- The complementary genuinely recursive owner sector. -/
def canonicalRoughLowQ2Owners (R : ℕ) : Finset ℕ :=
  ((primesUpTo (R - 1)).erase 2) \ canonicalRoughHighQ2Owners R

/-- Daughter energy in the nonrecursive high-owner sector. -/
def canonicalRoughHighQ2DaughterEnergy (R : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughHighQ2Owners R, rawQ2ChildEnergyReal R q

/-- Daughter energy in the genuinely recursive low-owner sector. -/
def canonicalRoughLowQ2DaughterEnergy (R : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R, rawQ2ChildEnergyReal R q

private theorem one_le_lowerEnvelope_globalTail
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  have hm0 : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  rw [hm0] at h0
  norm_num at h0
  exact h0

/-- A high owner really lands strictly below the current root. -/
theorem rawQ2ChildCutoff_lt_parent_of_mem_highQ2Owners
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    rawQ2ChildCutoff R q < R := by
  have hbase := (Finset.mem_filter.mp hq).1
  have hhigh := (Finset.mem_filter.mp hq).2
  have hqPrime := (mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2).1
  have hden : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
  unfold rawQ2ChildCutoff
  apply (Nat.div_lt_iff_lt_mul hden).2
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    rw [pow_two]
    have hpos : 0 < R * R := Nat.mul_pos (by omega) (by omega)
    exact Nat.sub_lt hpos (by norm_num)
  have hmul : R * R ≤ R * (q * q) :=
    Nat.mul_le_mul_left R hhigh
  exact hXlt.trans_le hmul

/-- The lower critical envelope converts a high-owner daughter into a root-scale
term.  The harmless factor three only removes the envelope's `M-1` shift. -/
theorem rawQ2ChildEnergyReal_le_three_mul_K_mul_root_of_mem_highQ2Owners
    {R q : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    rawQ2ChildEnergyReal R q ≤ 3 * K * (R : ℝ) := by
  let Y : ℕ := rawQ2ChildCutoff R q
  let m : ℝ := ((mertensSummatoryInt Y : ℤ) : ℝ)
  have hY : Y < R := by
    dsimp [Y]
    exact rawQ2ChildCutoff_lt_parent_of_mem_highQ2Owners hR hq
  have hshift := hK.2 Y hY
  have hmshift :
      (((mertensSummatoryInt Y - 1 : ℤ) : ℝ)) = m - 1 := by
    dsimp [m]
    push_cast
    ring
  rw [hmshift] at hshift
  have hYR : (((Y + 1 : ℕ) : ℝ)) ≤ (R : ℝ) := by
    exact_mod_cast (show Y + 1 ≤ R by omega)
  have hscale : K * (((Y + 1 : ℕ) : ℝ)) ≤ K * (R : ℝ) :=
    mul_le_mul_of_nonneg_left hYR hK.1
  have hK1 : 1 ≤ K := one_le_lowerEnvelope_globalTail (by omega) hK
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hKR : 2 ≤ K * (R : ℝ) := by nlinarith
  have hsplit : m ^ 2 ≤ 2 * (m - 1) ^ 2 + 2 := by
    nlinarith [sq_nonneg (m - 2)]
  unfold rawQ2ChildEnergyReal
  change m ^ 2 ≤ 3 * K * (R : ℝ)
  nlinarith

/-- There are at most `R` high owners because every owner already lies in the
prime prefix through `R-1`. -/
theorem card_canonicalRoughHighQ2Owners_le_root (R : ℕ) :
    (canonicalRoughHighQ2Owners R).card ≤ R := by
  have hsub : canonicalRoughHighQ2Owners R ⊆ Finset.range R := by
    intro q hq
    have hbase := (Finset.mem_filter.mp hq).1
    rcases mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2 with
      ⟨hqPrime, hqle⟩
    have hqR : q < R := by
      have hqpos : 0 < q := hqPrime.pos
      omega
    exact Finset.mem_range.mpr hqR
  simpa using Finset.card_le_card hsub

/-- **Milestone-2 tail theorem.**  The entire q^2 owner tail with `q^2 >= R`
is globally absorbable into the permitted root-scale envelope. -/
theorem canonicalRoughHighQ2DaughterEnergy_le_three_root_sq_K
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    canonicalRoughHighQ2DaughterEnergy R ≤
      3 * (R : ℝ) ^ 2 * K := by
  have hterm : ∀ q ∈ canonicalRoughHighQ2Owners R,
      rawQ2ChildEnergyReal R q ≤ 3 * K * (R : ℝ) := by
    intro q hq
    exact rawQ2ChildEnergyReal_le_three_mul_K_mul_root_of_mem_highQ2Owners
      hR hK hq
  have hcardNat := card_canonicalRoughHighQ2Owners_le_root R
  have hcard : ((canonicalRoughHighQ2Owners R).card : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hcardNat
  have hfactor : 0 ≤ 3 * K * (R : ℝ) := by
    have hK0 : 0 ≤ K := hK.1
    have hR0 : 0 ≤ (R : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) hK0) hR0
  unfold canonicalRoughHighQ2DaughterEnergy
  calc
    (∑ q ∈ canonicalRoughHighQ2Owners R, rawQ2ChildEnergyReal R q) ≤
        ∑ _q ∈ canonicalRoughHighQ2Owners R, 3 * K * (R : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          exact hterm q hq
    _ = ((canonicalRoughHighQ2Owners R).card : ℝ) *
          (3 * K * (R : ℝ)) := by simp
    _ ≤ (R : ℝ) * (3 * K * (R : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hcard hfactor
    _ = 3 * (R : ℝ) ^ 2 * K := by ring

end RHLean.Proof
