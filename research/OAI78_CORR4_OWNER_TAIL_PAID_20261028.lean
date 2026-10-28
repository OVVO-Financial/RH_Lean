import Mathlib
import «research.CORR4_OAI_POWER_DETERMINISTIC_FRAME_20261025»
import «research.CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026»
import «research.LOW_OWNER_Q2_NEAREST_SQUARE_ENDPOINT»

/-!
# Actual q²-owner tail paid by a supplied all-integer Mertens power bound

No prime number theorem and no new arithmetic hypothesis beyond the
Mertens power input. The original q² cutoff, odd-prime labels,
reciprocal weights, and signed parent/mixed interaction are retained.

For any beta >= 3/4, every owner q >= T² receives an extra factor 1/T
relative to the full unweighted q²-frame. Instantiating beta=7/8+epsilon
is permitted by the original OpenAI growth theorem.

The source-local mixed-tail estimate leaves a genuine small-owner bill;
it does not assert a new global Mertens exponent.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic RHLean.Analysis.MertensExponent
attribute [local instance] Classical.propDecidable

/-- Original low q² owners whose prime index is at least T². -/
def oai78PaidLargeQOwners (R T : ℕ) : Finset ℕ :=
  (canonicalRoughLowQ2Owners R).filter (fun q => T * T ≤ q)

/-- The original real reciprocal column restricted to paid large owners. -/
def oai78PaidLargeQReciprocal (R T : ℕ) : ℝ :=
  ∑ q ∈ oai78PaidLargeQOwners R T,
    (1 / (q : ℝ)) * (mertensSummatoryInt (rawQ2ChildCutoff R q) : ℝ)

/-- The complementary, genuine low-owner column. -/
def oai78PaidSmallQReciprocal (R T : ℕ) : ℝ :=
  ∑ q ∈ (canonicalRoughLowQ2Owners R).filter (fun q => q < T * T),
    (1 / (q : ℝ)) * (mertensSummatoryInt (rawQ2ChildCutoff R q) : ℝ)

/-- The complementary genuine daughter square energies. -/
def oai78PaidSmallQDaughterEnergy (R T : ℕ) : ℝ :=
  ∑ q ∈ (canonicalRoughLowQ2Owners R).filter (fun q => q < T * T),
    rawQ2ChildEnergyReal R q

def oai78PaidLargeQDaughterEnergy (R T : ℕ) : ℝ :=
  ∑ q ∈ oai78PaidLargeQOwners R T,
    rawQ2ChildEnergyReal R q

/-- All original daughters are retained in exactly one part of the split. -/
theorem oai78PaidReciprocal_split (R T : ℕ) :
    lowOwnerReciprocalMertensColumnReal R =
      oai78PaidSmallQReciprocal R T + oai78PaidLargeQReciprocal R T := by
  unfold lowOwnerReciprocalMertensColumnReal
    oai78PaidSmallQReciprocal oai78PaidLargeQReciprocal oai78PaidLargeQOwners
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := canonicalRoughLowQ2Owners R)
    (p := fun q => q < T * T)]
  simp only [Nat.not_lt]

theorem oai78PaidEnergy_split (R T : ℕ) :
    canonicalRoughLowQ2DaughterEnergy R =
      oai78PaidSmallQDaughterEnergy R T +
        oai78PaidLargeQDaughterEnergy R T := by
  unfold canonicalRoughLowQ2DaughterEnergy
    oai78PaidSmallQDaughterEnergy oai78PaidLargeQDaughterEnergy
    oai78PaidLargeQOwners
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := canonicalRoughLowQ2Owners R)
    (p := fun q => q < T * T)]
  simp only [Nat.not_lt]

/-- The original high-q daughter energy is nonnegative without an
    independence or pair-sign assumption. -/
theorem oai78PaidLargeQDaughterEnergy_nonneg (R T : ℕ) :
    0 ≤ oai78PaidLargeQDaughterEnergy R T := by
  unfold oai78PaidLargeQDaughterEnergy
  apply Finset.sum_nonneg
  intro q _hq
  unfold rawQ2ChildEnergyReal
  positivity

/-- A square-root improvement is available just from q >= T² and
    the exponent beta >= 3/4. This uses no prime-counting estimate. -/
theorem oai78Paid_extra_owner_power (q T : ℕ) (hq : 1 ≤ q)
    (hT : T * T ≤ q) (β : ℝ) (hβ : (3 / 4 : ℝ) ≤ β) :
    (T : ℝ) * (q : ℝ) ≤ Real.rpow (q : ℝ) (2 * β) := by
  have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqr0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hqrpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hTsq : (T : ℝ) ^ 2 ≤ (q : ℝ) := by
    have hTreal : (T : ℝ) * (T : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hT
    simpa only [pow_two] using hTreal
  have hTsqrt : (T : ℝ) ≤ Real.sqrt (q : ℝ) := by
    have hs := Real.sq_sqrt hqr0
    have hspos := Real.sqrt_nonneg (q : ℝ)
    have htpos : (0 : ℝ) ≤ (T : ℝ) := by positivity
    nlinarith
  have hPow :
      (q : ℝ) * Real.sqrt (q : ℝ) =
        Real.rpow (q : ℝ) (3 / 2) := by
    have ha := Real.rpow_add hqrpos (1 : ℝ) (1 / 2 : ℝ)
    rw [Real.rpow_one, ← Real.sqrt_eq_rpow] at ha
    simpa only [Real.rpow_eq_pow,
      show (1 + 1 / 2 : ℝ) = 3 / 2 by ring] using ha.symm
  calc
    (T : ℝ) * (q : ℝ) ≤
        (q : ℝ) * Real.sqrt (q : ℝ) := by
          nlinarith [mul_nonneg (show (0:ℝ) ≤ (q:ℝ) by positivity)
            (sub_nonneg.mpr hTsqrt)]
    _ = Real.rpow (q : ℝ) (3 / 2) := hPow
    _ ≤ Real.rpow (q : ℝ) (2 * β) :=
      Real.rpow_le_rpow_of_exponent_le hqr (by linarith)

/-- Exact original daughter cutoff and multiplication of its 7/8
    envelope by the FULL q^(2 beta) factor, not the weaker q factor. -/
theorem oai78Paid_raw_daughter_scale
    (R q : ℕ) (hR : 56 ≤ R)
    (hq : q ∈ canonicalRoughLowQ2Owners R)
    (β C : ℝ) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      ‖mertensSummatory n‖ ≤ C * Real.rpow (n : ℝ) β) :
    ‖mertensSummatory (rawQ2ChildCutoff R q)‖ *
        Real.rpow (q : ℝ) (2 * β) ≤
      C * Real.rpow (R : ℝ) (2 * β) := by
  have hsub : canonicalRoughLowQ2Owners R ⊆
      (primesUpTo (R - 1)).erase 2 := Finset.sdiff_subset
  have hprime := (mem_primesUpTo.mp
    (Finset.mem_erase.mp (hsub hq)).2).1
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hprime.pos
  let Y : ℕ := rawQ2ChildCutoff R q
  have hYpos : 0 < Y :=
    rawQ2ChildCutoff_pos_of_mem_lowQ2Owners (by omega) hq
  have hYle : Y * (q * q) ≤ squareRootEndpoint R := by
    dsimp [Y, rawQ2ChildCutoff]
    exact Nat.div_mul_le_self _ _
  have hYX : Y * (q * q) ≤ R ^ 2 := by
    exact hYle.trans (by
      unfold squareRootEndpoint
      exact Nat.sub_le _ _)
  have hYXreal : (Y : ℝ) * (q : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
    have hh : Y * q ^ 2 ≤ R ^ 2 := by
      simpa only [pow_two] using hYX
    exact_mod_cast hh
  have hqpow : (0 : ℝ) ≤ Real.rpow ((q : ℝ) ^ 2) β :=
    Real.rpow_nonneg (sq_nonneg _) _
  have hRaise :=
    Real.rpow_le_rpow
      (mul_nonneg (Nat.cast_nonneg Y) (sq_nonneg _))
      hYXreal hβ
  rw [Real.mul_rpow (Nat.cast_nonneg Y) (sq_nonneg _)] at hRaise
  have hRpow :
      Real.rpow ((R : ℝ) ^ 2) β =
        Real.rpow (R : ℝ) (2 * β) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul (Nat.cast_nonneg R) 2 β).symm
  have hqpowEq :
      Real.rpow ((q : ℝ) ^ 2) β =
        Real.rpow (q : ℝ) (2 * β) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul (Nat.cast_nonneg q) 2 β).symm
  have hMval := hM Y (by omega)
  calc
    ‖mertensSummatory Y‖ * Real.rpow (q : ℝ) (2 * β) =
        ‖mertensSummatory Y‖ *
          Real.rpow ((q : ℝ) ^ 2) β := by rw [hqpowEq]
    _ ≤ (C * Real.rpow (Y : ℝ) β) *
          Real.rpow ((q : ℝ) ^ 2) β :=
          mul_le_mul_of_nonneg_right hMval hqpow
    _ = C * (Real.rpow (Y : ℝ) β *
          Real.rpow ((q : ℝ) ^ 2) β) := by ring
    _ ≤ C * Real.rpow ((R : ℝ) ^ 2) β :=
          mul_le_mul_of_nonneg_left hRaise hC
    _ = C * Real.rpow (R : ℝ) (2 * β) := by rw [hRpow]

/-- The actual 7/8-bound admits an extra T in the denominator
    on every q >= T² reciprocal source atom. -/
theorem oai78Paid_single_large_owner
    (R q T : ℕ) (hR : 56 ≤ R)
    (hq : q ∈ oai78PaidLargeQOwners R T)
    (β C : ℝ) (hβ : (3 / 4 : ℝ) ≤ β) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      ‖mertensSummatory n‖ ≤ C * Real.rpow (n : ℝ) β) :
    (T : ℝ) *
      (‖mertensSummatory (rawQ2ChildCutoff R q)‖ / (q : ℝ)) ≤
      (C * Real.rpow (R : ℝ) (2 * β)) / (q : ℝ) ^ 2 := by
  have howner := (Finset.mem_filter.mp hq).1
  have hT := (Finset.mem_filter.mp hq).2
  have hsub : canonicalRoughLowQ2Owners R ⊆
      (primesUpTo (R - 1)).erase 2 := Finset.sdiff_subset
  have hprime := (mem_primesUpTo.mp
    (Finset.mem_erase.mp (hsub howner)).2).1
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hprime.pos
  have hpower := oai78Paid_extra_owner_power q T hprime.one_le hT β hβ
  have hscale := oai78Paid_raw_daughter_scale R q hR howner β C
    (by linarith) hC hM
  have hnorm := norm_nonneg (mertensSummatory (rawQ2ChildCutoff R q))
  have hprod :
      ‖mertensSummatory (rawQ2ChildCutoff R q)‖ * (T : ℝ) * (q : ℝ) ≤
        C * Real.rpow (R : ℝ) (2 * β) := by
    nlinarith [mul_le_mul_of_nonneg_left hpower hnorm]
  apply (le_div_iff₀ (sq_pos_of_pos hqpos)).2
  calc
    (T : ℝ) *
        (‖mertensSummatory (rawQ2ChildCutoff R q)‖ / (q : ℝ)) *
          (q : ℝ) ^ 2 =
      ‖mertensSummatory (rawQ2ChildCutoff R q)‖ * (T : ℝ) * (q : ℝ) := by
        field_simp
    _ ≤ _ := hprod

/-- High q² owner tail is fully paid by the supplied ALL-INTEGER Mertens
    power bound. The only summation cost is the already-certified odd-prime
    reciprocal-square budget 1/4; no PNT or harmonic estimate is used.
    This is a genuinely power-saving estimate for T tending to infinity. -/
theorem oai78Paid_large_owner_column_le_power
    (R T : ℕ) (hR : 56 ≤ R)
    (β C : ℝ) (hβ : (3 / 4 : ℝ) ≤ β) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      ‖mertensSummatory n‖ ≤ C * Real.rpow (n : ℝ) β) :
    (T : ℝ) * |oai78PaidLargeQReciprocal R T| ≤
      (1 / 4 : ℝ) * C * Real.rpow (R : ℝ) (2 * β) := by
  have hsub : oai78PaidLargeQOwners R T ⊆ canonicalRoughLowQ2Owners R := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hTri :
      |oai78PaidLargeQReciprocal R T| ≤
        ∑ q ∈ oai78PaidLargeQOwners R T,
          ‖mertensSummatory (rawQ2ChildCutoff R q)‖ / (q : ℝ) := by
    unfold oai78PaidLargeQReciprocal
    rw [← Real.norm_eq_abs]
    calc
      ‖∑ q ∈ oai78PaidLargeQOwners R T,
        (1 / (q : ℝ)) * (mertensSummatoryInt (rawQ2ChildCutoff R q) : ℝ)‖ ≤
        ∑ q ∈ oai78PaidLargeQOwners R T,
          ‖(1 / (q : ℝ)) * (mertensSummatoryInt (rawQ2ChildCutoff R q) : ℝ)‖ :=
          norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have howner := (Finset.mem_filter.mp hq).1
        have hpr :=
          (mem_primesUpTo.mp (Finset.mem_erase.mp
            (Finset.sdiff_subset howner)).2).1
        have hqpos : 0 < (q : ℝ) := by exact_mod_cast hpr.pos
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hqpos)]
        rw [← mertensSummatoryInt_cast]
        rw [Complex.norm_intCast, Real.norm_eq_abs]
        ring
  have hterms :
      (T : ℝ) * (∑ q ∈ oai78PaidLargeQOwners R T,
        ‖mertensSummatory (rawQ2ChildCutoff R q)‖ / (q : ℝ)) ≤
      (C * Real.rpow (R : ℝ) (2 * β)) *
        (∑ q ∈ oai78PaidLargeQOwners R T,
          (1 : ℝ) / (q : ℝ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    simpa only [div_eq_mul_inv, one_mul] using
      oai78Paid_single_large_owner R q T hR hq β C hβ hC hM
  have hrec :
      (∑ q ∈ oai78PaidLargeQOwners R T, (1 : ℝ) / (q : ℝ) ^ 2) ≤
      (1 / 4 : ℝ) := by
    calc
      _ ≤ ∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 : ℝ) / (q : ℝ) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro q _hq _hne
            positivity
      _ ≤ (1 / 4 : ℝ) := lowOwnerReciprocalSquareBudgetReal_le_quarter R
  have hCpow : 0 ≤ C * Real.rpow (R : ℝ) (2 * β) :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg R) _)
  calc
    (T : ℝ) * |oai78PaidLargeQReciprocal R T| ≤
      (T : ℝ) * (∑ q ∈ oai78PaidLargeQOwners R T,
        ‖mertensSummatory (rawQ2ChildCutoff R q)‖ / (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hTri (Nat.cast_nonneg T)
    _ ≤ (C * Real.rpow (R : ℝ) (2 * β)) *
      (∑ q ∈ oai78PaidLargeQOwners R T,
        (1 : ℝ) / (q : ℝ) ^ 2) := hterms
    _ ≤ (C * Real.rpow (R : ℝ) (2 * β)) * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hrec hCpow
    _ = _ := by ring

#print axioms oai78PaidReciprocal_split
#print axioms oai78PaidEnergy_split
#print axioms oai78Paid_extra_owner_power
#print axioms oai78Paid_raw_daughter_scale
#print axioms oai78Paid_large_owner_column_le_power

end RHLean.Proof
