import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm

/-!
# Frozen square-root history: exact prime-two HIGH-HIGH packet

At X_R = R^2-1, only the historical Mobius values mu(m), m<R,
occur. The root-adjacent odd parents 2*m>=R have no doubled child
inside the history. On their ordered pair carrier the exact physical
floor quotient lies in {1,2,3}. Hence the complete signed HIGH-HIGH
packet is exactly the historical odd-high square plus the two
hyperbola masks q=2 and q=3, for EVERY R>=2.

No Mobius values at n>=R, prime counts, RH, assumed cancellation,
or OAI moment bound enter the proof.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The odd historical parents whose doubled child lies outside [1,R). -/
def frozenOddHighParents (R : ℕ) : Finset ℕ :=
  (Finset.Ico 1 R).filter (fun m => Odd m ∧ R ≤ 2 * m)

/-- The actual frozen odd-high Mobius mass. -/
def frozenOddHighMass (R : ℕ) : ℤ :=
  ∑ m ∈ frozenOddHighParents R, (μ m : ℤ)

/-- The original ordered bilinear floor kernel restricted to odd-high parents. -/
def frozenOddHighPairFloor (R : ℕ) : ℤ :=
  ∑ m ∈ frozenOddHighParents R,
    ∑ n ∈ frozenOddHighParents R,
      (μ m : ℤ) * (μ n : ℤ) *
        (((R ^ 2 - 1) / (m * n) : ℕ) : ℤ)

/-- The only nontrivial reciprocal quotient masks on the HIGH-HIGH carrier. -/
def frozenOddHighPairMask (R q : ℕ) : ℤ :=
  ∑ m ∈ frozenOddHighParents R,
    ∑ n ∈ frozenOddHighParents R,
      if q * m * n ≤ R ^ 2 - 1
      then (μ m : ℤ) * (μ n : ℤ)
      else 0

private theorem frozenOddHigh_mem (R m : ℕ)
    (hm : m ∈ frozenOddHighParents R) :
    1 ≤ m ∧ m < R ∧ Odd m ∧ R ≤ 2 * m := by
  rcases Finset.mem_filter.mp hm with ⟨hmIco, h⟩
  rcases Finset.mem_Ico.mp hmIco with ⟨h1, hR⟩
  exact ⟨h1, hR, h.1, h.2⟩

/-- Every upper-upper historical floor quotient is 1, 2, or 3.
Both bounds are pure square-root geometry. -/
theorem frozenOddHigh_floor_one_to_three
    (R m n : ℕ) (hR : 2 ≤ R)
    (hm : m ∈ frozenOddHighParents R)
    (hn : n ∈ frozenOddHighParents R) :
    1 ≤ (R ^ 2 - 1) / (m * n) ∧
      (R ^ 2 - 1) / (m * n) < 4 := by
  obtain ⟨hm1, hmR, _, hmhi⟩ := frozenOddHigh_mem R m hm
  obtain ⟨hn1, hnR, _, hnhi⟩ := frozenOddHigh_mem R n hn
  have hmn : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  have hmnRR : m * n < R * R := by
    have h1 : m * n < R * n := Nat.mul_lt_mul_of_pos_right hmR (by omega)
    have h2 : R * n < R * R := Nat.mul_lt_mul_of_pos_left hnR (by omega)
    omega
  have h4 : R * R ≤ (2 * m) * (2 * n) :=
    Nat.mul_le_mul hmhi hnhi
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  have hXeq : (R ^ 2 - 1) + 1 = R ^ 2 := Nat.sub_add_cancel hsq
  have hmnR2 : m * n < R ^ 2 := by nlinarith [hmnRR]
  have hXlo : m * n ≤ R ^ 2 - 1 := by omega
  have hfour : R ^ 2 ≤ 4 * (m * n) := by nlinarith [h4]
  have hXhi : R ^ 2 - 1 < 4 * (m * n) := by omega
  constructor
  · apply (Nat.le_div_iff_mul_le hmn).2
    simpa using hXlo
  · apply (Nat.div_lt_iff_lt_mul hmn).2
    nlinarith

/-- Exact three-step floor identity. It is not a floor approximation. -/
theorem frozenOddHigh_floor_eq_three_masks
    (R m n : ℕ) (hR : 2 ≤ R)
    (hm : m ∈ frozenOddHighParents R)
    (hn : n ∈ frozenOddHighParents R) :
    (((R ^ 2 - 1) / (m * n) : ℕ) : ℤ) =
      1 +
      (if 2 * m * n ≤ R ^ 2 - 1 then (1 : ℤ) else 0) +
      (if 3 * m * n ≤ R ^ 2 - 1 then (1 : ℤ) else 0) := by
  have hmn : 0 < m * n := by
    have hm1 := (frozenOddHigh_mem R m hm).1
    have hn1 := (frozenOddHigh_mem R n hn).1
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨hlo, hhi⟩ := frozenOddHigh_floor_one_to_three R m n hR hm hn
  have htwo : (2 ≤ (R ^ 2 - 1) / (m * n)) ↔
      2 * m * n ≤ R ^ 2 - 1 := by
    simpa [Nat.mul_assoc] using
      (Nat.le_div_iff_mul_le hmn :
        2 ≤ (R ^ 2 - 1) / (m * n) ↔ 2 * (m * n) ≤ R ^ 2 - 1)
  have hthree : (3 ≤ (R ^ 2 - 1) / (m * n)) ↔
      3 * m * n ≤ R ^ 2 - 1 := by
    simpa [Nat.mul_assoc] using
      (Nat.le_div_iff_mul_le hmn :
        3 ≤ (R ^ 2 - 1) / (m * n) ↔ 3 * (m * n) ≤ R ^ 2 - 1)
  split_ifs <;> omega

/-- UNCONDITIONAL, ALL-ROOT, ORIGINAL-MOBIUS HIGH-HIGH IDENTITY.
The only terms are the historical square and q=2,3 signed masks. -/
theorem frozenOddHighPairFloor_eq_mass_square_add_two_masks
    (R : ℕ) (hR : 2 ≤ R) :
    frozenOddHighPairFloor R =
      frozenOddHighMass R ^ 2 +
        frozenOddHighPairMask R 2 + frozenOddHighPairMask R 3 := by
  unfold frozenOddHighPairFloor frozenOddHighMass frozenOddHighPairMask
  rw [pow_two (∑ m ∈ frozenOddHighParents R, (μ m : ℤ)), Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [frozenOddHigh_floor_eq_three_masks R m n hR hm hn]
  split_ifs <;> ring

/-- Exact signed defect after subtracting the historical square.
No separate absolute value or probabilistic parity estimate is used. -/
theorem frozenOddHighPairFloor_sub_mass_square
    (R : ℕ) (hR : 2 ≤ R) :
    frozenOddHighPairFloor R - frozenOddHighMass R ^ 2 =
      frozenOddHighPairMask R 2 + frozenOddHighPairMask R 3 := by
  rw [frozenOddHighPairFloor_eq_mass_square_add_two_masks R hR]
  ring


/-- The odd root-adjacent carrier is exactly the established dyadic annulus
at B=R-1. This is a set equality, not a statistical approximation. -/
theorem frozenOddHighParents_eq_dyadicBoundary (R : ℕ) (hR : 2 ≤ R) :
    frozenOddHighParents R = dyadicCofactorBoundary (R - 1) := by
  ext m
  simp only [frozenOddHighParents, Finset.mem_filter, Finset.mem_Ico,
    mem_dyadicCofactorBoundary]
  omega

/-- The historical odd-HIGH mass IS the original Mertens prefix, in the
repository's exact complex source coordinate. No post-root Mobius value. -/
theorem frozenOddHighMass_cast_eq_mertensSummatory
    (R : ℕ) (hR : 2 ≤ R) :
    (frozenOddHighMass R : ℂ) =
      RHLean.Analysis.mertensSummatory (R - 1) := by
  have hset := frozenOddHighParents_eq_dyadicBoundary R hR
  calc
    (frozenOddHighMass R : ℂ) =
      ∑ m ∈ frozenOddHighParents R, (((μ m : ℤ) : ℂ)) := by
        simp [frozenOddHighMass]
    _ = dyadicCofactorBoundaryMass (R - 1) := by
      rw [hset]
      rfl
    _ = RHLean.Analysis.mertensSummatory (R - 1) :=
      (mertensSummatory_eq_dyadicCofactorBoundaryMass (R - 1)).symm

/-- DIRECT ALL-ROOT MERTENS VERSION: the HIGH-HIGH physical floor packet
is the genuine historical M(R-1)^2 plus ONLY the q=2,3 signed hyperbola
masks. This composes two separately proved exact source identities. -/
theorem frozenOddHighPairFloor_cast_eq_historicalMertens_square_add_masks
    (R : ℕ) (hR : 2 ≤ R) :
    (frozenOddHighPairFloor R : ℂ) =
      RHLean.Analysis.mertensSummatory (R - 1) ^ 2 +
        (frozenOddHighPairMask R 2 : ℂ) +
        (frozenOddHighPairMask R 3 : ℂ) := by
  have h : (frozenOddHighPairFloor R : ℂ) =
      (frozenOddHighMass R : ℂ) ^ 2 +
        (frozenOddHighPairMask R 2 : ℂ) +
        (frozenOddHighPairMask R 3 : ℂ) := by
    exact_mod_cast (frozenOddHighPairFloor_eq_mass_square_add_two_masks R hR)
  rw [frozenOddHighMass_cast_eq_mertensSummatory R hR] at h
  exact h

end RHLean.Proof
