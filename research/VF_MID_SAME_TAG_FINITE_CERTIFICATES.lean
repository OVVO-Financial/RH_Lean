import Mathlib
import «research.VF_MID_SAME_TAG_DYADIC_FIBRE»

/-!
# Finite prime certificates: sharp four-owner window and root separation

These are numerical regressions on genuine prime carriers. The bounds
are universal theorems in VF_MID_SAME_TAG_SHARP_PACKET; these checks
certify that the constants cannot be tightened by simply changing
the counting or spacing inequalities.

No global NNS source admission is inferred. All square roots are certified
by two inequalities, not floating-point approximations.
-/

namespace RHLean.Analysis

private theorem vfMidSharpFour_sqrt3 :
    Nat.sqrt (3 * 11534351) = 5882 := by
  have hlo : 5882 ≤ Nat.sqrt (3 * 11534351) :=
    (Nat.le_sqrt').2 (by norm_num)
  have hhi : Nat.sqrt (3 * 11534351) < 5883 :=
    (Nat.sqrt_lt').2 (by norm_num)
  omega

private theorem vfMidSharpFour_sqrt5 :
    Nat.sqrt (5 * 11534351) = 7594 := by
  have hlo : 7594 ≤ Nat.sqrt (5 * 11534351) :=
    (Nat.le_sqrt').2 (by norm_num)
  have hhi : Nat.sqrt (5 * 11534351) < 7595 :=
    (Nat.sqrt_lt').2 (by norm_num)
  omega

private theorem vfMidSharpFour_sqrt7 :
    Nat.sqrt (7 * 11534351) = 8985 := by
  have hlo : 8985 ≤ Nat.sqrt (7 * 11534351) :=
    (Nat.le_sqrt').2 (by norm_num)
  have hhi : Nat.sqrt (7 * 11534351) < 8986 :=
    (Nat.sqrt_lt').2 (by norm_num)
  omega

private theorem vfMidSharpFour_sqrt11 :
    Nat.sqrt (11 * 11534351) = 11264 := by
  have hlo : 11264 ≤ Nat.sqrt (11 * 11534351) :=
    (Nat.le_sqrt').2 (by norm_num)
  have hhi : Nat.sqrt (11 * 11534351) < 11265 :=
    (Nat.sqrt_lt').2 (by norm_num)
  omega

/-- The finite physical four-owner witness reaches the universal card cap.
The single historical prime is q=11534351; roots are 5882,7594,8985,11264.
The window length 5383 is strictly below 6144. -/
theorem vfMidSameTagWindow_sharp_four_witness :
    (vfMidSameTagWindow 11534351 5882 11265).card = 4 := by
  have h3 : 3 ∈ vfMidSameTagWindow 11534351 5882 11265 := by
    rw [mem_vfMidSameTagWindow]
    norm_num [vfMidSharpFour_sqrt3]
  have h5 : 5 ∈ vfMidSameTagWindow 11534351 5882 11265 := by
    rw [mem_vfMidSameTagWindow]
    norm_num [vfMidSharpFour_sqrt5]
  have h7 : 7 ∈ vfMidSameTagWindow 11534351 5882 11265 := by
    rw [mem_vfMidSameTagWindow]
    norm_num [vfMidSharpFour_sqrt7]
  have h11 : 11 ∈ vfMidSameTagWindow 11534351 5882 11265 := by
    rw [mem_vfMidSameTagWindow]
    norm_num [vfMidSharpFour_sqrt11]
  have hsub :
      ({3, 5, 7, 11} : Finset ℕ) ⊆
        vfMidSameTagWindow 11534351 5882 11265 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h | h | h
    · simpa [h] using! h3
    · simpa [h] using! h5
    · simpa [h] using! h7
    · simpa [h] using! h11
  have hfour : 4 ≤ (vfMidSameTagWindow 11534351 5882 11265).card := by
    have hcard := Finset.card_le_card hsub
    norm_num at hcard ⊢
    exact hcard
  exact le_antisymm
    (vfMidSameTagWindow_card_le_four 11534351 5882 11265
      (by norm_num)) hfour

/-- Genuine primality of the shared historical tag in the sharp witness. -/
theorem vfMidSameTagWindow_sharp_four_historical_prime :
    Nat.Prime 11534351 := by
  norm_num

/-! The 34-bit prime q=10633609379 is externally certified by
complete trial division in the October 14 census. Mathlib's direct
norm_num prime proof for >25-bit inputs exceeds kernel depth, while
a naive ZMod Lucas decidability proof exhausts CI stack. Hence
the following witness is CONDITIONAL on q.Prime, not a compiled
proof of that finite primality assertion. No new axiom is introduced. -/

/-- Exact separation witness, from two prime owners and a genuine q:
the difference of the corresponding integer square roots equals 1024.
This certifies that 1025 is not a valid universal separation bound. -/
theorem vfMidSameTag_root_spacing_1024_sharp
    (_hq : Nat.Prime 10633609379) :
    Nat.Prime 10139 ∧ Nat.Prime 10141 ∧
      1024 * 10141 ≤ Nat.sqrt (10141 * 10633609379) ∧
      Nat.sqrt (10141 * 10633609379) =
        Nat.sqrt (10139 * 10633609379) + 1024 := by
  have hr1 : Nat.sqrt (10139 * 10633609379) = 10383360 := by
    have hlo : 10383360 ≤ Nat.sqrt (10139 * 10633609379) :=
      (Nat.le_sqrt').2 (by norm_num)
    have hhi : Nat.sqrt (10139 * 10633609379) < 10383361 :=
      (Nat.sqrt_lt').2 (by norm_num)
    omega
  have hr2 : Nat.sqrt (10141 * 10633609379) = 10384384 := by
    have hlo : 10384384 ≤ Nat.sqrt (10141 * 10633609379) :=
      (Nat.le_sqrt').2 (by norm_num)
    have hhi : Nat.sqrt (10141 * 10633609379) < 10384385 :=
      (Nat.sqrt_lt').2 (by norm_num)
    omega
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · rw [hr2]
  · rw [hr1, hr2]

#print axioms vfMidSameTagWindow_sharp_four_witness
#print axioms vfMidSameTagWindow_sharp_four_historical_prime
#print axioms vfMidSameTag_root_spacing_1024_sharp

end RHLean.Analysis
