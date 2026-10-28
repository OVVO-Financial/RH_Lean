import Mathlib

/-!
# Exact obstruction: global Mertens-size bounds do not imply shell L2

Construct a completely deterministic signed population which is constant
on each square block and alternates the block sign. Its square-endpoint
partial sums have amplitude exactly R, an RH-scale O(sqrt x) bound, while
each block increment has amplitude 2R+1 and hence dyadic squared energy
at least 4H^3.

This shows that EVEN a hypothetical RH-strength global prefix bound is
insufficient by itself to estimate L2 of sharply localized square-shell
increments. A genuine nontrivial moment/localization theorem on the
original Mobius source, not a rewriting of the imported 7/8 global
covariance statement, is necessary.

The construction is a COUNTEREXAMPLE TO AN INFERENCE FOR GENERAL SIGNED
SEQUENCES, not a claim that real Mobius has this behavior.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

def oaiAltSquarePrefix (R : ℕ) : ℤ :=
  if R % 2 = 0 then -(R : ℤ) else (R : ℤ)

def oaiAltSquareIncrement (R : ℕ) : ℤ :=
  oaiAltSquarePrefix (R + 1) - oaiAltSquarePrefix R

/-- The complete deterministic prefix is as small as root scale. -/
theorem oaiAltSquarePrefix_abs_le (R : ℕ) :
    |oaiAltSquarePrefix R| ≤ (R : ℤ) := by
  by_cases h : R % 2 = 0
  · simp [oaiAltSquarePrefix, h]
  · simp [oaiAltSquarePrefix, h]

/-- Nevertheless, every sampled square-block increment is maximum size,
with alternating orientation. -/
theorem oaiAltSquareIncrement_exact (R : ℕ) :
    oaiAltSquareIncrement R =
      if R % 2 = 0 then ((2 * R + 1 : ℕ) : ℤ)
      else -((2 * R + 1 : ℕ) : ℤ) := by
  by_cases h : R % 2 = 0
  · have hs : (R + 1) % 2 ≠ 0 := by omega
    simp [oaiAltSquareIncrement, oaiAltSquarePrefix, h, hs]
    omega
  · have hs : (R + 1) % 2 = 0 := by omega
    simp [oaiAltSquareIncrement, oaiAltSquarePrefix, h, hs]
    omega

/-- The squared increment has the FULL BLOCK WIDTH squared, rather than
random-sign size, despite the previous globally tiny prefix. -/
theorem oaiAltSquareIncrement_sq (R : ℕ) :
    oaiAltSquareIncrement R ^ 2 = (((2 * R + 1 : ℕ) : ℤ)) ^ 2 := by
  rw [oaiAltSquareIncrement_exact]
  split_ifs <;> ring

/-- The dyadic energy of the countermodel is at least 4H^3.
This is the rigorous obstruction to any purported global-7/8-to-shell
L2 implication using only upper bounds on prefixes. -/
theorem oaiAltSquareDyadicEnergy_cubic_lower (H : ℕ) :
    4 * (H : ℤ) ^ 3 ≤
      ∑ R ∈ Finset.Ico H (2 * H), oaiAltSquareIncrement R ^ 2 := by
  have hcount : (Finset.Ico H (2 * H)).card = H := by
    simp [Nat.card_Ico]
    omega
  have hpoint (R : ℕ) (hR : R ∈ Finset.Ico H (2 * H)) :
      4 * (H : ℤ) ^ 2 ≤ oaiAltSquareIncrement R ^ 2 := by
    rw [oaiAltSquareIncrement_sq]
    have hr : H ≤ R := (Finset.mem_Ico.mp hR).1
    have hcast : (H : ℤ) ≤ (R : ℤ) := by exact_mod_cast hr
    have hh : 0 ≤ (H : ℤ) := Int.natCast_nonneg H
    have hn : 0 ≤ (R : ℤ) := Int.natCast_nonneg R
    push_cast
    nlinarith [sq_nonneg ((R : ℤ) - (H : ℤ))]
  calc
    4 * (H : ℤ) ^ 3 =
        ∑ R ∈ Finset.Ico H (2 * H), 4 * (H : ℤ) ^ 2 := by
          simp [hcount]
          ring
    _ ≤ _ := Finset.sum_le_sum (fun R hR => hpoint R hR)

#print axioms oaiAltSquarePrefix_abs_le
#print axioms oaiAltSquareIncrement_exact
#print axioms oaiAltSquareIncrement_sq
#print axioms oaiAltSquareDyadicEnergy_cubic_lower

end RHLean.Analysis
