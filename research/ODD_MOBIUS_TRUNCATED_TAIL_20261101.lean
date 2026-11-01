import Mathlib
import «research.ODD_MOBIUS_FLOOR_TELESCOPE_20261101»

/-!
# Truncated odd Möbius floor tail

This module exposes the exact truncation interface needed by the accepted
near-root prime-ray argument.  A positive odd-cofactor prefix is the complete
finite odd Möbius telescope minus its explicitly displayed omitted tail.
When the completion interval has quotient one, the tail reduces to the
literal signed Möbius sum on that interval.

These are finite structural identities.  No tail estimate, moment bound,
complete-source gain, canonical VF theorem, or RH statement is assumed or
proved.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- The admitted positive odd-cofactor prefix with the original floor weight. -/
def oddMoebiusFloorPrefix (A L : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 L,
    if Odd m then
      (ArithmeticFunction.moebius m : ℤ) * ((A / m : ℕ) : ℤ)
    else 0

/-- The omitted completion tail, retaining its original floor weight. -/
def oddMoebiusFloorTail (A L : ℕ) : ℤ :=
  ∑ m ∈ Finset.Ioc L A,
    if Odd m then
      (ArithmeticFunction.moebius m : ℤ) * ((A / m : ℕ) : ℤ)
    else 0

/-- The literal signed odd Möbius tail after the floor quotient is known to be one. -/
def oddMoebiusTail (L A : ℕ) : ℤ :=
  ∑ m ∈ Finset.Ioc L A,
    if Odd m then ArithmeticFunction.moebius m else 0

/-- Exact finite split of the complete telescope into the admitted prefix and
its omitted upper tail. -/
theorem oddMoebiusFloorPrefix_add_tail
    (A L : ℕ) (hLA : L ≤ A) :
    oddMoebiusFloorPrefix A L + oddMoebiusFloorTail A L =
      oddMoebiusFloorSum A := by
  have hdisj : Disjoint (Finset.Icc 1 L) (Finset.Ioc L A) := by
    rw [Finset.disjoint_left]
    intro m hmPrefix hmTail
    simp only [Finset.mem_Icc] at hmPrefix
    simp only [Finset.mem_Ioc] at hmTail
    omega
  have hcover : Finset.Icc 1 L ∪ Finset.Ioc L A = Finset.Icc 1 A := by
    ext m
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold oddMoebiusFloorPrefix oddMoebiusFloorTail oddMoebiusFloorSum
  rw [← Finset.sum_union hdisj, hcover]

/-- If the omitted interval is shorter than one doubling, every floor quotient
there is exactly one, so the floor tail is the literal signed Möbius tail. -/
theorem oddMoebiusFloorTail_eq_tail
    (A L : ℕ) (hshort : A < 2 * (L + 1)) :
    oddMoebiusFloorTail A L = oddMoebiusTail L A := by
  unfold oddMoebiusFloorTail oddMoebiusTail
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_Ioc] at hm
  have hdiv : A / m = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  simp [hdiv]

/-- Source-faithful truncated-tail interface: the admitted prefix is the
power-of-two count minus the explicit omitted signed tail. -/
theorem oddMoebiusFloorPrefix_eq_count_sub_tail
    (A L : ℕ) (hLA : L ≤ A) (hshort : A < 2 * (L + 1)) :
    oddMoebiusFloorPrefix A L =
      finitePowerOfTwoCount A - oddMoebiusTail L A := by
  have hsplit := oddMoebiusFloorPrefix_add_tail A L hLA
  rw [oddMoebiusFloorTail_eq_tail A L hshort,
    oddMoebiusFloorSum_eq_finitePowerOfTwoCount] at hsplit
  omega

#print axioms oddMoebiusFloorPrefix_add_tail
#print axioms oddMoebiusFloorTail_eq_tail
#print axioms oddMoebiusFloorPrefix_eq_count_sub_tail

end RHLean.Analysis
