import Mathlib
import «research.EULER_FRACTIONAL_COUPLED_20261027»

/-!
# Exact odd-doubling conservation packet

For an odd positive modulus `d`, the remainder modulo `2*d` is either the
remainder modulo `d` or that remainder plus `d`.  Consequently columns whose
completed coefficients are `c` at `d` and `-2*c` at `2*d` form a binary
packet.  This is the arithmetic core of the original-source odd-doubling
packet; no estimate, static high-product grouping, or source admission beyond
the completed columns is asserted.

The Euclidean statement is stronger than the square-clock specialization: it
holds for every numerator `X`, not only `R^2-1`.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

/-- The completed `d,2d` packet with coefficients `c,-2c`. -/
def oddDoublingPacket (c : ℚ) (d X : ℕ) : ℚ :=
  2 * c * ((X % d : ℕ) : ℚ) / (d : ℚ) -
    4 * c * ((X % (2 * d) : ℕ) : ℚ) / ((2 * d : ℕ) : ℚ)

/-- The remainder modulo twice a positive modulus is one of its two lifts. -/
theorem mod_two_mul_eq_mod_or_mod_add
    {X d : ℕ} (hd : 0 < d) :
    X % (2 * d) = X % d ∨ X % (2 * d) = X % d + d := by
  have hdiv : d ∣ 2 * d := by
    refine ⟨2, ?_⟩
    omega
  have hmod : X % (2 * d) % d = X % d :=
    Nat.mod_mod_of_dvd X hdiv
  have hlt : X % (2 * d) < 2 * d :=
    Nat.mod_lt X (by omega)
  have hq : X % (2 * d) / d < 2 := by
    apply (Nat.div_lt_iff_lt_mul hd).2
    simpa [Nat.mul_comm] using hlt
  have hdecomp := Nat.mod_add_div (X % (2 * d)) d
  have hqcases : X % (2 * d) / d = 0 ∨ X % (2 * d) / d = 1 := by
    omega
  rcases hqcases with hq0 | hq1
  · left
    rw [hmod, hq0] at hdecomp
    omega
  · right
    rw [hmod, hq1] at hdecomp
    omega

/-- Every completed odd-doubling packet is exactly `0` or `-2*c`. -/
theorem oddDoublingPacket_eq_zero_or_neg_two_mul
    (c : ℚ) {d X : ℕ} (hd : 0 < d) :
    oddDoublingPacket c d X = 0 ∨
      oddDoublingPacket c d X = -2 * c := by
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hd)
  rcases mod_two_mul_eq_mod_or_mod_add (X := X) hd with h | h
  · left
    unfold oddDoublingPacket
    rw [h]
    push_cast
    field_simp [hdq]
    ring
  · right
    unfold oddDoublingPacket
    rw [h]
    push_cast
    field_simp [hdq]
    ring

/-- Centering by the exact principal value `-c` leaves constant square. -/
theorem oddDoublingPacket_centered_sq
    (c : ℚ) {d X : ℕ} (hd : 0 < d) :
    (oddDoublingPacket c d X + c) ^ 2 = c ^ 2 := by
  rcases oddDoublingPacket_eq_zero_or_neg_two_mul c hd with h | h
  · rw [h]
    ring
  · rw [h]
    ring

/-- The original square-clock specialization, with `X_R = R^2-1`. -/
def nativeEulerOddDoublingPacket (c : ℚ) (d R : ℕ) : ℚ :=
  oddDoublingPacket c d (squareRootEndpoint R)

/-- Pointwise conservation for the genuine square-clock numerator. -/
theorem nativeEulerOddDoublingPacket_centered_sq
    (c : ℚ) {d R : ℕ} (hd : 0 < d) :
    (nativeEulerOddDoublingPacket c d R + c) ^ 2 = c ^ 2 := by
  exact oddDoublingPacket_centered_sq c hd

/-- Exact full `2d`-root energy.  No incomplete-window sign is asserted. -/
theorem nativeEulerOddDoublingPacket_period_energy
    (c : ℚ) {d : ℕ} (hd : 0 < d) :
    (∑ R ∈ Finset.range (2 * d),
      (nativeEulerOddDoublingPacket c d R + c) ^ 2) =
      (2 * d : ℕ) * c ^ 2 := by
  calc
    (∑ R ∈ Finset.range (2 * d),
      (nativeEulerOddDoublingPacket c d R + c) ^ 2) =
        ∑ _R ∈ Finset.range (2 * d), c ^ 2 := by
          apply Finset.sum_congr rfl
          intro R _hR
          exact nativeEulerOddDoublingPacket_centered_sq c hd
    _ = (2 * d : ℕ) * c ^ 2 := by simp

#print axioms mod_two_mul_eq_mod_or_mod_add
#print axioms oddDoublingPacket_eq_zero_or_neg_two_mul
#print axioms oddDoublingPacket_centered_sq
#print axioms nativeEulerOddDoublingPacket_centered_sq
#print axioms nativeEulerOddDoublingPacket_period_energy

end RHLean.Proof
