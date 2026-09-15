import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_CLIPPED_FUBINI»
import «research.GLOBAL_RETURNED_CORE_ZERO_TARGET_COVARIANCE»

/-!
# Threshold double corner is the exact reciprocal critical exit

For two prime coordinates `c < r` and one positive stripped site `u`, the
commuting threshold incidences have an exact two-boundary decomposition

  chi_r(u,W) - chi_r(c*u,W)
    = chi_c(u,W)
      - 1_{c*u <= W, r*u <= W < r*c*u}.

Thus the second-owner residual has only two geometric modes:

* the already-existing current-c clipped edge `chi_c(u,W)`;
* a double-corner boundary where both single children `c*u` and `r*u` are
  admitted but the double child `r*c*u` is clipped.

On that double-corner geometry the compiled critical three-term covariance
identity has all three indicators equal to one.  Its coefficient therefore
collapses exactly to

  -1 + (1-1/r)^2 + (1/r)(1-1/r) = -1/r.

So the double-corner boundary is not merely a clipped support class: it carries
exactly the reciprocal owner amplitude whose square is `1/r^2`.

No approximation, Cauchy--Schwarz estimate, or spectral tail bound is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Both one-prime children are admitted at W while the double child is clipped. -/
def lowOwnerThresholdDoubleCornerBoundary
    (c r u W : ℕ) : ℝ :=
  if c * u ≤ W ∧ r * u ≤ W ∧ W < r * (c * u) then 1 else 0

/-- **Exact two-boundary decomposition of commuting threshold incidences.** -/
theorem lowOwnerThresholdClippedDifference_eq_current_sub_doubleCorner
    {c r u W : ℕ}
    (hc : c.Prime) (hr : r.Prime) (hcr : c < r) (hu : 0 < u) :
    lowOwnerThresholdClippedDifference c r u W =
      lowOwnerThresholdCrossingIndicator c u W -
        lowOwnerThresholdDoubleCornerBoundary c r u W := by
  have hu_cu : u ≤ c * u := by
    calc
      u = 1 * u := by simp
      _ ≤ c * u := Nat.mul_le_mul_right u hc.one_le
  have hcu_ru : c * u ≤ r * u :=
    Nat.mul_le_mul_right u (Nat.le_of_lt hcr)
  have hru_rcu : r * u ≤ r * (c * u) :=
    Nat.mul_le_mul_left r hu_cu
  unfold lowOwnerThresholdClippedDifference
    lowOwnerThresholdCrossingIndicator
    lowOwnerThresholdDoubleCornerBoundary
  split_ifs <;> norm_num <;> omega

/-- On a genuine clipped first-crossing square, the critical three-term
identity collapses to exactly `-1/r` times the parent zero-target excess. -/
theorem zeroTargetCriticalFourCorner_eq_neg_reciprocal_of_clippedFirstCrossing
    {W r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hraW : r * a ≤ W)
    (hlcmW : Nat.lcm a b ≤ W)
    (hwall : W < r * Nat.lcm a b)
    (hclip : W < r * b) :
    zeroTargetMellinPhysicalSuperLcmFourCorner W r
        (zeroTargetCriticalOwnerRatio r) a b =
      -(1 / (r : ℝ)) * postRootZeroTargetPairExcess (a, b) := by
  rw [zeroTargetMellinPhysicalSuperLcmFourCorner_critical_eq_threeTerm
    hr hra hrb hab hbW hraW]
  unfold zeroTargetCriticalFirstCrossingIndicator
    zeroTargetCriticalContinuationIndicator
    zeroTargetCriticalClippedExitIndicator
  simp [hlcmW, hwall, hraW, hclip]
  ring

/-- The LCM of a site and its c-child is exactly that child. -/
theorem lowOwner_lcm_parent_child (c u : ℕ) :
    Nat.lcm u (c * u) = c * u := by
  apply Nat.dvd_antisymm
  · apply (Nat.lcm_dvd_iff).2
    constructor
    · exact ⟨c, by simp [Nat.mul_comm]⟩
    · exact dvd_rfl
  · exact Nat.dvd_lcm_right u (c * u)

/-- A larger prime r is fresh to the c-child whenever it is fresh to u. -/
theorem largerPrime_not_dvd_child
    {c r u : ℕ}
    (hc : c.Prime) (hr : r.Prime) (hcr : c < r)
    (hru : ¬ r ∣ u) :
    ¬ r ∣ c * u := by
  have hrc : ¬ r ∣ c := by
    intro h
    have heq : r = c := (Nat.prime_dvd_prime_iff_eq hr hc).mp h
    omega
  intro h
  rcases hr.dvd_mul.mp h with hrc' | hru'
  · exact hrc hrc'
  · exact hru hru'

/-- **Double-corner reciprocal collapse.**  If `c*u` and `r*u` are admitted but
`r*c*u` is clipped, the critical r-square on the parent pair `(u,c*u)` is
exactly `-1/r` times its zero-target excess. -/
theorem zeroTargetCriticalFourCorner_parentChild_doubleCorner_eq_neg_reciprocal
    {W c r u : ℕ}
    (hc : c.Prime) (hr : r.Prime) (hcr : c < r) (hu : 0 < u)
    (hru : ¬ r ∣ u)
    (hcuW : c * u ≤ W) (hruW : r * u ≤ W)
    (hdouble : W < r * (c * u)) :
    zeroTargetMellinPhysicalSuperLcmFourCorner W r
        (zeroTargetCriticalOwnerRatio r) u (c * u) =
      -(1 / (r : ℝ)) *
        postRootZeroTargetPairExcess (u, c * u) := by
  have hruChild : ¬ r ∣ c * u :=
    largerPrime_not_dvd_child hc hr hcr hru
  have hu_cu : u ≤ c * u := by
    calc
      u = 1 * u := by simp
      _ ≤ c * u := Nat.mul_le_mul_right u hc.one_le
  have hlcm := lowOwner_lcm_parent_child c u
  apply zeroTargetCriticalFourCorner_eq_neg_reciprocal_of_clippedFirstCrossing
    hr hru hruChild hu_cu hcuW hruW
  · simpa [hlcm] using hcuW
  · simpa [hlcm] using hdouble
  · exact hdouble

/-- Active double-corner indicator gives the hypotheses of the reciprocal
collapse automatically. -/
theorem zeroTargetCriticalFourCorner_of_doubleCornerIndicator
    {W c r u : ℕ}
    (hc : c.Prime) (hr : r.Prime) (hcr : c < r) (hu : 0 < u)
    (hru : ¬ r ∣ u)
    (hdouble : lowOwnerThresholdDoubleCornerBoundary c r u W = 1) :
    zeroTargetMellinPhysicalSuperLcmFourCorner W r
        (zeroTargetCriticalOwnerRatio r) u (c * u) =
      -(1 / (r : ℝ)) *
        postRootZeroTargetPairExcess (u, c * u) := by
  unfold lowOwnerThresholdDoubleCornerBoundary at hdouble
  by_cases h : c * u ≤ W ∧ r * u ≤ W ∧ W < r * (c * u)
  · exact zeroTargetCriticalFourCorner_parentChild_doubleCorner_eq_neg_reciprocal
      hc hr hcr hu hru h.1 h.2.1 h.2.2
  · simp [h] at hdouble

/-- Squaring the exact double-corner amplitude produces the literal reciprocal
square coefficient. -/
theorem zeroTargetCriticalDoubleCorner_reciprocalCoefficient_sq
    (r : ℕ) :
    (-(1 / (r : ℝ))) ^ 2 = (1 / (r : ℝ)) ^ 2 := by
  ring

end RHLean.Proof
