import Mathlib
import RHLean.Arithmetic.CanonicalTerminalPrimeExtension
import RHLean.Proof.RealSquareBlockIncrements

/-!
# Canonical square-block activation zones

This module packages the largest-prime / lowest-cofactor population process as
an exact finite set of canonical activation triples and introduces the small,
transition, and large terminal-prime zones.  The exact three-zone decomposition
is proved without an analytic premise.  The transition cardinality and the two
outer cancellation estimates are exposed separately.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The finite square block `[m^2,(m+1)^2)`. -/
def canonicalPopulationBlock (m : ℕ) : Finset ℕ :=
  Finset.Ico (m ^ 2) ((m + 1) ^ 2)

/-- A bounded triple `(n,c,q)` is a canonical activation when `n=cq`, `q` is
prime, and `q` is the greatest prime divisor of `n`. -/
def IsCanonicalActivationTriple (m : ℕ) (t : ℕ × (ℕ × ℕ)) : Prop :=
  t.1 ∈ canonicalPopulationBlock m ∧
  t.2.2.Prime ∧
  t.2.1 * t.2.2 = t.1 ∧
  IsGreatestPrimeDivisor t.1 t.2.2

instance instDecidableIsCanonicalActivationTriple (m : ℕ) (t : ℕ × (ℕ × ℕ)) :
    Decidable (IsCanonicalActivationTriple m t) := by
  unfold IsCanonicalActivationTriple IsGreatestPrimeDivisor
  infer_instance

/-- All bounded canonical activation triples for square block `m`.  The bound
`(m+1)^2+1` contains the endpoint, parent, and terminal prime of every triple. -/
def canonicalActivationTriples (m : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  let U := Finset.range ((m + 1) ^ 2 + 1)
  (U.product (U.product U)).filter (IsCanonicalActivationTriple m)

/-- Möbius weight attached to an activation triple. -/
def canonicalActivationWeight (t : ℕ × (ℕ × ℕ)) : ℝ :=
  moebiusReal t.1

/-- Total canonical activation sum.  Once existence is connected, uniqueness
identifies this with the ordinary Möbius increment of the square block. -/
def canonicalActivationSum (m : ℕ) : ℝ :=
  ∑ t ∈ canonicalActivationTriples m, canonicalActivationWeight t

/-- Contribution from terminal primes below `lower`. -/
def smallTerminalZoneSum (m lower : ℕ) : ℝ :=
  ∑ t ∈ canonicalActivationTriples m,
    if t.2.2 < lower then canonicalActivationWeight t else 0

/-- Contribution from terminal primes in the closed transition band
`[lower,upper]`. -/
def transitionTerminalZoneSum (m lower upper : ℕ) : ℝ :=
  ∑ t ∈ canonicalActivationTriples m,
    if lower ≤ t.2.2 ∧ t.2.2 ≤ upper then canonicalActivationWeight t else 0

/-- Contribution from terminal primes above `upper`. -/
def largeTerminalZoneSum (m upper : ℕ) : ℝ :=
  ∑ t ∈ canonicalActivationTriples m,
    if upper < t.2.2 then canonicalActivationWeight t else 0

/-- Exact three-zone decomposition for arbitrary ordered integer thresholds. -/
theorem canonicalActivationSum_eq_three_zones
    (m lower upper : ℕ) (hlu : lower ≤ upper) :
    canonicalActivationSum m =
      smallTerminalZoneSum m lower +
        transitionTerminalZoneSum m lower upper +
          largeTerminalZoneSum m upper := by
  unfold canonicalActivationSum smallTerminalZoneSum
    transitionTerminalZoneSum largeTerminalZoneSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hsmall : t.2.2 < lower
  · have hnotTransition : ¬(lower ≤ t.2.2 ∧ t.2.2 ≤ upper) := by
      intro h
      exact (not_lt_of_ge h.1) hsmall
    have hnotLarge : ¬upper < t.2.2 := by
      exact not_lt_of_ge (hlu.trans (Nat.le_of_lt hsmall))
    simp [hsmall, hnotTransition, hnotLarge]
  · have hlower : lower ≤ t.2.2 := Nat.le_of_not_gt hsmall
    by_cases htransition : t.2.2 ≤ upper
    · have hnotLarge : ¬upper < t.2.2 := not_lt_of_ge htransition
      simp [hsmall, hlower, htransition, hnotLarge]
    · have hlarge : upper < t.2.2 := Nat.lt_of_not_ge htransition
      simp [hsmall, hlower, htransition, hlarge]

/-- Integer half-width thresholds corresponding to a narrow band around the
square-root scale. -/
def transitionLower (m r : ℕ) : ℕ := m - r

def transitionUpper (m r : ℕ) : ℕ := m + r

/-- The transition-band triple set. -/
def transitionActivationTriples (m r : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (canonicalActivationTriples m).filter fun t =>
    transitionLower m r ≤ t.2.2 ∧ t.2.2 ≤ transitionUpper m r

/-- Elementary transition-band counting target.  The condition `2r ≤ m`
keeps the terminal prime uniformly comparable to `m`; an absolute constant
then bounds the number of possible parents for each candidate terminal value. -/
def CanonicalTransitionBandCountStatement : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ m r : ℕ, 1 ≤ m → 2 * r ≤ m →
      (transitionActivationTriples m r).card ≤ C * (2 * r + 1)

/-- Consequence target converting transition-band cardinality into an absolute
Möbius bound. -/
def CanonicalTransitionBandWeightStatement : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ m r : ℕ, 1 ≤ m → 2 * r ≤ m →
      |transitionTerminalZoneSum m (transitionLower m r) (transitionUpper m r)| ≤
        (C * (2 * r + 1) : ℕ)

/-- Fixed-proportion lower terminal threshold `m-floor(num*m/den)`. -/
def proportionalLower (m num den : ℕ) : ℕ :=
  m - (num * m) / den

/-- Fixed-proportion upper terminal threshold `m+floor(num*m/den)`. -/
def proportionalUpper (m num den : ℕ) : ℕ :=
  m + (num * m) / den

/-- Frozen-prefix cancellation target for the large-terminal-prime zone. -/
def LargeTerminalZoneCancellationStatement : Prop :=
  ∀ num den : ℕ, 0 < num → num < den →
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        |largeTerminalZoneSum m (proportionalUpper m num den)| ≤ ε * m

/-- Deep-ancestry cancellation target for the small-terminal-prime zone. -/
def SmallTerminalZoneCancellationStatement : Prop :=
  ∀ num den : ℕ, 0 < num → num < den →
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        |smallTerminalZoneSum m (proportionalLower m num den)| ≤ ε * m

/-- Exact statement that canonical activation sums equal the ordinary real
square-block increments once every endpoint has its unique canonical triple. -/
def CanonicalActivationSumIdentificationStatement : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    canonicalActivationSum m = RHLean.Proof.realCanonicalTotalIncrement m

/-- The qualitative square-block target reached from the three-zone argument. -/
def CanonicalSquareBlockLittleOStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      |RHLean.Proof.realCanonicalTotalIncrement m| ≤ ε * m

end RHLean.Analysis
