import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_INCIDENCE_KERNEL»
import «research.RECIPROCAL_COVARIANCE_PAIR_AMPLITUDE_CONTRACTION»

/-!
# Threshold incidence to reciprocal Euler currency

The finite threshold kernel lives on a current first-owner incidence `p`, while
recursive covariance descent is controlled by the next separating owner `r`.
These are different coordinates.  The bridge is therefore not an identification
of the two owners: it is an exact intertwining of their incidence operators.

For the threshold potential `F_R`, put

  g_p(n) = F_R(n) - F_R(p*n),
  E_p(n) = n * g_p(n).

Then a second owner difference has the exact reciprocal-Euler form

  g_p(n) - g_p(r*n)
    = (1/n) * (E_p(n) - (1/r) * E_p(r*n)).

Consequently the complete `r`-four-corner of the current `p`-incidence weight
is literally the reciprocal Mobius pair amplitude `mu(a)mu(b)/(ab)` times two
critical `1/r` Euler differences.  This is an exact currency conversion; no
contraction is asserted here.

At the support level, half-open threshold crossings are themselves incidence
differences of tail indicators, so the `p` and `r` incidences commute exactly.
If an `r`-child leaves the physical clock, its threshold potential, current
`p`-incidence weight, and Euler coordinate all vanish.  Thus a clipped next
owner is literally a one-ended reciprocal-Euler edge.

No norm, Cauchy--Schwarz estimate, spectral approximation, or RH input is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Multiplicative finite difference along one owner edge. -/
def lowOwnerMultiplicativeIncidence
    (p : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n - f (p * n)

/-- Multiplicative owner incidences commute exactly. -/
theorem lowOwnerMultiplicativeIncidence_comm
    (p r : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    lowOwnerMultiplicativeIncidence p
        (fun m => lowOwnerMultiplicativeIncidence r f m) n =
      lowOwnerMultiplicativeIncidence r
        (fun m => lowOwnerMultiplicativeIncidence p f m) n := by
  unfold lowOwnerMultiplicativeIncidence
  change
    (f n - f (r * n)) - (f (p * n) - f (r * (p * n))) =
      (f n - f (p * n)) - (f (r * n) - f (p * (r * n)))
  have hmul : p * (r * n) = r * (p * n) := by
    ac_rfl
  rw [hmul]
  ring

/-- Current first-owner threshold-incidence weight. -/
def lowOwnerThresholdOwnerIncidenceWeight
    (R p n : ℕ) : ℝ :=
  lowOwnerThresholdPotential R n -
    lowOwnerThresholdPotential R (p * n)

/-- The incidence weight is exactly the compiled AMP daughter-minus-root
crossing weight. -/
theorem lowOwnerThresholdOwnerIncidenceWeight_eq_crossing
    {R p n : ℕ} (hp : 1 ≤ p) :
    lowOwnerThresholdOwnerIncidenceWeight R p n =
      lowOwnerDaughterCrossingWeight R p n -
        lowOwnerRootCrossingIndicator R p n := by
  unfold lowOwnerThresholdOwnerIncidenceWeight
  exact lowOwnerThresholdPotential_sub_mul hp

/-- Euler lift of the current threshold-incidence weight. -/
def lowOwnerThresholdOwnerEulerWeight
    (R p n : ℕ) : ℝ :=
  (n : ℝ) * lowOwnerThresholdOwnerIncidenceWeight R p n

/-- Critical `1/r` Euler difference at the next owner. -/
def lowOwnerThresholdCriticalEulerDifference
    (R p r n : ℕ) : ℝ :=
  lowOwnerThresholdOwnerEulerWeight R p n -
    (1 / (r : ℝ)) * lowOwnerThresholdOwnerEulerWeight R p (r * n)

/-- The next-owner difference of the current incidence weight. -/
def lowOwnerThresholdSecondOwnerDifference
    (R p r n : ℕ) : ℝ :=
  lowOwnerThresholdOwnerIncidenceWeight R p n -
    lowOwnerThresholdOwnerIncidenceWeight R p (r * n)

/-- **Exact Euler normalization.**  The critical Euler difference is `n` times
the next-owner difference of the threshold incidence. -/
theorem lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference
    {R p r n : ℕ} (hr : 0 < r) :
    lowOwnerThresholdCriticalEulerDifference R p r n =
      (n : ℝ) * lowOwnerThresholdSecondOwnerDifference R p r n := by
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hr)
  unfold lowOwnerThresholdCriticalEulerDifference
    lowOwnerThresholdOwnerEulerWeight
    lowOwnerThresholdSecondOwnerDifference
  have hcast : (((r * n : ℕ) : ℝ)) = (r : ℝ) * (n : ℝ) := by
    norm_num
  rw [hcast]
  field_simp [hr0]

/-- Reciprocal form of the preceding normalization. -/
theorem lowOwnerThresholdSecondOwnerDifference_eq_reciprocalEuler
    {R p r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    lowOwnerThresholdSecondOwnerDifference R p r n =
      (1 / (n : ℝ)) *
        lowOwnerThresholdCriticalEulerDifference R p r n := by
  rw [lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]

/-- **Pair currency conversion.**  A two-coordinate second incidence is exactly
reciprocal pair amplitude times the two critical Euler differences. -/
theorem lowOwnerThresholdSecondOwnerPair_eq_reciprocalPair_mul_eulerDifferences
    {R p r a b : ℕ} (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    postRootZeroTargetPairExcess (a, b) *
        lowOwnerThresholdSecondOwnerDifference R p r a *
        lowOwnerThresholdSecondOwnerDifference R p r b =
      postRootCovarianceReciprocalPairAmplitude (a, b) *
        lowOwnerThresholdCriticalEulerDifference R p r a *
        lowOwnerThresholdCriticalEulerDifference R p r b := by
  rw [lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr,
    lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr]
  simp only [postRootZeroTargetPairExcess_eq_weight]
  unfold postRootCovarianceReciprocalPairAmplitude
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  push_cast
  field_simp [ha0, hb0]

/-- **Complete next-owner four-corner in reciprocal currency.**  After a current
`p`-incidence has been formed, a complete fresh `r` square is the reciprocal
Mobius pair amplitude multiplied by two critical `1/r` Euler differences. -/
theorem lowOwnerThresholdIncidence_fourCorner_eq_reciprocalEuler
    {R p r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : 0 < a) (hb : 0 < b) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerThresholdOwnerIncidenceWeight R p) r a b =
      postRootCovarianceReciprocalPairAmplitude (a, b) *
        lowOwnerThresholdCriticalEulerDifference R p r a *
        lowOwnerThresholdCriticalEulerDifference R p r b := by
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
    (lowOwnerThresholdOwnerIncidenceWeight R p) hr hra hrb]
  exact lowOwnerThresholdSecondOwnerPair_eq_reciprocalPair_mul_eulerDifferences
    hr.pos ha hb

/-- Prefix-tail indicator underlying one half-open crossing. -/
def lowOwnerThresholdTailIndicator (n y : ℕ) : ℝ :=
  if n ≤ y then 1 else 0

/-- A half-open threshold crossing is the incidence difference of two tail
indicators. -/
theorem lowOwnerThresholdCrossingIndicator_eq_tail_sub_mul
    {p a y : ℕ} (hp : 1 ≤ p) :
    lowOwnerThresholdCrossingIndicator p a y =
      lowOwnerThresholdTailIndicator a y -
        lowOwnerThresholdTailIndicator (p * a) y := by
  unfold lowOwnerThresholdCrossingIndicator lowOwnerThresholdTailIndicator
  have hapa : a ≤ p * a := by
    calc
      a = 1 * a := by simp
      _ ≤ p * a := Nat.mul_le_mul_right a hp
  by_cases ha : a ≤ y
  · by_cases hpa : p * a ≤ y
    · have hnot : ¬ y < p * a := Nat.not_lt_of_ge hpa
      simp [ha, hpa, hnot]
    · have hy : y < p * a := Nat.lt_of_not_ge hpa
      simp [ha, hpa, hy]
  · have hpa : ¬ p * a ≤ y := by
      intro h
      exact ha (hapa.trans h)
    simp [ha, hpa]

/-- **Support-level owner commutation.**  A second incidence of a `p` threshold
crossing is exactly the corresponding difference of `r` threshold crossings.
This is the literal edge dictionary behind the reciprocal-Euler lift. -/
theorem lowOwnerThresholdCrossing_secondIncidence_comm
    {p r a y : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) :
    lowOwnerThresholdCrossingIndicator p a y -
        lowOwnerThresholdCrossingIndicator p (r * a) y =
      lowOwnerThresholdCrossingIndicator r a y -
        lowOwnerThresholdCrossingIndicator r (p * a) y := by
  rw [lowOwnerThresholdCrossingIndicator_eq_tail_sub_mul hp,
    lowOwnerThresholdCrossingIndicator_eq_tail_sub_mul hp,
    lowOwnerThresholdCrossingIndicator_eq_tail_sub_mul hr,
    lowOwnerThresholdCrossingIndicator_eq_tail_sub_mul hr]
  have hmul : p * (r * a) = r * (p * a) := by
    ac_rfl
  rw [hmul]
  ring

/-- If the next owner child leaves the physical clock, the current p-incidence
weight at that child vanishes as well. -/
theorem lowOwnerThresholdOwnerIncidenceWeight_eq_zero_of_next_clipped
    {R p r n : ℕ} (hR : 2 ≤ R) (hp : 1 ≤ p)
    (hclip : squareRootEndpoint R < r * n) :
    lowOwnerThresholdOwnerIncidenceWeight R p (r * n) = 0 := by
  have hle : r * n ≤ p * (r * n) := by
    calc
      r * n = 1 * (r * n) := by simp
      _ ≤ p * (r * n) := Nat.mul_le_mul_right (r * n) hp
  have hclip' : squareRootEndpoint R < p * (r * n) :=
    hclip.trans_le hle
  unfold lowOwnerThresholdOwnerIncidenceWeight
  rw [lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hclip,
    lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hclip']
  ring

/-- Hence the Euler coordinate of a clipped next-owner child is exactly zero. -/
theorem lowOwnerThresholdOwnerEulerWeight_eq_zero_of_next_clipped
    {R p r n : ℕ} (hR : 2 ≤ R) (hp : 1 ≤ p)
    (hclip : squareRootEndpoint R < r * n) :
    lowOwnerThresholdOwnerEulerWeight R p (r * n) = 0 := by
  unfold lowOwnerThresholdOwnerEulerWeight
  rw [lowOwnerThresholdOwnerIncidenceWeight_eq_zero_of_next_clipped hR hp hclip]
  ring

/-- A clipped critical Euler edge has exactly one surviving endpoint. -/
theorem lowOwnerThresholdCriticalEulerDifference_eq_parent_of_next_clipped
    {R p r n : ℕ} (hR : 2 ≤ R) (hp : 1 ≤ p)
    (hclip : squareRootEndpoint R < r * n) :
    lowOwnerThresholdCriticalEulerDifference R p r n =
      lowOwnerThresholdOwnerEulerWeight R p n := by
  unfold lowOwnerThresholdCriticalEulerDifference
  rw [lowOwnerThresholdOwnerEulerWeight_eq_zero_of_next_clipped hR hp hclip]
  ring

end RHLean.Proof
