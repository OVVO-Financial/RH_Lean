import Mathlib
import «research.VF_MID_915_PRIME_INTERVAL_LI_STRATIFICATION»

/-!
# #915: terminal top-third actual-prime / floor-Li transport

The historical odd cofactor carrier has a genuine blind sector:
if q > floor(B^2/3), there is NO proper odd multiple c*q (c >= 3)
at or before square endpoint B^2. This holds for all integers q,
regardless of whether they are actually prime or floor-Li-only events.

The primitive floor-Li backlog across [A^2,B^2] splits into the
top-third terminal mismatch plus the earlier descendant-eligible mismatch.
The terminal term cannot be bounded by a cofactor-only ancestry estimate.
Neither this split nor the arithmetic obstruction proves #915 hbalance.
-/

noncomputable section
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof

/-- Above the top-third cutoff there is no proper odd composite
descendant in the historical square endpoint B^2. -/
theorem vfMid915_topThird_noOddDescendant
    {B c q : ℕ} (hc : 3 ≤ c) (hq : B ^ 2 / 3 < q) :
    B ^ 2 < c * q := by
  have hthree : B ^ 2 < q * 3 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (3 : ℕ))).mp hq
  have hmul : 3 * q ≤ c * q :=
    Nat.mul_le_mul_right q hc
  nlinarith

/-- Consequently the top-third event cannot produce any proper odd
composite site in ANY prior square band r < B. -/
theorem vfMid915_topThird_notHistoricalOddComposite
    {B r c q : ℕ}
    (hc : 3 ≤ c) (hq : B ^ 2 / 3 < q)
    (hr : r + 1 ≤ B) :
    ¬ c * q ≤ (r + 1) ^ 2 := by
  intro hsite
  have hsq : (r + 1) * (r + 1) ≤ B * B :=
    Nat.mul_le_mul hr hr
  have htop := vfMid915_topThird_noOddDescendant hc hq
  nlinarith

/-- A genuinely chronological, exact split of the floor-Li primitive
mismatch: terminal q > B^2/3 plus descendant-eligible q <= B^2/3.
No fictitious prime/composite owner is added to either sector. -/
theorem vfMid915_halfRun_floorLiMismatch_eq_topThird_add_lower
    (A B : ℕ) (hA : A ^ 2 ≤ B ^ 2 / 3) :
    vfMidPrimeFloorLiIntegerBacklog (B ^ 2) -
      vfMidPrimeFloorLiIntegerBacklog (A ^ 2) =
    vfMidFloorLiSignedMismatchMass (B ^ 2 / 3) (B ^ 2) +
      vfMidFloorLiSignedMismatchMass (A ^ 2) (B ^ 2 / 3) := by
  have htop : B ^ 2 / 3 ≤ B ^ 2 := by omega
  rw [vfMidFloorLiSignedMismatchMass_eq_backlog_increment htop,
    vfMidFloorLiSignedMismatchMass_eq_backlog_increment hA]
  ring

end RHLean.Analysis
