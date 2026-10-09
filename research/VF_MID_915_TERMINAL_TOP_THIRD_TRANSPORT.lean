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


/-- Terminal top-third odd descendants do not exist, but every integer
terminal site is STILL decided by the genuine ascending low-prime wheel.
This is a prime FACTORIZATION theorem, not a floor-Li approximation. -/
theorem vfMid915_boundedWindow_lowWheel_iff_prime
    {B q : ℕ} (hBq : B < q) (hqB : q ≤ B ^ 2) :
    lowWheelHighSurvivor B q ↔ q.Prime := by
  constructor
  · intro hsurv
    by_contra hcomp
    have hqpos : 0 < q := by omega
    have hqone : q ≠ 1 := by omega
    let p := q.minFac
    have hpprime : p.Prime := by
      simpa [p] using Nat.minFac_prime hqone
    have hpdvd : p ∣ q := by
      simpa [p] using Nat.minFac_dvd q
    have hpsq : p ^ 2 ≤ q := by
      simpa [p] using Nat.minFac_sq_le_self hqpos hcomp
    have hpB : p ≤ B := by
      by_contra hnot
      have hpLarge : B + 1 ≤ p := by omega
      have hsqBig : (B + 1) ^ 2 ≤ p ^ 2 :=
        Nat.pow_le_pow_left hpLarge 2
      nlinarith
    have hpMem : p ∈ primesUpTo B :=
      mem_primesUpTo.mpr ⟨hpprime, hpB⟩
    exact hsurv p hpMem hpdvd
  · intro hprime p hpMem hpdvd
    have hpprime : p.Prime := prime_of_mem_primesUpTo hpMem
    have hpB : p ≤ B := (mem_primesUpTo.mp hpMem).2
    have hpq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpprime hprime).mp hpdvd
    omega

/-- At B >= 4, every top-third site lies ABOVE the cutoff wheel B.
Thus terminal primality is certified by the low-owner sieve through B. -/
theorem vfMid915_topThird_lowWheelB_iff_prime
    {B q : ℕ} (hB : 4 ≤ B)
    (hq : B ^ 2 / 3 < q) (hqB : q ≤ B ^ 2) :
    lowWheelHighSurvivor B q ↔ q.Prime := by
  have hmult : 4 * B ≤ B * B :=
    Nat.mul_le_mul_right B hB
  have hcut : 3 * (B + 1) ≤ B ^ 2 := by
    nlinarith
  have hBq : B < q := by omega
  exact vfMid915_boundedWindow_lowWheel_iff_prime hBq hqB

/-- Literal terminal integer candidates surviving the ACTUAL ascending
low-prime wheel through B, with no future odd descendant capacity. -/
def vfMid915TopThirdLowWheelSurvivors (B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (B ^ 2 / 3) (B ^ 2)).filter (lowWheelHighSurvivor B)

/-- A genuine sieve (least-owner) alternative to the missing high-q odd
descendants: the terminal survivor SET is exactly the actual prime SET.
No smallness of its floor-Li discrepancy is asserted. -/
theorem vfMid915_topThird_lowWheelSurvivors_eq_primes
    {B : ℕ} (hB : 4 ≤ B) :
    vfMid915TopThirdLowWheelSurvivors B =
      (Finset.Ioc (B ^ 2 / 3) (B ^ 2)).filter Nat.Prime := by
  classical
  ext q
  simp only [vfMid915TopThirdLowWheelSurvivors,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hsurv⟩
    exact ⟨⟨hlo, hhi⟩,
      (vfMid915_topThird_lowWheelB_iff_prime hB hlo hhi).1 hsurv⟩
  · rintro ⟨⟨hlo, hhi⟩, hprime⟩
    exact ⟨⟨hlo, hhi⟩,
      (vfMid915_topThird_lowWheelB_iff_prime hB hlo hhi).2 hprime⟩

end RHLean.Analysis
