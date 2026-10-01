import Mathlib
import «research.VF_MID_SQUARE_WHEEL_BACKLOG»

/-!
# VF-mid midpoint complement dispersion

This file isolates the exact finite identity behind the square-band midpoint
placement heuristic.

Inside the open square carrier

  R^2 < n < (R+1)^2,

prime sites and composite sites are exact complements.  Therefore, after
centering any prefix count by the same deterministic spatial fraction, the
prime discrepancy is exactly the negative composite discrepancy.  The two
absolute discrepancies are identical.

At the geometric midpoint

  R^2 + R + 1/2,

the last integer on the left is R^2+R and the open carrier has 2R sites, so
the centered identity reduces to

  leftPrime - totalPrime/2 = -(leftComposite - totalComposite/2).

Using the common-wheel theorem from VF_MID_SQUARE_WHEEL_BACKLOG, the same
identity holds with prime sites replaced by finite-wheel survivors.  Thus any
dispersion estimate proved on the composite kill pattern transfers with no
loss to the survivor/prime placement discrepancy.

This is an exact complement theorem only.  It does not estimate the total
prime supply P_R or the backlog recurrence.
-/

noncomputable section

namespace RHLean.Analysis

/-- Composite sites on the open square carrier. -/
def vfMidSquareWheelComposites (R : ℕ) : Finset ℕ :=
  (vfMidSquareWheelSites R).filter fun n => ¬ n.Prime

/-- Prefix of the square carrier through the integer cutoff t. -/
def vfMidSquareWheelPrefixSites (R t : ℕ) : Finset ℕ :=
  (vfMidSquareWheelSites R).filter fun n => n ≤ t

/-- Prime sites in the carrier prefix through t. -/
def vfMidSquareWheelPrimePrefix (R t : ℕ) : Finset ℕ :=
  (vfMidSquareWheelPrimes R).filter fun n => n ≤ t

/-- Composite sites in the carrier prefix through t. -/
def vfMidSquareWheelCompositePrefix (R t : ℕ) : Finset ℕ :=
  (vfMidSquareWheelComposites R).filter fun n => n ≤ t

/-- Common-wheel survivor sites in the carrier prefix through t. -/
def vfMidSquareWheelSurvivorPrefix (R t : ℕ) : Finset ℕ :=
  (vfMidSquareWheelSurvivors R).filter fun n => n ≤ t

/-- Prime and composite sites partition the open square carrier exactly. -/
theorem vfMidSquareWheel_prime_composite_partition (R : ℕ) :
    vfMidSquareWheelPrimes R ∪ vfMidSquareWheelComposites R =
      vfMidSquareWheelSites R := by
  classical
  ext n
  by_cases hp : n.Prime <;>
    simp [vfMidSquareWheelPrimes, vfMidSquareWheelComposites, hp]

/-- Prime and composite carrier sites are disjoint. -/
theorem vfMidSquareWheel_prime_composite_disjoint (R : ℕ) :
    Disjoint (vfMidSquareWheelPrimes R) (vfMidSquareWheelComposites R) := by
  classical
  rw [Finset.disjoint_left]
  intro n hp hc
  exact (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hp).2

/-- Total prime plus composite population is the deterministic carrier size. -/
theorem vfMidSquareWheel_prime_card_add_composite_card (R : ℕ) :
    (vfMidSquareWheelPrimes R).card +
        (vfMidSquareWheelComposites R).card =
      (vfMidSquareWheelSites R).card := by
  have hcard := congrArg Finset.card
    (vfMidSquareWheel_prime_composite_partition R)
  rw [Finset.card_union_of_disjoint
    (vfMidSquareWheel_prime_composite_disjoint R)] at hcard
  exact hcard

/-- Prime and composite sites partition every spatial prefix of the carrier. -/
theorem vfMidSquareWheel_prefix_prime_composite_partition (R t : ℕ) :
    vfMidSquareWheelPrimePrefix R t ∪
        vfMidSquareWheelCompositePrefix R t =
      vfMidSquareWheelPrefixSites R t := by
  classical
  ext n
  by_cases hp : n.Prime <;>
    simp [vfMidSquareWheelPrimePrefix, vfMidSquareWheelCompositePrefix,
      vfMidSquareWheelPrefixSites, vfMidSquareWheelPrimes,
      vfMidSquareWheelComposites, hp]

/-- Prime and composite populations are disjoint inside every prefix. -/
theorem vfMidSquareWheel_prefix_prime_composite_disjoint (R t : ℕ) :
    Disjoint (vfMidSquareWheelPrimePrefix R t)
      (vfMidSquareWheelCompositePrefix R t) := by
  classical
  rw [Finset.disjoint_left]
  intro n hp hc
  have hpPrime : n.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hcNotPrime : ¬ n.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
  exact hcNotPrime hpPrime

/-- Prefix prime plus prefix composite population is exactly the prefix size. -/
theorem vfMidSquareWheel_prefix_prime_card_add_composite_card (R t : ℕ) :
    (vfMidSquareWheelPrimePrefix R t).card +
        (vfMidSquareWheelCompositePrefix R t).card =
      (vfMidSquareWheelPrefixSites R t).card := by
  have hcard := congrArg Finset.card
    (vfMidSquareWheel_prefix_prime_composite_partition R t)
  rw [Finset.card_union_of_disjoint
    (vfMidSquareWheel_prefix_prime_composite_disjoint R t)] at hcard
  exact hcard

/-- Centered prime placement discrepancy of a carrier prefix. -/
def vfMidSquareWheelPrimePrefixDiscrepancy (R t : ℕ) : ℝ :=
  ((vfMidSquareWheelPrimePrefix R t).card : ℝ) -
    (((vfMidSquareWheelPrefixSites R t).card : ℝ) /
        ((vfMidSquareWheelSites R).card : ℝ)) *
      ((vfMidSquareWheelPrimes R).card : ℝ)

/-- Centered composite placement discrepancy of the same carrier prefix. -/
def vfMidSquareWheelCompositePrefixDiscrepancy (R t : ℕ) : ℝ :=
  ((vfMidSquareWheelCompositePrefix R t).card : ℝ) -
    (((vfMidSquareWheelPrefixSites R t).card : ℝ) /
        ((vfMidSquareWheelSites R).card : ℝ)) *
      ((vfMidSquareWheelComposites R).card : ℝ)

private theorem vfMid_centered_complement_identity
    {pp cp sp p c s : ℝ}
    (hpref : pp + cp = sp)
    (htotal : p + c = s)
    (hs : s ≠ 0) :
    pp - sp / s * p = -(cp - sp / s * c) := by
  have hcp : cp = sp - pp := by linarith
  have hc : c = s - p := by linarith
  rw [hcp, hc]
  field_simp [hs]
  ring

/-- **Exact complement-dispersion identity.**  At every integer cutoff in a
nonempty square carrier, centered prime displacement is exactly the negative
centered composite displacement. -/
theorem vfMidSquareWheel_primePrefixDiscrepancy_eq_neg_composite
    (R t : ℕ) (hR : 1 ≤ R) :
    vfMidSquareWheelPrimePrefixDiscrepancy R t =
      -vfMidSquareWheelCompositePrefixDiscrepancy R t := by
  have hprefNat :=
    vfMidSquareWheel_prefix_prime_card_add_composite_card R t
  have htotalNat :=
    vfMidSquareWheel_prime_card_add_composite_card R
  have hpref :
      ((vfMidSquareWheelPrimePrefix R t).card : ℝ) +
          ((vfMidSquareWheelCompositePrefix R t).card : ℝ) =
        ((vfMidSquareWheelPrefixSites R t).card : ℝ) := by
    exact_mod_cast hprefNat
  have htotal :
      ((vfMidSquareWheelPrimes R).card : ℝ) +
          ((vfMidSquareWheelComposites R).card : ℝ) =
        ((vfMidSquareWheelSites R).card : ℝ) := by
    exact_mod_cast htotalNat
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 0 < R by omega)
  have hsites :
      ((vfMidSquareWheelSites R).card : ℝ) ≠ 0 := by
    rw [vfMidSquareWheelSites_card]
    push_cast
    positivity
  unfold vfMidSquareWheelPrimePrefixDiscrepancy
    vfMidSquareWheelCompositePrefixDiscrepancy
  exact vfMid_centered_complement_identity hpref htotal hsites

/-- Prime and composite prefix discrepancies have exactly the same magnitude. -/
theorem vfMidSquareWheel_abs_primePrefixDiscrepancy_eq_abs_composite
    (R t : ℕ) (hR : 1 ≤ R) :
    |vfMidSquareWheelPrimePrefixDiscrepancy R t| =
      |vfMidSquareWheelCompositePrefixDiscrepancy R t| := by
  rw [vfMidSquareWheel_primePrefixDiscrepancy_eq_neg_composite R t hR,
    abs_neg]

/-- Exact equal-dispersion transfer at each prefix. -/
theorem vfMidSquareWheel_primePrefixDiscrepancy_eq_zero_iff_composite
    (R t : ℕ) (hR : 1 ≤ R) :
    vfMidSquareWheelPrimePrefixDiscrepancy R t = 0 ↔
      vfMidSquareWheelCompositePrefixDiscrepancy R t = 0 := by
  rw [vfMidSquareWheel_primePrefixDiscrepancy_eq_neg_composite R t hR]
  simp

/-- The theoretical statement "composites are exactly equally dispersed over
all prefixes" is equivalent to the identical statement for primes. -/
theorem vfMidSquareWheel_prime_uniformDispersion_iff_composite
    (R : ℕ) (hR : 1 ≤ R) :
    (∀ t, vfMidSquareWheelPrimePrefixDiscrepancy R t = 0) ↔
      (∀ t, vfMidSquareWheelCompositePrefixDiscrepancy R t = 0) := by
  constructor
  · intro h t
    exact
      (vfMidSquareWheel_primePrefixDiscrepancy_eq_zero_iff_composite
        R t hR).1 (h t)
  · intro h t
    exact
      (vfMidSquareWheel_primePrefixDiscrepancy_eq_zero_iff_composite
        R t hR).2 (h t)

/-! ## The geometric midpoint -/

/-- The geometric VF midpoint lies strictly between the two central integers
R^2+R and R^2+R+1. -/
theorem vfMidSquareWheel_midpoint_between_central_integers (R : ℕ) :
    (((R ^ 2 + R : ℕ) : ℝ) < vfMidBandMidpoint R) ∧
      (vfMidBandMidpoint R < ((R ^ 2 + R + 1 : ℕ) : ℝ)) := by
  unfold vfMidBandMidpoint
  push_cast
  constructor <;> norm_num

/-- Exactly R of the 2R open-carrier sites lie to the left of the geometric
midpoint. -/
theorem vfMidSquareWheel_midpointPrefix_card (R : ℕ) :
    (vfMidSquareWheelPrefixSites R (R ^ 2 + R)).card = R := by
  have hupper : R ^ 2 + R < (R + 1) ^ 2 := by
    nlinarith
  have hset :
      vfMidSquareWheelPrefixSites R (R ^ 2 + R) =
        Finset.Ioc (R ^ 2) (R ^ 2 + R) := by
    ext n
    simp only [vfMidSquareWheelPrefixSites, vfMidSquareWheelSites,
      Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ioc]
    omega
  rw [hset, Nat.card_Ioc]
  omega

/-- **Midpoint complement identity.**  Because the midpoint splits the 2R
interior seats into R left seats and R right seats, the left-half prime excess
over one half of total prime supply is exactly the negative left-half composite
excess over one half of total composite supply. -/
theorem vfMidSquareWheel_midpoint_prime_composite_discrepancy (R : ℕ) :
    ((vfMidSquareWheelPrimePrefix R (R ^ 2 + R)).card : ℝ) -
        ((vfMidSquareWheelPrimes R).card : ℝ) / 2 =
      -(((vfMidSquareWheelCompositePrefix R (R ^ 2 + R)).card : ℝ) -
        ((vfMidSquareWheelComposites R).card : ℝ) / 2) := by
  have hprefNat :=
    vfMidSquareWheel_prefix_prime_card_add_composite_card
      R (R ^ 2 + R)
  rw [vfMidSquareWheel_midpointPrefix_card R] at hprefNat
  have htotalNat :=
    vfMidSquareWheel_prime_card_add_composite_card R
  rw [vfMidSquareWheelSites_card] at htotalNat
  have hpref :
      ((vfMidSquareWheelPrimePrefix R (R ^ 2 + R)).card : ℝ) +
          ((vfMidSquareWheelCompositePrefix R (R ^ 2 + R)).card : ℝ) =
        (R : ℝ) := by
    exact_mod_cast hprefNat
  have htotal :
      ((vfMidSquareWheelPrimes R).card : ℝ) +
          ((vfMidSquareWheelComposites R).card : ℝ) =
        2 * (R : ℝ) := by
    exact_mod_cast htotalNat
  have hcp :
      ((vfMidSquareWheelCompositePrefix R (R ^ 2 + R)).card : ℝ) =
        (R : ℝ) -
          ((vfMidSquareWheelPrimePrefix R (R ^ 2 + R)).card : ℝ) := by
    linarith
  have hc :
      ((vfMidSquareWheelComposites R).card : ℝ) =
        2 * (R : ℝ) - ((vfMidSquareWheelPrimes R).card : ℝ) := by
    linarith
  rw [hcp, hc]
  ring

/-- The midpoint prime and composite placement errors have exactly equal
absolute magnitude. -/
theorem vfMidSquareWheel_abs_midpoint_prime_discrepancy_eq_composite
    (R : ℕ) :
    |((vfMidSquareWheelPrimePrefix R (R ^ 2 + R)).card : ℝ) -
        ((vfMidSquareWheelPrimes R).card : ℝ) / 2| =
      |((vfMidSquareWheelCompositePrefix R (R ^ 2 + R)).card : ℝ) -
        ((vfMidSquareWheelComposites R).card : ℝ) / 2| := by
  rw [vfMidSquareWheel_midpoint_prime_composite_discrepancy R, abs_neg]

/-- The finite common-wheel survivor placement obeys the same midpoint identity.
For R >= 2, survivor sites are literally the prime sites. -/
theorem vfMidSquareWheel_midpoint_survivor_composite_discrepancy
    (R : ℕ) (hR : 2 ≤ R) :
    ((vfMidSquareWheelSurvivorPrefix R (R ^ 2 + R)).card : ℝ) -
        ((vfMidSquareWheelSurvivors R).card : ℝ) / 2 =
      -(((vfMidSquareWheelCompositePrefix R (R ^ 2 + R)).card : ℝ) -
        ((vfMidSquareWheelComposites R).card : ℝ) / 2) := by
  have hsurv := vfMidSquareWheelSurvivors_eq_primes R hR
  have hprefix :
      vfMidSquareWheelSurvivorPrefix R (R ^ 2 + R) =
        vfMidSquareWheelPrimePrefix R (R ^ 2 + R) := by
    unfold vfMidSquareWheelSurvivorPrefix vfMidSquareWheelPrimePrefix
    rw [hsurv]
  rw [hprefix, hsurv]
  exact vfMidSquareWheel_midpoint_prime_composite_discrepancy R

end RHLean.Analysis
