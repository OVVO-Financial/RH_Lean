import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»
import RHLean.Analysis.NativePNTChebyshev

/-!
# Direct signed dynamics of the VF-mid square-band error

This file attacks the remaining VF-mid arithmetic discrepancy directly.
There is no sieve, Mertens transform, Li allocation model, or composite
recurrence here.

For one square band, write

  epsilon_R = P_R - V_R,

where P_R is the exact prime population and V_R is the VF midpoint mass.
The same exact primes are logarithmically reweighted. This separates epsilon_R
into

  (Theta_R - (2R+1)) / log(m_R)

plus a prime-location correction measuring only where the primes sit inside
the already-fixed square band.

The purpose is to remove within-band placement as a possible RH-scale
obstruction and leave only signed cumulative prime log-mass.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open Set

/-- Primes entering the prime-counting staircase between consecutive square
endpoints. -/
def vfMidDirectPrimeBand (R : ℕ) : Finset ℕ :=
  (Finset.Ioc (R ^ 2) ((R + 1) ^ 2)).filter Nat.Prime

/-- Real cardinality of the direct prime band. -/
def vfMidDirectPrimeBandCount (R : ℕ) : ℝ :=
  ((vfMidDirectPrimeBand R).card : ℝ)

/-- Logarithmically weighted prime mass in one square band. -/
def vfMidDirectThetaBandMass (R : ℕ) : ℝ :=
  ∑ p ∈ vfMidDirectPrimeBand R, Real.log p

/-- Signed prime-count error in one complete VF-mid square band. -/
def vfMidDirectBandError (R : ℕ) : ℝ :=
  vfMidDirectPrimeBandCount R - vfMidBandMass R

/-- Centered logarithmic prime mass of one complete square band. -/
def vfMidDirectThetaBandError (R : ℕ) : ℝ :=
  vfMidDirectThetaBandMass R - (2 * (R : ℝ) + 1)

/-- Difference between raw prime population and the same population after
reweighting every prime by log(p)/log(midpoint). This depends only on where
the primes lie inside the fixed square band. -/
def vfMidDirectLogPositionError (R : ℕ) : ℝ :=
  vfMidDirectPrimeBandCount R -
    vfMidDirectThetaBandMass R / Real.log (vfMidBandMidpoint R)

/-- The repository's exact finite prime set has cardinality pi(N).  This is a
local copy of the elementary cardinality argument, kept here so the direct
attack does not import any PNT transfer theorem. -/
private theorem vfMidDirect_nativePrimeSet_card_eq_primeCounting (N : ℕ) :
    (nativePrimeSet N).card = Nat.primeCounting N := by
  have hset :
      nativePrimeSet N = (Finset.range (N + 1)).filter Nat.Prime := by
    unfold nativePrimeSet
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_hp1, hpN⟩, hpPrime⟩
      exact ⟨hpN, hpPrime⟩
    · rintro ⟨hpN, hpPrime⟩
      exact ⟨⟨hpPrime.one_le, hpN⟩, hpPrime⟩
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  exact congrArg Finset.card hset

/-- Exact partition of the prime coordinates at the upper square endpoint into
the already-seen primes and the newly entered square band. -/
theorem vfMidDirect_nativePrimeSet_split (R : ℕ) :
    nativePrimeSet ((R + 1) ^ 2) =
      nativePrimeSet (R ^ 2) ∪ vfMidDirectPrimeBand R := by
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold nativePrimeSet vfMidDirectPrimeBand
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp1, hpU⟩, hpPrime⟩
    by_cases hpL : p ≤ R ^ 2
    · exact Or.inl ⟨⟨hp1, hpL⟩, hpPrime⟩
    · exact Or.inr ⟨⟨lt_of_not_ge hpL, hpU⟩, hpPrime⟩
  · rintro (h | h)
    · exact ⟨⟨h.1.1, h.1.2.trans hsq⟩, h.2⟩
    · exact ⟨⟨by omega, h.1.2⟩, h.2⟩

/-- The old-prime block and the new square-band block are disjoint. -/
theorem vfMidDirect_nativePrimeSet_disjoint_band (R : ℕ) :
    Disjoint (nativePrimeSet (R ^ 2)) (vfMidDirectPrimeBand R) := by
  rw [Finset.disjoint_left]
  intro p hpOld hpBand
  rcases Finset.mem_filter.mp hpOld with ⟨hpOldIcc, _⟩
  rcases Finset.mem_filter.mp hpBand with ⟨hpBandIoc, _⟩
  rcases Finset.mem_Icc.mp hpOldIcc with ⟨_, hpL⟩
  rcases Finset.mem_Ioc.mp hpBandIoc with ⟨hpGt, _⟩
  omega

/-- Prime-band cardinality is exactly the increment of the prime-counting
staircase across the two square endpoints. -/
theorem vfMidDirectPrimeBand_card_add_primeCounting_eq (R : ℕ) :
    (vfMidDirectPrimeBand R).card + Nat.primeCounting (R ^ 2) =
      Nat.primeCounting ((R + 1) ^ 2) := by
  have hcard := congrArg Finset.card (vfMidDirect_nativePrimeSet_split R)
  rw [Finset.card_union_of_disjoint
    (vfMidDirect_nativePrimeSet_disjoint_band R)] at hcard
  rw [vfMidDirect_nativePrimeSet_card_eq_primeCounting,
    vfMidDirect_nativePrimeSet_card_eq_primeCounting] at hcard
  omega

/-- Real-valued version of the exact prime-count increment. -/
theorem vfMidDirectPrimeBandCount_eq_primeCounting_sub (R : ℕ) :
    vfMidDirectPrimeBandCount R =
      (Nat.primeCounting ((R + 1) ^ 2) : ℝ) -
        (Nat.primeCounting (R ^ 2) : ℝ) := by
  have h := vfMidDirectPrimeBand_card_add_primeCounting_eq R
  have hR :
      ((vfMidDirectPrimeBand R).card : ℝ) +
          (Nat.primeCounting (R ^ 2) : ℝ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast h
  unfold vfMidDirectPrimeBandCount
  linarith

/-- The same finite partition gives an exact additive identity for the
log-weighted prime mass. -/
theorem vfMidDirectThetaBandMass_add_nativeTheta_eq (R : ℕ) :
    vfMidDirectThetaBandMass R + nativeTheta (R ^ 2) =
      nativeTheta ((R + 1) ^ 2) := by
  have hsplit := vfMidDirect_nativePrimeSet_split R
  have hdisj := vfMidDirect_nativePrimeSet_disjoint_band R
  unfold nativeTheta vfMidDirectThetaBandMass
  rw [hsplit, Finset.sum_union hdisj]
  ring

/-- The direct band log-mass is the increment of the exact finite theta mass. -/
theorem vfMidDirectThetaBandMass_eq_theta_sub (R : ℕ) :
    vfMidDirectThetaBandMass R =
      nativeTheta ((R + 1) ^ 2) - nativeTheta (R ^ 2) := by
  linarith [vfMidDirectThetaBandMass_add_nativeTheta_eq R]

/-- **Exact direct split of the band error.**

The first term is the centered logarithmic prime mass. The second term is only
the within-band log-position correction. No estimate is used here. -/
theorem vfMidDirectBandError_eq_theta_add_position (R : ℕ) :
    vfMidDirectBandError R =
      vfMidDirectThetaBandError R / Real.log (vfMidBandMidpoint R) +
        vfMidDirectLogPositionError R := by
  unfold vfMidDirectBandError vfMidDirectThetaBandError
    vfMidDirectLogPositionError vfMidBandMass
  ring

/-- Square-endpoint exact theta discrepancy. -/
def vfMidDirectThetaEndpointError (R : ℕ) : ℝ :=
  nativeTheta (R ^ 2) - (R : ℝ) ^ 2

/-- The centered band log-mass is the exact first difference of the
square-endpoint theta error. -/
theorem vfMidDirectThetaBandError_eq_endpoint_diff (R : ℕ) :
    vfMidDirectThetaBandError R =
      vfMidDirectThetaEndpointError (R + 1) -
        vfMidDirectThetaEndpointError R := by
  rw [vfMidDirectThetaBandError, vfMidDirectThetaBandMass_eq_theta_sub]
  unfold vfMidDirectThetaEndpointError
  push_cast
  ring

/-! ## The within-band prime-location term is lower order -/

/-- On a square tile, the derivative of log is bounded by the reciprocal of
the left square endpoint. -/
theorem vfMidDirect_abs_deriv_log_le_squareTile
    {R : ℕ} (hR : 2 ≤ R) {t : ℝ}
    (ht : t ∈ Icc ((R : ℝ) ^ 2) ((((R + 1 : ℕ) : ℝ) ^ 2))) :
    |deriv Real.log t| ≤ 1 / ((R : ℝ) ^ 2) := by
  have hR0 : 0 < (R : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hR)
  have ht0 : 0 < t := by
    have hsq0 : 0 < (R : ℝ) ^ 2 := sq_pos_of_pos hR0
    exact hsq0.trans_le ht.1
  rw [(Real.hasDerivAt_log ht0.ne').deriv]
  rw [abs_of_pos (inv_pos.mpr ht0)]
  simpa [one_div] using
    (one_div_le_one_div_of_le (sq_pos_of_pos hR0) ht.1)

/-- Every prime in a complete square band has log within 3/R of the
arithmetic midpoint log. The constant is intentionally crude; only a
uniformly summable-after-counting bound is needed. -/
theorem abs_vfMidDirect_logMidpoint_sub_log_prime_le
    {R p : ℕ} (hR : 2 ≤ R) (hp : p ∈ vfMidDirectPrimeBand R) :
    |Real.log (vfMidBandMidpoint R) - Real.log (p : ℝ)| ≤
      3 / (R : ℝ) := by
  have hR0 : 0 < (R : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hR)
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  rcases Finset.mem_filter.mp hp with ⟨hpIoc, _hpPrime⟩
  rcases Finset.mem_Ioc.mp hpIoc with ⟨hpLowNat, hpHighNat⟩
  have hpLow :
      (R : ℝ) ^ 2 ≤ (p : ℝ) := by
    exact_mod_cast hpLowNat.le
  have hpHigh :
      (p : ℝ) ≤ (((R + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast hpHighNat
  have hpTile :
      (p : ℝ) ∈ Icc ((R : ℝ) ^ 2)
        ((((R + 1 : ℕ) : ℝ) ^ 2)) :=
    ⟨hpLow, hpHigh⟩
  have hmTile :
      vfMidBandMidpoint R ∈ Icc ((R : ℝ) ^ 2)
        ((((R + 1 : ℕ) : ℝ) ^ 2)) := by
    dsimp [vfMidBandMidpoint]
    push_cast
    constructor <;> nlinarith
  have hLip :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Icc ((R : ℝ) ^ 2) ((((R + 1 : ℕ) : ℝ) ^ 2)))
      (f := Real.log)
      (x := vfMidBandMidpoint R) (y := (p : ℝ))
      (fun u hu => by
        have hu0 : 0 < u := by
          have hsq0 : 0 < (R : ℝ) ^ 2 := sq_pos_of_pos hR0
          exact hsq0.trans_le hu.1
        exact (Real.hasDerivAt_log hu0.ne').differentiableAt)
      (fun u hu => by
        simpa [Real.norm_eq_abs] using
          (vfMidDirect_abs_deriv_log_le_squareTile hR hu))
      (convex_Icc _ _) hmTile hpTile
  have hwidth :
      ((((R + 1 : ℕ) : ℝ) ^ 2) - (R : ℝ) ^ 2) ≤
        3 * (R : ℝ) := by
    push_cast
    nlinarith
  have hdist :
      |(p : ℝ) - vfMidBandMidpoint R| ≤ 3 * (R : ℝ) := by
    rw [abs_le]
    constructor
    · have hmLow := hmTile.1
      have hpUp := hpTile.2
      nlinarith
    · have hpLo := hpTile.1
      have hmUp := hmTile.2
      nlinarith
  have hlogdiff :
      |Real.log (p : ℝ) - Real.log (vfMidBandMidpoint R)| ≤
        (1 / ((R : ℝ) ^ 2)) *
          |(p : ℝ) - vfMidBandMidpoint R| := by
    simpa [Real.norm_eq_abs] using hLip
  rw [abs_sub_comm]
  calc
    |Real.log (p : ℝ) - Real.log (vfMidBandMidpoint R)|
        ≤ (1 / ((R : ℝ) ^ 2)) *
            |(p : ℝ) - vfMidBandMidpoint R| := hlogdiff
    _ ≤ (1 / ((R : ℝ) ^ 2)) * (3 * (R : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hdist
      positivity
    _ = 3 / (R : ℝ) := by
      field_simp [hR0.ne']
      ring

/-- One prime's normalized log-position correction is O(1/(R log 4)). -/
theorem abs_vfMidDirect_primeLogPositionTerm_le
    {R p : ℕ} (hR : 2 ≤ R) (hp : p ∈ vfMidDirectPrimeBand R) :
    |1 - Real.log (p : ℝ) / Real.log (vfMidBandMidpoint R)| ≤
      3 / ((R : ℝ) * Real.log 4) := by
  have hR0 : 0 < (R : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hR)
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hm4 : (4 : ℝ) ≤ vfMidBandMidpoint R := by
    unfold vfMidBandMidpoint
    nlinarith
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogLower :
      Real.log 4 ≤ Real.log (vfMidBandMidpoint R) :=
    Real.log_le_log (by norm_num) hm4
  have hlogMid :
      0 < Real.log (vfMidBandMidpoint R) :=
    hlog4.trans_le hlogLower
  have hnum :=
    abs_vfMidDirect_logMidpoint_sub_log_prime_le hR hp
  have hnum0 : 0 ≤ 3 / (R : ℝ) := by positivity
  have hfrac :
      1 - Real.log (p : ℝ) / Real.log (vfMidBandMidpoint R) =
        (Real.log (vfMidBandMidpoint R) - Real.log (p : ℝ)) /
          Real.log (vfMidBandMidpoint R) := by
    field_simp [hlogMid.ne']
    ring
  rw [hfrac, abs_div, abs_of_pos hlogMid]
  calc
    |Real.log (vfMidBandMidpoint R) - Real.log (p : ℝ)| /
          Real.log (vfMidBandMidpoint R)
        ≤ (3 / (R : ℝ)) / Real.log (vfMidBandMidpoint R) :=
      div_le_div_of_nonneg_right hnum hlogMid.le
    _ ≤ (3 / (R : ℝ)) / Real.log 4 :=
      div_le_div_of_nonneg_left hnum0 hlog4 hlogLower
    _ = 3 / ((R : ℝ) * Real.log 4) := by
      field_simp [hR0.ne', hlog4.ne']
      ring

/-- The direct prime population in one square band has the elementary linear
budget at most 3R. No prime-distribution estimate is used. -/
theorem vfMidDirectPrimeBandCount_le_three_mul
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidDirectPrimeBandCount R ≤ 3 * (R : ℝ) := by
  have hpc := vfMid_primeCounting_add_le (R ^ 2) (2 * R + 1)
  have hsq : R ^ 2 + (2 * R + 1) = (R + 1) ^ 2 := by
    ring
  rw [hsq] at hpc
  have hband := vfMidDirectPrimeBand_card_add_primeCounting_eq R
  have hcard : (vfMidDirectPrimeBand R).card ≤ 2 * R + 1 := by
    omega
  have hcardR :
      ((vfMidDirectPrimeBand R).card : ℝ) ≤ 2 * (R : ℝ) + 1 := by
    exact_mod_cast hcard
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  unfold vfMidDirectPrimeBandCount
  nlinarith

/-- The location correction is literally the sum of the normalized log
deviations of the primes in the band. -/
theorem vfMidDirectLogPositionError_eq_sum (R : ℕ) :
    vfMidDirectLogPositionError R =
      ∑ p ∈ vfMidDirectPrimeBand R,
        (1 - Real.log (p : ℝ) / Real.log (vfMidBandMidpoint R)) := by
  classical
  unfold vfMidDirectLogPositionError vfMidDirectPrimeBandCount
    vfMidDirectThetaBandMass
  simp [Finset.sum_sub_distrib, Finset.sum_div]

/-- Uniform within-band location bound.

After the exact theta reweighting, the remaining dependence on the positions
of primes inside a square band is bounded by an absolute constant. -/
theorem abs_vfMidDirectLogPositionError_le
    (R : ℕ) (hR : 2 ≤ R) :
    |vfMidDirectLogPositionError R| ≤ 9 / Real.log 4 := by
  rw [vfMidDirectLogPositionError_eq_sum]
  calc
    |∑ p ∈ vfMidDirectPrimeBand R,
        (1 - Real.log (p : ℝ) / Real.log (vfMidBandMidpoint R))|
        ≤ ∑ p ∈ vfMidDirectPrimeBand R,
            |1 - Real.log (p : ℝ) /
              Real.log (vfMidBandMidpoint R)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ vfMidDirectPrimeBand R,
          3 / ((R : ℝ) * Real.log 4) := by
      apply Finset.sum_le_sum
      intro p hp
      exact abs_vfMidDirect_primeLogPositionTerm_le hR hp
    _ = vfMidDirectPrimeBandCount R *
          (3 / ((R : ℝ) * Real.log 4)) := by
      unfold vfMidDirectPrimeBandCount
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * (R : ℝ)) *
          (3 / ((R : ℝ) * Real.log 4)) := by
      apply mul_le_mul_of_nonneg_right
        (vfMidDirectPrimeBandCount_le_three_mul R hR)
      positivity
    _ = 9 / Real.log 4 := by
      have hR0 : (0 : ℝ) < (R : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hR)
      have hlog4 : Real.log 4 ≠ 0 :=
        (Real.log_pos (by norm_num)).ne'
      field_simp [hR0.ne', hlog4]
      ring

/-- Cumulative within-band location correction through the square endpoint R. -/
def vfMidDirectLogPositionPrefix (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 2 R, vfMidDirectLogPositionError r

/-- The entire within-band prime-location contribution is only root scale.
It is therefore strictly below the R log R target scale. -/
theorem abs_vfMidDirectLogPositionPrefix_le (R : ℕ) :
    |vfMidDirectLogPositionPrefix R| ≤
      (9 / Real.log 4) * (R : ℝ) := by
  unfold vfMidDirectLogPositionPrefix
  calc
    |∑ r ∈ Finset.Ico 2 R, vfMidDirectLogPositionError r|
        ≤ ∑ r ∈ Finset.Ico 2 R,
            |vfMidDirectLogPositionError r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ Finset.Ico 2 R, 9 / Real.log 4 := by
      apply Finset.sum_le_sum
      intro r hr
      exact abs_vfMidDirectLogPositionError_le r
        (Finset.mem_Ico.mp hr).1
    _ = ((Finset.Ico 2 R).card : ℝ) * (9 / Real.log 4) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (R : ℝ) * (9 / Real.log 4) := by
      have hcard : (Finset.Ico 2 R).card ≤ R := by
        rw [Nat.card_Ico]
        omega
      have hcardR : ((Finset.Ico 2 R).card : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hcard
      exact mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = (9 / Real.log 4) * (R : ℝ) := by ring

end RHLean.Analysis
