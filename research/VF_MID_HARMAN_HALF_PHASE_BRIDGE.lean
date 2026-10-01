import Mathlib
import RHLean.Analysis.GrowingParentPhaseUniformity
import «research.VF_MID_UNIFORMITY_BIAS_CORRELATION»
import «research.VF_MID_DIRECT_SIGNED_DYNAMICS»
import «research.VF_MID_GLOBAL_PHASE_UNIFORMITY_BRIDGE»

/-!
# Harman/Vinogradov square-root phase bridge to VF-mid block bias

The repository already exposes the classical analytic input

  SquareRootPrimePhaseEquidistributionStatement,

which packages uniform distribution of the fractional parts {sqrt p} among
primes.  This file proves the missing exact finite bridge from that global
phase statement to the VF-mid square-block midpoint-bias sequence.

For the R-th square block, the integer midpoint cutoff is R^2 + R.  On an
integer p with R^2 < p < (R+1)^2,

  {sqrt p} < 1/2  <->  p <= R^2 + R.

Thus the half-phase count is literally the left-half prime count already used
by VF-mid.

If

  G_R = #{p <= R^2 : {sqrt p} < 1/2} - (1/2) pi(R^2),

then the block midpoint bias U_R satisfies the exact finite-difference identity

  U_R = G_(R+1) - G_R.

Consequently,

  sum_{k<n} U_(R+k) = G_(R+n) - G_R.

This is the exact route by which any classical global discrepancy estimate for
{sqrt p} transfers into a cumulative no-persistent-bias estimate on the VF-mid
square blocks.  It does not claim that global equidistribution by itself gives
the stronger lag-decorrelation theorem required for a final RH closure.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-! ## 1. The half-phase cutoff is exactly the integer midpoint -/

/-- On one open square carrier, phase < 1/2 is exactly the left integer half
through R^2+R.  There is no asymptotic approximation here. -/
theorem squareRootPrimePhase_lt_half_iff_midpoint
    {R n : ℕ} (hn : n ∈ vfMidSquareWheelSites R) :
    squareRootPrimePhase n < (1 / 2 : ℝ) ↔ n <= R ^ 2 + R := by
  have hnI := Finset.mem_Ioo.mp hn
  have hsqrtNat : Nat.sqrt n = R := by
    symm
    exact (Nat.eq_sqrt').2 ⟨hnI.1.le, hnI.2⟩
  have hsqrtSq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  have hsqrt0 : 0 <= Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  unfold squareRootPrimePhase
  rw [hsqrtNat]
  constructor
  · intro hphase
    by_contra hnot
    have hnat : R ^ 2 + R + 1 <= n := by omega
    have hreal : (((R ^ 2 + R + 1 : ℕ) : ℝ)) <= (n : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal
    nlinarith
  · intro hmid
    have hreal : (n : ℝ) <= (((R ^ 2 + R : ℕ) : ℝ)) := by
      exact_mod_cast hmid
    push_cast at hreal
    by_contra hnot
    have hge : (1 / 2 : ℝ) <= Real.sqrt (n : ℝ) - (R : ℝ) :=
      le_of_not_gt hnot
    nlinarith

/-- Prime sites in one complete square band whose square-root phase lies in the
half-window [0,1/2). -/
def vfMidSquareBlockHalfPhasePrimes (R : ℕ) : Finset ℕ :=
  (vfMidSquareWheelPrimes R).filter fun p =>
    squareRootPrimePhase p < (1 / 2 : ℝ)

/-- The half-phase prime set is literally the existing midpoint prime prefix. -/
theorem vfMidSquareBlockHalfPhasePrimes_eq_midpointPrefix (R : ℕ) :
    vfMidSquareBlockHalfPhasePrimes R =
      vfMidSquareWheelPrimePrefix R (R ^ 2 + R) := by
  ext p
  simp only [vfMidSquareBlockHalfPhasePrimes,
    vfMidSquareWheelPrimePrefix, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hphase⟩
    have hsite : p ∈ vfMidSquareWheelSites R := by
      exact (Finset.mem_filter.mp hp).1
    exact ⟨hp, (squareRootPrimePhase_lt_half_iff_midpoint hsite).1 hphase⟩
  · rintro ⟨hp, hmid⟩
    have hsite : p ∈ vfMidSquareWheelSites R := by
      exact (Finset.mem_filter.mp hp).1
    exact ⟨hp, (squareRootPrimePhase_lt_half_iff_midpoint hsite).2 hmid⟩

/-! ## 2. Global half-phase discrepancy -/

/-- Global primes up to X with square-root phase in [0,1/2). -/
def vfMidGlobalHalfPhasePrimeSet (X : ℕ) : Finset ℕ :=
  (Finset.Icc 2 X).filter fun p =>
    p.Prime ∧ squareRootPrimePhase p < (1 / 2 : ℝ)

/-- The local set above has exactly the cardinality used by the repository's
classical equidistribution interface. -/
theorem vfMidGlobalHalfPhasePrimeSet_card_eq_phaseWindowCount (X : ℕ) :
    (vfMidGlobalHalfPhasePrimeSet X).card =
      squareRootPrimePhaseWindowCount X 0 (1 / 2 : ℝ) := by
  unfold vfMidGlobalHalfPhasePrimeSet squareRootPrimePhaseWindowCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hpI, hpPrime, hhalf⟩
    exact ⟨hpI, hpPrime, squareRootPrimePhase_nonneg p, hhalf⟩
  · rintro ⟨hpI, hpPrime, _hzero, hhalf⟩
    exact ⟨hpI, hpPrime, hhalf⟩

/-- The global half-phase set splits exactly at consecutive square endpoints. -/
theorem vfMidGlobalHalfPhasePrimeSet_split (R : ℕ) :
    vfMidGlobalHalfPhasePrimeSet ((R + 1) ^ 2) =
      vfMidGlobalHalfPhasePrimeSet (R ^ 2) ∪
        ((vfMidDirectPrimeBand R).filter fun p =>
          squareRootPrimePhase p < (1 / 2 : ℝ)) := by
  ext p
  simp only [vfMidGlobalHalfPhasePrimeSet, vfMidDirectPrimeBand,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp2, hpU⟩, hpPrime, hhalf⟩
    by_cases hpL : p ≤ R ^ 2
    · left
      exact ⟨⟨hp2, hpL⟩, hpPrime, hhalf⟩
    · right
      refine ⟨?_, hhalf⟩
      exact ⟨⟨lt_of_not_ge hpL, hpU⟩, hpPrime⟩
  · intro h
    rcases h with hleft | hright
    · rcases hleft with ⟨⟨hp2, hpL⟩, hpPrime, hhalf⟩
      have hsq : R ^ 2 ≤ (R + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      exact ⟨⟨hp2, hpL.trans hsq⟩, hpPrime, hhalf⟩
    · rcases hright with ⟨hband, hhalf⟩
      rcases hband with ⟨⟨hpL, hpU⟩, hpPrime⟩
      exact ⟨⟨hpPrime.two_le, hpU⟩, hpPrime, hhalf⟩

/-- The old global half-phase set and the new square-band half-phase shell are
disjoint. -/
theorem vfMidGlobalHalfPhasePrimeSet_disjoint_band (R : ℕ) :
    Disjoint (vfMidGlobalHalfPhasePrimeSet (R ^ 2))
      ((vfMidDirectPrimeBand R).filter fun p =>
        squareRootPrimePhase p < (1 / 2 : ℝ)) := by
  rw [Finset.disjoint_left]
  intro p hpOld hpNew
  have hOld := (Finset.mem_filter.mp hpOld).1
  have hNew := (Finset.mem_filter.mp hpNew).1
  have hpOldLe := (Finset.mem_Icc.mp hOld).2
  have hpNewGt := (Finset.mem_filter.mp hNew).1
  exact (not_lt_of_ge hpOldLe) (Finset.mem_Ioc.mp hpNewGt).1

/-- Exact half-phase count increment across one square block. -/
theorem squareRootPrimePhaseWindowCount_square_succ
    (R : ℕ) :
    squareRootPrimePhaseWindowCount ((R + 1) ^ 2) 0 (1 / 2 : ℝ) =
      squareRootPrimePhaseWindowCount (R ^ 2) 0 (1 / 2 : ℝ) +
        (vfMidSquareBlockHalfPhasePrimes R).card := by
  have hsplit := vfMidGlobalHalfPhasePrimeSet_split R
  have hdisj := vfMidGlobalHalfPhasePrimeSet_disjoint_band R
  have hcard := congrArg Finset.card hsplit
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  rw [vfMidGlobalHalfPhasePrimeSet_card_eq_phaseWindowCount,
    vfMidGlobalHalfPhasePrimeSet_card_eq_phaseWindowCount] at hcard
  have hband :
      ((vfMidDirectPrimeBand R).filter fun p =>
          squareRootPrimePhase p < (1 / 2 : ℝ)) =
        vfMidSquareBlockHalfPhasePrimes R := by
    unfold vfMidSquareBlockHalfPhasePrimes
    rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  rw [hband] at hcard
  exact hcard

/-- Exact total-prime increment in the same block, expressed through the
repository's phase-count convention. -/
theorem primeCountUpTo_square_succ (R : ℕ) :
    primeCountUpTo ((R + 1) ^ 2) =
      primeCountUpTo (R ^ 2) + (vfMidSquareWheelPrimes R).card := by
  rw [primeCountUpTo_eq_primeCounting, primeCountUpTo_eq_primeCounting]
  have h := vfMidDirectPrimeBand_card_add_primeCounting_eq R
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes] at h
  omega

/-! ## 3. Exact global-to-local finite difference -/

/-- **Global phase discrepancy finite difference = local VF midpoint bias.** -/
theorem vfMidGlobalHalfPhaseDiscrepancy_succ_sub
    (R : ℕ) :
    vfMidGlobalHalfPhaseDiscrepancy (R + 1) -
        vfMidGlobalHalfPhaseDiscrepancy R =
      vfMidSquareBlockMidpointBias R := by
  have hphaseNat := squareRootPrimePhaseWindowCount_square_succ R
  have hprimeNat := primeCountUpTo_square_succ R
  have hhalfNat :=
    congrArg Finset.card (vfMidSquareBlockHalfPhasePrimes_eq_midpointPrefix R)
  have hphase :
      (squareRootPrimePhaseWindowCount ((R + 1) ^ 2) 0 (1 / 2 : ℝ) : ℝ) =
        (squareRootPrimePhaseWindowCount (R ^ 2) 0 (1 / 2 : ℝ) : ℝ) +
          ((vfMidSquareBlockHalfPhasePrimes R).card : ℝ) := by
    exact_mod_cast hphaseNat
  have hprime :
      (primeCountUpTo ((R + 1) ^ 2) : ℝ) =
        (primeCountUpTo (R ^ 2) : ℝ) +
          ((vfMidSquareWheelPrimes R).card : ℝ) := by
    exact_mod_cast hprimeNat
  have hhalf :
      ((vfMidSquareBlockHalfPhasePrimes R).card : ℝ) =
        ((vfMidSquareWheelPrimePrefix R (R ^ 2 + R)).card : ℝ) := by
    exact_mod_cast hhalfNat
  unfold vfMidGlobalHalfPhaseDiscrepancy vfMidSquareBlockMidpointBias
    vfMidSquareBlockPrimeLeft vfMidSquareBlockPrimeTotal
  rw [hphase, hprime, hhalf]
  ring

/-- Equivalent successor form. -/
theorem vfMidGlobalHalfPhaseDiscrepancy_succ_add
    (R : ℕ) :
    vfMidGlobalHalfPhaseDiscrepancy (R + 1) =
      vfMidGlobalHalfPhaseDiscrepancy R +
        vfMidSquareBlockMidpointBias R := by
  have h := vfMidGlobalHalfPhaseDiscrepancy_succ_sub R
  linarith

/-- **Exact cumulative square-block bias telescope.** -/
theorem sum_vfMidSquareBlockMidpointBias_eq_globalHalfPhaseDifference
    (R n : ℕ) :
    (∑ k ∈ Finset.range n, vfMidSquareBlockMidpointBias (R + k)) =
      vfMidGlobalHalfPhaseDiscrepancy (R + n) -
        vfMidGlobalHalfPhaseDiscrepancy R := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hs := vfMidGlobalHalfPhaseDiscrepancy_succ_add (R + n)
      rw [Nat.add_succ]
      nlinarith

/-! ## 4. Classical equidistribution consumer -/

/-- A quantitative half-phase discrepancy envelope at arbitrary X. -/
def SquareRootPrimeHalfPhaseDiscrepancyBound (B : ℕ → ℝ) : Prop :=
  ∀ X : ℕ,
    |(squareRootPrimePhaseWindowCount X 0 (1 / 2 : ℝ) : ℝ) -
        (1 / 2 : ℝ) * (primeCountUpTo X : ℝ)| <= B X

/-- Any quantitative global half-phase discrepancy bound transfers directly to
a cumulative square-block midpoint-bias bound. -/
theorem abs_sum_vfMidSquareBlockMidpointBias_le_of_globalBound
    {B : ℕ → ℝ}
    (hB : SquareRootPrimeHalfPhaseDiscrepancyBound B)
    (R n : ℕ) :
    |∑ k ∈ Finset.range n, vfMidSquareBlockMidpointBias (R + k)| <=
      B ((R + n) ^ 2) + B (R ^ 2) := by
  rw [sum_vfMidSquareBlockMidpointBias_eq_globalHalfPhaseDifference]
  have h1 := hB ((R + n) ^ 2)
  have h0 := hB (R ^ 2)
  unfold vfMidGlobalHalfPhaseDiscrepancy
  calc
    |(squareRootPrimePhaseWindowCount ((R + n) ^ 2) 0 (1 / 2 : ℝ) : ℝ) -
          (1 / 2 : ℝ) * (primeCountUpTo ((R + n) ^ 2) : ℝ) -
        ((squareRootPrimePhaseWindowCount (R ^ 2) 0 (1 / 2 : ℝ) : ℝ) -
          (1 / 2 : ℝ) * (primeCountUpTo (R ^ 2) : ℝ))|
        ≤
      |(squareRootPrimePhaseWindowCount ((R + n) ^ 2) 0 (1 / 2 : ℝ) : ℝ) -
          (1 / 2 : ℝ) * (primeCountUpTo ((R + n) ^ 2) : ℝ)| +
      |(squareRootPrimePhaseWindowCount (R ^ 2) 0 (1 / 2 : ℝ) : ℝ) -
          (1 / 2 : ℝ) * (primeCountUpTo (R ^ 2) : ℝ)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le
                ((squareRootPrimePhaseWindowCount ((R + n) ^ 2) 0 (1 / 2 : ℝ) : ℝ) -
                  (1 / 2 : ℝ) * (primeCountUpTo ((R + n) ^ 2) : ℝ))
                0
                ((squareRootPrimePhaseWindowCount (R ^ 2) 0 (1 / 2 : ℝ) : ℝ) -
                  (1 / 2 : ℝ) * (primeCountUpTo (R ^ 2) : ℝ)))
    _ ≤ B ((R + n) ^ 2) + B (R ^ 2) := add_le_add h1 h0

/-- The classical equidistribution proposition implies arbitrarily small
relative global half-phase discrepancy along square endpoints. -/
theorem vfMidGlobalHalfPhaseDiscrepancy_small_of_equidistribution
    (hphase : SquareRootPrimePhaseEquidistributionStatement)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R0 : ℕ, ∀ R : ℕ, R0 <= R →
      |vfMidGlobalHalfPhaseDiscrepancy R| <=
        ε * (primeCountUpTo (R ^ 2) : ℝ) := by
  rcases hphase 0 (1 / 2 : ℝ) ε
      (by norm_num) (by norm_num) (by norm_num) hε with ⟨X0, hX0⟩
  refine ⟨max 1 X0, ?_⟩
  intro R hR
  have hR1 : 1 <= R := (le_max_left 1 X0).trans hR
  have hX : X0 <= R ^ 2 := by
    have hX0R : X0 <= R := (le_max_right 1 X0).trans hR
    have hRR : R <= R ^ 2 := by nlinarith
    exact hX0R.trans hRR
  simpa [vfMidGlobalHalfPhaseDiscrepancy] using hX0 (R ^ 2) hX

/-- Therefore the cumulative midpoint bias over a long block run is exactly a
difference of two globally equidistributed half-phase discrepancies. -/
theorem abs_sum_vfMidSquareBlockMidpointBias_le_of_equidistribution
    (hphase : SquareRootPrimePhaseEquidistributionStatement)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R0 : ℕ, ∀ R n : ℕ, R0 <= R →
      |∑ k ∈ Finset.range n, vfMidSquareBlockMidpointBias (R + k)| <=
        ε * (primeCountUpTo ((R + n) ^ 2) : ℝ) +
          ε * (primeCountUpTo (R ^ 2) : ℝ) := by
  rcases vfMidGlobalHalfPhaseDiscrepancy_small_of_equidistribution
      hphase hε with ⟨R0, hR0⟩
  refine ⟨R0, ?_⟩
  intro R n hR
  rw [sum_vfMidSquareBlockMidpointBias_eq_globalHalfPhaseDifference]
  have hleft := hR0 (R + n) (by omega)
  have hright := hR0 R hR
  calc
    |vfMidGlobalHalfPhaseDiscrepancy (R + n) -
        vfMidGlobalHalfPhaseDiscrepancy R| ≤
      |vfMidGlobalHalfPhaseDiscrepancy (R + n)| +
        |vfMidGlobalHalfPhaseDiscrepancy R| := by
          simpa using
            (abs_sub_le
              (vfMidGlobalHalfPhaseDiscrepancy (R + n))
              0
              (vfMidGlobalHalfPhaseDiscrepancy R))
    _ ≤
        ε * (primeCountUpTo ((R + n) ^ 2) : ℝ) +
          ε * (primeCountUpTo (R ^ 2) : ℝ) :=
      add_le_add hleft hright

end RHLean.Analysis
