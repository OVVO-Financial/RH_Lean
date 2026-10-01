import Mathlib
import RHLean.Analysis.GrowingParentPhaseUniformity
import «research.VF_MID_UNIFORMITY_BIAS_CORRELATION»
import «research.VF_MID_SQUARE_WHEEL_BACKLOG»

/-!
# Global square-root prime phase to VF-mid square-block bias

This file connects the classical equidistribution problem for the fractional
parts {sqrt p} directly to the existing VF-mid midpoint-bias coordinate.

For the half phase window [0,1/2), define

  G_R = #{p <= R^2 : {sqrt p} < 1/2} - (1/2) pi(R^2).

The exact finite identity proved here is

  G_(R+1) - G_R = U_R,

where U_R is the midpoint spatial bias already used by the direct
pi - VF_mid architecture.  Consequently

  sum_{k<n} U_(R+k) = G_(R+n) - G_R.

Thus the classical global square-root phase theorem is not merely analogous
to the square-block picture: its half-window discrepancy is literally the
primitive of the VF-mid block-bias sequence.

The analytic equidistribution theorem itself remains an explicit input through
SquareRootPrimePhaseEquidistributionStatement, which is already the clean
theorem interface in GrowingParentPhaseUniformity.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Prime sites up to X whose square-root fractional phase lies in [0,1/2). -/
def vfMidHalfPhasePrimeSet (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 X).filter fun p =>
    p.Prime ∧
      0 ≤ squareRootPrimePhase p ∧
      squareRootPrimePhase p < (1 / 2 : ℝ)

/-- Half-phase primes contributed by the R-th square block. -/
def vfMidHalfPhasePrimeBand (R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (R ^ 2) ((R + 1) ^ 2)).filter fun p =>
    p.Prime ∧
      0 ≤ squareRootPrimePhase p ∧
      squareRootPrimePhase p < (1 / 2 : ℝ)

/-- The half-phase set is exactly the existing phase-window count at [0,1/2). -/
theorem vfMidHalfPhasePrimeSet_card_eq_phaseWindowCount (X : ℕ) :
    (vfMidHalfPhasePrimeSet X).card =
      squareRootPrimePhaseWindowCount X 0 (1 / 2 : ℝ) := by
  rfl

/-- The square-root fractional phase is always nonnegative. -/
theorem squareRootPrimePhase_nonneg (n : ℕ) :
    0 ≤ squareRootPrimePhase n := by
  have hfloor :
      ((⌊Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at hfloor
  unfold squareRootPrimePhase
  linarith

/-- Exact half-phase/midpoint dictionary on one square block.

For an integer p in (R^2,(R+1)^2), the condition {sqrt p} < 1/2 is equivalent
to p <= R^2+R.  The quarter-square offset disappears because p is integral.
-/
theorem squareRootPrimePhase_lt_half_iff_le_midpoint
    {R p : ℕ} (hp : p ∈ vfMidSquareWheelSites R) :
    squareRootPrimePhase p < (1 / 2 : ℝ) ↔ p ≤ R ^ 2 + R := by
  have hpI := Finset.mem_Ioo.mp hp
  have hsqrtNat : Nat.sqrt p = R := by
    symm
    exact (Nat.eq_sqrt').2 ⟨hpI.1.le, hpI.2⟩
  have hsqrt0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hright0 : 0 ≤ (R : ℝ) + (1 / 2 : ℝ) := by positivity
  have hsq : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  unfold squareRootPrimePhase
  rw [hsqrtNat]
  constructor
  · intro h
    have hsqrtlt :
        Real.sqrt (p : ℝ) < (R : ℝ) + (1 / 2 : ℝ) := by
      linarith
    have hsquare :
        (Real.sqrt (p : ℝ)) ^ 2 <
          ((R : ℝ) + (1 / 2 : ℝ)) ^ 2 :=
      (sq_lt_sq₀ hsqrt0 hright0).2 hsqrtlt
    rw [hsq] at hsquare
    have hnext :
        (p : ℝ) < ((R ^ 2 + R + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    have hnextNat : p < R ^ 2 + R + 1 := by
      exact_mod_cast hnext
    omega
  · intro h
    have hcast :
        (p : ℝ) ≤ ((R ^ 2 + R : ℕ) : ℝ) := by
      exact_mod_cast h
    have hsquare :
        (p : ℝ) < ((R : ℝ) + (1 / 2 : ℝ)) ^ 2 := by
      push_cast at hcast ⊢
      nlinarith
    have hsquares :
        (Real.sqrt (p : ℝ)) ^ 2 <
          ((R : ℝ) + (1 / 2 : ℝ)) ^ 2 := by
      rw [hsq]
      exact hsquare
    have hsqrtlt :
        Real.sqrt (p : ℝ) < (R : ℝ) + (1 / 2 : ℝ) :=
      (sq_lt_sq₀ hsqrt0 hright0).1 hsquares
    linarith

/-- The half-phase primes in one square block are exactly the primes in the
left half through R^2+R. -/
theorem vfMidHalfPhasePrimeBand_eq_leftPrefix (R : ℕ) :
    vfMidHalfPhasePrimeBand R =
      vfMidSquareWheelPrimePrefix R (R ^ 2 + R) := by
  classical
  ext p
  simp only [vfMidHalfPhasePrimeBand, vfMidSquareWheelPrimePrefix,
    vfMidSquareWheelPrimes, vfMidSquareWheelSites,
    Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioo]
  constructor
  · rintro ⟨⟨hlow, hhigh⟩, hpPrime, _hphase0, hphase⟩
    have hne : p ≠ (R + 1) ^ 2 := by
      intro hEq
      subst p
      have hcomp : ¬ ((R + 1) ^ 2).Prime := by
        exact Nat.Prime.not_prime_pow' (by omega : (2 : ℕ) ≠ 1)
      exact hcomp hpPrime
    have hsite : p ∈ vfMidSquareWheelSites R := by
      exact Finset.mem_Ioo.mpr ⟨hlow, lt_of_le_of_ne hhigh hne⟩
    have hmid :=
      (squareRootPrimePhase_lt_half_iff_le_midpoint hsite).1 hphase
    exact ⟨⟨⟨hlow, lt_of_le_of_ne hhigh hne⟩, hpPrime⟩, hmid⟩
  · rintro ⟨⟨⟨hlow, hhigh⟩, hpPrime⟩, hmid⟩
    have hsite : p ∈ vfMidSquareWheelSites R :=
      Finset.mem_Ioo.mpr ⟨hlow, hhigh⟩
    have hphase :=
      (squareRootPrimePhase_lt_half_iff_le_midpoint hsite).2 hmid
    exact ⟨⟨hlow, hhigh.le⟩, hpPrime,
      squareRootPrimePhase_nonneg p, hphase⟩

/-- Exact decomposition of the global half-phase set at consecutive square
endpoints. -/
theorem vfMidHalfPhasePrimeSet_split (R : ℕ) (hR : 2 ≤ R) :
    vfMidHalfPhasePrimeSet ((R + 1) ^ 2) =
      vfMidHalfPhasePrimeSet (R ^ 2) ∪ vfMidHalfPhasePrimeBand R := by
  classical
  ext p
  simp only [vfMidHalfPhasePrimeSet, vfMidHalfPhasePrimeBand,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp2, hpU⟩, hgood⟩
    by_cases hpL : p ≤ R ^ 2
    · exact Or.inl ⟨⟨hp2, hpL⟩, hgood⟩
    · exact Or.inr ⟨⟨lt_of_not_ge hpL, hpU⟩, hgood⟩
  · rintro (h | h)
    · exact ⟨⟨h.1.1, h.1.2.trans (Nat.pow_le_pow_left (by omega) 2)⟩, h.2⟩
    · exact ⟨⟨by omega, h.1.2⟩, h.2⟩

/-- The old half-phase prefix and the new half-phase square block are disjoint. -/
theorem vfMidHalfPhasePrimeSet_disjoint_band (R : ℕ) :
    Disjoint (vfMidHalfPhasePrimeSet (R ^ 2))
      (vfMidHalfPhasePrimeBand R) := by
  rw [Finset.disjoint_left]
  intro p hpOld hpNew
  have hOld :=
    (Finset.mem_filter.mp hpOld).1
  have hNew :=
    (Finset.mem_filter.mp hpNew).1
  have hpLe : p ≤ R ^ 2 := (Finset.mem_Icc.mp hOld).2
  have hpGt : R ^ 2 < p := (Finset.mem_Ioc.mp hNew).1
  omega

/-- Half-phase counts telescope by the literal left-half prime population. -/
theorem squareRootPrimePhaseWindowCount_sq_succ
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootPrimePhaseWindowCount ((R + 1) ^ 2) 0 (1 / 2 : ℝ) =
      squareRootPrimePhaseWindowCount (R ^ 2) 0 (1 / 2 : ℝ) +
        (vfMidSquareWheelPrimePrefix R (R ^ 2 + R)).card := by
  rw [← vfMidHalfPhasePrimeSet_card_eq_phaseWindowCount,
    ← vfMidHalfPhasePrimeSet_card_eq_phaseWindowCount,
    vfMidHalfPhasePrimeSet_split R hR,
    Finset.card_union_of_disjoint (vfMidHalfPhasePrimeSet_disjoint_band R),
    vfMidHalfPhasePrimeBand_eq_leftPrefix R]

/-- The repository's elementary prime count agrees with the local phase
module's finite prime count. -/
theorem primeCountUpTo_eq_primeCounting (X : ℕ) :
    primeCountUpTo X = Nat.primeCounting X := by
  classical
  have hset :
      (Finset.Icc 2 X).filter Nat.Prime =
        (Finset.range (X + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_hp2, hpX⟩, hpPrime⟩
      exact ⟨hpX, hpPrime⟩
    · rintro ⟨hpX, hpPrime⟩
      exact ⟨⟨hpPrime.two_le, hpX⟩, hpPrime⟩
  unfold primeCountUpTo Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  exact congrArg Finset.card hset

/-- Global centered half-phase discrepancy at the square endpoint R^2. -/
def vfMidGlobalHalfPhaseDiscrepancy (R : ℕ) : ℝ :=
  (squareRootPrimePhaseWindowCount (R ^ 2) 0 (1 / 2 : ℝ) : ℝ) -
    (1 / 2 : ℝ) * (primeCountUpTo (R ^ 2) : ℝ)

/-- Exact derivative identity.  The finite difference of the global
half-phase discrepancy is exactly the VF-mid midpoint block bias U_R. -/
theorem vfMidGlobalHalfPhaseDiscrepancy_succ
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidGlobalHalfPhaseDiscrepancy (R + 1) -
        vfMidGlobalHalfPhaseDiscrepancy R =
      vfMidSquareBlockMidpointBias R := by
  have hphase := squareRootPrimePhaseWindowCount_sq_succ R hR
  have hprime :=
    vfMidIntegerBlockPrimeSupply_add_primeCounting R
  have hprimeLocal :
      primeCountUpTo ((R + 1) ^ 2) =
        primeCountUpTo (R ^ 2) +
          (vfMidSquareWheelPrimes R).card := by
    rw [primeCountUpTo_eq_primeCounting,
      primeCountUpTo_eq_primeCounting]
    rw [← vfMidDirectPrimeBand_eq_squareWheelPrimes]
    simpa [vfMidIntegerBlockPrimeSupply, Nat.add_comm] using hprime.symm
  unfold vfMidGlobalHalfPhaseDiscrepancy
    vfMidSquareBlockMidpointBias
    vfMidSquareBlockPrimeLeft
    vfMidSquareBlockPrimeTotal
  push_cast at hphase hprimeLocal
  rw [hphase, hprimeLocal]
  ring

/-- Exact global-to-local telescope.  The accumulated midpoint biases are
the endpoint difference of the classical half-phase discrepancy. -/
theorem vfMidSquareBlockMidpointBias_sum_eq_globalPhaseDifference
    (R n : ℕ) (hR : 2 ≤ R) :
    (∑ k ∈ Finset.range n, vfMidSquareBlockMidpointBias (R + k)) =
      vfMidGlobalHalfPhaseDiscrepancy (R + n) -
        vfMidGlobalHalfPhaseDiscrepancy R := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hRn : 2 ≤ R + n := by omega
      rw [Finset.sum_range_succ, ih]
      have hstep :=
        vfMidGlobalHalfPhaseDiscrepancy_succ (R + n) hRn
      rw [Nat.add_succ]
      linarith

/-! ## Consequence of the classical global equidistribution theorem -/

/-- The classical square-root-prime phase theorem implies that the global
half-window discrepancy is arbitrarily small relative to pi(R^2) at all
sufficiently large square endpoints. -/
theorem vfMidGlobalHalfPhaseDiscrepancy_eventually_relative
    (hphase : SquareRootPrimePhaseEquidistributionStatement)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R0 : ℕ, ∀ R : ℕ, R0 ≤ R →
      |vfMidGlobalHalfPhaseDiscrepancy R| ≤
        ε * (primeCountUpTo (R ^ 2) : ℝ) := by
  rcases hphase 0 (1 / 2 : ℝ) ε
      (by norm_num) (by norm_num) (by norm_num) hε with
    ⟨X0, hX0⟩
  refine ⟨max X0 2, ?_⟩
  intro R hR
  have hRX0 : X0 ≤ R := le_trans (le_max_left X0 2) hR
  have hR2 : 2 ≤ R := le_trans (le_max_right X0 2) hR
  have hsq : X0 ≤ R ^ 2 := by
    have hRR : R ≤ R ^ 2 := by nlinarith
    exact hRX0.trans hRR
  simpa [vfMidGlobalHalfPhaseDiscrepancy] using hX0 (R ^ 2) hsq

/-- Consequently the cumulative square-block midpoint bias over any finite
window is controlled by the two global half-phase endpoint discrepancies. -/
theorem abs_vfMidSquareBlockMidpointBias_sum_le_globalPhaseEndpoints
    (R n : ℕ) (hR : 2 ≤ R) :
    |∑ k ∈ Finset.range n, vfMidSquareBlockMidpointBias (R + k)| ≤
      |vfMidGlobalHalfPhaseDiscrepancy (R + n)| +
        |vfMidGlobalHalfPhaseDiscrepancy R| := by
  rw [vfMidSquareBlockMidpointBias_sum_eq_globalPhaseDifference R n hR]
  exact abs_sub _ _

end RHLean.Analysis
