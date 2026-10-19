import RHLean.Analysis.BlockCovarianceRefinement
import «research.VF_919_SEVEN_EIGHTHS_DYADIC_SHELL_COVARIANCE_20261019»

/-!
# Chronological Euler prime arrivals and a symbolic prime-density baseline

Every newly admitted physical integer n contributes
    mu(n) * M(n-1)
to total signed pair covariance. For prime p this is EXACTLY -M(p-1).
For a generic prime-count baseline b, its discrete increments can be
inserted and subtracted with an *explicit signed weighted error*.

The PNT-style baseline b(x) = x/log x is instantiated only as a model,
not a bound on the signed error (or a local prime-count theorem).
The prime-square handoff is a separate, exactly conserved
reclassification; it does not change total physical covariance.

NO uniform 7/8, RH or weighted PNT covariance estimate is assumed.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

def vf919EulerPrimeIndicator (n : ℕ) : ℝ :=
  if n.Prime then 1 else 0

theorem vf919EulerPrimeMobius (p : ℕ) (hp : p.Prime) :
    realMoebiusStep p = -1 := by
  unfold realMoebiusStep
  rw [ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- The newly admitted prime changes the *real* pair covariance by -M(p-1). -/
theorem vf919EulerPrimeArrival_pairIncrement
    (p : ℕ) (hp : p.Prime) :
    realMertensPositiveLagPairSum (p + 1) -
      realMertensPositiveLagPairSum p = -realMertensLength p := by
  rw [realMertensPositiveLagPairSum_succ, vf919EulerPrimeMobius p hp]
  ring

def vf919EulerPrimeArrivalPairs (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K,
    -(vf919EulerPrimeIndicator n * realMertensLength n)

def vf919EulerNonprimeArrivalPairs (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K,
    if n.Prime then 0 else realMoebiusStep n * realMertensLength n

/-- No primes or composite arrivals omitted: genuine Green--Kubo source. -/
theorem vf919EulerPairs_eq_prime_add_nonprime (K : ℕ) :
    realMertensPositiveLagPairSum K =
      vf919EulerPrimeArrivalPairs K +
        vf919EulerNonprimeArrivalPairs K := by
  unfold realMertensPositiveLagPairSum
    vf919EulerPrimeArrivalPairs vf919EulerNonprimeArrivalPairs
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp [vf919EulerPrimeIndicator, hp, vf919EulerPrimeMobius n hp]
  · simp [vf919EulerPrimeIndicator, hp]

/-- A generic cumulative prime baseline, NOT an event-level prime indicator. -/
def vf919EulerBaselineStep (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  b n - b (n - 1)

/-- Signed pair contribution if arrivals were weighted by increments of b. -/
def vf919EulerModeledPrimePairs (b : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K,
    -(vf919EulerBaselineStep b n * realMertensLength n)

/-- The exact weighted discrepancy between actual primes and b increments. -/
def vf919EulerPrimeResidualPairs (b : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K,
    -((vf919EulerPrimeIndicator n - vf919EulerBaselineStep b n) *
        realMertensLength n)

/-- Valid for EVERY baseline b, irrespective of any PNT hypothesis. -/
theorem vf919EulerPrimePairs_eq_model_add_residual
    (b : ℕ → ℝ) (K : ℕ) :
    vf919EulerPrimeArrivalPairs K =
      vf919EulerModeledPrimePairs b K +
        vf919EulerPrimeResidualPairs b K := by
  unfold vf919EulerPrimeArrivalPairs vf919EulerModeledPrimePairs
    vf919EulerPrimeResidualPairs
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- All sources retained: modeled primes, prime-model error, composites. -/
theorem vf919EulerAllPairs_eq_model_residual_nonprime
    (b : ℕ → ℝ) (K : ℕ) :
    realMertensPositiveLagPairSum K =
      vf919EulerModeledPrimePairs b K +
        vf919EulerPrimeResidualPairs b K +
          vf919EulerNonprimeArrivalPairs K := by
  rw [vf919EulerPairs_eq_prime_add_nonprime,
    vf919EulerPrimePairs_eq_model_add_residual]

/-- Explicit x/log x baseline, defined as 0 at the two initial endpoints. -/
def vf919EulerXOverLogX (x : ℕ) : ℝ :=
  if x ≤ 1 then 0 else (x : ℝ) / Real.log (x : ℝ)

/-- PNT alone is NOT a weighted residual bound; this equality exposes it. -/
theorem vf919EulerXOverLogX_exactSignedCovariance (K : ℕ) :
    realMertensPositiveLagPairSum K =
      vf919EulerModeledPrimePairs vf919EulerXOverLogX K +
        vf919EulerPrimeResidualPairs vf919EulerXOverLogX K +
          vf919EulerNonprimeArrivalPairs K :=
  vf919EulerAllPairs_eq_model_residual_nonprime
    vf919EulerXOverLogX K

/-- Genuine high-prime offspring of p at the square boundary p^2,
with all cofactors c<p. -/
def vf919EulerPrimeSquareHandoff (p : ℕ) : ℝ :=
  ∑ c ∈ Finset.Ico 1 p, realMoebiusStep (p * c)

/-- At the exact prime-square transition, signed reclassification is
-M(p-1), without any density assumption or complex embedding. -/
theorem vf919EulerPrimeSquareHandoff_eq_neg_parent
    (p : ℕ) (hp : p.Prime) :
    vf919EulerPrimeSquareHandoff p = -realMertensLength p := by
  have hle : 1 ≤ p := by omega
  have hzero : realMertensLength 1 = 0 := by
    simp [realMertensLength, realMoebiusStep]
  have hIco :
      (∑ c ∈ Finset.Ico 1 p, realMoebiusStep c) =
        realMertensLength p - realMertensLength 1 := by
    simpa [realMertensLength] using
      (Finset.sum_Ico_eq_sub (fun c : ℕ => realMoebiusStep c) hle)
  unfold vf919EulerPrimeSquareHandoff
  calc
    (∑ c ∈ Finset.Ico 1 p, realMoebiusStep (p * c)) =
        ∑ c ∈ Finset.Ico 1 p, -realMoebiusStep c := by
      apply Finset.sum_congr rfl
      intro c hc
      exact realMoebiusStep_prime_mul_of_lt hp
        (Finset.mem_Ico.mp hc).2
    _ = -(∑ c ∈ Finset.Ico 1 p, realMoebiusStep c) := by
      rw [Finset.sum_neg_distrib]
    _ = -realMertensLength p := by rw [hIco, hzero]; ring

/-- Reclassifying a signed mass t and diagonal d from HIGH to LOW changes
the three pair covariance components but leaves their sum invariant.
The mass of an already admitted integer is NOT created a second time. -/
theorem vf919EulerHandoff_conserves_threeCovariances
    (L H KL KH t d : ℝ) :
    ((L + t) ^ 2 - (KL + d)) / 2 +
      ((H - t) ^ 2 - (KH - d)) / 2 +
        (L + t) * (H - t) =
    (L ^ 2 - KL) / 2 + (H ^ 2 - KH) / 2 + L * H := by
  ring

#print axioms vf919EulerPrimeMobius
#print axioms vf919EulerPrimeArrival_pairIncrement
#print axioms vf919EulerPairs_eq_prime_add_nonprime
#print axioms vf919EulerPrimePairs_eq_model_add_residual
#print axioms vf919EulerAllPairs_eq_model_residual_nonprime
#print axioms vf919EulerXOverLogX_exactSignedCovariance
#print axioms vf919EulerPrimeSquareHandoff_eq_neg_parent
#print axioms vf919EulerHandoff_conserves_threeCovariances

end RHLean.Analysis
