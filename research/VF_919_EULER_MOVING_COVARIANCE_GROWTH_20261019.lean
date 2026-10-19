import «research.VF_919_EULER_PRIME_DENSITY_LEDGER_20261019»
import «research.VF_919_MARKED_FIRST_OWNER_SHELL_20261019»

/-!
# Moving square-root low/high covariance; genuine shell prime/composite growth

Strict LOW at integer X means EVERY prime divisor p of a site obeys
p^2 < X. Equality p^2 = X remains HIGH. The physical Mobius weight of
a site NEVER changes on reclassification, only its component label.

Every completed square shell obeys the exact signed source identity
    S_R = B_R - Q_R
where Q_R is the actual prime count and B_R is the actual signed
nonprime Mobius response. We insert the cumulative model x/log x by
addition/subtraction, retaining BOTH full arithmetic error sources.

In dyadic H-shells, the exact energy is a large positive composite
square + prime square - twice the signed composite/prime interaction.
The conditional TWO-source error budget is proved, but neither error
budget is inferred from PNT. The independent 7/8 bound remains open.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- At time X, p is strictly LOW exactly when p²<X. -/
def vf919EulerStrictLow (X n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 < X

/-- A prime stays HIGH at X=p² and becomes strictly LOW
at X=p²+1. This is the literal arithmetic clock, not a heuristic. -/
theorem vf919EulerPrime_strictLow_crossing
    (p : ℕ) (hp : p.Prime) :
    ¬ vf919EulerStrictLow (p ^ 2) p ∧
      vf919EulerStrictLow (p ^ 2 + 1) p := by
  constructor
  · intro h
    have hb := h p hp (dvd_refl p)
    omega
  · intro q hq hd
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hd
    rw [hqp]
    omega

def vf919EulerLowSite (X n : ℕ) : ℝ :=
  if vf919EulerStrictLow X n then realMoebiusStep n else 0

def vf919EulerHighSite (X n : ℕ) : ℝ :=
  if vf919EulerStrictLow X n then 0 else realMoebiusStep n

theorem vf919EulerLowHigh_sitePartition (X n : ℕ) :
    realMoebiusStep n =
      vf919EulerLowSite X n + vf919EulerHighSite X n := by
  unfold vf919EulerLowSite vf919EulerHighSite
  by_cases h : vf919EulerStrictLow X n <;> simp [h]

theorem vf919EulerLowHigh_siteDiagonal (X n : ℕ) :
    realMoebiusStep n ^ 2 =
      vf919EulerLowSite X n ^ 2 + vf919EulerHighSite X n ^ 2 := by
  unfold vf919EulerLowSite vf919EulerHighSite
  by_cases h : vf919EulerStrictLow X n <;> simp [h]

def vf919EulerLowMass (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), vf919EulerLowSite X n

def vf919EulerHighMass (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), vf919EulerHighSite X n

def vf919EulerLowDiagonal (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), vf919EulerLowSite X n ^ 2

def vf919EulerHighDiagonal (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), vf919EulerHighSite X n ^ 2

theorem vf919EulerLowHigh_totalMass (X : ℕ) :
    realMertensLength (X + 1) =
      vf919EulerLowMass X + vf919EulerHighMass X := by
  unfold realMertensLength vf919EulerLowMass vf919EulerHighMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  exact vf919EulerLowHigh_sitePartition X n

theorem vf919EulerLowHigh_totalDiagonal (X : ℕ) :
    realMertensDiagonal (X + 1) =
      vf919EulerLowDiagonal X + vf919EulerHighDiagonal X := by
  unfold realMertensDiagonal vf919EulerLowDiagonal vf919EulerHighDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  exact vf919EulerLowHigh_siteDiagonal X n

def vf919EulerLLPairs (X : ℕ) : ℝ :=
  (vf919EulerLowMass X ^ 2 - vf919EulerLowDiagonal X) / 2

def vf919EulerHHPairs (X : ℕ) : ℝ :=
  (vf919EulerHighMass X ^ 2 - vf919EulerHighDiagonal X) / 2

def vf919EulerLHPairs (X : ℕ) : ℝ :=
  vf919EulerLowMass X * vf919EulerHighMass X

/-- EXACT every-X moving signed Gram: no independence and no density law. -/
theorem vf919EulerMovingCovariance_exact (X : ℕ) :
    realMertensPositiveLagPairSum (X + 1) =
      vf919EulerLLPairs X + vf919EulerHHPairs X +
        vf919EulerLHPairs X := by
  have h :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (X + 1)
  rw [vf919EulerLowHigh_totalMass X,
    vf919EulerLowHigh_totalDiagonal X] at h
  unfold vf919EulerLLPairs vf919EulerHHPairs vf919EulerLHPairs
  nlinarith [h]

/-- Physical prime admissions in [R²,(R+1)²), NOT just expected arrivals. -/
def vf919EulerShellPrimeCount (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
    vf919EulerPrimeIndicator n

/-- Signed true nonprime Mobius response in the same physical shell. -/
def vf919EulerShellCompositeMass (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
    if n.Prime then 0 else realMoebiusStep n

/-- Exact integer prime/composite shell source. Even n=1 is retained. -/
theorem vf919EulerSquareShell_eq_composites_sub_primes (R : ℕ) :
    vf919SquareShellSum R =
      vf919EulerShellCompositeMass R -
        vf919EulerShellPrimeCount R := by
  rw [vf919SquareShellSum_eq_physicalIco]
  unfold vf919EulerShellCompositeMass vf919EulerShellPrimeCount
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp [vf919EulerPrimeIndicator, hp, vf919EulerPrimeMobius n hp]
  · simp [vf919EulerPrimeIndicator, hp]

/-- Difference of the *cumulative* x/log x baseline across the exact
half-open square shell: [R²,(R+1)²). -/
def vf919EulerShellPNTBaseline (R : ℕ) : ℝ :=
  vf919EulerXOverLogX ((R + 1) ^ 2 - 1) -
    vf919EulerXOverLogX (R ^ 2 - 1)

def vf919EulerShellCompositeResponseError (R : ℕ) : ℝ :=
  vf919EulerShellCompositeMass R - vf919EulerShellPNTBaseline R

def vf919EulerShellPrimeCountError (R : ℕ) : ℝ :=
  vf919EulerShellPrimeCount R - vf919EulerShellPNTBaseline R

/-- The proposed growth-rate difference is EXACTLY the difference of two
SIGNED arithmetic errors, not the leading number-of-primes density alone. -/
theorem vf919EulerShell_growthDifference_exact (R : ℕ) :
    vf919SquareShellSum R =
      vf919EulerShellCompositeResponseError R -
        vf919EulerShellPrimeCountError R := by
  rw [vf919EulerSquareShell_eq_composites_sub_primes]
  unfold vf919EulerShellCompositeResponseError vf919EulerShellPrimeCountError
  ring

/-- Fully signed interaction, with the negative -2 B_R Q_R retained. -/
theorem vf919EulerShell_energy_decomposition (R : ℕ) :
    vf919SquareShellSum R ^ 2 =
      vf919EulerShellCompositeMass R ^ 2 +
        vf919EulerShellPrimeCount R ^ 2 -
          2 * vf919EulerShellCompositeMass R *
            vf919EulerShellPrimeCount R := by
  rw [vf919EulerSquareShell_eq_composites_sub_primes]
  ring

def vf919EulerDyadicCompositeResponseErrorEnergy (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    vf919EulerShellCompositeResponseError R ^ 2

def vf919EulerDyadicPrimeCountErrorEnergy (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    vf919EulerShellPrimeCountError R ^ 2

/-- Cauchy--Schwarz-friendly exact energy over actual Euler sources. -/
theorem vf919EulerDyadicEnergy_eq_growthDifference (H : ℕ) :
    vf919DyadicSquareShellEnergy H =
      ∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerShellCompositeResponseError R -
          vf919EulerShellPrimeCountError R) ^ 2 := by
  unfold vf919DyadicSquareShellEnergy
  apply Finset.sum_congr rfl
  intro R _
  rw [vf919EulerShell_growthDifference_exact]

/-- Sufficient TWO-SOURCE budget. This does NOT assume the budgets hold,
and a PNT first-order approximation alone does not establish them. -/
theorem vf919EulerDyadicEnergy_le_two_growthErrors (H : ℕ) :
    vf919DyadicSquareShellEnergy H ≤
      2 * (vf919EulerDyadicCompositeResponseErrorEnergy H +
        vf919EulerDyadicPrimeCountErrorEnergy H) := by
  rw [vf919EulerDyadicEnergy_eq_growthDifference]
  unfold vf919EulerDyadicCompositeResponseErrorEnergy
    vf919EulerDyadicPrimeCountErrorEnergy
  calc
    (∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerShellCompositeResponseError R -
          vf919EulerShellPrimeCountError R) ^ 2) ≤
      ∑ R ∈ Finset.Ico H (2 * H),
        (2 * (vf919EulerShellCompositeResponseError R ^ 2 +
          vf919EulerShellPrimeCountError R ^ 2)) := by
        apply Finset.sum_le_sum
        intro R _
        nlinarith [sq_nonneg (vf919EulerShellCompositeResponseError R +
          vf919EulerShellPrimeCountError R)]
    _ = 2 * ((∑ R ∈ Finset.Ico H (2 * H),
           vf919EulerShellCompositeResponseError R ^ 2) +
        (∑ R ∈ Finset.Ico H (2 * H),
           vf919EulerShellPrimeCountError R ^ 2)) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib]
      ring

/-- Named acceptance gate: both density-response error energies must
be bounded BY ARITHMETIC, not by an assumed Mertens theorem. -/
theorem vf919EulerDyadicEnergy_of_growthErrorBudgets
    (H : ℕ) (A B : ℝ)
    (hcomp : vf919EulerDyadicCompositeResponseErrorEnergy H ≤ A)
    (hprime : vf919EulerDyadicPrimeCountErrorEnergy H ≤ B) :
    vf919DyadicSquareShellEnergy H ≤ 2 * (A + B) := by
  have h := vf919EulerDyadicEnergy_le_two_growthErrors H
  linarith

#print axioms vf919EulerPrime_strictLow_crossing
#print axioms vf919EulerLowHigh_sitePartition
#print axioms vf919EulerLowHigh_siteDiagonal
#print axioms vf919EulerLowHigh_totalMass
#print axioms vf919EulerLowHigh_totalDiagonal
#print axioms vf919EulerMovingCovariance_exact
#print axioms vf919EulerSquareShell_eq_composites_sub_primes
#print axioms vf919EulerShell_growthDifference_exact
#print axioms vf919EulerShell_energy_decomposition
#print axioms vf919EulerDyadicEnergy_eq_growthDifference
#print axioms vf919EulerDyadicEnergy_le_two_growthErrors
#print axioms vf919EulerDyadicEnergy_of_growthErrorBudgets

end RHLean.Analysis
