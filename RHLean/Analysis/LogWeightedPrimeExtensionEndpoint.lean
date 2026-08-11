import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionFiber

/-!
# Endpoint form of the log-weighted child-fiber identity

This module packages the local squarefree child-fiber theorem into an exact
finite block identity.  It deliberately separates the endpoint-fiber theorem
from the remaining rectangular product-fiber reindexing.

The final section begins the architecture-native prime-number-theorem route.
Its first object is the finite Chebyshev `psi` mass, defined directly from the
von Mangoldt function already available at the repository's pinned Mathlib
revision.  No theorem asserting PNT is imported or used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The squarefree endpoint child fiber.  Non-squarefree endpoints contribute
zero, matching their Möbius weight. -/
def logWeightedEndpointFiber (n : ℕ) : ℝ :=
  if Squarefree n then
    ∑ p ∈ n.primeFactors, moebiusReal (n / p) * Real.log p
  else
    0

/-- Exact value of one endpoint child fiber. -/
theorem logWeightedEndpointFiber_eq (n : ℕ) :
    logWeightedEndpointFiber n = -moebiusReal n * Real.log n := by
  by_cases hs : Squarefree n
  · simp only [logWeightedEndpointFiber, if_pos hs]
    exact sum_log_p_mu_parent_eq_neg_mu_log n hs
  · simp only [logWeightedEndpointFiber, if_neg hs]
    have hmu : μ n = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
    simp [moebiusReal, hmu]

/-- Endpoint-first fresh child mass on the doubling block. -/
def logWeightedEndpointFiberMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N), logWeightedEndpointFiber n

/-- The endpoint-first child mass is exactly the negative log-weighted Möbius
block. -/
theorem logWeightedEndpointFiberMass_eq_neg_logWeightedBlock (N : ℕ) :
    logWeightedEndpointFiberMass N = -logWeightedBlock N := by
  unfold logWeightedEndpointFiberMass logWeightedBlock
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [logWeightedEndpointFiber_eq]
  ring

/-! ## Native PNT: finite von Mangoldt layer -/

/-- Finite Chebyshev `psi` mass through the integer endpoint `x`, defined
without any asymptotic theorem. -/
def nativePsi (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, Λ n

/-- Finite logarithmic mass through `x`. -/
def nativeLogMass (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, Real.log n

/-- Divisor-first form of the same logarithmic mass.  This is the first exact
multiplicative reindexing in the native Selberg route: every `log n` is the sum
of von Mangoldt weights over the divisor fibre of `n`. -/
def nativeDivisorVonMangoldtMass (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, Λ d

/-- Exact finite divisor identity underlying the architecture-native PNT route. -/
theorem nativeLogMass_eq_divisorVonMangoldtMass (x : ℕ) :
    nativeLogMass x = nativeDivisorVonMangoldtMass x := by
  unfold nativeLogMass nativeDivisorVonMangoldtMass
  apply Finset.sum_congr rfl
  intro n hn
  rw [ArithmeticFunction.vonMangoldt_sum]

end RHLean.Analysis
