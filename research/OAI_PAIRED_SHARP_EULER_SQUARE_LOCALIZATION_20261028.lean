import Mathlib
import «research.EULER_THREE_SITE_STRATIFIED_SAMPLING_20261028»
import «research.VF_919_OAI_TRUE_IDEAL_NORM_SHARP_SQUARE_BLOCK_20261019»
import «research.VF_919_SEVEN_EIGHTHS_ENDPOINT_TRANSFER_20261019»

/-!
# Exact original-sharp OAI localization into the moving Euler populations

This is the source-level piece that CAN be transferred without assumptions:
the actual quadratic ideal-norm *sharp* source at the two square walls
reassembles into the original three Euler prime-population increments.
The full physical source is formed by taking the endpoint difference
BEFORE squaring. It is NOT asserted to be the original OAI smoothed,
compensated cubic-theta detector probe.

Crucial analytic distinction:
- the imported OAI 7/8 theorem bounds a complete PREFIX square;
- an L² average of the SEPARATE sharp square-shell squares is stronger.
- OAI's smooth Hecke source moment bounds are NOT automatically a
  uniform sharp-window estimate. Such a theorem is not proved here.

All results below are source-faithful finite identities and a genuine
deterministic non-implication test with a bounded signed block model.
No new analytic moment estimate or exponent is asserted.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis
open RHLean.Proof

/-- The exact sharp square-block source in the true Eisenstein norm
coefficient, *not* the compensated/marked cubic-theta detector. -/
def oaiPairedActualSharpSource (R : ℕ) : ℂ :=
  vf919OAITrueSquareIdealNormSource R

/-- Full weighted squared-sharp energy, sampling the deterministic root R
over one dyadic band. All R-summation happens AFTER endpoint pairing. -/
def oaiPairedActualSharpEnergy (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H), ‖oaiPairedActualSharpSource R‖ ^ 2

/-- The true square-shell coefficient is the COMPLEX square-endpoint
difference of genuine integer Mobius prefixes. -/
theorem oaiPaired_squareShell_eq_originalMertensDifference
    (R : ℕ) (hR : 1 ≤ R) :
    (vf919SquareShellSum R : ℂ) =
      mertensSummatory (squareRootEndpoint (R + 1)) -
        mertensSummatory (squareRootEndpoint R) := by
  have hhi := vf919SquarePrefix_realComplex_exact (R + 1) (by omega)
  have hlo := vf919SquarePrefix_realComplex_exact R hR
  unfold vf919SquareShellSum squareRootEndpoint
  push_cast
  rw [hhi, hlo]

/-- Equivalence of the actual source's real signed shell and the native
three-prime-band sampler, without a random-sign assumption. -/
theorem oaiPaired_realShell_eq_eulerShell
    (R : ℕ) (hR : 1 ≤ R) :
    vf919SquareShellSum R = eulerThreeShellMobius R := by
  have h := oaiPaired_squareShell_eq_originalMertensDifference R hR
  have hr := congrArg Complex.re h
  simpa only [Complex.ofReal_re, eulerThreeShellMobius] using hr

/-- Actual sharp norm-fiber source equals all THREE signed moving Euler
prime-population fluxes, retaining every prime and quotient, exactly. -/
theorem oaiPaired_originalSharp_eq_movingPrimeFlux
    (R : ℕ) (hR : 4 ≤ R) :
    oaiPairedActualSharpSource R =
      (eulerThreeLow (R + 1) - eulerThreeLow R) +
      (eulerThreeMiddle (R + 1) - eulerThreeMiddle R) +
      (eulerThreeTop (R + 1) - eulerThreeTop R) := by
  unfold oaiPairedActualSharpSource
  rw [vf919OAITrueSquareIdealNormSource_eq_originalShell R hR]
  rw [oaiPaired_squareShell_eq_originalMertensDifference R (by omega)]
  rw [eulerThree_endpoint_eq_three_strata (R + 1) (by omega),
    eulerThree_endpoint_eq_three_strata R (by omega)]
  ring

/-- The SAME source is also the entire physical SITE-location flux;
upper-half site masses include composites and all moving boundary
transfers. Taking an endpoint difference prevents losing those terms. -/
theorem oaiPaired_originalSharp_eq_movingSiteFlux
    (R : ℕ) (hR : 4 ≤ R) :
    oaiPairedActualSharpSource R =
      (eulerSiteLow (R + 1) - eulerSiteLow R) +
      (eulerSiteMiddle (R + 1) - eulerSiteMiddle R) +
      (eulerSiteTop (R + 1) - eulerSiteTop R) := by
  unfold oaiPairedActualSharpSource
  rw [vf919OAITrueSquareIdealNormSource_eq_originalShell R hR]
  rw [oaiPaired_squareShell_eq_originalMertensDifference R (by omega)]
  rw [eulerSite_endpoint_eq_three_location_strata,
    eulerSite_endpoint_eq_three_location_strata]
  ring

/-- All newly entering physical integers of the square shell lie in the
upper half of the NEW endpoint, for R>=3. This geometric statement is
unrelated to whether those integers are prime: composites remain. -/
theorem oaiPaired_newShell_above_newHalf
    (R n : ℕ) (hR : 3 ≤ R) (hn : R ^ 2 ≤ n) :
    (R + 1) ^ 2 - 1 < 2 * n := by
  have hpos : 1 ≤ (R + 1) ^ 2 := by nlinarith
  have hid : (R + 1) ^ 2 - 1 = R ^ 2 + 2 * R := by
    have hs : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    omega
  rw [hid]
  nlinarith

/-- Dyadic sharp-norm energy is EXACTLY the existing, original integer
square-shell second moment. This identity is NOT the OAI detector moment
inequality, whose test functions are smooth and which averages character
rows rather than physical square roots. -/
theorem oaiPaired_actualSharpEnergy_eq_nativeDyadicEnergy
    (H : ℕ) (hH : 4 ≤ H) :
    oaiPairedActualSharpEnergy H = vf919DyadicSquareShellEnergy H := by
  unfold oaiPairedActualSharpEnergy vf919DyadicSquareShellEnergy
    oaiPairedActualSharpSource
  apply Finset.sum_congr rfl
  intro R hR
  have hroot : 4 ≤ R := (le_trans hH (Finset.mem_Ico.mp hR).1)
  rw [vf919OAITrueSquareIdealNormSource_eq_originalShell R hroot]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The same paired ideal norm energy is also the EXACT L² moment of
three moving prime-admission populations, including their signed cross
terms, without assuming decorrelation. -/
theorem oaiPaired_actualSharpEnergy_eq_primeSampler
    (H : ℕ) (hH : 4 ≤ H) :
    oaiPairedActualSharpEnergy H = eulerThreeSampledShellEnergy H := by
  rw [oaiPaired_actualSharpEnergy_eq_nativeDyadicEnergy H hH]
  unfold vf919DyadicSquareShellEnergy eulerThreeSampledShellEnergy
  apply Finset.sum_congr rfl
  intro R hR
  have hR1 : 1 ≤ R := by
    have hR0 := (Finset.mem_Ico.mp hR).1
    omega
  rw [oaiPaired_realShell_eq_eulerShell R hR1]

/-- A second moment upper bound for the ACTUAL, paired, sharp ideal
source has the desired consequence on the true three-Euler-band energy.
The analytic source inequality is an EXPLICIT argument, not imported
from OpenAI's global 7/8 theorem by a mistaken non-implication. -/
theorem oaiPaired_actualSharpMoment_consumer
    (H : ℕ) (hH : 4 ≤ H) (T : ℝ)
    (hSharp : oaiPairedActualSharpEnergy H ≤ T) :
    eulerThreeSampledShellEnergy H ≤ T := by
  rwa [oaiPaired_actualSharpEnergy_eq_primeSampler H hH] at hSharp


/-- UNIFORM PARTITION CONSTANTS STAY UNIFORM: if each of the three
moving Euler streams has the same dyadic second-moment bound T, the
actual physical source has bound 9*T. Nothing about a moving boundary
changes the factor 9. The analytic component hypotheses are explicit;
they do not follow from the original OAI profile family automatically. -/
theorem oaiPaired_threeUniformDyadicEnergy
    (H : ℕ) (hH : 4 ≤ H) (T : ℝ)
    (hL : (∑ R ∈ Finset.Ico H (2 * H),
      (eulerThreeShellLow R) ^ 2) ≤ T)
    (hM : (∑ R ∈ Finset.Ico H (2 * H),
      (eulerThreeShellMiddle R) ^ 2) ≤ T)
    (hU : (∑ R ∈ Finset.Ico H (2 * H),
      (eulerThreeShellTop R) ^ 2) ≤ T) :
    oaiPairedActualSharpEnergy H ≤ 9 * T := by
  rw [oaiPaired_actualSharpEnergy_eq_primeSampler H hH]
  unfold eulerThreeSampledShellEnergy
  calc
    _ = ∑ R ∈ Finset.Ico H (2 * H),
        (eulerThreeShellLow R + eulerThreeShellMiddle R +
          eulerThreeShellTop R) ^ 2 := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [eulerThree_shellFlow_eq_three R
        (by have hr := (Finset.mem_Ico.mp hR).1; omega)]
    _ ≤ ∑ R ∈ Finset.Ico H (2 * H),
        3 * ((eulerThreeShellLow R) ^ 2 +
          (eulerThreeShellMiddle R) ^ 2 +
          (eulerThreeShellTop R) ^ 2) := by
      apply Finset.sum_le_sum
      intro R _hR
      let a := eulerThreeShellLow R
      let b := eulerThreeShellMiddle R
      let c := eulerThreeShellTop R
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c),
        sq_nonneg (b - c)]
    _ = 3 * ((∑ R ∈ Finset.Ico H (2 * H),
        (eulerThreeShellLow R) ^ 2) +
      (∑ R ∈ Finset.Ico H (2 * H),
        (eulerThreeShellMiddle R) ^ 2) +
      (∑ R ∈ Finset.Ico H (2 * H),
        (eulerThreeShellTop R) ^ 2)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 9 * T := by linarith

#print axioms oaiPaired_squareShell_eq_originalMertensDifference
#print axioms oaiPaired_originalSharp_eq_movingPrimeFlux
#print axioms oaiPaired_originalSharp_eq_movingSiteFlux
#print axioms oaiPaired_newShell_above_newHalf
#print axioms oaiPaired_actualSharpEnergy_eq_nativeDyadicEnergy
#print axioms oaiPaired_actualSharpEnergy_eq_primeSampler
#print axioms oaiPaired_actualSharpMoment_consumer
#print axioms oaiPaired_threeUniformDyadicEnergy

end RHLean.Analysis
