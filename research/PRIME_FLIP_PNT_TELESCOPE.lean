import Mathlib
import RHLean.Analysis.PrimeSieveAbelIdentity
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.LargePrimeTerminalFlipLayers

/-!
# Euler-paired upper-prime response with PNT multiplicity replacement

This research layer formalizes the four-step route:

1. keep the post-root Euler response `1 - M(floor(x/q))` intact;
2. group primes only after that response has been formed, by the exact reciprocal
   quotient `d = floor(x/q)`;
3. replace only the prime multiplicity on each reciprocal band by the repository's
   Li/PNT mass;
4. retain the signed replacement error inside the assembled quadratic energy.

The prime-location error admits a second telescope.  The reciprocal-band
discrepancy is a forward difference of the classical prime-count discrepancy,
while the inherited response is `1-M(d)`.  Therefore the replacement error is
not an arbitrary Mertens-weighted interval sum: after Abel summation its interior
coefficients are the Möbius atoms themselves.

No PNT error estimate, RH hypothesis, or FinalStokes bound is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- The completed lower-prefix response copied by one fresh prime in quotient
band `d`.  This is half of the prime-comb signed update
`2 * (1 - M(d))`. -/
def primeFlipInheritedResponse (d : ℕ) : ℂ :=
  1 - mertensSummatory d

/-- Exact post-cutoff response, before any density replacement. -/
def primeFlipExactResponse (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    primeSievePrimeIndicator q * primeFlipInheritedResponse (x / q)

/-- Deterministic Li/PNT model obtained by replacing only prime multiplicity. -/
def primeFlipPNTResponse (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    primeSievePNTDensity q * primeFlipInheritedResponse (x / q)

/-- Signed error of the multiplicity replacement.  The inherited response is
not approximated. -/
def primeFlipPNTError (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    (primeSievePrimeIndicator q - primeSievePNTDensity q) *
      primeFlipInheritedResponse (x / q)

/-- Exact split: actual prime multiplicity = Li multiplicity + discrepancy. -/
theorem primeFlipExactResponse_eq_pnt_add_error
    (y x : ℕ) :
    primeFlipExactResponse y x =
      primeFlipPNTResponse y x + primeFlipPNTError y x := by
  classical
  unfold primeFlipExactResponse primeFlipPNTResponse primeFlipPNTError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Generic reciprocal-fibre reindexing for an arbitrary inherited response. -/
theorem sum_response_div_eq_reciprocalIntervals
    (y x : ℕ) (a : ℕ → ℂ) (b : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc y x, a q * b (x / q)) =
      ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ q ∈ primeSieveReciprocalInterval y x d, a q) * b d := by
  classical
  calc
    (∑ q ∈ Finset.Ioc y x, a q * b (x / q)) =
        ∑ q ∈ Finset.Ioc y x,
          ∑ d ∈ primeSieveQuotientSupport y x,
            if x / q = d then a q * b d else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hd := div_mem_primeSieveQuotientSupport_of_mem_Ioc hq
      simp [hd]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        ∑ q ∈ Finset.Ioc y x,
          if x / q = d then a q * b d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        ∑ q ∈ primeSieveQuotientFiber y x d, a q * b d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [primeSieveQuotientFiber, Finset.sum_filter]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ q ∈ primeSieveQuotientFiber y x d, a q) * b d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]
    _ = ∑ d ∈ primeSieveQuotientSupport y x,
        (∑ q ∈ primeSieveReciprocalInterval y x d, a q) * b d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := by
        have := (Finset.mem_Icc.mp hd).1
        omega
      rw [primeSieveQuotientFiber_eq_reciprocalInterval y x d hdpos]

/-- Exact response after grouping identical inherited prime actions. -/
theorem primeFlipExactResponse_eq_reciprocalPrimeCounts
    (y x : ℕ) :
    primeFlipExactResponse y x =
      ∑ d ∈ primeSieveQuotientSupport y x,
        primeSieveReciprocalPrimeCount y x d * primeFlipInheritedResponse d := by
  unfold primeFlipExactResponse
  rw [sum_response_div_eq_reciprocalIntervals
    y x primeSievePrimeIndicator primeFlipInheritedResponse]
  rfl

/-- PNT model after the same reciprocal-band grouping. -/
theorem primeFlipPNTResponse_eq_reciprocalLiMass
    (y x : ℕ) :
    primeFlipPNTResponse y x =
      ∑ d ∈ primeSieveQuotientSupport y x,
        primeSieveReciprocalLiMass y x d * primeFlipInheritedResponse d := by
  unfold primeFlipPNTResponse
  rw [sum_response_div_eq_reciprocalIntervals
    y x primeSievePNTDensity primeFlipInheritedResponse]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_primeSievePNTDensity_reciprocalInterval]

/-- The replacement error is exactly the reciprocal prime-count-minus-Li
discrepancy weighted by the inherited Euler response. -/
theorem primeFlipPNTError_eq_reciprocalDiscrepancy
    (y x : ℕ) :
    primeFlipPNTError y x =
      ∑ d ∈ primeSieveQuotientSupport y x,
        primeSieveReciprocalPrimeDiscrepancy y x d *
          primeFlipInheritedResponse d := by
  unfold primeFlipPNTError
  rw [sum_response_div_eq_reciprocalIntervals
    y x (fun q => primeSievePrimeIndicator q - primeSievePNTDensity q)
      primeFlipInheritedResponse]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_primeIndicator_sub_density_reciprocalInterval]

/-- Unweighted prime-indicator-minus-Li mass on one ordinary interval is the
difference of the classical prefix discrepancies. -/
theorem sum_primeIndicator_sub_density_Ioc_eq_discrepancy_sub
    {y x : ℕ} (hxy : y ≤ x) :
    (∑ q ∈ Finset.Ioc y x,
      (primeSievePrimeIndicator q - primeSievePNTDensity q)) =
      primeSievePrimeDiscrepancy x - primeSievePrimeDiscrepancy y := by
  have hprime :=
    Finset.sum_Ioc_consecutive
      (f := primeSievePrimeIndicator) (Nat.zero_le y) hxy
  have hli := sum_primeSievePNTDensity_Ioc hxy
  unfold primeSievePrimeDiscrepancy primeSievePrefixPrimeCount
  rw [Finset.sum_sub_distrib, hli]
  linear_combination -hprime

/-- First telescope of the replacement error.  The constant part of
`1-M(floor(x/q))` is the ordinary prime-count discrepancy increment; the
remaining part is exactly the already-formalized Mertens-weighted PNT error. -/
theorem primeFlipPNTError_eq_endpointDiscrepancy_sub_mertensPNTError
    {y x : ℕ} (hxy : y ≤ x) :
    primeFlipPNTError y x =
      (primeSievePrimeDiscrepancy x - primeSievePrimeDiscrepancy y) -
        primeSievePNTError y x := by
  classical
  unfold primeFlipPNTError primeFlipInheritedResponse primeSievePNTError
  calc
    (∑ q ∈ Finset.Ioc y x,
        (primeSievePrimeIndicator q - primeSievePNTDensity q) *
          (1 - mertensSummatory (x / q))) =
      (∑ q ∈ Finset.Ioc y x,
          (primeSievePrimeIndicator q - primeSievePNTDensity q)) -
        ∑ q ∈ Finset.Ioc y x,
          (primeSievePrimeIndicator q - primeSievePNTDensity q) *
            mertensSummatory (x / q) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = (primeSievePrimeDiscrepancy x - primeSievePrimeDiscrepancy y) -
        ∑ q ∈ Finset.Ioc y x,
          (primeSievePrimeIndicator q - primeSievePNTDensity q) *
            mertensSummatory (x / q) := by
      rw [sum_primeIndicator_sub_density_Ioc_eq_discrepancy_sub hxy]
    _ = (primeSievePrimeDiscrepancy x - primeSievePrimeDiscrepancy y) -
        primeSievePNTError y x := by
      rfl

/-- Second telescope: substitute the existing Abel identity.  The large
Mertens weights disappear from the interior and are replaced by individual
Möbius atoms in `primeSieveMoebiusDiscrepancySum`, plus one endpoint term. -/
theorem primeFlipPNTError_eq_endpoint_sub_moebiusDiscrepancy_add_boundary
    {y x : ℕ} (hxy : y ≤ x) :
    primeFlipPNTError y x =
      (primeSievePrimeDiscrepancy x - primeSievePrimeDiscrepancy y) -
        primeSieveMoebiusDiscrepancySum y x +
          primeSieveAbelBoundary y x := by
  rw [primeFlipPNTError_eq_endpointDiscrepancy_sub_mertensPNTError hxy,
    primeSievePNTError_eq_moebiusDiscrepancySum_sub_abelBoundary]
  ring

/-- Square-endpoint specialization of the atomized replacement error.

The endpoint discrepancy at `X=R^2-1` cancels the `d=1` Möbius term exactly.
What remains is an interior sum with coefficients `mu(d)` only, plus the
single lower endpoint boundary `(M(R-1)-1) * Delta(R)`. -/
theorem squareRoot_primeFlipPNTError_eq_moebiusAtoms
    (R : ℕ) (hR : 2 ≤ R) :
    primeFlipPNTError R (squareRootEndpoint R) =
      -(∑ d ∈ Finset.Icc 2 (R - 1),
          (((μ d : ℤ) : ℂ)) *
            primeSievePrimeDiscrepancy (squareRootEndpoint R / d)) +
        (mertensSummatory (R - 1) - 1) * primeSievePrimeDiscrepancy R := by
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    nlinarith
  rw [primeFlipPNTError_eq_endpoint_sub_moebiusDiscrepancy_add_boundary hRX]
  have htop :
      squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R (by omega)
  have hset :
      Finset.Icc 1 (R - 1) =
        ({1} : Finset ℕ) ∪ Finset.Icc 2 (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_singleton] at hd1
    subst d
    simp at hd2
  unfold primeSieveMoebiusDiscrepancySum primeSieveQuotientSupport
    primeSieveAbelBoundary
  rw [htop, hset, Finset.sum_union hdisj, Finset.sum_singleton]
  simp
  ring

/-- Real part of the exact response; all ingredients are real-valued, but this
interface matches the repository's scalar energy coordinates. -/
def primeFlipExactResponseReal (y x : ℕ) : ℝ :=
  (primeFlipExactResponse y x).re

def primeFlipPNTResponseReal (y x : ℕ) : ℝ :=
  (primeFlipPNTResponse y x).re

def primeFlipPNTErrorReal (y x : ℕ) : ℝ :=
  (primeFlipPNTError y x).re

theorem primeFlipExactResponseReal_eq_pnt_add_error
    (y x : ℕ) :
    primeFlipExactResponseReal y x =
      primeFlipPNTResponseReal y x + primeFlipPNTErrorReal y x := by
  unfold primeFlipExactResponseReal primeFlipPNTResponseReal primeFlipPNTErrorReal
  rw [primeFlipExactResponse_eq_pnt_add_error]
  rfl

/-- Quadratic energy of a root-stage scalar after the full late-prime update.
The factor two is the literal prime-comb sign reversal. -/
def primeFlipAssembledEnergy
    (base response diagonal : ℝ) : ℝ :=
  (base + 2 * response) ^ 2 - diagonal

/-- Signed energy change produced by replacing Li multiplicities by actual
prime multiplicities. -/
def primeFlipPNTReplacementSignedEffect
    (base model error : ℝ) : ℝ :=
  4 * (base + 2 * model) * error + 4 * error ^ 2

/-- Exact signed energy transfer.  No triangle inequality or separate squaring
of the actual/model responses is used. -/
theorem primeFlipAssembledEnergy_exact_transfer
    (base model error diagonal : ℝ) :
    primeFlipAssembledEnergy base (model + error) diagonal =
      primeFlipAssembledEnergy base model diagonal +
        primeFlipPNTReplacementSignedEffect base model error := by
  unfold primeFlipAssembledEnergy primeFlipPNTReplacementSignedEffect
  ring

/-- The exact prime response differs from the PNT model only through the signed
replacement effect. -/
theorem primeFlipAssembledEnergy_prime_eq_pnt_add_signedEffect
    (y x : ℕ) (base diagonal : ℝ) :
    primeFlipAssembledEnergy base (primeFlipExactResponseReal y x) diagonal =
      primeFlipAssembledEnergy base (primeFlipPNTResponseReal y x) diagonal +
        primeFlipPNTReplacementSignedEffect base
          (primeFlipPNTResponseReal y x) (primeFlipPNTErrorReal y x) := by
  rw [primeFlipExactResponseReal_eq_pnt_add_error]
  exact primeFlipAssembledEnergy_exact_transfer
    base (primeFlipPNTResponseReal y x) (primeFlipPNTErrorReal y x) diagonal

/-- If the actual prime-location error points against the assembled PNT model,
the favorable cross term is retained and the replacement costs only the error
square. -/
theorem primeFlipPNTReplacementSignedEffect_le_four_error_sq
    {base model error : ℝ}
    (hcross : (base + 2 * model) * error ≤ 0) :
    primeFlipPNTReplacementSignedEffect base model error ≤ 4 * error ^ 2 := by
  unfold primeFlipPNTReplacementSignedEffect
  nlinarith

/-- Unconditional fallback.  This deliberately records the cost of discarding
the cross-term sign, so later refinements can be measured against it. -/
theorem primeFlipPNTReplacementSignedEffect_le_model_sq_add_eight_error_sq
    (base model error : ℝ) :
    primeFlipPNTReplacementSignedEffect base model error ≤
      (base + 2 * model) ^ 2 + 8 * error ^ 2 := by
  unfold primeFlipPNTReplacementSignedEffect
  nlinarith [sq_nonneg ((base + 2 * model) - 2 * error)]

end RHLean.Analysis
