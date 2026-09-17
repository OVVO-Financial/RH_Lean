import Mathlib
import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelRawConductorWeight
import «research.GLOBAL_RETURNED_CORE_STOKES_ARBITRARY_CLOCK_WHEEL»

/-!
# Natural square-sensitive Stokes torus

The general Stokes wheel uses an intentionally oversized common modulus so that
its algebraic identification is valid already from `R >= 2`.  The analytic RH
consumer only starts at `R >= 56`.  In that regime the complete square-sensitive
raw period already lies strictly beyond the entire physical clock.

Hence the quantitative frame may use the natural modulus

  P_R = product_{p <= sqrt X_R} p^2

itself.  This removes the artificial extra torus factor and puts the raw
conductor coefficient exactly on the natural modulus required by the compiled
product-weight formula.

Everything in this file is still identity/arithmetic certification only.  No
frame estimate or norm inequality is introduced.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

attribute [local instance] Classical.propDecidable

/-- The Stokes square-sensitive period is the square of the product of all
primes through the physical square-root cutoff. -/
theorem lowOwnerStokesSquareSensitivePeriod_eq_primeProductUpTo_sq
    (R : ℕ) :
    lowOwnerStokesSquareSensitivePeriod R =
      (primeProductUpTo (Nat.sqrt (squareRootEndpoint R))) ^ 2 := by
  unfold lowOwnerStokesSquareSensitivePeriod lowOwnerStokesWheelPrimes
    primeProductUpTo
  exact Finset.prod_pow
    (primesUpTo (Nat.sqrt (squareRootEndpoint R))) 2 id

/-- The RH-consumer regime has square-root cutoff at least five. -/
theorem five_le_lowOwnerStokesWheelCutoff
    {R : ℕ} (hR : 56 ≤ R) :
    5 ≤ Nat.sqrt (squareRootEndpoint R) := by
  apply Nat.le_sqrt.mpr
  unfold squareRootEndpoint
  apply Nat.le_sub_of_add_le
  nlinarith

/-- In the RH-consumer regime, the natural square-sensitive period already
contains the complete physical Stokes clock. -/
theorem squareRootEndpoint_lt_lowOwnerStokesSquareSensitivePeriod
    {R : ℕ} (hR : 56 ≤ R) :
    squareRootEndpoint R < lowOwnerStokesSquareSensitivePeriod R := by
  let y := Nat.sqrt (squareRootEndpoint R)
  have hy : 5 ≤ y := by
    dsimp [y]
    exact five_le_lowOwnerStokesWheelCutoff hR
  have hprod := lt_primeProductUpTo y hy
  have hprodSucc : y + 1 ≤ primeProductUpTo y := by omega
  have hsqrt : squareRootEndpoint R < (y + 1) ^ 2 := by
    dsimp [y]
    exact Nat.lt_succ_sqrt' (squareRootEndpoint R)
  rw [lowOwnerStokesSquareSensitivePeriod_eq_primeProductUpTo_sq]
  dsimp [y] at hprodSucc hsqrt ⊢
  exact hsqrt.trans_le (Nat.pow_le_pow_left hprodSucc 2)

/-- The double-finset physical period is exactly the generic raw natural modulus
used by the conductor-weight calculus. -/
theorem lowOwnerStokesSquareSensitivePeriod_eq_rawNaturalModulus
    (R : ℕ) :
    lowOwnerStokesSquareSensitivePeriod R =
      primeWheelRawNaturalModulus (lowOwnerStokesWheelPrimes R) := by
  unfold lowOwnerStokesSquareSensitivePeriod primeWheelRawNaturalModulus
  exact
    (Finset.prod_coe_sort
      (lowOwnerStokesWheelPrimes R) (fun p : ℕ => p ^ 2)).symm

/-- The natural-period corrected wheel used by the quantitative Stokes frame. -/
def lowOwnerStokesNaturalWheelSystem
    (R : ℕ) (hR : 56 ≤ R) : PrimeWheelFiniteSystem where
  lower := 0
  upper := squareRootEndpoint R
  modulus := lowOwnerStokesSquareSensitivePeriod R
  lower_lt_upper := squareRootEndpoint_pos_of_two_le (by omega)
  modulus_pos := lowOwnerStokesSquareSensitivePeriod_pos R
  upper_lt_modulus :=
    squareRootEndpoint_lt_lowOwnerStokesSquareSensitivePeriod hR
  primeCoordinates := lowOwnerStokesWheelPrimes R
  primeCoordinates_prime := by
    intro p hp
    exact lowOwnerStokesWheelPrimes_prime hp

/-- Its torus modulus is definitionally the physical square-sensitive period. -/
@[simp] theorem lowOwnerStokesNaturalWheelSystem_modulus
    (R : ℕ) (hR : 56 ≤ R) :
    (lowOwnerStokesNaturalWheelSystem R hR).modulus =
      lowOwnerStokesSquareSensitivePeriod R := rfl

/-- The natural Stokes torus is exactly the generic raw natural modulus. -/
theorem lowOwnerStokesNaturalWheelSystem_modulus_eq_rawNaturalModulus
    (R : ℕ) (hR : 56 ≤ R) :
    (lowOwnerStokesNaturalWheelSystem R hR).modulus =
      primeWheelRawNaturalModulus (lowOwnerStokesWheelPrimes R) := by
  rw [lowOwnerStokesNaturalWheelSystem_modulus,
    lowOwnerStokesSquareSensitivePeriod_eq_rawNaturalModulus]

/-- Every local square period divides the natural Stokes torus modulus. -/
theorem prime_sq_dvd_lowOwnerStokesNaturalWheelModulus
    {R p : ℕ} (hR : 56 ≤ R)
    (hp : p ∈ lowOwnerStokesWheelPrimes R) :
    p ^ 2 ∣ (lowOwnerStokesNaturalWheelSystem R hR).modulus := by
  change p ^ 2 ∣ lowOwnerStokesSquareSensitivePeriod R
  exact prime_sq_dvd_lowOwnerStokesSquareSensitivePeriod hp

/-- Exact arithmetic certificate on the natural-period wheel. -/
def lowOwnerStokesNaturalWheelArithmeticCertificate
    (R : ℕ) (hR : 56 ≤ R) :
    (lowOwnerStokesNaturalWheelSystem R hR).ArithmeticCertificate where
  corrected_eq_moebius := by
    intro n hnpos hnupper
    change correctedPrimeWheelSite
      (lowOwnerStokesWheelPrimes R) (squareRootEndpoint R) n = μ n
    exact correctedPrimeWheelSite_eq_moebius
      (lowOwnerStokesWheelPrimes R)
      (fun p hp => lowOwnerStokesWheelPrimes_prime hp)
      (lowOwnerStokesWheelPrimes_sqrtCoverage R)
      hnpos hnupper

/-- The natural wheel uses the same physical prefix interval `(0,x] = [1,x]`. -/
theorem lowOwnerStokesNaturalWheel_prefixInterval_eq_Icc
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ) :
    (lowOwnerStokesNaturalWheelSystem R hR).prefixInterval x =
      Finset.Icc 1 x := by
  ext n
  simp [PrimeWheelFiniteSystem.prefixInterval,
    lowOwnerStokesNaturalWheelSystem]
  omega

/-- Every physical prefix is exactly Mertens on the natural-period wheel. -/
theorem lowOwnerStokesNaturalWheel_residual_eq_mertensSummatoryInt
    {R x : ℕ} (hR : 56 ≤ R)
    (hx : x ≤ squareRootEndpoint R) :
    (lowOwnerStokesNaturalWheelSystem R hR).residual x =
      mertensSummatoryInt x := by
  rw [(lowOwnerStokesNaturalWheelSystem R hR).residual_eq_moebius_sum
    (lowOwnerStokesNaturalWheelArithmeticCertificate R hR) hx]
  rw [lowOwnerStokesNaturalWheel_prefixInterval_eq_Icc,
    ← mertensSummatoryInt_eq_Icc]

/-- Every positive physical prefix is the same exact corrected spectral prefix
on the natural square-sensitive torus. -/
theorem lowOwnerStokesNaturalWheel_spectralPrefix_eq_mertensSummatory
    {R x : ℕ} (hR : 56 ≤ R)
    (hxpos : 0 < x) (hx : x ≤ squareRootEndpoint R) :
    (lowOwnerStokesNaturalWheelSystem R hR).spectralPrefix x =
      mertensSummatory x := by
  calc
    (lowOwnerStokesNaturalWheelSystem R hR).spectralPrefix x =
        (((lowOwnerStokesNaturalWheelSystem R hR).residual x : ℤ) : ℂ) := by
      exact
        (lowOwnerStokesNaturalWheelSystem R hR).spectralPrefix_eq_residual
          (lowOwnerStokesNaturalWheelSystem R hR).canonicalTorusRealizationCertificate
          hxpos hx
    _ = ((mertensSummatoryInt x : ℤ) : ℂ) := by
      rw [lowOwnerStokesNaturalWheel_residual_eq_mertensSummatoryInt hR hx]
    _ = mertensSummatory x := mertensSummatoryInt_cast x

/-- The exact normalized raw conductor coefficient on the natural Stokes torus
is therefore the compiled independent product of local conductor weights. -/
theorem lowOwnerStokesRawConductorArithmeticCoefficient_normalized_eq_neg_prod
    (R : ℕ) (hR : 56 ≤ R)
    (c : PrimeWheelRawExpansionPoint (lowOwnerStokesWheelPrimes R)) :
    primeWheelRawConductorArithmeticCoefficient
        (lowOwnerStokesWheelPrimes R)
        (lowOwnerStokesNaturalWheelSystem R hR).modulus
        (primeWheelRawExpansionDivisor (lowOwnerStokesWheelPrimes R) c) *
        ((((lowOwnerStokesNaturalWheelSystem R hR).modulus : ℕ) : ℂ)⁻¹) =
      -∏ p : {p // p ∈ lowOwnerStokesWheelPrimes R},
        ((localPrimeRawSignedConductorWeight p.val (c p) : ℝ) : ℂ) := by
  rw [lowOwnerStokesNaturalWheelSystem_modulus_eq_rawNaturalModulus]
  exact
    primeWheelRawConductorArithmeticCoefficient_normalized_eq_neg_prod
      (lowOwnerStokesWheelPrimes R)
      (fun p hp => lowOwnerStokesWheelPrimes_prime hp)
      c

end RHLean.Proof
