import Mathlib
import RHLean.Analysis.CorrectedConductorHighSectorCutoffError
import RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse

/-!
# Large expansion-point form of the signed high core

The eighth-root cutoff error is already controlled.  The remaining hard object
is the single signed collapsed core.  This file changes coordinates once more,
but still before any norm: its large raw boundary part is collapsed from
boundary divisors to the genuine ternary prime-comb expansion points.

After the common torus normalization, the factor `Q / D_e` cancels against
`Q^{-1}`.  Thus each large raw expansion point appears as

`- w_e * B_{D_e}(0;L,x) / D_e`,

where the local expansion weights are exactly `[1,-2,1]`.  This is the
multiplicative second-difference stencil.  The conductor-one bulk and fully
collapsed smooth correction remain in the same signed core and are not normed
separately.

No estimate is asserted here; the purpose is to put the already-isolated hard
Gram into the coordinates in which fresh-prime scale descent can act.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Generic filtered version of the exact raw expansion-point collapse.  The
cutoff is placed on the *expansion divisor* after the complete upper-Moebius
reindexing. -/
theorem sum_rawUpperMobiusTransform_mul_filter_gt_eq_expansion_filter_gt
    (S : Finset ℕ) (N R : ℕ) (hN : N ≠ 0)
    (hdiv : ∀ e : PrimeWheelRawExpansionPoint S,
      primeWheelRawExpansionDivisor S e ∣ N)
    (B : ℕ → ℂ) :
    (∑ d ∈ N.divisors,
      if R < d then
        primeWheelRawUpperMobiusTransform S N d * B d
      else 0) =
      -∑ e : PrimeWheelRawExpansionPoint S,
        if R < primeWheelRawExpansionDivisor S e then
          primeWheelRawExpansionWeight S e *
            (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
            B (primeWheelRawExpansionDivisor S e)
        else 0 := by
  classical
  have hcollapse :=
    sum_rawUpperMobiusTransform_mul_eq_exactExpansionPairing
      S N hN hdiv (fun d => if R < d then B d else 0)
  calc
    (∑ d ∈ N.divisors,
      if R < d then
        primeWheelRawUpperMobiusTransform S N d * B d
      else 0) =
        ∑ d ∈ N.divisors,
          primeWheelRawUpperMobiusTransform S N d *
            (if R < d then B d else 0) := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hRd : R < d <;> simp [hRd]
    _ = -∑ e : PrimeWheelRawExpansionPoint S,
        primeWheelRawExpansionWeight S e *
          (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
          (if R < primeWheelRawExpansionDivisor S e then
            B (primeWheelRawExpansionDivisor S e)
          else 0) := hcollapse
    _ = -∑ e : PrimeWheelRawExpansionPoint S,
        if R < primeWheelRawExpansionDivisor S e then
          primeWheelRawExpansionWeight S e *
            (((N / primeWheelRawExpansionDivisor S e : ℕ) : ℂ)) *
            B (primeWheelRawExpansionDivisor S e)
        else 0 := by
          congr 1
          apply Fintype.sum_congr
          intro e
          by_cases hRe : R < primeWheelRawExpansionDivisor S e <;>
            simp [hRe]

/-- Large raw boundary pairing written directly on ternary expansion points. -/
def primorialRawLargeExpansionBoundaryPairing
    (k x R : ℕ) : ℂ :=
  -∑ e : PrimeWheelRawExpansionPoint (primorialWheelPrimes k),
    if R < primeWheelRawExpansionDivisor (primorialWheelPrimes k) e then
      primeWheelRawExpansionWeight (primorialWheelPrimes k) e *
        (((((primorialMinimalWheelSystem k).modulus /
          primeWheelRawExpansionDivisor (primorialWheelPrimes k) e : ℕ) : ℂ))) *
        (((divisorIntervalBoundary
          (primeWheelRawExpansionDivisor (primorialWheelPrimes k) e) 0
          (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))
    else 0

/-- The large divisor-indexed raw boundary piece is exactly the large
expansion-point pairing. -/
theorem primorialRawLargeCollapsedBoundaryPairing_eq_expansion
    (k x R : ℕ) (hk : 2 ≤ k) :
    primorialRawLargeCollapsedBoundaryPairing k x R =
      primorialRawLargeExpansionBoundaryPairing k x R := by
  unfold primorialRawLargeCollapsedBoundaryPairing
    primorialRawLargeExpansionBoundaryPairing
  exact sum_rawUpperMobiusTransform_mul_filter_gt_eq_expansion_filter_gt
    (primorialWheelPrimes k)
    (primorialMinimalWheelSystem k).modulus R
    (Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos)
    (fun e => primorialRawExpansionDivisor_dvd_minimalModulus k hk e)
    (fun d => (((divisorIntervalBoundary d 0
      (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)))

/-- Normalized unshifted divisor-boundary sawtooth.  The next analytic stage
acts on this bounded endpoint discrepancy rather than on conductor packets. -/
def primorialRawBoundarySawtooth
    (k x d : ℕ) : ℂ :=
  ((d : ℂ)⁻¹) *
    (((divisorIntervalBoundary d 0
      (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))

private theorem inv_natCast_mul_natDiv_cast_eq_inv_natCast
    (N d : ℕ) (hN : 0 < N) (hdvd : d ∣ N) :
    ((N : ℂ)⁻¹) * (((N / d : ℕ) : ℂ)) = ((d : ℂ)⁻¹) := by
  have hNne : N ≠ 0 := Nat.ne_of_gt hN
  have hdne : d ≠ 0 := by
    intro hd0
    subst d
    have : N = 0 := by simpa using hdvd
    exact hNne this
  have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdvd
  have hNneC : (N : ℂ) ≠ 0 := by exact_mod_cast hNne
  have hdneC : (d : ℂ) ≠ 0 := by exact_mod_cast hdne
  field_simp [hNneC, hdneC]
  exact_mod_cast hmul

/-- Large normalized raw expansion pairing.  The torus modulus has disappeared
from every summand; only the expansion weight and normalized boundary remain. -/
def primorialNormalizedRawLargeExpansionPairing
    (k x R : ℕ) : ℂ :=
  -∑ e : PrimeWheelRawExpansionPoint (primorialWheelPrimes k),
    if R < primeWheelRawExpansionDivisor (primorialWheelPrimes k) e then
      primeWheelRawExpansionWeight (primorialWheelPrimes k) e *
        primorialRawBoundarySawtooth k x
          (primeWheelRawExpansionDivisor (primorialWheelPrimes k) e)
    else 0

/-- Exact cancellation of the ambient torus normalization in the large raw
expansion family. -/
theorem normalized_primorialRawLargeCollapsedBoundaryPairing_eq_expansion
    (k x R : ℕ) (hk : 2 ≤ k) :
    (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        primorialRawLargeCollapsedBoundaryPairing k x R =
      primorialNormalizedRawLargeExpansionPairing k x R := by
  rw [primorialRawLargeCollapsedBoundaryPairing_eq_expansion k x R hk]
  unfold primorialRawLargeExpansionBoundaryPairing
    primorialNormalizedRawLargeExpansionPairing
  rw [mul_neg, Finset.mul_sum]
  congr 1
  apply Fintype.sum_congr
  intro e
  by_cases hRe : R < primeWheelRawExpansionDivisor (primorialWheelPrimes k) e
  · simp only [hRe, if_true]
    let D := primeWheelRawExpansionDivisor (primorialWheelPrimes k) e
    have hDvd : D ∣ (primorialMinimalWheelSystem k).modulus :=
      primorialRawExpansionDivisor_dvd_minimalModulus k hk e
    have hcancel := inv_natCast_mul_natDiv_cast_eq_inv_natCast
      (primorialMinimalWheelSystem k).modulus D
      (primorialMinimalWheelSystem k).modulus_pos hDvd
    unfold primorialRawBoundarySawtooth
    change
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
          (primeWheelRawExpansionWeight (primorialWheelPrimes k) e *
            (((((primorialMinimalWheelSystem k).modulus / D : ℕ) : ℂ))) *
            (((divisorIntervalBoundary D 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))) =
        primeWheelRawExpansionWeight (primorialWheelPrimes k) e *
          ((D : ℂ)⁻¹ *
            (((divisorIntervalBoundary D 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)))
    calc
      _ = primeWheelRawExpansionWeight (primorialWheelPrimes k) e *
          ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
            (((((primorialMinimalWheelSystem k).modulus / D : ℕ) : ℂ))) *
            (((divisorIntervalBoundary D 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))) := by ring
      _ = primeWheelRawExpansionWeight (primorialWheelPrimes k) e *
          ((D : ℂ)⁻¹ *
            (((divisorIntervalBoundary D 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))) := by
            rw [hcancel]
  · simp [hRe]

/-- The high collapsed core with its large raw part now expressed as a genuine
expansion-point sum.  The raw bulk and collapsed smooth correction remain signed
with it. -/
def primorialHighExpansionCore
    (k x R : ℕ) : ℂ :=
  primorialNormalizedRawLargeExpansionPairing k x R +
    (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
      primorialRawRetainedBulk k x -
    2 * ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
      (((primorialSmoothCollapsedBoundaryBulk k x : ℤ) : ℂ)))

/-- Exact coordinate change from the collapsed high core to the normalized
large expansion core. -/
theorem primorialHighCollapsedCore_eq_expansionCore
    (k x R : ℕ) (hk : 2 ≤ k) :
    primorialHighCollapsedCore k x R =
      primorialHighExpansionCore k x R := by
  unfold primorialHighCollapsedCore primorialHighExpansionCore
  rw [← normalized_primorialRawLargeCollapsedBoundaryPairing_eq_expansion
    k x R hk]
  ring

/-- Multiplicative second difference attached to one fresh prime scale. -/
def rawMultiplicativeSecondDifference
    (p : ℕ) (f : ℕ → ℂ) (d : ℕ) : ℂ :=
  f d - 2 * f (d * p) + f (d * p ^ 2)

/-- The prime-comb local expansion weights are literally the second-difference
stencil `[1,-2,1]`. -/
theorem rawMultiplicativeSecondDifference_eq_fin3_weighted_sum
    (p : ℕ) (f : ℕ → ℂ) (d : ℕ) :
    rawMultiplicativeSecondDifference p f d =
      ∑ j : Fin 3,
        (((localPrimeCombExpansionWeight j : ℤ) : ℂ)) *
          f (d * p ^ j.val) := by
  have hfin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    native_decide
  rw [hfin]
  simp [rawMultiplicativeSecondDifference,
    localPrimeCombExpansionWeight]
  ring

end RHLean.Analysis
