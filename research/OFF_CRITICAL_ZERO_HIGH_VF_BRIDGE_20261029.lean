import Mathlib
import RHLean.Analysis.CanonicalHighSectorBridge
import RHLean.Analysis.MertensEnergyRHForward
import «research.MERTENS_EXPONENT_STRIP_MAP»
import «research.VF_CANONICAL_SQRT_TWO»
import «research.VF_MID_925_FACTOR_THETA_SPECTRAL_WELD»

/-!
# Off-critical zero, canonical HIGH, and genuine-prime VF/theta coarsening

This module adds no RH hypothesis, no new uniform source estimate, no zero
residue assumption, and no source-independent stochastic assertion.

It provides three finite/conditional bridges:

1. An ACTUAL nontrivial zeta zero strictly right of 1/2 implies failure
   of the canonical HIGH local-energy criterion, by the existing
   low/high equivalence and internally proved Mertens-energy -> RH forward map.
2. Coarsening ANY genuine square-endpoint shortage is exact telescoping
   of its original endpoint potential. Applied to nativeTheta, this
   aggregates true prime-weighted blocks without claiming q*p is prime.
3. The canonical VF increment equals the original signed theta shortage
   (with the exact prime-position term) and equals the original signed
   native-owner charge plus descent remainder.

The analytic pole/residue/Mellin continuation theorems are intentionally
NOT claimed here. Their source-faithful conditions are recorded in the
adjacent research contract. No "sorry" or new axioms are used here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- A right-of-critical-line ZERO OF THE ACTUAL RIEMANN ZETA FUNCTION. -/
def OffCriticalRightZero (rho : ℂ) : Prop :=
  MertensExponent.NontrivialZetaZero rho ∧
    (1 : ℝ) / 2 < rho.re

/-- An off-critical zeta zero excludes EVERY fixed-gate canonical HIGH
uniform local-energy bound. This implication uses an internally proved
Mertens-energy-to-zero-free result and has no classical RH criterion argument. -/
theorem offCriticalRightZero_forces_highEnergyCriterion_failure
    (Lambda : ℝ) {rho : ℂ} (hzero : OffCriticalRightZero rho) :
    ¬ RHLean.Proof.CanonicalHighUniformLocalBoundedStatement Lambda := by
  intro hHigh
  have hTotal : SquarePrefixUniformLocalBoundedStatement :=
    (RHLean.Proof.canonicalHighUniformLocalBounded_iff_squarePrefixUniformLocalBounded_realized
      Lambda).mp hHigh
  have hMertens : MertensEnergyBoundedStatement :=
    squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded.mp hTotal
  have hnotOne : rho ≠ 1 := by
    intro heq
    have hlt : rho.re < (1 : ℝ) := hzero.1.2.2
    rw [heq] at hlt
    norm_num at hlt
  exact
    (riemannZeta_ne_zero_of_half_lt_re hMertens hzero.2 hnotOne)
      hzero.1.1

/-- The same hypothetical zero forbids a smaller global Mertens power
envelope. The exponent inequality is strict, so no assertion is made at
the boundary exponent. -/
theorem offCriticalRightZero_forces_mertensPower_failure
    {rho : ℂ} (hzero : OffCriticalRightZero rho) {a : ℝ}
    (ha : 0 ≤ a) (hsmall : a < rho.re) :
    ¬ MertensExponent.MertensPowerBound a := by
  intro hPower
  exact (not_le_of_gt hsmall)
    (MertensExponent.zero_re_le_of_powerBound ha hPower hzero.1)

/-! ## Exact finite square-scale coarsening on genuine arithmetic endpoints -/

/-- The deficit of a general integer-endpoint cumulative function from
the square main term. For f = nativeTheta this is x - theta(x)
restricted to integer-square endpoints. -/
def squareEndpointPotential (f : ℕ → ℝ) (R : ℕ) : ℝ :=
  (R : ℝ) ^ 2 - f (R ^ 2)

/-- Genuine square-block shortage, as one FIRST DIFFERENCE of the potential. -/
def squareEndpointShortage (f : ℕ → ℝ) (R : ℕ) : ℝ :=
  squareEndpointPotential f (R + 1) - squareEndpointPotential f R

/-- Arithmetic coarsening averages q CONSECUTIVE original square blocks;
it does not rescale the individual prime labels. -/
def squareScaleCoarsen (q : ℕ) (A : ℕ → ℝ) (R : ℕ) : ℝ :=
  (∑ j ∈ Finset.Ico (q * R) (q * (R + 1)), A j) / (q : ℝ)

/-- No interior endpoint leakage: every finite square-block difference
telescopes exactly on the actual fine-block index set. -/
theorem squareScaleCoarsen_endpointShortage
    (f : ℕ → ℝ) (q R : ℕ) :
    squareScaleCoarsen q (squareEndpointShortage f) R =
      (squareEndpointPotential f (q * (R + 1)) -
        squareEndpointPotential f (q * R)) / (q : ℝ) := by
  have hle : q * R ≤ q * (R + 1) :=
    Nat.mul_le_mul_left q (Nat.le_succ R)
  unfold squareScaleCoarsen squareEndpointShortage
  rw [Finset.sum_Ico_sub (squareEndpointPotential f) hle]

/-- The special case f = nativeTheta is the true square-block shortage,
not a floor-Li, VF-event, or modeled prime sequence. -/
def actualThetaSquareShortage (R : ℕ) : ℝ :=
  squareEndpointShortage nativeTheta R

/-- Physical first-owner theta forcing agrees with that actual endpoint
shortage. The original factor-wheel/FTA bridge supplies this identification. -/
theorem actualThetaSquareShortage_eq_physicalFactorSource
    (R : ℕ) (hR : 5 ≤ R) :
    actualThetaSquareShortage R = vf925FactorThetaForcing R := by
  unfold actualThetaSquareShortage squareEndpointShortage squareEndpointPotential
    vf925FactorThetaForcing
  rw [vf925FactorRangeThetaMass_eq_thetaDifference R hR]
  push_cast
  ring

/-- The exact source-native multi-block coarsening formula, valid with no
prime-distribution assumptions and no interior clipping. -/
theorem actualThetaSquareShortage_coarsen_eq_endpoints
    (q R : ℕ) :
    squareScaleCoarsen q actualThetaSquareShortage R =
      (squareEndpointPotential nativeTheta (q * (R + 1)) -
        squareEndpointPotential nativeTheta (q * R)) / (q : ℝ) := by
  exact squareScaleCoarsen_endpointShortage nativeTheta q R

/-! ## The ACTUAL prime/VF escape channel -/

/-- Exact one-block prime-minus-canonical-VF step: the theta shortage enters
with the negative sign, and the prime-position correction is retained. -/
theorem canonicalVF_step_eq_thetaShortage_and_position
    (R : ℕ) (hR : 5 ≤ R) :
    vfCanonicalSquareDefect (R + 1) - vfCanonicalSquareDefect R =
      -(vf925FactorThetaForcing R / Real.log (vfMidBandMidpoint R)) +
        vfMidDirectLogPositionError R := by
  calc
    vfCanonicalSquareDefect (R + 1) - vfCanonicalSquareDefect R =
        vfMidDirectBandError R := by
          rw [vfCanonicalSquareDefect_succ R (by omega : 2 ≤ R)]
          ring
    _ = vfMidDirectThetaBandError R / Real.log (vfMidBandMidpoint R) +
        vfMidDirectLogPositionError R :=
          vfMidDirectBandError_eq_theta_add_position R
    _ = -(vf925FactorThetaForcing R / Real.log (vfMidBandMidpoint R)) +
        vfMidDirectLogPositionError R := by
          rw [vf925FactorThetaForcing_eq_neg_thetaBandError R hR]
          ring

/-- All WITHIN-BLOCK position corrections cancel once the source is expressed
in the original signed native-owner coordinates. No new source payment is
smuggled into this exact finite identity. -/
theorem canonicalVF_step_eq_signed_nativeOwner_and_descent
    (R : ℕ) (hR : 7 ≤ R) :
    vfCanonicalSquareDefect (R + 1) - vfCanonicalSquareDefect R =
      -(vfMidRecursiveAggregateNativeCharge R +
        vfMidNativeDescentRemainder R) := by
  calc
    vfCanonicalSquareDefect (R + 1) - vfCanonicalSquareDefect R =
        vfMidDirectBandError R := by
          rw [vfCanonicalSquareDefect_succ R (by omega : 2 ≤ R)]
          ring
    _ = -(vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R) :=
        vfMidDirectBandError_eq_neg_native_add_remainder R hR

end RHLean.Analysis
