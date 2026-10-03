import Mathlib
import «research.VF_MID_ENDPOINT_TRIGGER_DICTIONARY»
import «research.VF_MID_ACTUAL_CRITICAL_OWNER_RECURSION»

/-!
# Physical actual-minus-Li forcing is an affine Mobius field

The solved exact-Li critical and reciprocal systems already provide the
homogeneous propagator.  This file isolates the new actual-prime forcing on
the frozen depth-two square-wheel carrier before taking any norm.

On that carrier every survivor is either a prime, with mu = -1, or a
rank-two semiprime, with mu = +1.  Therefore the Boolean prime indicator is

  1_Prime(n) = 1/2 - (1/2) mu(n).

Subtracting the exact singleton Li mass gives the pointwise forcing law

  1_Prime(n) - w_Li(n)
    = (1/2 - w_Li(n)) - (1/2) mu(n).

Thus after subtracting the deterministic affine target 1/2 - w_Li, the
physical actual-minus-Li forcing is exactly -mu/2.  The same identity survives
both the critical sqrt coordinate and the reciprocal coordinate, so those
two solved fantasy propagators see the same physical Mobius source.

No estimate, triangle inequality, probabilistic assumption, PNT error bound,
RH hypothesis, sorry, admit, or local axiom is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Actual-minus-Li forcing at one integer site, before any critical or
reciprocal weighting. -/
def vfMidActualLiForcingAtom (n : ℕ) : ℂ :=
  primeSievePrimeIndicator n - primeSievePNTDensity n

/-- Deterministic affine center of the physical forcing. -/
def vfMidActualLiAffineTarget (n : ℕ) : ℂ :=
  (1 / 2 : ℂ) - primeSievePNTDensity n

/-- Complex cast of the physical VF-minus-actual seat charge agrees with
VF fractional mass minus the exact complex prime indicator. -/
theorem vfMidOddSignedSeatCharge_cast_eq_vf_sub_indicator
    (R n : ℕ) :
    ((vfMidOddSignedSeatCharge R n : ℝ) : ℂ) =
      (vfMidOddFractionalPrimeSeatWeight R : ℂ) -
        primeSievePrimeIndicator n := by
  unfold vfMidOddSignedSeatCharge vfMidActualPrimeSeatMass
    primeSievePrimeIndicator
  by_cases hn : n.Prime <;> simp [hn]

/-- Exact forcing split through the physical VF seat field.

This is the identity
  actual - Li = -(VF - actual) + (VF - Li)
on one integer site. -/
theorem vfMidActualLiForcingAtom_eq_neg_vfCharge_add_vfLi
    (R n : ℕ) :
    vfMidActualLiForcingAtom n =
      -((vfMidOddSignedSeatCharge R n : ℝ) : ℂ) +
        ((vfMidOddFractionalPrimeSeatWeight R : ℂ) -
          primeSievePNTDensity n) := by
  unfold vfMidActualLiForcingAtom
  rw [vfMidOddSignedSeatCharge_cast_eq_vf_sub_indicator]
  ring

/-- On a frozen cubic-depth survivor carrier the Boolean prime process itself
is an affine Mobius field. -/
theorem primeSievePrimeIndicator_eq_half_sub_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    primeSievePrimeIndicator n =
      (1 / 2 : ℂ) -
        (1 / 2 : ℂ) * (((μ n : ℤ) : ℂ)) := by
  by_cases hp : n.Prime
  · rw [primeSievePrimeIndicator]
    simp only [hp, if_true]
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  · have hsplit :=
      vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
        (A := A) (R := R) (by omega : 2 ≤ R) hAR
    have hmem :
        n ∈ vfMidSquareWheelPrimes R ∪
          vfMidSquareBandPrefixCompositeSurvivors A R := by
      rw [← hsplit]
      exact hn
    have hnComp :
        n ∈ vfMidSquareBandPrefixCompositeSurvivors A R := by
      rcases Finset.mem_union.mp hmem with hnPrime | hnComp
      · exact (hp (Finset.mem_filter.mp hnPrime).2).elim
      · exact hnComp
    have hmu :=
      vfMidSquareBandPrefixComposite_moebius_eq_one_of_cube
        hA hAR hcube hnComp
    rw [primeSievePrimeIndicator]
    simp only [hp, if_false]
    rw [hmu]
    norm_num

/-- **Physical forcing decoder.**

On the exact frozen depth-two carrier, actual-minus-Li forcing is a
deterministic half-minus-Li target plus exactly minus one half of the physical
Mobius sign.  The intermediate VF fractional weight cancels completely. -/
theorem vfMidActualLiForcingAtom_eq_affineTarget_sub_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    vfMidActualLiForcingAtom n =
      vfMidActualLiAffineTarget n -
        (1 / 2 : ℂ) * (((μ n : ℤ) : ℂ)) := by
  unfold vfMidActualLiForcingAtom vfMidActualLiAffineTarget
  rw [primeSievePrimeIndicator_eq_half_sub_half_moebius_of_cube
    hA hAR hcube hn]
  ring

/-- After removing the deterministic target, the actual-minus-Li forcing is
literally the physical Mobius field with scale -1/2. -/
theorem vfMidActualLiForcingAtom_sub_target_eq_neg_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    vfMidActualLiForcingAtom n - vfMidActualLiAffineTarget n =
      -(1 / 2 : ℂ) * (((μ n : ℤ) : ℂ)) := by
  rw [vfMidActualLiForcingAtom_eq_affineTarget_sub_half_moebius_of_cube
    hA hAR hcube hn]
  ring

/-- The doubly centered physical forcing Gram is exactly one quarter of the
physical Mobius pair product. -/
theorem vfMidActualLiCenteredPair_eq_quarter_moebiusPair_of_cube
    {A R S n m : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hAS : A ≤ S)
    (hcubeR : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hcubeS : (S + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R)
    (hm : m ∈ vfMidSquarePrefixWheelSurvivors A S) :
    (vfMidActualLiForcingAtom n - vfMidActualLiAffineTarget n) *
        (vfMidActualLiForcingAtom m - vfMidActualLiAffineTarget m) =
      (1 / 4 : ℂ) * (((μ n : ℤ) : ℂ)) * (((μ m : ℤ) : ℂ)) := by
  rw [vfMidActualLiForcingAtom_sub_target_eq_neg_half_moebius_of_cube
      hA hAR hcubeR hn,
    vfMidActualLiForcingAtom_sub_target_eq_neg_half_moebius_of_cube
      hA hAS hcubeS hm]
  ring

/-- Critical-coordinate deterministic target. -/
def vfMidActualLiCriticalAffineTarget (n : ℕ) : ℂ :=
  vfMidActualLiAffineTarget n * criticalSqrtWeight n

/-- Critical-coordinate Mobius source atom. -/
def vfMidCriticalMobiusSourceAtom (n : ℕ) : ℂ :=
  (((μ n : ℤ) : ℂ)) * criticalSqrtWeight n

/-- The critical actual-minus-Li forcing has the same affine Mobius decoder. -/
theorem criticalCenteredPrimeFrequencyWeight_eq_target_sub_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    criticalCenteredPrimeFrequencyWeight n =
      vfMidActualLiCriticalAffineTarget n -
        (1 / 2 : ℂ) * vfMidCriticalMobiusSourceAtom n := by
  unfold criticalCenteredPrimeFrequencyWeight
    vfMidActualLiCriticalAffineTarget
    vfMidCriticalMobiusSourceAtom
    vfMidActualLiAffineTarget
  rw [primeSievePrimeIndicator_eq_half_sub_half_moebius_of_cube
    hA hAR hcube hn]
  ring

/-- Reciprocal-coordinate deterministic target. -/
def vfMidActualLiReciprocalAffineTarget (n : ℕ) : ℂ :=
  vfMidActualLiAffineTarget n * reciprocalWeight n

/-- Reciprocal-coordinate Mobius source atom. -/
def vfMidReciprocalMobiusSourceAtom (n : ℕ) : ℂ :=
  (((μ n : ℤ) : ℂ)) * reciprocalWeight n

/-- The reciprocal actual-minus-Li forcing has the identical affine Mobius
decoder.  Thus the critical and reciprocal solved fantasy propagators see the
same physical signed source, differing only by their known coordinate weight. -/
theorem reciprocalCenteredPrimeFrequencyWeight_eq_target_sub_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    reciprocalCenteredPrimeFrequencyWeight n =
      vfMidActualLiReciprocalAffineTarget n -
        (1 / 2 : ℂ) * vfMidReciprocalMobiusSourceAtom n := by
  unfold reciprocalCenteredPrimeFrequencyWeight
    vfMidActualLiReciprocalAffineTarget
    vfMidReciprocalMobiusSourceAtom
    vfMidActualLiAffineTarget
  rw [primeSievePrimeIndicator_eq_half_sub_half_moebius_of_cube
    hA hAR hcube hn]
  ring

/-- Fresh-prime Mobius sign reversal with no size hypothesis. -/
theorem moebius_mul_fresh_prime_eq_neg
    {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    μ (p * n) = -μ n := by
  have hcop : Nat.Coprime p n :=
    (hp.coprime_iff_not_dvd).2 hpn
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- **Fresh-prime transport law for the physical forcing.**
Whenever a fresh-prime child and its parent both lie on valid cubic-depth
physical carriers, the centered actual-minus-Li forcing reverses sign exactly.
This is the requested law F(T_p x) = -F(x), with no estimate. -/
theorem vfMidActualLiCenteredForcing_mul_freshPrime_eq_neg
    {A R S p n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hAS : A ≤ S)
    (hcubeR : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hcubeS : (S + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R)
    (hchild : p * n ∈ vfMidSquarePrefixWheelSurvivors A S) :
    vfMidActualLiForcingAtom (p * n) -
        vfMidActualLiAffineTarget (p * n) =
      -(vfMidActualLiForcingAtom n -
        vfMidActualLiAffineTarget n) := by
  rw [vfMidActualLiForcingAtom_sub_target_eq_neg_half_moebius_of_cube
      hA hAS hcubeS hchild,
    vfMidActualLiForcingAtom_sub_target_eq_neg_half_moebius_of_cube
      hA hAR hcubeR hn,
    moebius_mul_fresh_prime_eq_neg hp hpn]
  push_cast
  ring

/-- The critical centered source is exactly the Mobius source atom. -/
theorem criticalCenteredPrimeFrequencyWeight_sub_target_eq_neg_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    criticalCenteredPrimeFrequencyWeight n -
        vfMidActualLiCriticalAffineTarget n =
      -(1 / 2 : ℂ) * vfMidCriticalMobiusSourceAtom n := by
  rw [criticalCenteredPrimeFrequencyWeight_eq_target_sub_half_moebius_of_cube
    hA hAR hcube hn]
  ring

/-- **Critical fresh-prime transport.**
The already-solved critical coordinate sees a fresh prime as the exact
multiplier -criticalSqrtWeight(p). -/
theorem criticalCenteredPrimeFrequencyWeight_mul_freshPrime
    {A R S p n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hAS : A ≤ S)
    (hcubeR : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hcubeS : (S + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R)
    (hchild : p * n ∈ vfMidSquarePrefixWheelSurvivors A S) :
    criticalCenteredPrimeFrequencyWeight (p * n) -
        vfMidActualLiCriticalAffineTarget (p * n) =
      -criticalSqrtWeight p *
        (criticalCenteredPrimeFrequencyWeight n -
          vfMidActualLiCriticalAffineTarget n) := by
  rw [criticalCenteredPrimeFrequencyWeight_sub_target_eq_neg_half_moebius_of_cube
      hA hAS hcubeS hchild,
    criticalCenteredPrimeFrequencyWeight_sub_target_eq_neg_half_moebius_of_cube
      hA hAR hcubeR hn]
  unfold vfMidCriticalMobiusSourceAtom
  rw [moebius_mul_fresh_prime_eq_neg hp hpn,
    criticalSqrtWeight_mul]
  push_cast
  ring

/-- The reciprocal centered source is exactly the Mobius source atom. -/
theorem reciprocalCenteredPrimeFrequencyWeight_sub_target_eq_neg_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    reciprocalCenteredPrimeFrequencyWeight n -
        vfMidActualLiReciprocalAffineTarget n =
      -(1 / 2 : ℂ) * vfMidReciprocalMobiusSourceAtom n := by
  rw [reciprocalCenteredPrimeFrequencyWeight_eq_target_sub_half_moebius_of_cube
    hA hAR hcube hn]
  ring

/-- **Reciprocal fresh-prime transport.**
The solved reciprocal coordinate sees the same physical source with exact
multiplier -reciprocalWeight(p). -/
theorem reciprocalCenteredPrimeFrequencyWeight_mul_freshPrime
    {A R S p n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hAS : A ≤ S)
    (hcubeR : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hcubeS : (S + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R)
    (hchild : p * n ∈ vfMidSquarePrefixWheelSurvivors A S) :
    reciprocalCenteredPrimeFrequencyWeight (p * n) -
        vfMidActualLiReciprocalAffineTarget (p * n) =
      -reciprocalWeight p *
        (reciprocalCenteredPrimeFrequencyWeight n -
          vfMidActualLiReciprocalAffineTarget n) := by
  rw [reciprocalCenteredPrimeFrequencyWeight_sub_target_eq_neg_half_moebius_of_cube
      hA hAS hcubeS hchild,
    reciprocalCenteredPrimeFrequencyWeight_sub_target_eq_neg_half_moebius_of_cube
      hA hAR hcubeR hn]
  unfold vfMidReciprocalMobiusSourceAtom
  rw [moebius_mul_fresh_prime_eq_neg hp hpn,
    reciprocalWeight_mul]
  push_cast
  ring

/-- Unweighted actual-minus-Li forcing over one frozen survivor block. -/
def vfMidCubeActualLiForcingMass (A R : ℕ) : ℂ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
    vfMidActualLiForcingAtom n

/-- Deterministic affine target mass over the same carrier. -/
def vfMidCubeActualLiAffineTargetMass (A R : ℕ) : ℂ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
    vfMidActualLiAffineTarget n

/-- Complex signed Mobius mass over the same physical carrier. -/
def vfMidCubeSurvivorMobiusMassComplex (A R : ℕ) : ℂ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
    (((μ n : ℤ) : ℂ))

/-- Aggregate forcing decoder before any absolute value:
large actual and deterministic populations collapse to one signed Mobius
observable plus the explicit deterministic target. -/
theorem vfMidCubeActualLiForcingMass_eq_target_sub_half_moebius
    {A R : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3) :
    vfMidCubeActualLiForcingMass A R =
      vfMidCubeActualLiAffineTargetMass A R -
        (1 / 2 : ℂ) * vfMidCubeSurvivorMobiusMassComplex A R := by
  unfold vfMidCubeActualLiForcingMass
    vfMidCubeActualLiAffineTargetMass
    vfMidCubeSurvivorMobiusMassComplex
  calc
    (∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
      vfMidActualLiForcingAtom n) =
        ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
          (vfMidActualLiAffineTarget n -
            (1 / 2 : ℂ) * (((μ n : ℤ) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact vfMidActualLiForcingAtom_eq_affineTarget_sub_half_moebius_of_cube
        hA hAR hcube hn
    _ =
        (∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
          vfMidActualLiAffineTarget n) -
          (1 / 2 : ℂ) *
            (∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
              (((μ n : ℤ) : ℂ))) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

end RHLean.Analysis
