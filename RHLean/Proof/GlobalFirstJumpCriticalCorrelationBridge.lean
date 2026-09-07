import Mathlib
import RHLean.Analysis.BlockCovarianceRefinement
import RHLean.Proof.GlobalFirstJumpCofactorCompression
import RHLean.Proof.CanonicalRoughCriticalCorrelationContraction
import RHLean.Proof.PrimeCombReciprocalBandCancellation
import RHLean.Proof.SquareRootLowPrimeMatchedCoreMertensObstruction

/-!
# Critical reciprocal-correlation bridge for the recombined defect

The first-jump-only norm target is too strong.  After recombination, the exact
endpoint object is `lowWheelCanonicalDefectLedger R`.  The canonical rough
correlation already differs from this defect by only the single root Mobius
atom, while its reciprocal prefixes are exactly the coordinate on which the
fresh-prime Euler factor `1 - 1/p` acts.

This file makes that reduction quantitative.  A uniform reciprocal-prefix bound
of size `(log R + 1) / R` implies the desired root-scale `R (log R + 1)` bound on
the recombined canonical defect.  No first-jump-prime or cofactor-column norm is
inserted in the argument.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- The canonical defect is the lower Mertens value minus the square endpoint
Mertens value. -/
theorem canonicalDefectLedger_eq_mertens_sub_squareRootEndpoint
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalDefectLedger R =
      mertensSummatory R - mertensSummatory (squareRootEndpoint R) := by
  have hdown := squarePrefixMertens_eq_mertens_sub_canonicalDowncross R hR
  have hend := squarePrefixMertens_pred_eq_mertens_squareRootEndpoint R (by omega)
  rw [hend] at hdown
  rw [lowWheelCanonicalDefectLedger_eq_downcrossLedger]
  linear_combination hdown

/-- **Defect/correlation bridge.**  The RH-critical canonical rough correlation
misses the recombined endpoint defect by exactly one Mobius atom at the root. -/
theorem canonicalDefectLedger_eq_roughCorrelation_add_rootAtom
    (R : ℕ) (hR : 3 ≤ R) :
    lowWheelCanonicalDefectLedger R =
      squareRootCanonicalRoughCorrelation R + canonicalMoebiusWeight R := by
  rw [canonicalDefectLedger_eq_mertens_sub_squareRootEndpoint R hR,
    squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R (by omega)]
  have hsucc := RHLean.Analysis.mertensSummatory_succ (R - 1)
  have hpred : R - 1 + 1 = R := by omega
  rw [hpred] at hsucc
  rw [hsucc]
  unfold canonicalMoebiusWeight
  ring

/-- The reciprocal-prefix scale naturally matched to an `R log R` endpoint
after the exact Abel return.  This is the coordinate on which the repository's
fresh-prime Euler contraction already acts. -/
def CriticalReciprocalPrefixRootBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ∀ k ≤ squareRootEndpoint R,
        ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ ≤
          C * (Real.log (R : ℝ) + 1) / (R : ℝ)

/-- A critical reciprocal-prefix bound gives the corresponding `R log R` bound
on the uncentered canonical rough correlation. -/
theorem roughCorrelationLogBound_of_criticalReciprocalPrefixRootBound
    (hprefix : CriticalReciprocalPrefixRootBound) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 3 ≤ R →
        ‖squareRootCanonicalRoughCorrelation R‖ ≤
          C * (R : ℝ) * (Real.log (R : ℝ) + 1) := by
  rcases hprefix with ⟨C, hC, hprefix⟩
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro R hR
  let L : ℝ := Real.log (R : ℝ) + 1
  let A : ℝ := C * L / (R : ℝ)
  have hA : ∀ k ≤ squareRootEndpoint R,
      ‖squareRootCanonicalRoughCorrelationReciprocalPrefix R k‖ ≤ A := by
    intro k hk
    simpa [A, L] using hprefix R hR k hk
  have habel :=
    squareRootCanonicalRoughCorrelation_norm_le_two_endpoint_mul R A hA
  have hRpos : 0 < (R : ℝ) := by positivity
  have hR0 : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  have hlog : 0 ≤ Real.log (R : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ R by omega)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    linarith
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg hC hL0) hRpos.le
  have hXnat : squareRootEndpoint R ≤ R ^ 2 := by
    unfold squareRootEndpoint
    omega
  have hX : (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hXnat
  calc
    ‖squareRootCanonicalRoughCorrelation R‖ ≤
        2 * (squareRootEndpoint R : ℝ) * A := habel
    _ ≤ 2 * ((R : ℝ) ^ 2) * A := by
      have h2 : 2 * (squareRootEndpoint R : ℝ) ≤ 2 * ((R : ℝ) ^ 2) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right h2 hA0
    _ = (2 * C) * (R : ℝ) * L := by
      dsimp [A]
      field_simp [hR0]
      ring
    _ = (2 * C) * (R : ℝ) * (Real.log (R : ℝ) + 1) := by rfl

/-- **Concrete closure criterion.**  Control the exact reciprocal correlation
prefixes at their native `log R / R` scale, and the recombined dense-plus-first-
jump endpoint satisfies the desired `R log R` bound.  The extra `+1` in the
constant pays only for the single root Mobius atom. -/
theorem recombinedCanonicalDefectLogBound_of_criticalReciprocalPrefixRootBound
    (hprefix : CriticalReciprocalPrefixRootBound) :
    RecombinedCanonicalDefectLogBound := by
  rcases roughCorrelationLogBound_of_criticalReciprocalPrefixRootBound hprefix with
    ⟨C, hC, hcorr⟩
  refine ⟨C + 1, by linarith, ?_⟩
  intro R hR
  rw [canonicalDefectLedger_eq_roughCorrelation_add_rootAtom R hR]
  have hmu : ‖canonicalMoebiusWeight R‖ ≤ (1 : ℝ) := by
    rcases ArithmeticFunction.moebius_eq_or R with h | h | h <;>
      simp [canonicalMoebiusWeight, h]
  have hcorrR := hcorr R hR
  have hRone : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hlog : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg hRone
  have hLone : (1 : ℝ) ≤ Real.log (R : ℝ) + 1 := by linarith
  have hscaleOne :
      (1 : ℝ) ≤ (R : ℝ) * (Real.log (R : ℝ) + 1) := by
    have hmul := mul_le_mul hRone hLone (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ (R : ℝ))
    simpa using hmul
  calc
    ‖squareRootCanonicalRoughCorrelation R + canonicalMoebiusWeight R‖ ≤
        ‖squareRootCanonicalRoughCorrelation R‖ +
          ‖canonicalMoebiusWeight R‖ := norm_add_le _ _
    _ ≤ C * (R : ℝ) * (Real.log (R : ℝ) + 1) + 1 :=
      add_le_add hcorrR hmu
    _ ≤ (C + 1) * (R : ℝ) * (Real.log (R : ℝ) + 1) := by
      calc
        C * (R : ℝ) * (Real.log (R : ℝ) + 1) + 1 ≤
            C * (R : ℝ) * (Real.log (R : ℝ) + 1) +
              (R : ℝ) * (Real.log (R : ℝ) + 1) :=
          add_le_add_left hscaleOne _
        _ = (C + 1) * (R : ℝ) * (Real.log (R : ℝ) + 1) := by ring

/-! ## Post-root covariance descent on reciprocal bands

This is the second-difference route.  A post-root prime family is an exact
sign-reversed copy of a lower prefix in mass and an isometric copy in pair
covariance.  Grouping by `z = floor(W/p)` therefore leaves one lower-scale
covariance value per reciprocal band, multiplied only by the population of that
band.  No norm and no PNT estimate enters this identity.
-/

/-- Pair covariance carried by every post-root prime family in one reciprocal
quotient band. -/
def postRootReciprocalBandFamilyCovariance (W z : ℕ) : ℝ :=
  ∑ p ∈ primeCombPostRootReciprocalBand W z,
    largePrimeFamilyPairSum p (z + 1)

/-- A post-root reciprocal band is literally its prime multiplicity times the
one lower-scale covariance `C(z+1)`.  This is the exact scale descent that the
fixed-prime norm route destroyed. -/
theorem postRootReciprocalBandFamilyCovariance_eq_card_mul_lowerCovariance
    (W z : ℕ) (hz : 0 < z) :
    postRootReciprocalBandFamilyCovariance W z =
      ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        realMertensPositiveLagPairSum (z + 1) := by
  unfold postRootReciprocalBandFamilyCovariance
  calc
    (∑ p ∈ primeCombPostRootReciprocalBand W z,
        largePrimeFamilyPairSum p (z + 1)) =
      ∑ _p ∈ primeCombPostRootReciprocalBand W z,
        realMertensPositiveLagPairSum (z + 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases mem_primeCombPostRootReciprocalBand.mp hp with
        ⟨hpBand, hpRoot⟩
      have hpPrime := primeCombReciprocalBand_prime hpBand
      have hW : W < p * p := (Nat.sqrt_lt).1 hpRoot
      have hdiv := primeCombReciprocalBand_div_eq hz hpBand
      calc
        largePrimeFamilyPairSum p (z + 1) =
            largePrimeFamilyPairSum p (W / p + 1) := by rw [hdiv]
        _ = realMertensPositiveLagPairSum (W / p + 1) :=
          largePrimeFamilyPairSum_postRoot hpPrime hW
        _ = realMertensPositiveLagPairSum (z + 1) := by rw [hdiv]
    _ = ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        realMertensPositiveLagPairSum (z + 1) := by simp

/-- The multiplicity of a post-root reciprocal band is bounded by the literal
integer width of the corresponding quotient interval.  This throws away both
primality and the post-root restriction, so it needs no PNT input. -/
theorem card_primeCombPostRootReciprocalBand_le_width
    (W z : ℕ) :
    (primeCombPostRootReciprocalBand W z).card ≤
      W / z - W / (z + 1) := by
  have hsub :
      primeCombPostRootReciprocalBand W z ⊆
        Finset.Ioc (W / (z + 1)) (W / z) := by
    intro p hp
    rcases mem_primeCombPostRootReciprocalBand.mp hp with ⟨hpBand, _hpRoot⟩
    rcases mem_primeCombReciprocalBand.mp hpBand with ⟨hlow, hhigh, _hpPrime⟩
    exact Finset.mem_Ioc.mpr ⟨hlow, hhigh⟩
  calc
    (primeCombPostRootReciprocalBand W z).card ≤
        (Finset.Ioc (W / (z + 1)) (W / z)).card :=
      Finset.card_le_card hsub
    _ = W / z - W / (z + 1) := by simp

/-- Signed band covariance needs only the positive part of the lower-scale
covariance.  In particular a negative lower covariance helps rather than costs
anything. -/
theorem postRootReciprocalBandFamilyCovariance_le_width_mul_positivePart
    (W z : ℕ) (hz : 0 < z) :
    postRootReciprocalBandFamilyCovariance W z ≤
      ((W / z - W / (z + 1) : ℕ) : ℝ) *
        max (realMertensPositiveLagPairSum (z + 1)) 0 := by
  rw [postRootReciprocalBandFamilyCovariance_eq_card_mul_lowerCovariance W z hz]
  have hcard :
      ((primeCombPostRootReciprocalBand W z).card : ℝ) ≤
        ((W / z - W / (z + 1) : ℕ) : ℝ) := by
    exact_mod_cast card_primeCombPostRootReciprocalBand_le_width W z
  have hcov :
      realMertensPositiveLagPairSum (z + 1) ≤
        max (realMertensPositiveLagPairSum (z + 1)) 0 :=
    le_max_left _ _
  have hcard0 :
      (0 : ℝ) ≤ ((primeCombPostRootReciprocalBand W z).card : ℝ) := by positivity
  have hwidth0 :
      (0 : ℝ) ≤ ((W / z - W / (z + 1) : ℕ) : ℝ) := by positivity
  have hmax0 :
      (0 : ℝ) ≤ max (realMertensPositiveLagPairSum (z + 1)) 0 :=
    le_max_right _ _
  calc
    ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        realMertensPositiveLagPairSum (z + 1) ≤
      ((primeCombPostRootReciprocalBand W z).card : ℝ) *
        max (realMertensPositiveLagPairSum (z + 1)) 0 :=
      mul_le_mul_of_nonneg_left hcov hcard0
    _ ≤ ((W / z - W / (z + 1) : ℕ) : ℝ) *
        max (realMertensPositiveLagPairSum (z + 1)) 0 :=
      mul_le_mul_of_nonneg_right hcard hmax0

end RHLean.Proof