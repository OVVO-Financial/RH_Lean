import Mathlib
import RHLean.Proof.GlobalFirstJumpCofactorCompression
import RHLean.Proof.CanonicalRoughCriticalCorrelationContraction
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

end RHLean.Proof
