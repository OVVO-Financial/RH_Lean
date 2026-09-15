import Mathlib
import «research.GLOBAL_RETURNED_CORE_WEIGHTED_GRAM»

/-!
# The zero-frequency AMP remainder is one real weighted Möbius amplitude

The rough correlation is exactly the negative complementary Möbius tail
`R <= n <= X_R`.  The reciprocal q² daughter column has already been put on the
same physical Möbius clock.  Therefore their difference is one scalar-weighted
real trajectory, not a sum of separately normed packets.

This is the object whose square is to be expanded by first-separation owner.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Real complementary Möbius tail appearing with a minus sign in the canonical
rough correlation. -/
def lowOwnerFarTailAmplitudeReal (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
    lowOwnerFarTailWeight R n * realMoebiusStep n

/-- The entire zero-frequency correction as one real weighted Möbius sum. -/
def lowOwnerZeroFrequencyMobiusAmplitude (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
    lowOwnerZeroFrequencyMobiusWeight R n * realMoebiusStep n

/-- The far-tail indicator simply restricts the common physical clock to
`R <= n <= X_R`. -/
theorem lowOwnerFarTailAmplitudeReal_eq_Icc
    (R : ℕ) (hR : 2 ≤ R) :
    lowOwnerFarTailAmplitudeReal R =
      ∑ n ∈ Finset.Icc R (squareRootEndpoint R), realMoebiusStep n := by
  have hRX : R ≤ squareRootEndpoint R := le_squareRootEndpoint_self hR
  unfold lowOwnerFarTailAmplitudeReal lowOwnerFarTailWeight
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The real tail is exactly `M(X_R)-M(R-1)` after casting to the complex
coordinate used by the AMP identity. -/
theorem lowOwnerFarTailAmplitudeReal_cast_eq_mertens_sub
    (R : ℕ) (hR : 2 ≤ R) :
    (lowOwnerFarTailAmplitudeReal R : ℂ) =
      mertensSummatory (squareRootEndpoint R) - mertensSummatory (R - 1) := by
  rw [lowOwnerFarTailAmplitudeReal_eq_Icc R hR]
  have hRX : R ≤ squareRootEndpoint R := le_squareRootEndpoint_self hR
  have hpred : R - 1 ≤ squareRootEndpoint R := by omega
  have hset :
      Finset.Ioc (R - 1) (squareRootEndpoint R) =
        Finset.Icc R (squareRootEndpoint R) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have htail := moebius_Ioc_cast_eq_mertens_sub hpred
  rw [hset] at htail
  calc
    ((∑ n ∈ Finset.Icc R (squareRootEndpoint R), realMoebiusStep n : ℝ) : ℂ) =
        ∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          (((μ n : ℤ) : ℂ)) := by
            push_cast
            simp [realMoebiusStep]
    _ = mertensSummatory (squareRootEndpoint R) -
          mertensSummatory (R - 1) := htail

/-- Consequently the far-tail amplitude is exactly the negative rough
correlation. -/
theorem lowOwnerFarTailAmplitudeReal_cast_eq_neg_correlation
    (R : ℕ) (hR : 2 ≤ R) :
    (lowOwnerFarTailAmplitudeReal R : ℂ) =
      -squareRootCanonicalRoughCorrelation R := by
  rw [lowOwnerFarTailAmplitudeReal_cast_eq_mertens_sub R hR,
    squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R hR]
  ring

/-- The combined site weight is exactly tail plus reciprocal daughter mass on
the same clock. -/
theorem lowOwnerZeroFrequencyMobiusAmplitude_eq_tail_add_reciprocal
    (R : ℕ) :
    lowOwnerZeroFrequencyMobiusAmplitude R =
      lowOwnerFarTailAmplitudeReal R + lowOwnerReciprocalMertensColumnReal R := by
  rw [lowOwnerReciprocalMertensColumnReal_eq_weightedMobiusSum]
  unfold lowOwnerZeroFrequencyMobiusAmplitude
    lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailAmplitudeReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- **One-amplitude identification.**  The single real weighted Möbius sum is
exactly `reciprocal daughter column - rough correlation`. -/
theorem lowOwnerZeroFrequencyMobiusAmplitude_cast_eq_reciprocal_sub_correlation
    (R : ℕ) (hR : 2 ≤ R) :
    (lowOwnerZeroFrequencyMobiusAmplitude R : ℂ) =
      lowOwnerReciprocalMertensColumn R -
        squareRootCanonicalRoughCorrelation R := by
  rw [lowOwnerZeroFrequencyMobiusAmplitude_eq_tail_add_reciprocal]
  push_cast
  rw [lowOwnerFarTailAmplitudeReal_cast_eq_neg_correlation R hR,
    lowOwnerReciprocalMertensColumnReal_cast]
  ring

/-- **Exact AMP square coordinate.**  Above the physical stable-far onset, the
actual zero-frequency amplitude remainder is the negative of one real weighted
Möbius trajectory.  Hence its norm-square is literally the square of this real
sum; no packetwise triangle inequality is needed. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_neg_oneAmplitude
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      -(lowOwnerZeroFrequencyMobiusAmplitude R : ℂ) := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
      R hR,
    lowOwnerZeroFrequencyMobiusAmplitude_cast_eq_reciprocal_sub_correlation
      R (by omega)]
  ring

/-- The corresponding energy identity. -/
theorem norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_oneAmplitude_sq
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 =
      lowOwnerZeroFrequencyMobiusAmplitude R ^ 2 := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_neg_oneAmplitude R hR]
  simp [Real.norm_eq_abs, sq_abs]

end RHLean.Proof
