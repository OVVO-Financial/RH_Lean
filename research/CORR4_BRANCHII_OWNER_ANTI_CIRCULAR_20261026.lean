import Mathlib
import «research.CORR4_DECODER_FINITE_PREFIX_20261026»
import «research.CORR4_B6_UNIT_MASS_20261026»

/-!
# CORR-4: exact fixed-owner Branch-II anti-circularity identity

The second fixed-hyperbola branch is the high-Mobius-owner part of
a6 = mu6 * b6, where the Mobius owner is above a fixed cutoff r.

The full d*b6 decoder on that branch is not a newly small source:
it reproduces rational Mobius minus the finite six-point correction
of the complementary low-owner function. Hence dropping the
complement or bounding Branch II by an assumed new power is circular.

These are literal ArithmeticFunction identities for the genuine
excluded-six coefficients. No RH, prime-interval, or source-size
hypothesis is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Restricted rational Mobius, with p=2,3 excluded. -/
def corr4Mu6 : ArithmeticFunction ℂ :=
  vf919ArithmeticTwist vf919PrimeToSixMask vf919RationalMobius

/-- The first Mobius-cofactor owner is restricted to 1<=a<=r. -/
def corr4Mu6Low (r : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun a => if a ≤ r then corr4Mu6 a else 0, by simp⟩

/-- Fixed-owner counterpart of the asymmetric hyperbola Branch II. -/
def corr4Mu6High (r : ℕ) : ArithmeticFunction ℂ :=
  corr4Mu6 - corr4Mu6Low r

theorem corr4_low_high_owner_exact (r : ℕ) :
    corr4Mu6Low r + corr4Mu6High r = corr4Mu6 := by
  unfold corr4Mu6High
  ring

theorem corr4_excluded_norm_eq_mu6_mul_b6 :
    vf919ExcludedNormCoefficients = corr4Mu6 * corr4B6 := by
  change vf919ArithmeticTwist vf919PrimeToSixMask
      (vf919RationalMobius * vf919QuadraticInverse) =
    vf919ArithmeticTwist vf919PrimeToSixMask vf919RationalMobius *
      vf919ArithmeticTwist vf919PrimeToSixMask vf919QuadraticInverse
  exact vf919ArithmeticTwist_mul _ vf919PrimeToSixMask_mul _ _

theorem corr4_full_decoder_actual_a6_eq_mobius :
    corr4DecoderEuler * vf919ExcludedNormCoefficients =
      vf919RationalMobius := by
  exact vf919ExcludedNorm_restored_character_eq_mobius

/-- Fixed-hyperbola Branch I owner vanishes under the full decoder
*after* its complete six-point correction is taken into account.
There is no pointwise claim that the finite correction is zero. -/
theorem corr4_decoder_low_owner_eq_six_collar (r : ℕ) :
    corr4DecoderEuler * (corr4Mu6Low r * corr4B6) =
      corr4Mu6Low r *
        (1 - vf919DirichletDelta 2 - vf919DirichletDelta 3 +
          vf919DirichletDelta 6) := by
  rw [← corr4_decoder_mul_actual_b6_eq_four_delta]
  ring

/-- Exact anti-circularity. Branch II under the full quotient decoder
is rational Mobius minus the low-owner six-point collar, not zero. -/
theorem corr4_decoder_high_owner_eq_mobius_sub_six_collar (r : ℕ) :
    corr4DecoderEuler * (corr4Mu6High r * corr4B6) =
      vf919RationalMobius -
        corr4Mu6Low r *
          (1 - vf919DirichletDelta 2 - vf919DirichletDelta 3 +
            vf919DirichletDelta 6) := by
  unfold corr4Mu6High
  calc
    corr4DecoderEuler *
      ((corr4Mu6 - corr4Mu6Low r) * corr4B6) =
      corr4DecoderEuler * (corr4Mu6 * corr4B6) -
        corr4DecoderEuler * (corr4Mu6Low r * corr4B6) := by ring
    _ = vf919RationalMobius -
        corr4Mu6Low r *
          (1 - vf919DirichletDelta 2 - vf919DirichletDelta 3 +
            vf919DirichletDelta 6) := by
       rw [← corr4_excluded_norm_eq_mu6_mul_b6,
         corr4_full_decoder_actual_a6_eq_mobius,
         corr4_decoder_low_owner_eq_six_collar]

#print axioms corr4_excluded_norm_eq_mu6_mul_b6
#print axioms corr4_decoder_low_owner_eq_six_collar
#print axioms corr4_decoder_high_owner_eq_mobius_sub_six_collar

end RHLean.Analysis
