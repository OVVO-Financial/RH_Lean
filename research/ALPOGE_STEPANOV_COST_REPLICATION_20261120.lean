import Mathlib
import RHLean.Proof.FinitePartialMoments
import RHLean.Analysis.NativePNTErrorMass

/-!
# Source-native Stepanov amplification stress test

The exact selected Mobius/second-Selberg mask in PR #1157 is a signed
lower-prefix matrix. Its inverse is bounded, but its upper operator norm
is not: one fixed all-negative physical response gives cubic one-sided
output energy even though the input energy is merely linear.

This is a FINITE arithmetic cost test, not a Riemann hypothesis bound.
Alpoge's genuine multiplicity argument requires a *paid* error bracket
with geometry, divisibility, widths, and complementary source restored.
See research/ALPOGE_STEPANOV_COST_REPLICATION_20261120.md.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Prefix response for m cumulative signed directions. -/
def alpogeNativePrefixResponse (v : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (i + 1), v j

/-- A constant negative source has cumulative response of magnitude i+1. -/
theorem alpogeNativePrefix_negOne (n : ℕ) :
    (∑ _j ∈ Finset.range n, (-1 : ℝ)) = -(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Lower partial square energy on the all-negative prefix response. -/
def alpogeNativeNegativeSemivariance (m : ℕ) : ℝ :=
  lowerPartialMomentNat 2 (Finset.range m)
    (alpogeNativePrefixResponse (fun _ => -1))

/-- The actual selected negative response is maximally unfavorable:
every LPM2 summand is the entire cumulative square. -/
theorem alpogeNativeNegativeSemivariance_eq_squares (m : ℕ) :
    alpogeNativeNegativeSemivariance m =
      ∑ i ∈ Finset.range m, ((i : ℝ) + 1) ^ 2 := by
  unfold alpogeNativeNegativeSemivariance lowerPartialMomentNat
  apply Finset.sum_congr rfl
  intro i _hi
  change (negativePart (∑ _j ∈ Finset.range (i + 1), (-1 : ℝ))) ^ 2 =
    ((i : ℝ) + 1) ^ 2
  rw [alpogeNativePrefix_negOne]
  simp only [negativePart, neg_neg]
  rw [max_eq_left (Nat.cast_nonneg (i + 1))]
  norm_num [Nat.cast_add]

/-- Conversely, the upper partial energy of this all-negative response is 0.
A one-sided criterion must have its sign aligned with the actual source. -/
theorem alpogeNativePositiveSemivariance_eq_zero (m : ℕ) :
    upperPartialMomentNat 2 (Finset.range m)
      (alpogeNativePrefixResponse (fun _ => -1)) = 0 := by
  unfold upperPartialMomentNat
  apply Finset.sum_eq_zero
  intro i _hi
  change (positivePart (∑ _j ∈ Finset.range (i + 1), (-1 : ℝ))) ^ 2 = 0
  rw [alpogeNativePrefix_negOne]
  simp only [positivePart]
  rw [max_eq_right (neg_nonpos.mpr (Nat.cast_nonneg (i + 1)))]
  norm_num

/-- Elementary sum of the squares of the exact prefix amplitudes. -/
theorem alpogeNativePrefixSumSquares (m : ℕ) :
    (∑ i ∈ Finset.range m, ((i : ℝ) + 1) ^ 2) =
      (m : ℝ) * ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Cubic lower semivariance: the source matrix amplifies a bad sign
by at least order m^2 relative to its order-m input energy. -/
theorem alpogeNativeNegativeSemivariance_ge_cubic (m : ℕ) :
    (m : ℝ) ^ 3 / 3 ≤ alpogeNativeNegativeSemivariance m := by
  rw [alpogeNativeNegativeSemivariance_eq_squares,
    alpogeNativePrefixSumSquares]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmp : 0 ≤ ((m : ℝ) ^ 2 / 2 + (m : ℝ) / 6) := by positivity
  nlinarith

/-- The characteristic THREE costs in Alpoge's complete error bracket.
This is its stripped real algebraic *shape*; parameter witnesses and
arithmetic-geometric estimates are additional nontrivial requirements. -/
def alpogeNativeCostBracket
    (T a m k n b u delta : ℝ) : ℝ :=
  T * a * (1 + m ^ 2 / k) +
    m * (2 * n * m * b * u + delta * k * b * u ^ 2 / n)

/-- Exact normalization by the full main multiplicity T*m*b*delta.
The three algebraic taxes are source length, lift collisions and
the covolume/width return, not merely a rank count. -/
theorem alpogeNativeCostBracket_normalize
    (T a m k n b u delta : ℝ)
    (hT : T ≠ 0) (hm : m ≠ 0) (hk : k ≠ 0)
    (hn : n ≠ 0) (hb : b ≠ 0) (hd : delta ≠ 0) :
    alpogeNativeCostBracket T a m k n b u delta / (T * m * b * delta) =
      (a / (m * b * delta)) * (1 + m ^ 2 / k) +
        2 * n * m * u / (T * delta) + k * u ^ 2 / (n * T) := by
  unfold alpogeNativeCostBracket
  field_simp
  ring


/-- Actual-source UPM2 of the Chebyshev error at square endpoints. Its
uniform critical H^3 bound would support the *opposite* Alpoge sign s0=-1:
-Gz(x) <= O(x^(1/2+epsilon)). The estimate remains OPEN. -/
def alpogeSquarePositiveSemivariance (H : ℕ) : ℝ :=
  upperPartialMomentNat 2 (Finset.Ico H (2 * H))
    (fun R => nativePNTError (R ^ 2 - 1))

theorem alpogeSquarePositiveSemivariance_eq_source (H : ℕ) :
    alpogeSquarePositiveSemivariance H =
      ∑ R ∈ Finset.Ico H (2 * H),
        (max (nativePsi (R ^ 2 - 1) - ((R ^ 2 - 1 : ℕ) : ℝ)) 0) ^ 2 := by
  unfold alpogeSquarePositiveSemivariance upperPartialMomentNat
  rfl

theorem alpogeSquarePositiveSemivariance_nonneg (H : ℕ) :
    0 ≤ alpogeSquarePositiveSemivariance H := by
  unfold alpogeSquarePositiveSemivariance upperPartialMomentNat
  exact Finset.sum_nonneg (fun R _hR =>
    sq_nonneg (positivePart (nativePNTError (R ^ 2 - 1))))

/-- The new opposite-sign RH-strength supplier, kept explicitly unproved. -/
def AlpogeCriticalSquarePositiveSemivariance : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ H : ℕ, 1 ≤ H →
        alpogeSquarePositiveSemivariance H ≤
          C * ((H : ℝ) ^ ((3 : ℝ) + epsilon))

end RHLean.Analysis
