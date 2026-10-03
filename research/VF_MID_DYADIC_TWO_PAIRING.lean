import Mathlib
import «research.ALL_SCALE_LI_DISPLACEMENT_REDUCTION»
import «research.LI_MODEL_DISCRETIZATION»

/-!
# Prime-two pairing of the VF actual-to-Li dyadic wavelet

PR #862 rewrites the mean-zero part of the physical actual-minus-Li
displacement as the boundary-free dyadic Abel wavelet

  sum_j sum_d mu(d) * A_j(d).

This file performs the prime-two Mobius pairing *before any norm is taken*.
The complete wavelet is rewritten onto odd reciprocal indices as

  sum_{d<R, d odd} mu(d) *
    (F_R(d) - 1_{2d<R} F_R(2d)),

where F_R(d) is the sum of the boundary-free Abel potentials at d.

Consequently the wavelet norm is bounded by the literal l1 variation of these
paired cross-scale differences.  This removes the generic sqrt(R) loss from
Cauchy--Schwarz and reduces the quantitative problem to deterministic dyadic
scale transfer.

No analytic hypothesis is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Sum of all occupied-block Abel potentials at one reciprocal index.  Only
one occupied dyadic block can contribute, but keeping the finite sum makes the
reindexing below independent of a separate uniqueness lemma. -/
def squareRootDyadicTotalAbelPotential (R d : ℕ) : ℂ :=
  ∑ j ∈ primeSieveDyadicBlockIndices R (squareRootEndpoint R),
    primeSieveDyadicBlockAbelPotential R (squareRootEndpoint R) j d

/-- The complete boundary-free wavelet is a single Mobius sum against the
pointwise total Abel potential. -/
theorem squareRoot_waveletPNTError_eq_moebius_totalAbelPotential
    (R : ℕ) :
    primeSieveDyadicWaveletPNTError R (squareRootEndpoint R) =
      ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
        canonicalMoebiusWeight d * squareRootDyadicTotalAbelPotential R d := by
  rw [primeSieveDyadicWaveletPNTError_eq_boundaryFreeAbel]
  unfold squareRootDyadicTotalAbelPotential canonicalMoebiusWeight
  calc
    (∑ j ∈ primeSieveDyadicBlockIndices R (squareRootEndpoint R),
        ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
          (((μ d : ℤ) : ℂ)) *
            primeSieveDyadicBlockAbelPotential
              R (squareRootEndpoint R) j d) =
      ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
        ∑ j ∈ primeSieveDyadicBlockIndices R (squareRootEndpoint R),
          (((μ d : ℤ) : ℂ)) *
            primeSieveDyadicBlockAbelPotential
              R (squareRootEndpoint R) j d := by
            rw [Finset.sum_comm]
    _ = ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
        (((μ d : ℤ) : ℂ)) *
          ∑ j ∈ primeSieveDyadicBlockIndices R (squareRootEndpoint R),
            primeSieveDyadicBlockAbelPotential
              R (squareRootEndpoint R) j d := by
            apply Finset.sum_congr rfl
            intro d _hd
            rw [Finset.mul_sum]

/-- Generic exact prime-two pairing for a Mobius-weighted finite prefix.
Even squarefree indices are paired with their unique odd parent; multiples of
four vanish. -/
theorem sum_Ico_canonicalMoebiusWeight_mul_eq_odd_twoPair
    (F : ℕ → ℂ) (R : ℕ) :
    (∑ d ∈ Finset.Ico 1 R, canonicalMoebiusWeight d * F d) =
      ∑ d ∈ Finset.Ico 1 R,
        if Odd d then
          canonicalMoebiusWeight d *
            (F d - if 2 * d < R then F (2 * d) else 0)
        else 0 := by
  have hsplit :
      (∑ d ∈ Finset.Ico 1 R, canonicalMoebiusWeight d * F d) =
        (∑ d ∈ Finset.Ico 1 R,
          if Odd d then canonicalMoebiusWeight d * F d else 0) +
        ∑ d ∈ Finset.Ico 1 R,
          if Even d then canonicalMoebiusWeight d * F d else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    rcases Nat.even_or_odd d with he | ho
    · have hno : ¬ Odd d := Nat.not_odd_iff_even.mpr he
      simp [he, hno]
    · have hne : ¬ Even d := Nat.not_even_iff_odd.mpr ho
      simp [ho, hne]
  have heven :
      (∑ d ∈ Finset.Ico 1 R,
          if Even d then canonicalMoebiusWeight d * F d else 0) =
        ∑ d ∈ Finset.Ico 1 R,
          if Odd d then
            (if 2 * d < R then
              -(canonicalMoebiusWeight d * F (2 * d))
            else 0)
          else 0 := by
    rw [RHLean.Proof.sum_Ico_even_eq_sum_double
      (R := R) (fun d => canonicalMoebiusWeight d * F d)]
    apply Finset.sum_congr rfl
    intro d _hd
    rcases Nat.even_or_odd d with he | ho
    · have hno : ¬ Odd d := Nat.not_odd_iff_even.mpr he
      simp [hno, RHLean.Proof.canonicalMoebiusWeight_two_mul_of_even he]
    · by_cases h2 : 2 * d < R
      · simp [ho, h2, RHLean.Proof.canonicalMoebiusWeight_two_mul_of_odd ho]
      · simp [ho, h2]
  rw [hsplit, heven, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases ho : Odd d
  · simp only [ho, if_true]
    by_cases h2 : 2 * d < R
    · simp [h2]
      ring
    · simp [h2]
  · simp [ho]

/-- Cross-scale Abel difference left after exact prime-two pairing. -/
def squareRootDyadicTwoPairedAbelDifference (R d : ℕ) : ℂ :=
  squareRootDyadicTotalAbelPotential R d -
    if 2 * d < R then squareRootDyadicTotalAbelPotential R (2 * d) else 0

/-- **Exact odd-only form of the #862 wavelet.**
At the square-root endpoint the quotient support is exactly 1,...,R-1, so
prime-two Mobius pairing converts the complete mean-zero actual-to-Li
displacement into adjacent-dyadic-scale differences on odd indices. -/
theorem squareRootCenteredDyadicWaveletDisplacement_eq_oddTwoPaired
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCenteredDyadicWaveletDisplacement R =
      ∑ d ∈ Finset.Ico 1 R,
        if Odd d then
          canonicalMoebiusWeight d *
            squareRootDyadicTwoPairedAbelDifference R d
        else 0 := by
  rw [squareRootCenteredDyadicWaveletDisplacement_eq_waveletPNTError,
    squareRoot_waveletPNTError_eq_moebius_totalAbelPotential]
  have htop :
      squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R (by omega)
  have hsupp :
      primeSieveQuotientSupport R (squareRootEndpoint R) =
        Finset.Ico 1 R := by
    unfold primeSieveQuotientSupport
    rw [htop]
    ext d
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsupp,
    sum_Ico_canonicalMoebiusWeight_mul_eq_odd_twoPair
      (squareRootDyadicTotalAbelPotential R) R]
  unfold squareRootDyadicTwoPairedAbelDifference

/-- **Deterministic variation bound with no Mobius-dispersion loss.**
After the exact prime-two pairing, taking absolute values costs only the
cross-scale Abel variation itself; there is no factor sqrt(R). -/
theorem norm_squareRootCenteredDyadicWaveletDisplacement_le_oddTwoPairedVariation
    (R : ℕ) (hR : 2 ≤ R) :
    ‖squareRootCenteredDyadicWaveletDisplacement R‖ ≤
      ∑ d ∈ Finset.Ico 1 R,
        if Odd d then
          ‖squareRootDyadicTwoPairedAbelDifference R d‖
        else 0 := by
  rw [squareRootCenteredDyadicWaveletDisplacement_eq_oddTwoPaired R hR]
  calc
    ‖∑ d ∈ Finset.Ico 1 R,
        if Odd d then
          canonicalMoebiusWeight d *
            squareRootDyadicTwoPairedAbelDifference R d
        else 0‖
        ≤ ∑ d ∈ Finset.Ico 1 R,
            ‖if Odd d then
              canonicalMoebiusWeight d *
                squareRootDyadicTwoPairedAbelDifference R d
            else 0‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ico 1 R,
        if Odd d then
          ‖squareRootDyadicTwoPairedAbelDifference R d‖
        else 0 := by
          apply Finset.sum_le_sum
          intro d _hd
          by_cases ho : Odd d
          · simp only [ho, if_true, norm_mul]
            exact
              (mul_le_mul_of_nonneg_right
                (norm_canonicalMoebiusWeight_le_one d)
                (norm_nonneg (squareRootDyadicTwoPairedAbelDifference R d))).trans_eq
                (one_mul _)
          · simp [ho]

end RHLean.Analysis
