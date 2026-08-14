import Mathlib
import RHLean.Analysis.DyadicTransportCompression
import RHLean.Analysis.NativePNTSignedLogSquarePrimeCells

/-!
# Exact parity decomposition of the full signed log-square transform

The pointwise prime cells are only useful quantitatively if they sit inside the
actual second-Selberg signed error mass with bounded overlap.  This module
proves that exact statement at the cofactor level for the fixed fresh prime `2`.

Every positive Möbius cofactor is either an odd parent or the doubled child of
an odd parent; doubling an even parent gives a multiple of `4`, hence zero
Möbius weight.  The full reciprocal `mu * log^2` transform therefore splits
into multiplicity-one odd parent/doubled-child pairs.  The apparent top odd
boundary has quotient fibre `k = 1`, so its log-square weight is exactly zero.

No estimate and no Selberg remainder bound enters this decomposition.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- One outer-cofactor contribution to the signed log-square reciprocal error
transform. -/
def nativePNTMobiusLogSquareSignedCofactorTerm (N m : ℕ) : ℝ :=
  (μ : ArithmeticFunction ℝ) m *
    nativePNTMobiusLogSquareReciprocalFiber N m
      (fun d => nativePNTError (N / d))

/-- The complete signed log-square transform is the finite sum of its cofactor
terms. -/
theorem nativePNTMobiusLogSquareReciprocalSignedErrorMass_eq_sum_cofactorTerms
    (N : ℕ) :
    nativePNTMobiusLogSquareReciprocalSignedErrorMass N =
      ∑ m ∈ Finset.Icc 1 N,
        nativePNTMobiusLogSquareSignedCofactorTerm N m := by
  rfl

private theorem nativeMobiusReal_two_mul (m : ℕ) :
    (μ : ArithmeticFunction ℝ) (2 * m) =
      if Odd m then -(μ : ArithmeticFunction ℝ) m else 0 := by
  by_cases hm : Odd m
  · rw [if_pos hm]
    change (((μ (2 * m) : ℤ) : ℝ)) = -(((μ m : ℤ) : ℝ))
    rw [moebius_two_mul_of_odd m hm]
    push_cast
    rfl
  · rw [if_neg hm]
    have heven : Even m := Nat.not_odd_iff_even.mp hm
    have hzero : μ (2 * m) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hsq
      have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
      apply hnot
      rcases heven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    change (((μ (2 * m) : ℤ) : ℝ)) = 0
    rw [hzero]
    simp

/-- A doubled even parent contributes nothing to the log-square transform. -/
theorem nativePNTMobiusLogSquareSignedCofactorTerm_two_mul_of_even
    (N m : ℕ) (hm : Even m) :
    nativePNTMobiusLogSquareSignedCofactorTerm N (2 * m) = 0 := by
  unfold nativePNTMobiusLogSquareSignedCofactorTerm
  have hnotOdd : ¬ Odd m := Nat.not_odd_iff_even.mpr hm
  rw [nativeMobiusReal_two_mul m, if_neg hnotOdd]
  ring

/-- One multiplicity-one parity pair in the outer Möbius cofactor coordinate. -/
def nativePNTMobiusLogSquareParityCofactorPair (N m : ℕ) : ℝ :=
  nativePNTMobiusLogSquareSignedCofactorTerm N m +
    nativePNTMobiusLogSquareSignedCofactorTerm N (2 * m)

private theorem nativePNT_sum_Icc_eq_odd_add_even
    (B : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 B, f m) =
      (∑ m ∈ oddCofactorPrefix B, f m) +
        ∑ m ∈ evenCofactorPrefix B, f m := by
  calc
    (∑ m ∈ Finset.Icc 1 B, f m) =
        ∑ m ∈ Finset.Icc 1 B,
          ((if Odd m then f m else 0) +
            (if Even m then f m else 0)) := by
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hodd : Odd m
      · have hnotEven : ¬ Even m := Nat.not_even_iff_odd.mpr hodd
        simp [hodd, hnotEven]
      · have heven : Even m := Nat.not_odd_iff_even.mp hodd
        simp [hodd, heven]
    _ =
        (∑ m ∈ oddCofactorPrefix B, f m) +
          ∑ m ∈ evenCofactorPrefix B, f m := by
      rw [Finset.sum_add_distrib]
      unfold oddCofactorPrefix evenCofactorPrefix
      rw [Finset.sum_filter, Finset.sum_filter]

private theorem nativePNT_sum_evenCofactorPrefix_eq_sum_double
    (B : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ evenCofactorPrefix B, f m) =
      ∑ d ∈ Finset.Icc 1 (B / 2), f (2 * d) := by
  classical
  symm
  refine Finset.sum_bij (fun d _ => 2 * d) ?_ ?_ ?_ ?_
  · intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hdB⟩
    have h2dB : 2 * d ≤ B := by
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).1 hdB
      simpa [Nat.mul_comm] using hmul
    exact mem_evenCofactorPrefix.mpr
      ⟨by omega, h2dB, even_two_mul d⟩
  · intro d1 _hd1 d2 _hd2 h
    change 2 * d1 = 2 * d2 at h
    omega
  · intro m hm
    rcases mem_evenCofactorPrefix.mp hm with ⟨hm1, hmB, hmeven⟩
    have hdouble : 2 * (m / 2) = m := Nat.two_mul_div_two_of_even hmeven
    refine ⟨m / 2, ?_, hdouble⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have hmne : m ≠ 0 := by omega
      have hmgt : 1 < m := Nat.one_lt_of_ne_zero_of_even hmne hmeven
      omega
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      have hmul : m / 2 * 2 = m := by
        simpa [Nat.mul_comm] using hdouble
      rw [hmul]
      exact hmB
  · intro d _hd
    rfl

private theorem nativePNT_sum_double_terms_eq_odd_half
    (N B : ℕ) :
    (∑ d ∈ Finset.Icc 1 (B / 2),
      nativePNTMobiusLogSquareSignedCofactorTerm N (2 * d)) =
      ∑ d ∈ oddCofactorPrefix (B / 2),
        nativePNTMobiusLogSquareSignedCofactorTerm N (2 * d) := by
  calc
    (∑ d ∈ Finset.Icc 1 (B / 2),
        nativePNTMobiusLogSquareSignedCofactorTerm N (2 * d)) =
      ∑ d ∈ Finset.Icc 1 (B / 2),
        if Odd d then
          nativePNTMobiusLogSquareSignedCofactorTerm N (2 * d)
        else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hodd : Odd d
      · simp [hodd]
      · have heven : Even d := Nat.not_odd_iff_even.mp hodd
        simp [hodd,
          nativePNTMobiusLogSquareSignedCofactorTerm_two_mul_of_even
            N d heven]
    _ = ∑ d ∈ oddCofactorPrefix (B / 2),
        nativePNTMobiusLogSquareSignedCofactorTerm N (2 * d) := by
      unfold oddCofactorPrefix
      rw [Finset.sum_filter]

/-- Exact outer-cofactor parity compression, retaining the explicit top odd
boundary. -/
theorem nativePNTMobiusLogSquareReciprocalSignedErrorMass_eq_parityPairs_add_boundary
    (N : ℕ) :
    nativePNTMobiusLogSquareReciprocalSignedErrorMass N =
      (∑ d ∈ oddCofactorPrefix (N / 2),
        nativePNTMobiusLogSquareParityCofactorPair N d) +
      ∑ d ∈ dyadicCofactorBoundary N,
        nativePNTMobiusLogSquareSignedCofactorTerm N d := by
  have hsubset := oddCofactorPrefix_half_subset N
  have hoddSplit :
      (∑ d ∈ oddCofactorPrefix N,
          nativePNTMobiusLogSquareSignedCofactorTerm N d) =
        (∑ d ∈ dyadicCofactorBoundary N,
          nativePNTMobiusLogSquareSignedCofactorTerm N d) +
        ∑ d ∈ oddCofactorPrefix (N / 2),
          nativePNTMobiusLogSquareSignedCofactorTerm N d := by
    unfold dyadicCofactorBoundary
    exact (Finset.sum_sdiff hsubset).symm
  rw [nativePNTMobiusLogSquareReciprocalSignedErrorMass_eq_sum_cofactorTerms]
  rw [nativePNT_sum_Icc_eq_odd_add_even N
    (fun m => nativePNTMobiusLogSquareSignedCofactorTerm N m)]
  rw [nativePNT_sum_evenCofactorPrefix_eq_sum_double N
    (fun m => nativePNTMobiusLogSquareSignedCofactorTerm N m)]
  rw [nativePNT_sum_double_terms_eq_odd_half N N]
  rw [hoddSplit]
  unfold nativePNTMobiusLogSquareParityCofactorPair
  rw [Finset.sum_add_distrib]
  ring

/-- The top odd cofactor boundary has only quotient `k = 1`; its log-square
fibre therefore vanishes exactly. -/
theorem nativePNTMobiusLogSquareSignedCofactorTerm_eq_zero_of_boundary
    (N d : ℕ) (hd : d ∈ dyadicCofactorBoundary N) :
    nativePNTMobiusLogSquareSignedCofactorTerm N d = 0 := by
  rcases mem_dyadicCofactorBoundary.mp hd with ⟨hd1, hdN, _hdodd, hNd⟩
  have hdpos : 0 < d := by omega
  have hlo : 1 * d ≤ N := by simpa using hdN
  have hhi : N < (1 + 1) * d := by simpa using hNd
  have hdiv : N / d = 1 := Nat.div_eq_of_lt_le hlo hhi
  unfold nativePNTMobiusLogSquareSignedCofactorTerm
    nativePNTMobiusLogSquareReciprocalFiber
  rw [hdiv]
  simp

/-- **Global multiplicity-one parity decomposition.**  The complete signed
second-Selberg log-square transform is exactly the sum of odd-parent/doubled-
child cofactor pairs.  The boundary disappears algebraically by `log 1 = 0`. -/
theorem nativePNTMobiusLogSquareReciprocalSignedErrorMass_eq_parityPairs
    (N : ℕ) :
    nativePNTMobiusLogSquareReciprocalSignedErrorMass N =
      ∑ d ∈ oddCofactorPrefix (N / 2),
        nativePNTMobiusLogSquareParityCofactorPair N d := by
  rw [nativePNTMobiusLogSquareReciprocalSignedErrorMass_eq_parityPairs_add_boundary]
  have hzero :
      (∑ d ∈ dyadicCofactorBoundary N,
        nativePNTMobiusLogSquareSignedCofactorTerm N d) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    exact nativePNTMobiusLogSquareSignedCofactorTerm_eq_zero_of_boundary N d hd
  rw [hzero]
  ring

/-- The same multiplicity-one parity sum is therefore exactly the signed
`Lambda_2` error mass. -/
theorem nativeLambdaTwoSignedErrorMass_eq_parityPairs
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      nativeLambdaTwo d * nativePNTError (N / d)) =
      ∑ m ∈ oddCofactorPrefix (N / 2),
        nativePNTMobiusLogSquareParityCofactorPair N m := by
  rw [nativeLambdaTwoSignedErrorMass_eq_mobiusLogSquareReciprocal,
    nativePNTMobiusLogSquareReciprocalSignedErrorMass_eq_parityPairs]

end RHLean.Analysis
