import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionFiber
import RHLean.Analysis.AlpogeMobiusPartialMoments

/-!
# Positive prime-parent transfer for the genuine Mobius UPM/LPM populations

The new ingredient is NOT an absolute value or a hypothetical inequality.
It is the pointwise exact positive transfer:
  mu_+(n) = sum_(fresh p|n) log(p)/log(n) * mu_-(n/p),
  mu_-(n) = sum_(fresh p|n) log(p)/log(n) * mu_+(n/p),  n>=2.
The probabilities add to one for squarefree n>1. For nonsquarefree n,
both sides vanish; the square-producing terms have already cancelled
in the complete (mu*Lambda)(n) native identity.

This re-expresses both original two-wall finite-C partial moments as
NONNEGATIVE prime-extension populations, with every parent sign flipped
before any absolute value. The "row stochastic" normalization is exact,
but it DOES NOT give a global operator bound: many large prime children
can share the same parent (in particular parent 1).

No RH claim or paid multiplicity/covolume bound is asserted.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Positive Mobius population at one actual integer. -/
def alpogeFreshMuPlus (n : ℕ) : ℝ :=
  positivePart (moebiusReal n)

/-- Negative Mobius population at one actual integer. -/
def alpogeFreshMuMinus (n : ℕ) : ℝ :=
  negativePart (moebiusReal n)

/-- Nonnegative normalized transfer from opposite-sign fresh-prime parents
to the positive Mobius population at n. -/
def alpogeFreshParentUPM (n : ℕ) : ℝ :=
  (∑ p ∈ freshPrimeDivisors n,
      alpogeFreshMuMinus (n / p) * Real.log p) /
        Real.log n

/-- Nonnegative normalized transfer from opposite-sign fresh-prime parents
to the negative Mobius population at n. -/
def alpogeFreshParentLPM (n : ℕ) : ℝ :=
  (∑ p ∈ freshPrimeDivisors n,
      alpogeFreshMuPlus (n / p) * Real.log p) /
        Real.log n

/-- The genuine prime-factor weights, not arbitrary independent
probabilities, sum to one for every squarefree integer n>=2. -/
theorem alpogeFreshPrimeParent_probability_one
    (n : ℕ) (hn : 2 ≤ n) (hs : Squarefree n) :
    (∑ p ∈ n.primeFactors,
        Real.log p / Real.log (n : ℝ)) = 1 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos hn1).ne'
  rw [← Finset.sum_div, sum_log_primeFactors_eq_log hs,
    div_self hlog]

/-- Pointwise EXACT UPM transfer. Every squarefree child is a convex
combination of opposite-sign parents; non-squarefree atoms pay zero
after their already-checked prime-power cancellation. -/
theorem alpogeFreshParentUPM_eq_muPlus
    (n : ℕ) (hn : 2 ≤ n) :
    alpogeFreshParentUPM n = alpogeFreshMuPlus n := by
  classical
  by_cases hs : Squarefree n
  · have hn1 : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n by omega)
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos hn1).ne'
    have hsum :
        (∑ p ∈ n.primeFactors,
            alpogeFreshMuMinus (n / p) * Real.log p) =
          alpogeFreshMuPlus n * Real.log n := by
      calc
        _ = ∑ p ∈ n.primeFactors,
              alpogeFreshMuPlus n * Real.log p := by
                apply Finset.sum_congr rfl
                intro p hp
                unfold alpogeFreshMuMinus alpogeFreshMuPlus
                rw [moebiusReal_div_prime_eq_neg hs hp]
                simp [positivePart, negativePart]
        _ = alpogeFreshMuPlus n *
              (∑ p ∈ n.primeFactors, Real.log p) := by
                rw [Finset.mul_sum]
        _ = alpogeFreshMuPlus n * Real.log n := by
                rw [sum_log_primeFactors_eq_log hs]
    unfold alpogeFreshParentUPM
    rw [freshPrimeDivisors_eq_primeFactors_of_squarefree hs]
    exact (div_eq_iff hlog).mpr hsum
  · have hzero : moebiusReal n = 0 := by
      unfold moebiusReal
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      norm_num
    have hsum :
        (∑ p ∈ freshPrimeDivisors n,
            alpogeFreshMuMinus (n / p) * Real.log p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hbad := not_squarefree_div_of_fresh_prime hs hp
      have hparent : moebiusReal (n / p) = 0 := by
        unfold moebiusReal
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbad]
        norm_num
      simp [alpogeFreshMuMinus, negativePart, hparent]
    simp [alpogeFreshParentUPM, alpogeFreshMuPlus, positivePart,
      hsum, hzero]

/-- Pointwise EXACT LPM transfer, dual to the UPM theorem. -/
theorem alpogeFreshParentLPM_eq_muMinus
    (n : ℕ) (hn : 2 ≤ n) :
    alpogeFreshParentLPM n = alpogeFreshMuMinus n := by
  classical
  by_cases hs : Squarefree n
  · have hn1 : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n by omega)
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos hn1).ne'
    have hsum :
        (∑ p ∈ n.primeFactors,
            alpogeFreshMuPlus (n / p) * Real.log p) =
          alpogeFreshMuMinus n * Real.log n := by
      calc
        _ = ∑ p ∈ n.primeFactors,
              alpogeFreshMuMinus n * Real.log p := by
                apply Finset.sum_congr rfl
                intro p hp
                unfold alpogeFreshMuMinus alpogeFreshMuPlus
                rw [moebiusReal_div_prime_eq_neg hs hp]
                simp [positivePart, negativePart]
        _ = alpogeFreshMuMinus n *
              (∑ p ∈ n.primeFactors, Real.log p) := by
                rw [Finset.mul_sum]
        _ = alpogeFreshMuMinus n * Real.log n := by
                rw [sum_log_primeFactors_eq_log hs]
    unfold alpogeFreshParentLPM
    rw [freshPrimeDivisors_eq_primeFactors_of_squarefree hs]
    exact (div_eq_iff hlog).mpr hsum
  · have hzero : moebiusReal n = 0 := by
      unfold moebiusReal
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      norm_num
    have hsum :
        (∑ p ∈ freshPrimeDivisors n,
            alpogeFreshMuPlus (n / p) * Real.log p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hbad := not_squarefree_div_of_fresh_prime hs hp
      have hparent : moebiusReal (n / p) = 0 := by
        unfold moebiusReal
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbad]
        norm_num
      simp [alpogeFreshMuPlus, positivePart, hparent]
    simp [alpogeFreshParentLPM, alpogeFreshMuMinus, negativePart,
      hsum, hzero]

/-- The signed real Mobius value is exactly the difference of the
two positive prime-parent contributions at each n>=2. -/
theorem alpogeFreshParentUPM_sub_LPM_eq_mu
    (n : ℕ) (hn : 2 ≤ n) :
    alpogeFreshParentUPM n - alpogeFreshParentLPM n =
      moebiusReal n := by
  rw [alpogeFreshParentUPM_eq_muPlus n hn,
    alpogeFreshParentLPM_eq_muMinus n hn]
  exact positivePart_sub_negativePart (moebiusReal n)

/-- Both parent channels sum to the genuine absolute Mobius mass,
not the unrestricted prime-power population. -/
theorem alpogeFreshParentUPM_add_LPM_eq_abs_mu
    (n : ℕ) (hn : 2 ≤ n) :
    alpogeFreshParentUPM n + alpogeFreshParentLPM n =
      |moebiusReal n| := by
  rw [alpogeFreshParentUPM_eq_muPlus n hn,
    alpogeFreshParentLPM_eq_muMinus n hn]
  exact positivePart_add_negativePart (moebiusReal n)

/-- Exact UPM1 with the strict-history sign switch at R and the top
physical square endpoint. The exceptional n=1 seed remains positive. -/
def alpogeFreshTwoWallUPM (R : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.Icc 2 (R ^ 2 - 1),
    if n < R then alpogeFreshParentUPM n
    else alpogeFreshParentLPM n

/-- Exact LPM1 with the reverse two-wall sign. -/
def alpogeFreshTwoWallLPM (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (R ^ 2 - 1),
    if n < R then alpogeFreshParentLPM n
    else alpogeFreshParentUPM n

/-- Original signed two-wall integer population in the native real
Mobius coordinate used by the pre-existing prime-fibre theorem. -/
def alpogeFreshTwoWallSource (R : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.Icc 2 (R ^ 2 - 1),
    alpogeMobiusTwoWall R n * moebiusReal n

/-- The FULL positive prime-parent UPM-LPM transfer is exact at every
root, including the historical switch, physical upper wall and n=1.
This is not an RH-strength inequality by itself. -/
theorem alpogeFreshTwoWallUPM_sub_LPM (R : ℕ) :
    alpogeFreshTwoWallUPM R -
      alpogeFreshTwoWallLPM R =
        alpogeFreshTwoWallSource R := by
  classical
  unfold alpogeFreshTwoWallUPM alpogeFreshTwoWallLPM
    alpogeFreshTwoWallSource
  have hsum :
      (∑ n ∈ Finset.Icc 2 (R ^ 2 - 1),
        ((if n < R then alpogeFreshParentUPM n
          else alpogeFreshParentLPM n) -
        (if n < R then alpogeFreshParentLPM n
          else alpogeFreshParentUPM n))) =
      ∑ n ∈ Finset.Icc 2 (R ^ 2 - 1),
        alpogeMobiusTwoWall R n * moebiusReal n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    by_cases hroot : n < R
    · simp only [if_pos hroot]
      rw [alpogeFreshParentUPM_sub_LPM_eq_mu n hn2]
      simp [alpogeMobiusTwoWall, hroot]
    · simp only [if_neg hroot]
      have hmu := alpogeFreshParentUPM_sub_LPM_eq_mu n hn2
      simp only [alpogeMobiusTwoWall, hroot, if_false]
      linarith
  rw [← Finset.sum_sub_distrib] at hsum
  linarith

end RHLean.Analysis
