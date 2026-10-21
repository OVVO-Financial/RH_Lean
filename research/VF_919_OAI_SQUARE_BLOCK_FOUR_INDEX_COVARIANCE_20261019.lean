import «research.VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019»
import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»

/-!
# EXACT covariance weld, each original physical pair and both Hecke divisors

THIS file has the ORIGINAL vf919SquareShellCovariance R on the left. On the
right it carries every ordered physical pair R^2 <= m < n < (R+1)^2,
and the complete signed two-ended Dirichlet convolution
  mu_Z(m) = sum_{de=m} chi_{-3}(d) a_F(e),
  mu_Z(n) = sum_{fg=n} chi_{-3}(f) a_F(g).
NO dropped diagonal, cross-pair, squareful zero, shell boundary, repeated
norm coefficient, absolute-value substitution or random-sign claim.

The two-ended four-index signed series is a real equality with the actual
RH_Lean within-square-block covariance. It is not by itself the OAI
prime-ideal theta probe: identifying the constructed coefficient a_F with
the true norm sum over ideal mu_F, preserving *individual* sextic phases,
and matching OAI's smooth marked/rescaled physical source are distinct,
concrete proofs. They must not be assumed by multiplying by arbitrary
OAI-local parameters.

This is the precise Fubini / coefficient target for that next proof.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

/-- The ACTUAL all-divisor rational-to-Eisenstein norm coefficient.
    This includes split, inert, ramified and squareful contributions. -/
def vf919SquareShellCompleteHeckeCoefficient (n : ℕ) : ℂ :=
  ∑ t ∈ Nat.divisorsAntidiagonal n,
    vf919ChiMinusThree t.1 *
      vf919EisensteinNormCoefficients t.2

/-- Exact source equality at EACH integer, using the previously proved
    quadratic-norm Euler convolution, not a new assumed incidence map. -/
theorem vf919SquareShellCompleteHeckeCoefficient_eq_actualMu (n : ℕ) :
    vf919SquareShellCompleteHeckeCoefficient n =
      vf919RationalMobius n := by
  unfold vf919SquareShellCompleteHeckeCoefficient
  rw [← vf919QuadraticCharacter_mul_norm_eq_mobius]
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [vf919QuadraticCharacter_apply]

/-- The exact, fully UNCOLLAPSED four-index Hecke-rational covariance.
    The independent divisor pairs at m,n remain explicitly visible. -/
def vf919SquareShellFourIndexHeckeCovariance (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
    ∑ m ∈ Finset.Ico (R ^ 2) n,
      ∑ s ∈ Nat.divisorsAntidiagonal m,
        ∑ t ∈ Nat.divisorsAntidiagonal n,
          (vf919ChiMinusThree s.1 *
            vf919EisensteinNormCoefficients s.2) *
          (vf919ChiMinusThree t.1 *
            vf919EisensteinNormCoefficients t.2)

/-- The original native signed covariance is genuinely ALL ordered pairs
    m < n of physical integers IN THE SAME SQUARE SHELL, not an artificial
    grand-prefix covariance or a low-prime-only component. -/
theorem vf919SquareShellCovariance_eq_true_ordered_physical_pairs
    (R : ℕ) :
    vf919SquareShellCovariance R =
      ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        ∑ m ∈ Finset.Ico (R ^ 2) n,
          realMoebiusStep m * realMoebiusStep n := by
  let a : ℕ := R ^ 2
  let b : ℕ := (R + 1) ^ 2
  have hab : a ≤ b := by
    have hs : (R + 1) ^ 2 = R ^ 2 + (2 * R + 1) := by ring
    dsimp [a, b]
    rw [hs]
    omega
  have hC :
      (∑ n ∈ Finset.Ico a b,
        realMoebiusStep n * realMertensLength n) =
      realMertensPositiveLagPairSum b -
        realMertensPositiveLagPairSum a := by
    unfold realMertensPositiveLagPairSum
    exact Finset.sum_Ico_eq_sub _ hab
  have hS :
      (∑ n ∈ Finset.Ico a b, realMoebiusStep n) =
        realMertensLength b - realMertensLength a := by
    unfold realMertensLength
    exact Finset.sum_Ico_eq_sub _ hab
  have hinner (n : ℕ) (hna : a ≤ n) :
      (∑ m ∈ Finset.Ico a n, realMoebiusStep m) =
        realMertensLength n - realMertensLength a := by
    unfold realMertensLength
    exact Finset.sum_Ico_eq_sub _ hna
  calc
    vf919SquareShellCovariance R =
        (∑ n ∈ Finset.Ico a b,
          realMoebiusStep n * realMertensLength n) -
        realMertensLength a *
          (∑ n ∈ Finset.Ico a b, realMoebiusStep n) := by
      dsimp [vf919SquareShellCovariance, vf919SquareShellSum, a, b]
      rw [hC, hS]
    _ = ∑ n ∈ Finset.Ico a b,
          realMoebiusStep n *
            (realMertensLength n - realMertensLength a) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = ∑ n ∈ Finset.Ico a b,
          ∑ m ∈ Finset.Ico a n,
            realMoebiusStep m * realMoebiusStep n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hna : a ≤ n := (Finset.mem_Ico.mp hn).1
      rw [← hinner n hna, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      ring

/-- Term-for-term complex pair identity before the expansion of either
    Hecke divisor fibre. -/
theorem vf919SquareShellFourIndexHeckeCovariance_eq_actualMuPairs
    (R : ℕ) :
    vf919SquareShellFourIndexHeckeCovariance R =
      ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        ∑ m ∈ Finset.Ico (R ^ 2) n,
          vf919RationalMobius m * vf919RationalMobius n := by
  unfold vf919SquareShellFourIndexHeckeCovariance
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro m _hm
  calc
    (∑ s ∈ Nat.divisorsAntidiagonal m,
      ∑ t ∈ Nat.divisorsAntidiagonal n,
        (vf919ChiMinusThree s.1 * vf919EisensteinNormCoefficients s.2) *
          (vf919ChiMinusThree t.1 * vf919EisensteinNormCoefficients t.2)) =
      vf919SquareShellCompleteHeckeCoefficient m *
        vf919SquareShellCompleteHeckeCoefficient n := by
          unfold vf919SquareShellCompleteHeckeCoefficient
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _hs
          rw [Finset.mul_sum]
    _ = vf919RationalMobius m * vf919RationalMobius n := by
      rw [vf919SquareShellCompleteHeckeCoefficient_eq_actualMu,
        vf919SquareShellCompleteHeckeCoefficient_eq_actualMu]

/-- Rational Möbius coefficient = the original integer sign complexified:
    no extra ideal multiplicity is introduced by source conversion. -/
theorem vf919SquareShell_actualMu_cast (n : ℕ) :
    (realMoebiusStep n : ℂ) = vf919RationalMobius n := by
  unfold realMoebiusStep vf919RationalMobius
  push_cast
  rfl

/-- MAIN THEOREM: the COMPLETE four-index Hecke divisor covariance is
    EXACTLY THE ORIGINAL square-block signed real pair sum, embedded
    in the complex Hecke coefficient ring. Holds at EVERY R. -/
theorem vf919SquareShell_actual_signed_covariance_eq_fourIndexHecke
    (R : ℕ) :
    (vf919SquareShellCovariance R : ℂ) =
      vf919SquareShellFourIndexHeckeCovariance R := by
  rw [vf919SquareShellCovariance_eq_true_ordered_physical_pairs,
    vf919SquareShellFourIndexHeckeCovariance_eq_actualMuPairs]
  push_cast
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro m _hm
  rw [vf919SquareShell_actualMu_cast m,
    vf919SquareShell_actualMu_cast n]

/-- The exact original Green--Kubo energy, on the original square-block
    carrier, with the four-index Hecke terms substituted WITHOUT dropping
    any covariance or bounding separate Euler primes. -/
theorem vf919SquareShell_original_energy_eq_fourIndexHecke
    (R : ℕ) :
    vf919SquareShellSum R ^ 2 =
      vf919SquareShellDiagonal R +
        2 * (vf919SquareShellFourIndexHeckeCovariance R).re := by
  have hC :=
    vf919SquareShell_actual_signed_covariance_eq_fourIndexHecke R
  have hRe :
      vf919SquareShellCovariance R =
        (vf919SquareShellFourIndexHeckeCovariance R).re := by
    rw [← hC]
    simp
  rw [← hRe]
  exact vf919SquareShell_signedGreenKubo R

#print axioms vf919SquareShellCompleteHeckeCoefficient_eq_actualMu
#print axioms vf919SquareShellCovariance_eq_true_ordered_physical_pairs
#print axioms vf919SquareShellFourIndexHeckeCovariance_eq_actualMuPairs
#print axioms vf919SquareShell_actualMu_cast
#print axioms vf919SquareShell_actual_signed_covariance_eq_fourIndexHecke
#print axioms vf919SquareShell_original_energy_eq_fourIndexHecke

end RHLean.Analysis
