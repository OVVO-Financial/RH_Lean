import «research.VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019»

/-!
# Dyadic aggregate square-shell signed covariance: the weaker 7/8 gate

The independent 2026-10-16 square-shell energy research note already
identified the dyadic condition

    sum_{H <= R < 2*H} S_R^2 = O_epsilon(H^(5/2+epsilon))

as SUFFICIENT for the global Mertens 7/8 exponent by shell telescoping
and Cauchy-Schwarz. It is weaker than the proposed pointwise
S_R^2 = O_epsilon(R^(3/2+epsilon)) (no individual shell cap required).

This module only establishes the EXACT signed Green--Kubo decomposition
and an unconditional O(H^2) diagonal upper bound; the true arithmetic
covariance saving of H^(1/2) versus the naive O(H^3) pair count
remains open. No Hecke moments, zeta zero-free theorem or prior
conjectured covariance bound are imported.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Exact squared Mobius shell amplitudes on the dyadic root range. -/
def vf919DyadicSquareShellEnergy (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H), vf919SquareShellSum R ^ 2

/-- Sum of genuine squarefree shell diagonals, no density approximation. -/
def vf919DyadicSquareShellDiagonal (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H), vf919SquareShellDiagonal R

/-- Complete within-shell signed covariance on the dyadic root range. -/
def vf919DyadicSquareShellCovariance (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H), vf919SquareShellCovariance R

/-- All signed covariance and every physical diagonal, with zero omitted
pairs, add up EXACTLY to the dyadic shell energy. -/
theorem vf919DyadicSquareShell_signedGreenKubo (H : ℕ) :
    vf919DyadicSquareShellEnergy H =
      vf919DyadicSquareShellDiagonal H +
        2 * vf919DyadicSquareShellCovariance H := by
  unfold vf919DyadicSquareShellEnergy vf919DyadicSquareShellDiagonal
    vf919DyadicSquareShellCovariance
  calc
    (∑ R ∈ Finset.Ico H (2 * H), vf919SquareShellSum R ^ 2) =
      ∑ R ∈ Finset.Ico H (2 * H),
        (vf919SquareShellDiagonal R + 2 * vf919SquareShellCovariance R) := by
          apply Finset.sum_congr rfl
          intro R _
          exact vf919SquareShell_signedGreenKubo R
    _ = (∑ R ∈ Finset.Ico H (2 * H), vf919SquareShellDiagonal R) +
          2 * (∑ R ∈ Finset.Ico H (2 * H), vf919SquareShellCovariance R) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Every diagonal contributes at most the literal odd shell width. -/
theorem vf919DyadicSquareShell_diagonal_le_widthSum (H : ℕ) :
    vf919DyadicSquareShellDiagonal H ≤
      ∑ R ∈ Finset.Ico H (2 * H), (2 : ℝ) * R + 1 := by
  unfold vf919DyadicSquareShellDiagonal
  apply Finset.sum_le_sum
  intro R _
  exact vf919SquareShell_diagonal_le_width R

/-- An unconditional rough diagonal budget of order H^2, even with no
squarefree density theorem: each of H shells has at most 4H+1 sites. -/
theorem vf919DyadicSquareShell_diagonal_le_rough (H : ℕ) :
    vf919DyadicSquareShellDiagonal H ≤
      (H : ℝ) * (4 * (H : ℝ) + 1) := by
  have hcard : (Finset.Ico H (2 * H)).card = H := by
    simp only [Finset.card_Ico]
    omega
  calc
    vf919DyadicSquareShellDiagonal H ≤
        ∑ R ∈ Finset.Ico H (2 * H), (2 : ℝ) * R + 1 :=
      vf919DyadicSquareShell_diagonal_le_widthSum H
    _ ≤ ∑ _R ∈ Finset.Ico H (2 * H), (4 : ℝ) * H + 1 := by
      apply Finset.sum_le_sum
      intro R hR
      have hN : R < 2 * H := (Finset.mem_Ico.mp hR).2
      have hReal : (R : ℝ) ≤ (2 * H : ℕ) := by
        exact_mod_cast hN.le
      push_cast at hReal
      linarith
    _ = (H : ℝ) * (4 * (H : ℝ) + 1) := by
      simp [hcard, nsmul_eq_mul]

/-- The dyadic signed-covariance gate is the ONLY nontrivial part of the
sufficient dyadic energy criterion; the diagonal has already been paid. -/
theorem vf919DyadicSquareShell_energy_of_signedCovariance
    (H : ℕ) (T : ℝ)
    (hC : 2 * vf919DyadicSquareShellCovariance H ≤ T) :
    vf919DyadicSquareShellEnergy H ≤
      (H : ℝ) * (4 * (H : ℝ) + 1) + T := by
  have h := vf919DyadicSquareShell_signedGreenKubo H
  have hK := vf919DyadicSquareShell_diagonal_le_rough H
  linarith

/-! ## Source-faithful finite dyadic Cauchy--Schwarz / telescoping -/

/-- The H square shells exactly telescope over [H^2,(2H)^2).
No Hecke ideal, Fourier transformation or smoothing is used. -/
theorem vf919DyadicSquareShell_increment_eq_sum (H : ℕ) :
    realMertensLength ((2 * H) ^ 2) - realMertensLength (H ^ 2) =
      ∑ R ∈ Finset.Ico H (2 * H), vf919SquareShellSum R := by
  have hle : H ≤ 2 * H := by omega
  rw [Finset.sum_Ico_eq_sub _ hle]
  rw [vf919SquareShell_telescope, vf919SquareShell_telescope]

/-- Exactly H sign-bearing square shells are present, even when their
individual lengths are not equal. -/
theorem vf919DyadicSquareShell_count (H : ℕ) :
    (Finset.Ico H (2 * H)).card = H := by
  simp [Finset.card_Ico]
  omega

/-- The precise finite H-point Cauchy--Schwarz inequality. This keeps the
entire SIGNED sum inside the square and all actual shell amplitudes
in the diagonal energy. -/
theorem vf919DyadicSquareShell_cauchy (H : ℕ) :
    (∑ R ∈ Finset.Ico H (2 * H), vf919SquareShellSum R) ^ 2 ≤
      (H : ℝ) * vf919DyadicSquareShellEnergy H := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.Ico H (2 * H))
      (fun _R => (1 : ℝ)) vf919SquareShellSum
  simpa [vf919DyadicSquareShellEnergy, vf919DyadicSquareShell_count H]
    using hcs

/-- Native dyadic Mertens increment has a squared bound with exactly
the cost H, and NO loss from pairwise absolute values. -/
theorem vf919DyadicSquareShell_increment_sq_le_energy (H : ℕ) :
    ‖realMertensLength ((2 * H) ^ 2) -
        realMertensLength (H ^ 2)‖ ^ 2 ≤
      (H : ℝ) * vf919DyadicSquareShellEnergy H := by
  have hcs := vf919DyadicSquareShell_cauchy H
  rw [← vf919DyadicSquareShell_increment_eq_sum] at hcs
  simpa [Real.norm_eq_abs, sq_abs] using hcs

/-- Partial dyadic shell bands cost at most the WHOLE dyadic energy.
This is needed for an arbitrary square-prefix endpoint, not only 2H. -/
theorem vf919DyadicSquareShell_partial_cauchy
    (H K : ℕ) (hHK : H ≤ K) (hK : K ≤ 2 * H) :
    (∑ R ∈ Finset.Ico H K, vf919SquareShellSum R) ^ 2 ≤
      (H : ℝ) * vf919DyadicSquareShellEnergy H := by
  have hsubset : Finset.Ico H K ⊆ Finset.Ico H (2 * H) := by
    intro R hR
    simp only [Finset.mem_Ico] at hR ⊢
    exact ⟨hR.1, lt_of_lt_of_le hR.2 hK⟩
  have hpart :
      (∑ R ∈ Finset.Ico H K, vf919SquareShellSum R ^ 2) ≤
        vf919DyadicSquareShellEnergy H := by
    unfold vf919DyadicSquareShellEnergy
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro R _ _
    positivity
  have hsize : (((Finset.Ico H K).card : ℕ) : ℝ) ≤ (H : ℝ) := by
    rw [Finset.card_Ico]
    exact_mod_cast (show K - H ≤ H by omega)
  have hpartialNonneg :
      0 ≤ ∑ R ∈ Finset.Ico H K, vf919SquareShellSum R ^ 2 := by
    positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.Ico H K) (fun _R => (1 : ℝ)) vf919SquareShellSum
  have hcs' :
      (∑ R ∈ Finset.Ico H K, vf919SquareShellSum R) ^ 2 ≤
        ((Finset.Ico H K).card : ℝ) *
          (∑ R ∈ Finset.Ico H K, vf919SquareShellSum R ^ 2) := by
    simpa using hcs
  exact hcs'.trans (mul_le_mul hsize hpart hpartialNonneg
    (Nat.cast_nonneg H))

/-- The exact Cauchy--Schwarz payment for any dyadic partial square
block, telescoped back to a genuine Mertens difference. -/
theorem vf919DyadicSquareShell_partial_increment_sq
    (H K : ℕ) (hHK : H ≤ K) (hK : K ≤ 2 * H) :
    ‖realMertensLength (K ^ 2) -
        realMertensLength (H ^ 2)‖ ^ 2 ≤
      (H : ℝ) * vf919DyadicSquareShellEnergy H := by
  have hsum :
      (∑ R ∈ Finset.Ico H K, vf919SquareShellSum R) =
        realMertensLength (K ^ 2) -
          realMertensLength (H ^ 2) := by
    rw [Finset.sum_Ico_eq_sub _ hHK]
    rw [vf919SquareShell_telescope, vf919SquareShell_telescope]
  have hcs := vf919DyadicSquareShell_partial_cauchy H K hHK hK
  rw [hsum] at hcs
  simpa [Real.norm_eq_abs, sq_abs] using hcs

#print axioms vf919DyadicSquareShell_increment_eq_sum
#print axioms vf919DyadicSquareShell_count
#print axioms vf919DyadicSquareShell_cauchy
#print axioms vf919DyadicSquareShell_increment_sq_le_energy
#print axioms vf919DyadicSquareShell_partial_cauchy
#print axioms vf919DyadicSquareShell_partial_increment_sq
#print axioms vf919DyadicSquareShell_signedGreenKubo
#print axioms vf919DyadicSquareShell_diagonal_le_widthSum
#print axioms vf919DyadicSquareShell_diagonal_le_rough
#print axioms vf919DyadicSquareShell_energy_of_signedCovariance

end RHLean.Analysis
