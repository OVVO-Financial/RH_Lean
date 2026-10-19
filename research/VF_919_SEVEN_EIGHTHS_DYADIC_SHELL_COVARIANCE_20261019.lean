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
      ∑ R ∈ Finset.Ico H (2 * H), ((2 : ℝ) * R + 1) := by
  unfold vf919DyadicSquareShellDiagonal
  exact Finset.sum_le_sum (s := Finset.Ico H (2 * H))
    (f := vf919SquareShellDiagonal) (g := fun R => (2 : ℝ) * R + 1)
    (fun R _ => vf919SquareShell_diagonal_le_width R)

/-- Literal dyadic square-shell diagonals telescope to the endpoint
difference. This is a genuine squarefree-site count, not a density model. -/
theorem vf919DyadicSquareShell_diagonal_telescope (H : ℕ) :
    vf919DyadicSquareShellDiagonal H =
      realMertensDiagonal ((2 * H) ^ 2) -
        realMertensDiagonal (H ^ 2) := by
  have hfull (K : ℕ) :
      (∑ R ∈ Finset.range K, vf919SquareShellDiagonal R) =
        realMertensDiagonal (K ^ 2) := by
    induction K with
    | zero => simp [realMertensDiagonal]
    | succ K ih =>
        rw [Finset.sum_range_succ, ih]
        unfold vf919SquareShellDiagonal
        ring
  unfold vf919DyadicSquareShellDiagonal
  rw [Finset.sum_Ico_eq_sub _ (show H ≤ 2 * H by omega)]
  rw [hfull, hfull]

/-- SHARP unconditional H-shell diagonal: the union of all square shells
[H^2,(2H)^2) has exactly 3H^2 integer positions. -/
theorem vf919DyadicSquareShell_diagonal_le_three_sq (H : ℕ) :
    vf919DyadicSquareShellDiagonal H ≤ 3 * (H : ℝ) ^ 2 := by
  have hle : H ^ 2 ≤ (2 * H) ^ 2 := by nlinarith
  have hbound :=
    vf919Diagonal_interval_le (H ^ 2) ((2 * H) ^ 2) hle
  have hgap : (2 * H) ^ 2 - H ^ 2 = 3 * H ^ 2 := by
    have hexpand : (2 * H) ^ 2 = H ^ 2 + 3 * H ^ 2 := by ring
    omega
  rw [hgap] at hbound
  rw [vf919DyadicSquareShell_diagonal_telescope]
  push_cast at hbound
  nlinarith

/-- An unconditional rough diagonal budget of order H^2, even with no
squarefree density theorem: each of H shells has at most 4H+1 sites. -/
theorem vf919DyadicSquareShell_diagonal_le_rough (H : ℕ) :
    vf919DyadicSquareShellDiagonal H ≤
      (H : ℝ) * (4 * (H : ℝ) + 1) := by
  -- The stronger physical-capacity bound already pays the whole diagonal.
  -- Avoid a redundant sum estimate and its fragile constant-sum simp.
  have hsharp := vf919DyadicSquareShell_diagonal_le_three_sq H
  have hH : 0 ≤ (H : ℝ) := Nat.cast_nonneg H
  nlinarith [sq_nonneg (H : ℝ)]

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

/-- Tight dyadic energy envelope: the actual diagonal costs only 3H^2.
No sign estimate has been made; the signed covariance premise is EXPLICIT. -/
theorem vf919DyadicSquareShell_energy_of_signedCovariance_sharp
    (H : ℕ) (T : ℝ)
    (hC : 2 * vf919DyadicSquareShellCovariance H ≤ T) :
    vf919DyadicSquareShellEnergy H ≤
      3 * (H : ℝ) ^ 2 + T := by
  have hGram := vf919DyadicSquareShell_signedGreenKubo H
  have hDiag := vf919DyadicSquareShell_diagonal_le_three_sq H
  linarith

/-! ## Global square-prefix energy: exact algebraic consumer -/

/-- Nonnegative full-prefix shell energy. The dyadic 5/2 arithmetic gate
must later be used to bound this object with a geometric dyadic cover. -/
def vf919SquareShellPrefixEnergy (K : ℕ) : ℝ :=
  ∑ R ∈ Finset.range K, vf919SquareShellSum R ^ 2

/-- Full-prefix Mertens is controlled by the TRUE full-prefix shell energy.
No dyadic bound is claimed by this theorem: it is the deterministic
Cauchy--Schwarz consumer to be fed by the dyadic geometric aggregation. -/
theorem vf919SquareShell_prefixCauchy (K : ℕ) :
    ‖realMertensLength (K ^ 2)‖ ^ 2 ≤
      (K : ℝ) * vf919SquareShellPrefixEnergy K := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range K) (fun _R => (1 : ℝ)) vf919SquareShellSum
  have hcs' :
      (∑ R ∈ Finset.range K, vf919SquareShellSum R) ^ 2 ≤
      (K : ℝ) * vf919SquareShellPrefixEnergy K := by
    simpa [vf919SquareShellPrefixEnergy] using hcs
  rw [vf919SquareShell_telescope] at hcs'
  simpa [Real.norm_eq_abs, sq_abs] using hcs'

/-- Exact decomposition of full-prefix square-shell energy into lower
prefix plus one dyadic band. No covariance upper bound is used. -/
theorem vf919SquareShellPrefixEnergy_double (H : ℕ) :
    vf919SquareShellPrefixEnergy (2 * H) =
      vf919SquareShellPrefixEnergy H +
        vf919DyadicSquareShellEnergy H := by
  have h :=
    Finset.sum_Ico_eq_sub
      (fun R => vf919SquareShellSum R ^ 2)
      (show H ≤ 2 * H by omega)
  unfold vf919DyadicSquareShellEnergy vf919SquareShellPrefixEnergy
  linarith

/-- ALL powers-of-two shell energies aggregate by an exact finite
telescoping identity; this is the discrete skeleton of the dyadic-to-
global route. A uniform 5/2+epsilon bound still needs to be supplied
before estimating the sum on the right. -/
theorem vf919SquareShellPrefixEnergy_powTwo (k : ℕ) :
    vf919SquareShellPrefixEnergy (2 ^ k) =
      vf919SquareShellPrefixEnergy 1 +
        ∑ j ∈ Finset.range k, vf919DyadicSquareShellEnergy (2 ^ j) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        vf919SquareShellPrefixEnergy (2 ^ (k + 1)) =
            vf919SquareShellPrefixEnergy (2 * 2 ^ k) := by
              congr 1
              rw [pow_succ]
              ring
        _ = vf919SquareShellPrefixEnergy (2 ^ k) +
              vf919DyadicSquareShellEnergy (2 ^ k) :=
          vf919SquareShellPrefixEnergy_double (2 ^ k)
        _ = vf919SquareShellPrefixEnergy 1 +
              ∑ j ∈ Finset.range (k + 1),
                vf919DyadicSquareShellEnergy (2 ^ j) := by
            rw [Finset.sum_range_succ, ih]
            ring

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
  simp [Nat.card_Ico]
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
    rw [Nat.card_Ico]
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

/-- The quantitative dyadic reduction with no unsourced cancellation:
a proved one-sided covariance budget T controls the GENUINE Mobius
increment on the physical interval [H^2,(2H)^2). -/
theorem vf919DyadicSquareShell_increment_sq_of_signedCovariance
    (H : ℕ) (T : ℝ)
    (hC : 2 * vf919DyadicSquareShellCovariance H ≤ T) :
    ‖realMertensLength ((2 * H) ^ 2) -
        realMertensLength (H ^ 2)‖ ^ 2 ≤
      (H : ℝ) * (3 * (H : ℝ) ^ 2 + T) := by
  have hCS := vf919DyadicSquareShell_increment_sq_le_energy H
  have henergy :=
    vf919DyadicSquareShell_energy_of_signedCovariance_sharp H T hC
  exact hCS.trans (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg H))

/-- Same signed covariance budget controls every PARTIAL dyadic Mertens
increment (essential when K is not the dyadic right endpoint). -/
theorem vf919DyadicSquareShell_partial_increment_sq_of_signedCovariance
    (H K : ℕ) (hHK : H ≤ K) (hK : K ≤ 2 * H)
    (T : ℝ) (hC : 2 * vf919DyadicSquareShellCovariance H ≤ T) :
    ‖realMertensLength (K ^ 2) -
        realMertensLength (H ^ 2)‖ ^ 2 ≤
      (H : ℝ) * (3 * (H : ℝ) ^ 2 + T) := by
  have hCS := vf919DyadicSquareShell_partial_increment_sq H K hHK hK
  have henergy :=
    vf919DyadicSquareShell_energy_of_signedCovariance_sharp H T hC
  exact hCS.trans (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg H))

#print axioms vf919DyadicSquareShell_increment_sq_of_signedCovariance
#print axioms vf919DyadicSquareShell_partial_increment_sq_of_signedCovariance
#print axioms vf919SquareShellPrefixEnergy_double
#print axioms vf919SquareShellPrefixEnergy_powTwo
#print axioms vf919SquareShell_prefixCauchy
#print axioms vf919DyadicSquareShell_increment_eq_sum
#print axioms vf919DyadicSquareShell_count
#print axioms vf919DyadicSquareShell_cauchy
#print axioms vf919DyadicSquareShell_increment_sq_le_energy
#print axioms vf919DyadicSquareShell_partial_cauchy
#print axioms vf919DyadicSquareShell_partial_increment_sq
#print axioms vf919DyadicSquareShell_energy_of_signedCovariance_sharp
#print axioms vf919DyadicSquareShell_diagonal_telescope
#print axioms vf919DyadicSquareShell_diagonal_le_three_sq
#print axioms vf919DyadicSquareShell_signedGreenKubo
#print axioms vf919DyadicSquareShell_diagonal_le_widthSum
#print axioms vf919DyadicSquareShell_diagonal_le_rough
#print axioms vf919DyadicSquareShell_energy_of_signedCovariance

end RHLean.Analysis
