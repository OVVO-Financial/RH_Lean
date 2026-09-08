import RHLean.Proof.PostRootCovarianceUnconditionalDecayScratch
import RHLean.Analysis.NativePNTAxer

/-!
# Normalized decay on the signed post-root covariance remainder

The Bessel return path and the repository's unconditional `M(N)=o(N)` theorem
already imply more than a fixed constant improvement: the *positive part* of the
signed post-root remainder is `o(W^2)` pointwise.  This is independent of the
stronger zero-free-region rate used in the scratch file.

Together with the exact product-packing lower bound
`E(W) >= -(W + W*sqrt W)/2`, this isolates the two signs sharply: positive
quadratic-scale excursions vanish asymptotically, while negative excursions are
already bounded at the `W^(3/2)` scale.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The normalized positive part of the signed post-root covariance remainder
vanishes unconditionally.  This uses only the elementary Axer/PNT contraction
`M(W)/W -> 0` already compiled in the repository and the exact Bessel return
inequality `E(W) <= M(W)^2/2`. -/
theorem postRootCovarianceRemainder_posPart_div_sq_tendsto_zero :
    Tendsto
      (fun W : ℕ =>
        max (postRootCovarianceRemainder W) 0 / ((W : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hM :
      Tendsto
        (fun W : ℕ => realMertensLength (W + 1) / (W : ℝ))
        atTop (𝓝 0) := by
    simpa [realMertensLength_succ_eq_nativeMertensSummatory] using
      RHLean.Analysis.nativeMertens_div_atTop_zero
  have hsq :
      Tendsto
        (fun W : ℕ =>
          (realMertensLength (W + 1) / (W : ℝ)) ^ 2 / 2)
        atTop (𝓝 0) := by
    simpa using (hM.pow 2).div_const 2
  refine squeeze_zero' ?_ ?_ hsq
  · filter_upwards [eventually_ge_atTop 1] with W hW
    have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (show 0 < W by omega)
    exact div_nonneg (le_max_right _ _) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with W hW
    have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (show 0 < W by omega)
    have hE := postRootCovarianceRemainder_le_half_mertensSquare W
    have hmax :
        max (postRootCovarianceRemainder W) 0 <=
          realMertensLength (W + 1) ^ 2 / 2 := by
      exact max_le hE (div_nonneg (sq_nonneg _) (by norm_num))
    rw [div_le_iff₀ (sq_pos_of_pos hWpos)]
    calc
      max (postRootCovarianceRemainder W) 0 <=
          realMertensLength (W + 1) ^ 2 / 2 := hmax
      _ =
          ((realMertensLength (W + 1) / (W : ℝ)) ^ 2 / 2) *
            ((W : ℝ) ^ 2) := by
        field_simp
        ring

/-- Epsilon form: every fixed positive fraction of the quadratic scale is
:eventually excluded on the positive side. -/
theorem postRootCovarianceRemainder_eventually_lt_eps_sq
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ W : ℕ in atTop,
      postRootCovarianceRemainder W < eps * ((W : ℝ) ^ 2) := by
  have hlim := postRootCovarianceRemainder_posPart_div_sq_tendsto_zero
  have hsmall :
      ∀ᶠ W : ℕ in atTop,
        max (postRootCovarianceRemainder W) 0 / ((W : ℝ) ^ 2) < eps :=
    (tendsto_order.1 hlim).2 eps heps
  filter_upwards [hsmall, eventually_ge_atTop 1] with W hWsmall hW
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (show 0 < W by omega)
  have hposle :
      postRootCovarianceRemainder W <= max (postRootCovarianceRemainder W) 0 :=
    le_max_left _ _
  have hmul := (div_lt_iff₀ (sq_pos_of_pos hWpos)).1 hWsmall
  exact lt_of_le_of_lt hposle hmul

/-- A completely explicit two-sided envelope on the current signed carrier.
The positive side uses the repository's finished strong Mertens rate; the
negative side uses only exact post-root quotient packing.  No record or envelope
hypothesis occurs in the statement.

This is the useful pointwise synthesis: whichever sign `E(W)` takes, its
absolute value is bounded by the larger of a subexponentially contracted
quadratic term and the elementary `W^(3/2)` packing term. -/
theorem abs_postRootCovarianceRemainder_le_twoSidedUnconditionalEnvelope :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ W : ℕ, 3 ≤ W →
        |postRootCovarianceRemainder W| ≤
          max
            ((C * (W : ℝ) *
              Real.exp (-c * (Real.log (W : ℝ)) ^ ((1 : ℝ) / 10))) ^ 2 / 2)
            (((W : ℝ) + (Nat.sqrt W : ℝ) * (W : ℝ)) / 2) := by
  rcases postRootCovarianceRemainder_le_strongMertensSubexp with
    ⟨c, C, hc, hC, hupper⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro W hW
  let U : ℝ :=
    (C * (W : ℝ) *
      Real.exp (-c * (Real.log (W : ℝ)) ^ ((1 : ℝ) / 10))) ^ 2 / 2
  let B : ℝ := ((W : ℝ) + (Nat.sqrt W : ℝ) * (W : ℝ)) / 2
  have hu : postRootCovarianceRemainder W ≤ U := by
    simpa [U] using hupper W hW
  have hl :=
    neg_half_endpoint_add_sqrt_mul_endpoint_le_postRootCovarianceRemainder W
  have hl' : -B ≤ postRootCovarianceRemainder W := by
    dsimp [B]
    linarith
  have hleft : -max U B ≤ postRootCovarianceRemainder W := by
    have hB : B ≤ max U B := le_max_right _ _
    linarith
  have hright : postRootCovarianceRemainder W ≤ max U B :=
    hu.trans (le_max_left _ _)
  have habs : |postRootCovarianceRemainder W| ≤ max U B :=
    abs_le.mpr ⟨hleft, hright⟩
  simpa [U, B] using habs

end RHLean.Proof
