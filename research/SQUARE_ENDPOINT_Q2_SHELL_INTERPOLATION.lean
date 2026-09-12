import RHLean.Proof.SquareEndpointQ2Amplification
import RHLean.Analysis.SquareWheelNesting

/-!
# Unsigned q² shell interpolation at square endpoints

This scratch module isolates the deterministic shell step needed after the
signed #674 reassembly.  It deliberately uses no Möbius cancellation: the only
arithmetic input is the trivial interval-variation bound

  ‖M(b) - M(a)‖ ≤ b - a.

For the raw q² daughter cutoff `Y = floor(X_R / q²)` and its lower square root
`s = floor(sqrt Y)`, the lower complete-square endpoint is `s² - 1`.  Young's
inequality with parameter 36 gives

  M(Y)^2 ≤ (37/36) M(s² - 1)^2 + 148 (s+1)^2.

The coefficient `37/36` therefore contains no hidden signed cancellation.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Literal q² daughter cutoff before square-endpoint rounding. -/
def rawQ2ChildCutoff (R q : ℕ) : ℕ :=
  squareRootEndpoint R / (q * q)

/-- Unshifted Mertens energy at the literal q² daughter cutoff. -/
def rawQ2ChildEnergyReal (R q : ℕ) : ℝ :=
  ((mertensSummatoryInt (rawQ2ChildCutoff R q) : ℤ) : ℝ) ^ 2

private theorem norm_mertensSummatory_sq_eq_realInt_sq (x : ℕ) :
    ‖RHLean.Analysis.mertensSummatory x‖ ^ 2 =
      ((mertensSummatoryInt x : ℤ) : ℝ) ^ 2 := by
  rw [← mertensSummatoryInt_cast x, Complex.norm_intCast]
  exact sq_abs (((mertensSummatoryInt x : ℤ) : ℝ))

private theorem roundedQ2Child_endpoint_le_raw
    (R q : ℕ) :
    squareRootEndpoint (roundedQ2ChildRoot R q) ≤ rawQ2ChildCutoff R q := by
  change (Nat.sqrt (rawQ2ChildCutoff R q)) ^ 2 - 1 ≤ rawQ2ChildCutoff R q
  exact (Nat.sub_le _ _).trans (Nat.sqrt_le' _)

private theorem rawQ2Child_shell_gap_le
    (R q : ℕ) :
    rawQ2ChildCutoff R q - squareRootEndpoint (roundedQ2ChildRoot R q) ≤
      2 * (roundedQ2ChildRoot R q + 1) := by
  simpa [rawQ2ChildCutoff, roundedQ2ChildRoot, squareRootEndpoint,
    canonicalSquareAnchor] using
      canonicalSquareAnchor_gap_le (rawQ2ChildCutoff R q)

/-- **Unsigned shell interpolation.**  The `37/36` coefficient is obtained only
from Young's inequality and the trivial interval variation of Mertens.  No sign
or cancellation theorem is used. -/
theorem rawQ2ChildEnergyReal_le_thirtySeven_thirtySix_rounded_add_shell
    (R q : ℕ) :
    rawQ2ChildEnergyReal R q ≤
      (37 : ℝ) / 36 *
          squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q) +
        148 * (((roundedQ2ChildRoot R q : ℕ) : ℝ) + 1) ^ 2 := by
  let Y : ℕ := rawQ2ChildCutoff R q
  let s : ℕ := roundedQ2ChildRoot R q
  let a : ℕ := squareRootEndpoint s
  let u : ℝ := ‖RHLean.Analysis.mertensSummatory a‖
  let v : ℝ := ‖RHLean.Analysis.mertensSummatory Y -
    RHLean.Analysis.mertensSummatory a‖

  have haY : a ≤ Y := by
    dsimp [a, Y, s]
    exact roundedQ2Child_endpoint_le_raw R q
  have hgapNat : Y - a ≤ 2 * (s + 1) := by
    dsimp [Y, a, s]
    exact rawQ2Child_shell_gap_le R q
  have hvar : v ≤ ((Y - a : ℕ) : ℝ) := by
    dsimp [v]
    exact norm_mertensSummatory_sub_le a Y haY
  have hgapReal : ((Y - a : ℕ) : ℝ) ≤ 2 * ((s : ℝ) + 1) := by
    exact_mod_cast hgapNat
  have hv : v ≤ 2 * ((s : ℝ) + 1) := hvar.trans hgapReal

  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact norm_nonneg _
  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact norm_nonneg _
  have hs0 : 0 ≤ (s : ℝ) + 1 := by positivity
  have htarget0 : 0 ≤ ‖RHLean.Analysis.mertensSummatory Y‖ := norm_nonneg _
  have htri :
      ‖RHLean.Analysis.mertensSummatory Y‖ ≤ u + v := by
    calc
      ‖RHLean.Analysis.mertensSummatory Y‖ =
          ‖RHLean.Analysis.mertensSummatory a +
            (RHLean.Analysis.mertensSummatory Y -
              RHLean.Analysis.mertensSummatory a)‖ := by
                congr 1
                ring
      _ ≤ u + v := by
        dsimp [u, v]
        exact norm_add_le _ _
  have hyoung :
      (u + v) ^ 2 ≤ (37 : ℝ) / 36 * u ^ 2 + 37 * v ^ 2 := by
    nlinarith [sq_nonneg (u - 36 * v)]
  have htriSq :
      ‖RHLean.Analysis.mertensSummatory Y‖ ^ 2 ≤ (u + v) ^ 2 := by
    nlinarith
  have hvSq : v ^ 2 ≤ 4 * ((s : ℝ) + 1) ^ 2 := by
    nlinarith
  have hmain :
      ‖RHLean.Analysis.mertensSummatory Y‖ ^ 2 ≤
        (37 : ℝ) / 36 * u ^ 2 + 148 * ((s : ℝ) + 1) ^ 2 := by
    calc
      ‖RHLean.Analysis.mertensSummatory Y‖ ^ 2 ≤ (u + v) ^ 2 := htriSq
      _ ≤ (37 : ℝ) / 36 * u ^ 2 + 37 * v ^ 2 := hyoung
      _ ≤ (37 : ℝ) / 36 * u ^ 2 + 148 * ((s : ℝ) + 1) ^ 2 := by
        nlinarith

  change ((mertensSummatoryInt Y : ℤ) : ℝ) ^ 2 ≤
      (37 : ℝ) / 36 *
          ((mertensSummatoryInt (squareRootEndpoint s) : ℤ) : ℝ) ^ 2 +
        148 * ((s : ℝ) + 1) ^ 2
  rw [← norm_mertensSummatory_sq_eq_realInt_sq Y,
    ← norm_mertensSummatory_sq_eq_realInt_sq (squareRootEndpoint s)]
  simpa [u, a] using hmain

end RHLean.Proof
