import Mathlib
import «research.SQUARE_SHELL_DIVISOR_SYNTHESIS_20261030»

/-!
# Exact arithmetic falsifiers for overly strong signed-persistence targets

These are actual Mobius shell values, not arbitrary signed sequences.
A universal nonpositive adjacent correlation and a universal nonpositive
coprime-band Gram are both false. This does NOT disprove an aggregate
power-saving bound, which may allow positive local correlations.
All finite evaluations use Lean's kernel, not native_decide or new axioms.
-/
noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
namespace RHLean.Proof

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The original square block [225,256) has Mobius sum -4. -/
theorem synthesisShell_fifteen : synthesisDivisorMobiusWindow 15 1 = -4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The next original square block [256,289) has Mobius sum -6. -/
theorem synthesisShell_sixteen : synthesisDivisorMobiusWindow 16 1 = -6 := by
  decide +kernel

/-- Adjacent square-block covariance need not have a restoring sign. -/
theorem synthesisAdjacentShell_product_positive :
    synthesisDivisorMobiusWindow 15 1 * synthesisDivisorMobiusWindow 16 1 = 24 := by
  rw [synthesisShell_fifteen, synthesisShell_sixteen]
  norm_num

theorem synthesis_not_universal_nonpositive_adjacent :
    ¬ (∀ R : ℕ, 3 ≤ R →
      synthesisDivisorMobiusWindow R 1 * synthesisDivisorMobiusWindow (R+1) 1 ≤ 0) := by
  intro h
  have hbad := h 15 (by norm_num)
  norm_num only [show (15 : ℕ)+1=16 by norm_num,
    synthesisAdjacentShell_product_positive] at hbad

/-- Exact divisor expression of the original coprime-kernel Gram. -/
def synthesisCoprimeBandEnergy (H : ℕ) : ℤ :=
  ∑ R ∈ Finset.Ico H (2*H),
    ∑ h ∈ Finset.Icc 1 R, (μ h : ℤ) * synthesisDivisorMobiusWindow R h ^ 2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- A complete dyadic root window has POSITIVE coprime signed Gram. -/
theorem synthesisCoprimeBand_five : synthesisCoprimeBandEnergy 5 = 14 := by
  decide +kernel

theorem synthesis_not_universal_nonpositive_coprime :
    ¬ (∀ H : ℕ, 3 ≤ H → synthesisCoprimeBandEnergy H ≤ 0) := by
  intro h
  have hbad := h 5 (by norm_num)
  rw [synthesisCoprimeBand_five] at hbad
  norm_num at hbad

#print axioms synthesisShell_fifteen
#print axioms synthesisShell_sixteen
#print axioms synthesis_not_universal_nonpositive_adjacent
#print axioms synthesisCoprimeBand_five
#print axioms synthesis_not_universal_nonpositive_coprime
end RHLean.Proof
