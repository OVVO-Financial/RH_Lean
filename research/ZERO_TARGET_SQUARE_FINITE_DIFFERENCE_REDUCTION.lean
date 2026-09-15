import Mathlib
import RHLean.Proof.PostRootMertensSquareFiniteDifference
import «research.ZERO_TARGET_COVARIANCE_OWNER_DESCENT»

/-!
# Reduce the post-root square finite difference to zero-target owner advantage

The exact Bessel/square-energy identity already says

  Delta_sq(W) = 2 * postRootCovarianceRemainder(W) + diagonalResidual(W).

The zero-target owner descent from #711 says the covariance remainder is

  terminalExcess(W) - sum_parent multiplicity(parent) * parentExcess(parent),

where every terminal excess is nonpositive and

  parentExcess = coPartial_0 - divergent_0.

Combining the two identities before any magnitude estimate gives

  Delta_sq(W)
    = 2 * terminalExcess(W)
      + 2 * parentAdvantage(W)
      + diagonalResidual(W),

with

  parentAdvantage
    = sum multiplicity * (divergent_0 - coPartial_0).

The terminal contribution has favorable sign and the existing complementary
diagonal is at most W.  Hence the entire RH-strength square finite-difference
seam has the one-sided reduction

  Delta_sq(W) <= W + 2 * parentAdvantage(W).

This module also records the exact sufficient power statement: any
W^(1+epsilon) upper bound on this one remaining zero-target owner advantage
feeds the already-compiled square finite-difference closure and hence the
protected Mertens-energy criterion.

No absolute value is taken on the signed owner advantage, no multiplicity is
replaced by a support count, and no RH hypothesis is introduced.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The favorable/nonfavorable terminal population from the exact zero-target
owner descent.  Its sign is already known to be nonpositive. -/
def postRootZeroTargetTerminalExcess (W : ℕ) : ℝ :=
  ∑ mn ∈ postRootCovarianceRemainderTerminalPairCarrier W,
    postRootZeroTargetPairExcess mn

/-- The only potentially positive owner contribution after zero-target sector
reversal: minus the multiplicity-weighted parent excess. -/
def postRootZeroTargetParentMultiplicityAdvantage (W : ℕ) : ℝ :=
  -∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
    (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
      postRootZeroTargetPairExcess parent

/-- NNS-style display of the same owner advantage: child multiplicity weights
`divergent_0 - coPartial_0` on the parent pair. -/
theorem postRootZeroTargetParentMultiplicityAdvantage_eq_divergent_sub_coPartial
    (W : ℕ) :
    postRootZeroTargetParentMultiplicityAdvantage W =
      ∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
        (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
          (zeroTargetDivergentPair
              (realMoebiusStep parent.1) (realMoebiusStep parent.2) -
            zeroTargetCoPartialPair
              (realMoebiusStep parent.1) (realMoebiusStep parent.2)) := by
  unfold postRootZeroTargetParentMultiplicityAdvantage
  symm
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro parent _hparent
  unfold postRootZeroTargetPairExcess zeroTargetPairExcess
  ring

/-- The terminal zero-target population can only help an upper bound. -/
theorem postRootZeroTargetTerminalExcess_nonpos (W : ℕ) :
    postRootZeroTargetTerminalExcess W ≤ 0 := by
  unfold postRootZeroTargetTerminalExcess
  exact sum_postRootCovarianceRemainderTerminalPair_zeroTargetExcess_nonpos W

/-- **Exact zero-target square-energy decomposition.**  This is just the
existing square/Bessel identity composed with the signed owner descent; no
estimate has yet entered. -/
theorem postRootMertensSquareFiniteDifference_eq_two_terminal_add_two_advantage_add_diagonal
    (W : ℕ) :
    postRootMertensSquareFiniteDifference W =
      2 * postRootZeroTargetTerminalExcess W +
        2 * postRootZeroTargetParentMultiplicityAdvantage W +
        postRootComplementDiagonalResidual W := by
  rw [postRootMertensSquareFiniteDifference_eq_two_mul_remainder_add_diagonal,
    postRootCovarianceRemainder_eq_terminalZeroTarget_sub_parentMultiplicity]
  unfold postRootZeroTargetTerminalExcess
    postRootZeroTargetParentMultiplicityAdvantage
  ring

/-- **One-sided reduction of the RH-strength square seam.**  Terminals are
nonpositive and the complementary Bessel diagonal costs only one endpoint. -/
theorem postRootMertensSquareFiniteDifference_le_endpoint_add_two_zeroTargetAdvantage
    (W : ℕ) :
    postRootMertensSquareFiniteDifference W ≤
      (W : ℝ) + 2 * postRootZeroTargetParentMultiplicityAdvantage W := by
  rw [postRootMertensSquareFiniteDifference_eq_two_terminal_add_two_advantage_add_diagonal]
  have hterminal := postRootZeroTargetTerminalExcess_nonpos W
  have hdiag := postRootComplementDiagonalResidual_le_endpoint W
  linarith

/-- Same one-sided reduction with the four zero-target partial-moment sectors
visible. -/
theorem postRootMertensSquareFiniteDifference_le_endpoint_add_two_multiplicity_divergent_sub_coPartial
    (W : ℕ) :
    postRootMertensSquareFiniteDifference W ≤
      (W : ℝ) +
        2 * ∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
          (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
            (zeroTargetDivergentPair
                (realMoebiusStep parent.1) (realMoebiusStep parent.2) -
              zeroTargetCoPartialPair
                (realMoebiusStep parent.1) (realMoebiusStep parent.2)) := by
  rw [← postRootZeroTargetParentMultiplicityAdvantage_eq_divergent_sub_coPartial]
  exact postRootMertensSquareFiniteDifference_le_endpoint_add_two_zeroTargetAdvantage W

/-- Positive-power target for the sole remaining zero-target owner advantage. -/
def PostRootZeroTargetMultiplicityAdvantagePowerStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ W : ℕ, 2 ≤ W →
        postRootZeroTargetParentMultiplicityAdvantage W ≤
          D * Real.rpow (W : ℝ) (1 + ε)

/-- **Closure to the existing square finite-difference seam.**  Once the
multiplicity-weighted `divergent_0 - coPartial_0` owner advantage is controlled,
all other terms cost only one endpoint unit. -/
theorem postRootMertensSquareFiniteDifferencePower_of_zeroTargetMultiplicityAdvantagePower
    (hadv : PostRootZeroTargetMultiplicityAdvantagePowerStatement) :
    PostRootMertensSquareFiniteDifferencePowerStatement := by
  intro ε hε
  rcases hadv ε hε with ⟨D, hD, hbound⟩
  refine ⟨2 * D + 1, by positivity, ?_⟩
  intro W hW
  have ha := hbound W hW
  have hs := endpoint_le_postRootPowerScale hε hW
  have hfd :=
    postRootMertensSquareFiniteDifference_le_endpoint_add_two_zeroTargetAdvantage W
  nlinarith

/-- **Terminal implication.**  A power bound on the zero-target owner advantage
is sufficient for the already-protected Mertens-energy criterion. -/
theorem mertensEnergyBounded_of_postRootZeroTargetMultiplicityAdvantagePower
    (hadv : PostRootZeroTargetMultiplicityAdvantagePowerStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootMertensSquareFiniteDifferencePower
    (postRootMertensSquareFiniteDifferencePower_of_zeroTargetMultiplicityAdvantagePower hadv)

end RHLean.Proof
