import RHLean.Proof.ExceptionalTransportCoboundary
import RHLean.Proof.ExceptionalOwnerEnergyClosure
import RHLean.Proof.PhysicalExceptionalCompensatedCellIntertwine

/-!
# What a joint-daughter contraction actually requires

For three already-compensated daughters, a synthesis coefficient below one
requires negative cross-OWNER energy, up to the boundary allowance. Cancellation
between `F` and `T` inside a single daughter does not assert this cross-owner
inequality. The exact statements below keep this distinction explicit.

Moreover, for the compiled scalar predecessor cubes at `X >= 1470`, every
additive incidence image of `F` is zero. Thus a proposed scalar incidence lift
has no within-owner `F/T` cross term in this regime. These statements do not
replace an unsummed physical field by its scalar prefix.

Finally, the universal three-vector bound already has a subcritical restricted
scale budget: `3*(1/9+1/25+1/49)=1891/3675<1`. If a physical parent and its
daughters had the asserted unit-normalized energy dictionary, this bound would
close the induction without any subunit frame. That physical dictionary is an
explicit hypothesis below, not a result proved by this audit.
-/

noncomputable section

namespace RHLean.Proof

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Sum of the energies of the three intact signed daughters. -/
def jointDaughterDiagonalEnergy (u v w : V) : ℝ :=
  ‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2

/-- Signed interactions between different owners, after each daughter has
already retained its own full compensation. -/
def jointDaughterCrossOwnerEnergy (u v w : V) : ℝ :=
  inner ℝ u v + inner ℝ u w + inner ℝ v w

/-- Exact synthesis energy on three whole signed daughter vectors. -/
theorem jointDaughter_energy_identity (u v w : V) :
    ‖u + v + w‖ ^ 2 = jointDaughterDiagonalEnergy u v w +
      2 * jointDaughterCrossOwnerEnergy u v w := by
  rw [norm_add_sq (𝕜 := ℝ), norm_add_sq (𝕜 := ℝ)]
  simp only [inner_add_left]
  change ‖u‖ ^ 2 + 2 * inner ℝ u v + ‖v‖ ^ 2 +
    2 * (inner ℝ u w + inner ℝ v w) + ‖w‖ ^ 2 = _
  unfold jointDaughterDiagonalEnergy jointDaughterCrossOwnerEnergy
  ring

/-- The proposed joint frame estimate is precisely a cross-owner inequality.
When `c < 1`, the required negative allowance is `(1-c)` times the diagonal
energy, except for what the independently bounded error `B` absorbs. -/
theorem jointDaughter_bound_iff_crossOwner_bound
    (u v w : V) (c B : ℝ) :
    (‖u + v + w‖ ^ 2 ≤ c * jointDaughterDiagonalEnergy u v w + B) ↔
      2 * jointDaughterCrossOwnerEnergy u v w ≤
        B - (1 - c) * jointDaughterDiagonalEnergy u v w := by
  rw [jointDaughter_energy_identity]
  constructor <;> intro h <;> nlinarith

/-- Even zero aggregate cross-owner energy does not give a coefficient below
one for free: the error must then absorb the stated share of the diagonal. -/
theorem jointDaughter_bound_iff_error_absorbs_diagonal_of_cross_zero
    (u v w : V) (c B : ℝ)
    (hcross : jointDaughterCrossOwnerEnergy u v w = 0) :
    (‖u + v + w‖ ^ 2 ≤ c * jointDaughterDiagonalEnergy u v w + B) ↔
      (1 - c) * jointDaughterDiagonalEnergy u v w ≤ B := by
  rw [jointDaughter_bound_iff_crossOwner_bound, hcross]
  constructor <;> intro h <;> nlinarith

omit [InnerProductSpace ℝ V] in
/-- The universal synthesis bound is applied only to intact signed daughters.
It supplies no physical source-to-daughter comparison. -/
theorem jointDaughter_norm_sq_le_three (u v w : V) :
    ‖u + v + w‖ ^ 2 ≤ 3 * jointDaughterDiagonalEnergy u v w := by
  have htri : ‖u + v + w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ :=
    (norm_add_le (u + v) w).trans (add_le_add_right (norm_add_le u v) _)
  have hs : ‖u + v + w‖ ^ 2 ≤ (‖u‖ + ‖v‖ + ‖w‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
  unfold jointDaughterDiagonalEnergy
  nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖u‖ - ‖w‖),
    sq_nonneg (‖v‖ - ‖w‖)]

omit [InnerProductSpace ℝ V] in
/-- An additive incidence map of the literal scalar frozen daughter is zero
after predecessor-cube completion. No unsummed field identity is asserted. -/
theorem exceptionalScalarIncidence_frozen_eq_zero
    {q X : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) (hX : 1470 ≤ X)
    (A : ℤ →+ V) :
    A (squareRootLowPrimeGoWallSquareResidual q X) = 0 := by
  rw [exceptionalGoDaughter_eq_zero hq hX, map_zero]

omit [InnerProductSpace ℝ V] in
/-- The signed scalar incidence lift is entirely transported high mass in
this regime, regardless of the particular additive incidence map. -/
theorem exceptionalScalarIncidence_joint_eq_neg_transport
    {q X : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) (hX : 1470 ≤ X)
    (A : ℤ →+ V) :
    A (squareRootLowPrimeGoWallSquareResidual q X - q2DaughterHighTransport q X) =
      -A (q2DaughterHighTransport q X) := by
  rw [exceptionalGoDaughter_eq_zero hq hX, zero_sub, map_neg]

/-- Therefore the proposed within-owner frozen/transport inner product is
exactly zero for any linear incidence applied to these scalar arguments. -/
theorem exceptionalScalarIncidence_frozen_transport_inner_eq_zero
    {q X : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) (hX : 1470 ≤ X)
    (A : ℤ →+ V) :
    inner ℝ (A (squareRootLowPrimeGoWallSquareResidual q X))
      (A (q2DaughterHighTransport q X)) = 0 := by
  rw [exceptionalScalarIncidence_frozen_eq_zero hq hX A]
  simp

end InnerProduct

/-- The universal factor-three synthesis fits the restricted scale budget. -/
theorem jointDaughter_threeFrame_scaleBudget :
    exceptionalOwnerEnergyBudget 3 3 3 = (1891 : ℚ) / 3675 := by
  norm_num [exceptionalOwnerEnergyBudget]

/-- A normalized factor-three recurrence would already close linearly.
The physical recurrence is explicit; none of its arithmetic content is
obtained from the universal synthesis inequality alone. -/
theorem jointDaughter_threeFrame_step_implies_linear
    {E : ℕ → ℚ} {C : ℚ}
    (hzero : E 0 = 0) (hC : 0 ≤ C)
    (hstep : ExceptionalOwnerEnergyStep E C 3 3 3) :
    ∀ X : ℕ, E X ≤ ((3675 : ℚ) / 1784 * C) * (X : ℚ) := by
  apply exceptionalOwnerEnergyStep_implies_linear_of_fixedPointBudget hzero
    (by positivity) (by norm_num) (by norm_num) (by norm_num) ?_ hstep
  rw [jointDaughter_threeFrame_scaleBudget]
  linarith

/-- This makes the missing normalization visible. If the physical parent
were dominated by the three joint scalar daughters with a linear error, and
each whole daughter by the same energy at its smaller scale, no additional
subunit frame theorem would be necessary. Both comparisons remain hypotheses. -/
theorem normalizedJointDaughter_bounds_imply_linear
    {E phi3 phi5 phi7 : ℕ → ℚ} {C : ℚ}
    (hzero : E 0 = 0) (hC : 0 ≤ C)
    (hparent : ∀ X, E X ≤ C * (X : ℚ) +
      (phi3 X + phi5 X + phi7 X) ^ 2)
    (h3 : ∀ X, (phi3 X) ^ 2 ≤ E (X / 9))
    (h5 : ∀ X, (phi5 X) ^ 2 ≤ E (X / 25))
    (h7 : ∀ X, (phi7 X) ^ 2 ≤ E (X / 49)) :
    ∀ X : ℕ, E X ≤ ((3675 : ℚ) / 1784 * C) * (X : ℚ) := by
  apply jointDaughter_threeFrame_step_implies_linear hzero hC
  intro X
  have hp := hparent X
  have hthree : (phi3 X + phi5 X + phi7 X) ^ 2 ≤
      3 * ((phi3 X) ^ 2 + (phi5 X) ^ 2 + (phi7 X) ^ 2) := by
    nlinarith [sq_nonneg (phi3 X - phi5 X), sq_nonneg (phi3 X - phi7 X),
      sq_nonneg (phi5 X - phi7 X)]
  have hsum := add_le_add (add_le_add (h3 X) (h5 X)) (h7 X)
  change E X ≤ C * (X : ℚ) + 3 * E (X / 9) + 3 * E (X / 25) + 3 * E (X / 49)
  linarith

end RHLean.Proof
