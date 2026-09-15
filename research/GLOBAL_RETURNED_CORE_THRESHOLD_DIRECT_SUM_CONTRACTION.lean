import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_RECIPROCAL_INTERTWINING»
import «research.GLOBAL_RETURNED_CORE_CLIPPED_QUOTIENT»

/-!
# Owner-labelled direct-sum contraction for the threshold/Euler lift

The threshold-to-reciprocal intertwining leaves a potentially large Euler
coefficient on a stripped covariance parent.  That coefficient must not be
estimated in absolute value.  For a fixed parent and fixed next owner `r`, it
is common to every child in the literal `r`-owner fibre.  Hence it factors out
of the child-energy sum exactly.

Keeping the next owner as an explicit direct-sum coordinate gives the sharp
termwise contraction

  inherited child energy = multiplicity/r^2 * parent weighted energy.

For a genuine next chronological owner `p < r`, primality forces `r >= 3`.
The generic two-child fibre therefore contracts by at most `2/9`.  On the
companion-clipped fibre the multiplicity is at most one, so the coefficient is
at most `1/9`.

No bound on the Euler coefficient itself is used.  This is precisely the
advantage of stacking the owner coordinate instead of collapsing all owners
before squaring.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The two critical Euler factors carried by one stripped parent at next owner
`r`. -/
def lowOwnerThresholdEulerPairCoefficient
    (R p r : ℕ) (parent : ℕ × ℕ) : ℝ :=
  lowOwnerThresholdCriticalEulerDifference R p r parent.1 *
    lowOwnerThresholdCriticalEulerDifference R p r parent.2

/-- Reciprocal parent energy with the owner-labelled Euler coefficient retained
exactly. -/
def lowOwnerThresholdEulerParentEnergy
    (R p r : ℕ) (parent : ℕ × ℕ) : ℝ :=
  lowOwnerThresholdEulerPairCoefficient R p r parent ^ 2 *
    postRootCovarianceReciprocalPairEnergy parent

/-- A child inherits the same stripped-parent Euler coefficient.  This is the
correct local energy currency for the next-owner fibre. -/
def lowOwnerThresholdEulerInheritedChildEnergy
    (R p r : ℕ) (parent child : ℕ × ℕ) : ℝ :=
  lowOwnerThresholdEulerPairCoefficient R p r parent ^ 2 *
    postRootCovarianceReciprocalPairEnergy child

@[simp] theorem lowOwnerThresholdEulerParentEnergy_nonneg
    (R p r : ℕ) (parent : ℕ × ℕ) :
    0 ≤ lowOwnerThresholdEulerParentEnergy R p r parent := by
  unfold lowOwnerThresholdEulerParentEnergy
  positivity

/-- **Exact fixed-owner currency conversion.**  The potentially large Euler
coefficient factors out unchanged, and the existing reciprocal child theorem
supplies the entire `multiplicity/r^2` factor. -/
theorem sum_lowOwnerThresholdEulerInheritedChildEnergy_eq
    (R p W r : ℕ) (parent : ℕ × ℕ) :
    (∑ child ∈ postRootCovarianceFixedOwnerChildFiber W parent r,
      lowOwnerThresholdEulerInheritedChildEnergy R p r parent child) =
      (postRootCovarianceFixedOwnerChildMultiplicity W parent r : ℝ) /
          (r : ℝ) ^ 2 *
        lowOwnerThresholdEulerParentEnergy R p r parent := by
  unfold lowOwnerThresholdEulerInheritedChildEnergy
    lowOwnerThresholdEulerParentEnergy
  rw [← Finset.mul_sum]
  rw [sum_postRootCovarianceFixedOwnerChild_energy_eq]
  ring

/-- A genuine chronological next prime is at least three. -/
theorem three_le_of_prime_lt_prime
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    3 ≤ r := by
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- The generic next-owner fibre contracts by `2/9` in the owner-labelled
direct-sum energy.  No reciprocal-prime sum is needed because `r` is not
collapsed with the other owner coordinates. -/
theorem sum_lowOwnerThresholdEulerInheritedChildEnergy_le_two_ninths
    {R p W r : ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ child ∈ postRootCovarianceFixedOwnerChildFiber W parent r,
      lowOwnerThresholdEulerInheritedChildEnergy R p r parent child) ≤
      (2 / 9 : ℝ) * lowOwnerThresholdEulerParentEnergy R p r parent := by
  rw [sum_lowOwnerThresholdEulerInheritedChildEnergy_eq]
  have hr3nat : 3 ≤ r := three_le_of_prime_lt_prime hp hr hpr
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3nat
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hmultNat := postRootCovarianceFixedOwnerChildMultiplicity_le_two W parent r
  have hmult :
      (postRootCovarianceFixedOwnerChildMultiplicity W parent r : ℝ) ≤ 2 := by
    exact_mod_cast hmultNat
  have hratio :
      (postRootCovarianceFixedOwnerChildMultiplicity W parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 2 / 9 := by
    have hsquare : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hdenpos : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    have hmul0 :
        (0 : ℝ) ≤ (postRootCovarianceFixedOwnerChildMultiplicity W parent r : ℝ) := by
      positivity
    calc
      (postRootCovarianceFixedOwnerChildMultiplicity W parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 2 / (r : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmult (le_of_lt hdenpos)
      _ ≤ 2 / 9 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsquare
  exact mul_le_mul_of_nonneg_right hratio
    (lowOwnerThresholdEulerParentEnergy_nonneg R p r parent)

/-- On a companion-clipped next owner there is at most one surviving child, so
owner-labelled energy contracts by `1/9`. -/
theorem sum_lowOwnerThresholdEulerInheritedChildEnergy_le_one_ninth_of_clipped
    {R p W r : ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hclip : W < r * parent.2) :
    (∑ child ∈ postRootCovarianceFixedOwnerChildFiber W parent r,
      lowOwnerThresholdEulerInheritedChildEnergy R p r parent child) ≤
      (1 / 9 : ℝ) * lowOwnerThresholdEulerParentEnergy R p r parent := by
  rw [sum_lowOwnerThresholdEulerInheritedChildEnergy_eq]
  have hr3nat : 3 ≤ r := three_le_of_prime_lt_prime hp hr hpr
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3nat
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hmultNat :=
    postRootCovarianceFixedOwnerChildMultiplicity_le_one_of_clipped
      (W := W) (p := r) (parent := parent) hclip
  have hmult :
      (postRootCovarianceFixedOwnerChildMultiplicity W parent r : ℝ) ≤ 1 := by
    exact_mod_cast hmultNat
  have hratio :
      (postRootCovarianceFixedOwnerChildMultiplicity W parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 1 / 9 := by
    have hsquare : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hdenpos : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    calc
      (postRootCovarianceFixedOwnerChildMultiplicity W parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 1 / (r : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmult (le_of_lt hdenpos)
      _ ≤ 1 / 9 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsquare
  exact mul_le_mul_of_nonneg_right hratio
    (lowOwnerThresholdEulerParentEnergy_nonneg R p r parent)

/-- Direct-sum form: any finite family of genuine next owners contracts
termwise by `2/9`, with each owner retaining its own Euler coefficient. -/
theorem sum_nextOwners_lowOwnerThresholdEulerInheritedChildEnergy_le_two_ninths
    {R p W : ℕ} {owners : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (howners : ∀ r ∈ owners, r.Prime ∧ p < r) :
    (∑ r ∈ owners,
      ∑ child ∈ postRootCovarianceFixedOwnerChildFiber W parent r,
        lowOwnerThresholdEulerInheritedChildEnergy R p r parent child) ≤
      (2 / 9 : ℝ) *
        (∑ r ∈ owners,
          lowOwnerThresholdEulerParentEnergy R p r parent) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hrmem
  rcases howners r hrmem with ⟨hrPrime, hpr⟩
  exact sum_lowOwnerThresholdEulerInheritedChildEnergy_le_two_ninths
    hp hrPrime hpr

end RHLean.Proof
