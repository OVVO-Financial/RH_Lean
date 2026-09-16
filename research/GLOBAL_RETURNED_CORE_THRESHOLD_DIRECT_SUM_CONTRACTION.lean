import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_RECIPROCAL_INTERTWINING»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONGESTION»

/-!
# Owner-labelled direct-sum contraction on the greatest-owner graph

The global signed assembly chooses the unique greatest remaining fresh owner.
Accordingly the local contraction must live on the same reversed owner graph,
not on the older least-owner child fibres.

For a fixed stripped parent and fixed greatest owner `r`, the Euler coefficient
is retained unchanged while the reciprocal pair energy of every literal child
is exactly `1/r^2` times the parent energy.  Keeping `r` as an explicit direct-
sum coordinate gives the termwise contraction without a prime-sum congestion
tax.

For a genuine next owner `p < r`, primality gives `r >= 3`.  The two-candidate
greatest-owner fibre therefore costs at most `2/9`; under the companion-clipped
condition only one candidate survives and the factor is at most `1/9`.

No owner labels are collapsed in this file.
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

/-- A greatest-owner child inherits the same stripped-parent Euler coefficient. -/
def lowOwnerThresholdEulerInheritedGreatestChildEnergy
    (R p r : ℕ) (parent child : ℕ × ℕ) : ℝ :=
  lowOwnerThresholdEulerPairCoefficient R p r parent ^ 2 *
    postRootCovarianceReciprocalPairEnergy child

@[simp] theorem lowOwnerThresholdEulerParentEnergy_nonneg
    (R p r : ℕ) (parent : ℕ × ℕ) :
    0 ≤ lowOwnerThresholdEulerParentEnergy R p r parent := by
  unfold lowOwnerThresholdEulerParentEnergy
  exact mul_nonneg
    (sq_nonneg (lowOwnerThresholdEulerPairCoefficient R p r parent))
    (postRootCovarianceReciprocalPairEnergy_nonneg parent)

/-- **Exact fixed-owner currency conversion on the greatest-owner graph.** -/
theorem sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_eq
    {R p r : ℕ} (hr : r.Prime) (parent : ℕ × ℕ) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy R p r parent child) =
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 *
        lowOwnerThresholdEulerParentEnergy R p r parent := by
  unfold lowOwnerThresholdEulerInheritedGreatestChildEnergy
    lowOwnerThresholdEulerParentEnergy
  rw [← Finset.mul_sum]
  rw [sum_lowOwnerGreatestOwnerFixedParentChild_energy_eq hr]
  ring

/-- A genuine chronological next prime is at least three. -/
theorem three_le_of_prime_lt_prime
    {p r : ℕ} (hp : p.Prime) (hpr : p < r) :
    3 ≤ r := by
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- The fixed-r greatest-owner fibre contracts by `2/9` in owner-labelled
energy. -/
theorem sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy R p r parent child) ≤
      (2 / 9 : ℝ) * lowOwnerThresholdEulerParentEnergy R p r parent := by
  rw [sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_eq hr]
  have hr3nat : 3 ≤ r := three_le_of_prime_lt_prime hp hpr
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3nat
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hmultNat :=
    lowOwnerGreatestOwnerFixedParentChildMultiplicity_le_two R parent r
  have hmult :
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) ≤ 2 := by
    exact_mod_cast hmultNat
  have hratio :
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 2 / 9 := by
    have hsquare : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hdenpos : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    calc
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 2 / (r : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmult (le_of_lt hdenpos)
      _ ≤ 2 / 9 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsquare
  exact mul_le_mul_of_nonneg_right hratio
    (lowOwnerThresholdEulerParentEnergy_nonneg R p r parent)

/-- On a companion-clipped greatest-owner fibre there is at most one surviving
child, hence `1/9`.  This theorem is only for inherited reciprocal atoms that
have already left the Dirichlet polarization. -/
theorem sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_one_ninth_of_clipped
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hclip : squareRootEndpoint R < r * parent.2) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy R p r parent child) ≤
      (1 / 9 : ℝ) * lowOwnerThresholdEulerParentEnergy R p r parent := by
  rw [sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_eq hr]
  have hr3nat : 3 ≤ r := three_le_of_prime_lt_prime hp hpr
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3nat
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hmultNat :=
    lowOwnerGreatestOwnerFixedParentChildFiber_card_le_one_of_clipped
      (R := R) (p := r) (parent := parent) hclip
  have hmult :
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) ≤ 1 := by
    unfold lowOwnerGreatestOwnerFixedParentChildMultiplicity
    exact_mod_cast hmultNat
  have hratio :
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 1 / 9 := by
    have hsquare : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hdenpos : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    calc
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 1 / (r : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmult (le_of_lt hdenpos)
      _ ≤ 1 / 9 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsquare
  exact mul_le_mul_of_nonneg_right hratio
    (lowOwnerThresholdEulerParentEnergy_nonneg R p r parent)

/-- Direct-sum form.  The right side deliberately remains a sum of owner-
labelled parent energies; it is not collapsed to one p-cell square. -/
theorem sum_nextOwners_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths
    {R p : ℕ} {owners : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (howners : ∀ r ∈ owners, r.Prime ∧ p < r) :
    (∑ r ∈ owners,
      ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        lowOwnerThresholdEulerInheritedGreatestChildEnergy R p r parent child) ≤
      (2 / 9 : ℝ) *
        (∑ r ∈ owners,
          lowOwnerThresholdEulerParentEnergy R p r parent) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hrmem
  rcases howners r hrmem with ⟨hrPrime, hpr⟩
  exact sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths
    hp hrPrime hpr

end RHLean.Proof