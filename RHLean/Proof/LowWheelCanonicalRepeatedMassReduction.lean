import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedMovableCancellation

/-!
# Repeated canonical downcross mass reduces exactly to frozen first crossings

The repeated-parent carrier is the disjoint union of its movable and frozen
parts.  The movable part has already been cancelled by the opposite face/tail
Othello involution, so the complete repeated signed ledger equals the frozen
ledger before any norm is taken.

The frozen ledger then splits disjointly into the nontrivial-cofactor population
and the terminal `c = 1` population.  No estimate is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Movable and frozen repeated states are disjoint. -/
theorem lowWheelCanonicalRepeatedMovable_disjoint_frozen
    (R : ℕ) :
    Disjoint
      (lowWheelCanonicalRepeatedMovablePart R)
      (lowWheelCanonicalRepeatedFrozenPart R) := by
  rw [Finset.disjoint_left]
  intro y hm hf
  have hmov := (Finset.mem_filter.mp hm).2
  have hshape := (Finset.mem_filter.mp hf).2
  have hrep := (Finset.mem_filter.mp hf).1
  have hcarrier := (Finset.mem_filter.mp hrep).1
  rcases hmov with ⟨q, hqPrime, hpq, hactive⟩
  rcases hactive with hface | htail
  · have hlt := hshape.2 q hface
    omega
  · rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with
      ⟨_ht, hx⟩
    have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
    have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
      simpa [lowWheelTaggedDowncrossPivot] using hshell.1
    have htailOne :
        y.2.2 / lowWheelTaggedDowncrossPivot y = 1 := by
      rw [hshape.1]
      exact Nat.div_self hp.pos
    rw [htailOne] at htail
    exact hqPrime.not_dvd_one htail

/-- Frozen nontrivial-cofactor and terminal populations are disjoint. -/
theorem lowWheelCanonicalRepeatedFrozenCofactor_disjoint_terminal
    (R : ℕ) :
    Disjoint
      (lowWheelCanonicalRepeatedFrozenCofactorPart R)
      (lowWheelCanonicalRepeatedTerminalBoundary R) := by
  rw [Finset.disjoint_left]
  intro y hc ht
  have hcgt := (Finset.mem_filter.mp hc).2
  have hceq := (Finset.mem_filter.mp ht).2
  omega

/-- Signed mass of the frozen repeated-parent population. -/
def lowWheelCanonicalRepeatedFrozenLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedFrozenPart R,
    lowWheelTaggedDowncrossWeight y

/-- Signed mass of the frozen nontrivial-cofactor population. -/
def lowWheelCanonicalRepeatedFrozenCofactorLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R,
    lowWheelTaggedDowncrossWeight y

/-- Signed mass of the terminal `c = 1` repeated population. -/
def lowWheelCanonicalRepeatedTerminalLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalRepeatedTerminalBoundary R,
    lowWheelTaggedDowncrossWeight y

/-- **Exact Othello reduction.**  The entire repeated-parent signed mass is the
frozen first-crossing mass. -/
theorem lowWheelCanonicalDowncrossRepeatedParentLedger_eq_frozen
    (R : ℕ) :
    lowWheelCanonicalDowncrossRepeatedParentLedger R =
      lowWheelCanonicalRepeatedFrozenLedger R := by
  unfold lowWheelCanonicalDowncrossRepeatedParentLedger
    lowWheelCanonicalRepeatedFrozenLedger
  rw [lowWheelCanonicalRepeatedParent_eq_movable_union_frozen R]
  rw [Finset.sum_union (lowWheelCanonicalRepeatedMovable_disjoint_frozen R)]
  rw [sum_lowWheelCanonicalRepeatedMovablePart_eq_zero]
  simp

/-- The frozen mass is exactly nontrivial cofactor plus terminal boundary. -/
theorem lowWheelCanonicalRepeatedFrozenLedger_eq_cofactor_add_terminal
    (R : ℕ) :
    lowWheelCanonicalRepeatedFrozenLedger R =
      lowWheelCanonicalRepeatedFrozenCofactorLedger R +
        lowWheelCanonicalRepeatedTerminalLedger R := by
  unfold lowWheelCanonicalRepeatedFrozenLedger
    lowWheelCanonicalRepeatedFrozenCofactorLedger
    lowWheelCanonicalRepeatedTerminalLedger
  rw [lowWheelCanonicalRepeatedFrozen_eq_cofactor_union_terminal R]
  rw [Finset.sum_union
    (lowWheelCanonicalRepeatedFrozenCofactor_disjoint_terminal R)]

/-- Combined exact reduction from the original canonical downcross ledger to
one root-bounded unique term plus the two frozen first-crossing populations. -/
theorem lowWheelCanonicalDowncrossLedger_eq_unique_add_frozenCofactor_add_terminal
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      lowWheelCanonicalDowncrossUniqueParentLedger R +
        lowWheelCanonicalRepeatedFrozenCofactorLedger R +
          lowWheelCanonicalRepeatedTerminalLedger R := by
  rw [lowWheelCanonicalDowncrossLedger_eq_unique_add_repeated,
    lowWheelCanonicalDowncrossRepeatedParentLedger_eq_frozen,
    lowWheelCanonicalRepeatedFrozenLedger_eq_cofactor_add_terminal]
  ring

end RHLean.Proof
