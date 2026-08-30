import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedMovableCancellation

/-!
# The full canonical downcross ledger reduces to frozen first crossings

The local movable/frozen dichotomy applies to every canonical downcross state.
A movable state can never belong to the unique-parent population: the lifted
face/tail toggle is a distinct state of the same carrier with the same root-side
parent.  Hence every movable state lies in the repeated movable population and
cancels under the canonical opposite involution.

Therefore the *entire* canonical downcross ledger equals the signed mass of the
single frozen first-crossing carrier.  This removes the unique/repeated split
from the subsequent top/bottom argument entirely.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Frozen first-crossing states in the complete tagged downcross carrier. -/
def lowWheelCanonicalFrozenDowncrossPart (R : ℕ) :
    Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalTaggedDowncrossCarrier R).filter
    LowWheelDowncrossFrozenShape

/-- Every movable downcross occurrence is automatically repeated: its legal
face/tail toggle is a distinct occurrence with exactly the same parent. -/
theorem lowWheelCanonicalMovable_mem_repeated
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalTaggedDowncrossCarrier R)
    (hmov : ∃ q, LowWheelDowncrossMovablePrime y q) :
    y ∈ lowWheelCanonicalDowncrossRepeatedParentPart R := by
  rcases hmov with ⟨q, hq⟩
  have hmate := lowWheelTaggedDowncrossFaceTailToggleAt_mem hy hq
  have hparent := lowWheelTaggedDowncrossFaceTailToggleAt_parent hy hq
  have hne := lowWheelTaggedDowncrossFaceTailToggleAt_ne hy hq
  apply Finset.mem_filter.mpr
  refine ⟨hy, ?_⟩
  intro huniq
  have heq : lowWheelTaggedDowncrossFaceTailToggleAt q y = y :=
    huniq _ hmate hparent
  exact hne heq

/-- The complete tagged downcross carrier is exactly movable-repeated plus
frozen. -/
theorem lowWheelCanonicalTaggedDowncrossCarrier_eq_movable_union_frozen
    (R : ℕ) :
    lowWheelCanonicalTaggedDowncrossCarrier R =
      lowWheelCanonicalRepeatedMovablePart R ∪
        lowWheelCanonicalFrozenDowncrossPart R := by
  ext y
  constructor
  · intro hy
    rcases lowWheelCanonicalDowncross_movable_or_frozen hy with hmov | hfrozen
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr
          ⟨lowWheelCanonicalMovable_mem_repeated hy hmov, hmov⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hy, hfrozen⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hm | hf
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
    · exact (Finset.mem_filter.mp hf).1

/-- Movable and frozen parts are disjoint. -/
theorem lowWheelCanonicalRepeatedMovable_disjoint_frozenDowncross
    (R : ℕ) :
    Disjoint
      (lowWheelCanonicalRepeatedMovablePart R)
      (lowWheelCanonicalFrozenDowncrossPart R) := by
  rw [Finset.disjoint_left]
  intro y hm hf
  have hmov := (Finset.mem_filter.mp hm).2
  have hshape := (Finset.mem_filter.mp hf).2
  rcases hmov with ⟨q, hqPrime, hpq, hactive⟩
  rcases hactive with hface | htail
  · exact (Nat.not_lt_of_ge hpq) (hshape.2 q hface)
  · have hcarrier := (Finset.mem_filter.mp hf).1
    rcases mem_lowWheelCanonicalTaggedDowncrossCarrier.mp hcarrier with
      ⟨_ht, hx⟩
    have hshell := lowWheelCanonicalDowncrossPart_adjacent_shell hx
    have hp : (lowWheelTaggedDowncrossPivot y).Prime := by
      simpa [lowWheelTaggedDowncrossPivot] using hshell.1
    have hquot : y.2.2 / lowWheelTaggedDowncrossPivot y = 1 := by
      rw [hshape.1]
      exact Nat.div_self hp.pos
    rw [hquot] at htail
    exact hqPrime.not_dvd_one htail

/-- Signed mass of all frozen first-crossing states. -/
def lowWheelCanonicalFrozenDowncrossLedger (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelCanonicalFrozenDowncrossPart R,
    lowWheelTaggedDowncrossWeight y

/-- **Full finite Othello reduction.**  Every non-frozen downcross occurrence
cancels exactly, so the complete tagged residual is the frozen ledger. -/
theorem lowWheelCanonicalTaggedDowncrossLedger_eq_frozen
    (R : ℕ) :
    lowWheelCanonicalTaggedDowncrossLedger R =
      lowWheelCanonicalFrozenDowncrossLedger R := by
  unfold lowWheelCanonicalTaggedDowncrossLedger
    lowWheelCanonicalFrozenDowncrossLedger
  rw [lowWheelCanonicalTaggedDowncrossCarrier_eq_movable_union_frozen R]
  rw [Finset.sum_union
    (lowWheelCanonicalRepeatedMovable_disjoint_frozenDowncross R)]
  rw [sum_lowWheelCanonicalRepeatedMovablePart_eq_zero]
  simp

/-- The original nested canonical downcross ledger has the same exact frozen
normal form. -/
theorem lowWheelCanonicalDowncrossLedger_eq_frozen
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      lowWheelCanonicalFrozenDowncrossLedger R := by
  rw [lowWheelCanonicalDowncrossLedger_eq_tagged,
    lowWheelCanonicalTaggedDowncrossLedger_eq_frozen]

end RHLean.Proof
