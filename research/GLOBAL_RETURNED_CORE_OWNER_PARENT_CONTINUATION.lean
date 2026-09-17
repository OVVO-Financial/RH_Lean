import Mathlib
import «research.GLOBAL_RETURNED_CORE_EMITTED_RECIPROCAL_CHARGE»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_CONTINUATION_LEDGER»

/-!
# Named continuation on the duplicate-free owner-parent ledger

The positive reciprocal ledger exposed after the completed incidence gate is
indexed by `(p,sig,r,parent)`, where `parent` is the stripped ordered parent of
an admitted greatest-owner pair.  The existing continuation theorem is stated
one layer earlier, on positive-lag child pairs.

This file closes that carrier mismatch only.  It proves that every parent block
in `lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks` has a positive-lag
witness with the same stripped ordered parent and therefore inherits the
already-compiled named continuation alternatives.

No energy estimate, rank recurrence, AMP bound, or signed-polarization estimate
is introduced here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Stripping and then ordering a specified-prime parent is symmetric in the two
child coordinates. -/
theorem squarefreePairPrimeOrderedParent_comm
    (r m n : ℕ) :
    squarefreePairPrimeOrderedParent r m n =
      squarefreePairPrimeOrderedParent r n m := by
  unfold squarefreePairPrimeOrderedParent
  dsimp only
  let um := squarefreePrimeFamilyParent r m
  let un := squarefreePrimeFamilyParent r n
  by_cases hmn : um < un
  · have hnm : ¬ un < um := Nat.not_lt_of_ge (Nat.le_of_lt hmn)
    simp [um, un, hmn, hnm]
  · by_cases hnm : un < um
    · simp [um, un, hmn, hnm]
    · have heq : um = un := Nat.le_antisymm
        (Nat.le_of_not_gt hnm) (Nat.le_of_not_gt hmn)
      simp [um, un, heq]

/-- Greatest fresh-prime ownership is symmetric in the pair coordinates. -/
theorem isSquarefreePairGreatestFreshPrimeOwner_comm
    {r m n : ℕ}
    (h : IsSquarefreePairGreatestFreshPrimeOwner r m n) :
    IsSquarefreePairGreatestFreshPrimeOwner r n m := by
  unfold IsSquarefreePairGreatestFreshPrimeOwner at h ⊢
  rw [squarefreePairFreshPrimeSet_comm n m]
  exact h

/-- A greatest-owner pair is genuinely off diagonal. -/
theorem ne_of_isSquarefreePairGreatestFreshPrimeOwner
    {r m n : ℕ}
    (h : IsSquarefreePairGreatestFreshPrimeOwner r m n) :
    m ≠ n := by
  intro hmn
  subst n
  have hr := h.1
  simp [squarefreePairFreshPrimeSet] at hr

/-- Every ordered admitted greatest-owner child has a positive-lag orientation
which remains in the same owner fibre and has the same stripped ordered parent. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerPair_has_positive_orientation
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r) :
    ∃ a b : ℕ,
      (a, b) ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r ∧
      squarefreePairPrimeOrderedParent r a b =
        squarefreePairPrimeOrderedParent r m n := by
  rcases mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hmn with
    ⟨hpair, howner⟩
  have hne : m ≠ n := ne_of_isSquarefreePairGreatestFreshPrimeOwner howner
  rcases Finset.mem_product.mp hpair with ⟨hm, hn⟩
  by_cases hlt : m < n
  · refine ⟨m, n, ?_, rfl⟩
    unfold lowOwnerFirstOwnerGreatestOwnerPositivePairFiber
      lowOwnerFirstOwnerGreatestOwnerPairFiber
      lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier
    simp only [Finset.mem_filter]
    exact ⟨⟨⟨hpair, hne⟩, howner⟩, hlt⟩
  · have hrev : n < m := by omega
    have hpair' : (n, m) ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig :=
      Finset.mem_product.mpr ⟨hn, hm⟩
    have howner' : IsSquarefreePairGreatestFreshPrimeOwner r n m :=
      isSquarefreePairGreatestFreshPrimeOwner_comm howner
    refine ⟨n, m, ?_, ?_⟩
    · unfold lowOwnerFirstOwnerGreatestOwnerPositivePairFiber
        lowOwnerFirstOwnerGreatestOwnerPairFiber
        lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier
      simp only [Finset.mem_filter]
      exact ⟨⟨⟨hpair', ne_of_lt hrev⟩, howner'⟩, hrev⟩
    · exact (squarefreePairPrimeOrderedParent_comm r m n).symm

/-- Every duplicate-free `(r,parent)` block has a positive-lag child witness on
exactly the same stripped-parent label. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_has_positiveWitness
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent : parent ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r) :
    ∃ m n : ℕ,
      (m, n) ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r ∧
      squarefreePairPrimeOrderedParent r m n = parent := by
  rcases Finset.mem_image.mp hparent with ⟨mn, hmn, hparentEq⟩
  rcases mn with ⟨m, n⟩
  rcases lowOwnerFirstOwnerAdmittedGreatestOwnerPair_has_positive_orientation
      hmn with ⟨a, b, hab, horient⟩
  refine ⟨a, b, hab, ?_⟩
  rw [horient]
  exact hparentEq

/-- Named continuation predicate on one duplicate-free owner-parent block.
The top-level complete-family alternative is kept explicit because it occurs
before the post-root remainder continuation is entered. -/
def LowOwnerFirstOwnerParentNamedContinuation
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (parent : ℕ × ℕ) : Prop :=
  ∃ m n : ℕ,
    (m, n) ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r ∧
    squarefreePairPrimeOrderedParent r m n = parent ∧
    let W := squareRootEndpoint R
    (m, n) ∈ postRootPrimePhysicalPairUnion W ∨
      SquarefreePairPrimeParentsEqual r (m, n) ∨
      W < r * parent.2 ∨
      parent ∈ postRootPrimePhysicalPairUnion (W / r) ∨
      parent ∈ postRootCovarianceRemainderTerminalPairCarrier (W / r) ∨
      (parent ∈ postRootCovarianceRemainderRecursivePairCarrier (W / r) ∧
        (squarefreePairFreshPrimeSet parent.1 parent.2).card + 1 =
          (squarefreePairFreshPrimeSet m n).card ∧
        ∀ q ∈ squarefreePairFreshPrimeSet parent.1 parent.2, q < r)

/-- **Parent-block continuation has no unnamed residual class.** -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_namedContinuation
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r) :
    LowOwnerFirstOwnerParentNamedContinuation R p sig r parent := by
  rcases lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_has_positiveWitness
      hparent with ⟨m, n, hmn, hparentEq⟩
  refine ⟨m, n, hmn, hparentEq, ?_⟩
  have hcont := lowOwnerFirstOwnerGreatestOwnerPositivePair_namedContinuation
    hp hmn
  dsimp only at hcont ⊢
  rw [hparentEq] at hcont
  exact hcont

end RHLean.Proof
