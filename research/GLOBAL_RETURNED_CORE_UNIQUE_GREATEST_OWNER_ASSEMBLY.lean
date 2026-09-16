import Mathlib
import «research.GLOBAL_RETURNED_CORE_COMPENSATED_CELL_DESCENT_CARRIER»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_FOUR_CORNER_ENERGY_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»

/-!
# Unique-greatest-owner assembly for compensated first-owner cells

This is the combinatorial guardrail for the final signed Fubini.

The local `2/9` theorem is owner-labelled.  Therefore every off-diagonal
admitted pair must be assigned to exactly one next owner before any energy
estimate is summed.  The owner used here is the greatest remaining fresh prime.

A second duplication has to be excluded as well: two sibling children can have
the same greatest owner and the same stripped parent.  The local fixed-parent
`2/9` block must therefore be summed once per `(owner,stripped-parent)` block,
not once per child.  The parent-block carrier below is a `Finset.image`, so that
quotienting is literal and duplicate-free.

No sum over owner-labelled parent energies is collapsed to a single cell square.
No clipped mass is estimated here: clipped mass remains inside the Dirichlet
polarization and only inherited reciprocal atoms may use the local `1/9` bound.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Greatest ownership is genuinely single-valued. -/
theorem isSquarefreePairGreatestFreshPrimeOwner_unique
    {r s m n : ℕ}
    (hr : IsSquarefreePairGreatestFreshPrimeOwner r m n)
    (hs : IsSquarefreePairGreatestFreshPrimeOwner s m n) :
    r = s := by
  have hrs : r ≤ s := hs.2 r hr.1
  have hsr : s ≤ r := hr.2 s hs.1
  omega

/-- Ordered admitted pairs in one compensated first-owner cell whose unique
next owner is `r`.  Diagonal pairs occur in no such fibre. -/
def lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerAdmittedPairCarrier R p sig).filter fun mn =>
    IsSquarefreePairGreatestFreshPrimeOwner r mn.1 mn.2

@[simp] theorem mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber
    {R p r m n : ℕ} {sig : Finset ℕ} :
    (m, n) ∈ lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r ↔
      (m, n) ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig ∧
        IsSquarefreePairGreatestFreshPrimeOwner r m n := by
  simp [lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber]

/-- Distinct greatest-owner fibres are disjoint.  This is the formal protection
against paying the same pair's local contraction twice under two owners. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber_disjoint
    {R p r s : ℕ} {sig : Finset ℕ} (hrs : r ≠ s) :
    Disjoint
      (lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r)
      (lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig s) := by
  rw [Finset.disjoint_left]
  intro mn hrm hsm
  have hrOwner :=
    (mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hrm).2
  have hsOwner :=
    (mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hsm).2
  exact hrs (isSquarefreePairGreatestFreshPrimeOwner_unique hrOwner hsOwner)

/-- The greatest fresh coordinate of one nontrivial admitted pair exists and is
an actual physical prime. -/
theorem lowOwnerFirstOwnerAdmittedPair_exists_greatestOwner
    {R p m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig)
    (hmne : m ≠ n) :
    ∃ r ∈ primesUpTo (squareRootEndpoint R),
      p < r ∧
      (m, n) ∈ lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r := by
  rcases Finset.mem_product.mp hmn with ⟨hmAd, hnAd⟩
  have hmCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hmAd).1).1
  have hnCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hnAd).1).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, _hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, _hnPos⟩
  have hne : (squarefreePairFreshPrimeSet m n).Nonempty :=
    squarefreePairFreshPrimeSet_nonempty hmSq hnSq hmne
  let r := (squarefreePairFreshPrimeSet m n).max' hne
  have hrFresh : r ∈ squarefreePairFreshPrimeSet m n := by
    dsimp [r]
    exact Finset.max'_mem _ hne
  have hrMax : ∀ q ∈ squarefreePairFreshPrimeSet m n, q ≤ r := by
    intro q hq
    dsimp [r]
    exact Finset.le_max' _ q hq
  have hrOwner : IsSquarefreePairGreatestFreshPrimeOwner r m n :=
    ⟨hrFresh, hrMax⟩
  rcases freshPrime_of_nonzeroPhysicalPair hmCar hnCar hrFresh with
    ⟨hrPrime, hrX⟩
  have hpr : p < r :=
    lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner hp hmAd hnAd hrFresh
  refine ⟨r, mem_primesUpTo.mpr ⟨hrPrime, hrX⟩, hpr, ?_⟩
  exact mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mpr
    ⟨hmn, hrOwner⟩

/-- Existence plus uniqueness in the exact form needed by finite Fubini: every
nontrivial admitted pair has exactly one physical next-owner label. -/
theorem lowOwnerFirstOwnerAdmittedPair_existsUnique_greatestOwner
    {R p m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig)
    (hmne : m ≠ n) :
    ∃! r : ℕ,
      r ∈ primesUpTo (squareRootEndpoint R) ∧ p < r ∧
        (m, n) ∈ lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r := by
  rcases lowOwnerFirstOwnerAdmittedPair_exists_greatestOwner hp hmn hmne with
    ⟨r, hrPrime, hpr, hrFiber⟩
  refine ⟨r, ⟨hrPrime, hpr, hrFiber⟩, ?_⟩
  intro s hs
  have hrOwner :=
    (mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hrFiber).2
  have hsOwner :=
    (mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hs.2.2).2
  exact isSquarefreePairGreatestFreshPrimeOwner_unique hsOwner hrOwner

/-- One owner-labelled contraction block is indexed by the stripped ordered
parent, not by one of its children.  `Finset.image` quotients sibling children
with the same `(r,parent)` to a single block. -/
def lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r).image fun mn =>
    squarefreePairPrimeOrderedParent r mn.1 mn.2

/-- Every owned child lands in exactly its stripped-parent block. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwner_strippedParent_mem_blocks
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r) :
    squarefreePairPrimeOrderedParent r m n ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r := by
  unfold lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks
  exact Finset.mem_image.mpr ⟨(m, n), hmn, rfl⟩

/-- A nonempty owner-parent block certifies that this owner is genuinely larger
than the current first owner. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_owner_gt
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r) :
    p < r := by
  rcases Finset.mem_image.mp hparent with ⟨mn, hmn, _hparentEq⟩
  rcases mn with ⟨m, n⟩
  rcases mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hmn with
    ⟨hpair, howner⟩
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  exact lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner
    hp hmAd hnAd howner.1

/-- Owner-labelled recursive inheritance, summed once per unique
`(r,stripped-parent)` block.  The owner coordinate is retained on both sides. -/
def lowOwnerFirstOwnerRecursiveInheritedEnergy
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ r ∈ primesUpTo (squareRootEndpoint R),
    ∑ parent ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r,
      ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        lowOwnerThresholdEulerInheritedGreatestChildEnergy
          R p r parent child

/-- The matching owner-labelled parent energy.  Deliberately not identified
with a single p-cell square. -/
def lowOwnerFirstOwnerRecursiveOwnerParentEnergy
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ r ∈ primesUpTo (squareRootEndpoint R),
    ∑ parent ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r,
      lowOwnerThresholdEulerParentEnergy R p r parent

/-- **Cell-level direct-sum contraction with no owner collapse.**

This is the strongest legal global use of the local `2/9` fact at this stage:
every `(r,parent)` block is counted exactly once, and the right-hand side stays
as the sum of owner-labelled parent energies. -/
theorem lowOwnerFirstOwnerRecursiveInheritedEnergy_le_two_ninths_ownerParentEnergy
    {R p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    lowOwnerFirstOwnerRecursiveInheritedEnergy R p sig ≤
      (2 / 9 : ℝ) * lowOwnerFirstOwnerRecursiveOwnerParentEnergy R p sig := by
  unfold lowOwnerFirstOwnerRecursiveInheritedEnergy
    lowOwnerFirstOwnerRecursiveOwnerParentEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hrMem
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro parent hparent
  have hrPrime : r.Prime := (mem_primesUpTo.mp hrMem).1
  have hpr : p < r :=
    lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_owner_gt hp hparent
  exact sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths
    (R := R) (p := p) (r := r) (parent := parent) hp hrPrime hpr

/-- Legal assembly target.  The clipped contribution is not a separate
nonnegative budget: it remains inside `lowOwnerFirstOwnerSignedCellTelescope`.
The only positive recursive term exposed to contraction is inherited reciprocal
energy already partitioned by unique `(owner,stripped-parent)` blocks. -/
def LowOwnerUniqueOwnerSignedFubiniAssembly (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) ≤
      C * (R : ℝ) ^ 2 * K

end RHLean.Proof
