import Mathlib
import RHLean.Arithmetic.SquareBlockParityPopulation
import RHLean.Proof.CanonicalSignedParent

/-!
# One-block invariant architecture (issue #146)

This module makes the governing finite induction architecture explicit.

The completed prefix is represented by the exact recursive sum of square-block
increments. The next block is not treated as independent: its nonzero
squarefree states must be inherited from canonical full-factorization parents in
the already-frozen carrier. The quantitative estimate is kept as an explicit
field of the invariant rather than silently assumed.

Nothing in this module claims the open quantitative preservation theorem. It
constructs the exact structural implication:

```text
OneBlockInvariant N + OneBlockExtensionData N -> OneBlockInvariant (N+1).
```

It also isolates the sole remaining theorem as the existence of valid extension
data at every finite stage.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Old frozen parent cutoff used by issue #146 for target square block `a`. -/
def oldParentCutoff (a : ℕ) : ℕ :=
  (a ^ 2 - 1) / 2

/-- Full-factorization inheritance statement for one square block.

Every squarefree nontrivial child in block `a` has its canonical parent in the
old carrier, and the certified complete-state edge flips both Möbius sign and
factorization parity. -/
def PriorCarrierDeterminesBlock (a : ℕ) : Prop :=
  ∀ n : ℕ, n ∈ squareBlockInterval a → Squarefree n → 1 < n →
    canonicalCofactor n ≤ oldParentCutoff a ∧
    μ n = -μ (canonicalCofactor n) ∧
    (FullFactorizationState.canonical n).omega =
      (FullFactorizationState.canonical (canonicalCofactor n)).omega + 1

/-- Once the elementary parent-cutoff estimate is available, all sign and parity
parts of one-block inheritance follow from the merged full-factorization bridge. -/
theorem priorCarrierDeterminesBlock_of_parent_bound
    {a : ℕ}
    (hbound : ∀ n : ℕ, n ∈ squareBlockInterval a → Squarefree n → 1 < n →
      canonicalCofactor n ≤ oldParentCutoff a) :
    PriorCarrierDeterminesBlock a := by
  intro n hn hsq hn1
  exact ⟨hbound n hn hsq hn1,
    canonicalSignedParent_moebius hsq hn1,
    canonicalSignedParent_omega_succ hsq hn1⟩

/-- Exact cumulative discrepancy after the first `N` square blocks.

The recursive definition makes the one-block recurrence definitional and keeps
all reasoning finite. -/
def completedBlockPrefixSum : ℕ → ℤ
  | 0 => 0
  | N + 1 => completedBlockPrefixSum N + squareBlockMoebius (N + 1)

@[simp] theorem completedBlockPrefixSum_zero : completedBlockPrefixSum 0 = 0 := rfl

@[simp] theorem completedBlockPrefixSum_succ (N : ℕ) :
    completedBlockPrefixSum (N + 1) =
      completedBlockPrefixSum N + squareBlockMoebius (N + 1) := rfl

/-- The finite state that issue #146 requires at stage `N`.

It retains the next-block parent inheritance, an exact signed frontier value for
the completed prefix, and a quantitative energy budget. The budget is genuine
data, not an asserted theorem hidden behind notation. -/
structure OneBlockInvariant (N : ℕ) where
  nextBlockInherited : PriorCarrierDeterminesBlock (N + 1)
  signedFrontier : ℤ
  signedFrontier_eq_prefix : signedFrontier = completedBlockPrefixSum N
  energyBudget : ℕ
  energy_control : signedFrontier ^ 2 ≤ (energyBudget : ℤ)

/-- Exact data needed to extend a valid stage by one finite block.

The open mathematics sits in constructing this data uniformly with a useful
next budget. The structural update itself is elementary. -/
structure OneBlockExtensionData (N : ℕ) (hN : OneBlockInvariant N) where
  followingBlockInherited : PriorCarrierDeterminesBlock (N + 2)
  nextSignedFrontier : ℤ
  frontier_update :
    nextSignedFrontier = hN.signedFrontier + squareBlockMoebius (N + 1)
  nextEnergyBudget : ℕ
  next_energy_control : nextSignedFrontier ^ 2 ≤ (nextEnergyBudget : ℤ)

/-- The exact one-block extension constructor demanded by issue #146. -/
def oneBlockInvariant_succ
    {N : ℕ} (hN : OneBlockInvariant N)
    (hstep : OneBlockExtensionData N hN) :
    OneBlockInvariant (N + 1) where
  nextBlockInherited := hstep.followingBlockInherited
  signedFrontier := hstep.nextSignedFrontier
  signedFrontier_eq_prefix := by
    calc
      hstep.nextSignedFrontier =
          hN.signedFrontier + squareBlockMoebius (N + 1) := hstep.frontier_update
      _ = completedBlockPrefixSum N + squareBlockMoebius (N + 1) := by
          rw [hN.signedFrontier_eq_prefix]
      _ = completedBlockPrefixSum (N + 1) := by
          rw [completedBlockPrefixSum_succ]
  energyBudget := hstep.nextEnergyBudget
  energy_control := hstep.next_energy_control

/-- Uniform one-block law: every valid finite stage admits valid extension data. -/
def OneBlockExtensionLaw : Prop :=
  ∀ N : ℕ, ∀ hN : OneBlockInvariant N,
    Nonempty (OneBlockExtensionData N hN)

/-- A base invariant plus the uniform one-block law yields every finite stage by
ordinary induction. No completed infinity is used. -/
theorem oneBlockInvariant_all
    (h0 : OneBlockInvariant 0)
    (hlaw : OneBlockExtensionLaw) :
    ∀ N : ℕ, Nonempty (OneBlockInvariant N) := by
  intro N
  induction N with
  | zero => exact ⟨h0⟩
  | succ N ih =>
      obtain ⟨hN⟩ := ih
      obtain ⟨hstep⟩ := hlaw N hN
      exact ⟨oneBlockInvariant_succ hN hstep⟩

/-- The precise unresolved theorem package for issue #146.

The structural induction is complete above. Closing this statement requires the
uniform parent-cutoff theorem and, critically, a quantitatively controlled
extension datum at every stage. -/
def OneBlockInvariantClosureStatement : Prop :=
  Nonempty (OneBlockInvariant 0) ∧ OneBlockExtensionLaw

end RHLean.Proof
