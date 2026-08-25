import Mathlib
import RHLean.Proof.SquareRootLowPrimeSequentialDissipation

/-!
# Global ownership for the low-prime dissipation obstruction

`SquareRootLowPrimeSequentialDissipation` isolates, at every fresh prime, a
forced negative natural deletion and one signed proper-parent obstruction.  The
present module makes the ownership assertion literal at the level of response
atoms and records the exact running-state sign convention used by the energy
diagnostic.

A response atom remembers whether it belongs to the born or high channel and
its cofactor.  Its owner is not chosen after the fact: it is the cofactor's
canonical largest prime.  Hence the owned atom sets for distinct fresh primes
are pairwise disjoint, even though one cofactor may legitimately occur once in
each of the two response channels at its unique owner.

No absolute value, analytic estimate, covariance normalization, or endpoint
reconstruction is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The two response channels retained together in one fresh-prime increment. -/
inductive SquareRootLowPrimeResponseChannel
  | born
  | high
  deriving DecidableEq

/-- A concrete response atom consists of its channel and its arithmetic
cofactor. -/
abbrev SquareRootLowPrimeResponseAtom :=
  SquareRootLowPrimeResponseChannel × ℕ

/-- Proper-parent response atoms owned by the fresh prime `p`.  Channel tags
keep the two legitimate appearances of one cofactor distinct, while the
cofactor itself determines the unique prime owner. -/
def squareRootLowPrimeOwnedProperParentAtoms
    (R p : ℕ) : Finset SquareRootLowPrimeResponseAtom :=
  (squareRootLowPrimeProperBornCofactors R p).image
      (fun c => (SquareRootLowPrimeResponseChannel.born, c)) ∪
    (squareRootLowPrimeProperHighCofactors R p).image
      (fun c => (SquareRootLowPrimeResponseChannel.high, c))

/-- The canonical owner of a response atom is the largest prime factor of its
cofactor. -/
def squareRootLowPrimeResponseAtomOwner
    (x : SquareRootLowPrimeResponseAtom) : ℕ :=
  canonicalLargestPrimeFactor x.2

/-- Membership in an owned atom set forces the displayed prime to be the
canonical owner.  This is a source property, not a residual definition. -/
theorem squareRootLowPrimeResponseAtomOwner_eq_of_mem
    {R p : ℕ} {x : SquareRootLowPrimeResponseAtom}
    (hx : x ∈ squareRootLowPrimeOwnedProperParentAtoms R p) :
    squareRootLowPrimeResponseAtomOwner x = p := by
  unfold squareRootLowPrimeOwnedProperParentAtoms at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_image.mp hx with ⟨c, hc, rfl⟩
    unfold squareRootLowPrimeResponseAtomOwner
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp hc).2).2
  · rcases Finset.mem_image.mp hx with ⟨c, hc, rfl⟩
    unfold squareRootLowPrimeResponseAtomOwner
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp hc).2).2

/-- **Global ownership.**  Distinct fresh primes own disjoint sets of concrete
proper-parent response atoms.  Thus no later absolute-value argument is allowed
to charge one atom independently to several primes. -/
theorem squareRootLowPrimeOwnedProperParentAtoms_disjoint
    {R p q : ℕ} (hpq : p ≠ q) :
    Disjoint (squareRootLowPrimeOwnedProperParentAtoms R p)
      (squareRootLowPrimeOwnedProperParentAtoms R q) := by
  rw [Finset.disjoint_left]
  intro x hxp hxq
  apply hpq
  exact (squareRootLowPrimeResponseAtomOwner_eq_of_mem hxp).symm.trans
    (squareRootLowPrimeResponseAtomOwner_eq_of_mem hxq)

/-- The accepted sign convention: the fresh response increment is exactly
`T(p-1)-T(p)` for the running imbalance `T=1-S`. -/
theorem squareRootLowPrimeRunningImbalance_step_eq_freshIncrement
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootLowPrimeRunningImbalance R K j (p - 1) -
        squareRootLowPrimeRunningImbalance R K j p =
      squareRootLowPrimeFreshIncrement R K j p := by
  unfold squareRootLowPrimeRunningImbalance
  calc
    (1 - squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1)) -
        (1 - squareRootBornPostTailRunningLowPrimeResponse R K j p) =
      squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) := by
          ring
    _ = squareRootLowPrimeFreshIncrement R K j p :=
      squareRootBornPostTailRunningLowPrimeResponse_step_eq_lowPrimeFreshIncrement
        R K j p hp

/-- Exact energy identity in the running-state convention.  No sign choice is
left implicit: `Delta_p = T(p-1)-T(p)`. -/
theorem squareRootLowPrimeRunningEnergy_step
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootLowPrimeRunningImbalance R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalance R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          squareRootLowPrimeFreshIncrement R K j p -
        squareRootLowPrimeFreshIncrement R K j p ^ 2 := by
  have hstep :=
    squareRootLowPrimeRunningImbalance_step_eq_freshIncrement R K j p hp
  calc
    squareRootLowPrimeRunningImbalance R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalance R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          (squareRootLowPrimeRunningImbalance R K j (p - 1) -
            squareRootLowPrimeRunningImbalance R K j p) -
        (squareRootLowPrimeRunningImbalance R K j (p - 1) -
          squareRootLowPrimeRunningImbalance R K j p) ^ 2 := by
            ring
    _ = 2 * squareRootLowPrimeRunningImbalance R K j (p - 1) *
          squareRootLowPrimeFreshIncrement R K j p -
        squareRootLowPrimeFreshIncrement R K j p ^ 2 := by
          rw [hstep]

/-- The one-sided decomposition written directly in the accepted running-state
sign convention. -/
theorem squareRootLowPrimeSequentialDissipation_runningImbalance
    {R K j p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    (squareRootLowPrimeRunningImbalance R K j (p - 1) -
        squareRootLowPrimeRunningImbalance R K j p =
      -((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
        squareRootLowPrimeProperParentBadMass R K j p) ∧
      (0 : ℤ) ≤ (squareRootLowPrimePrimeDeletionCount R K j p : ℤ) := by
  constructor
  · rw [squareRootLowPrimeRunningImbalance_step_eq_freshIncrement R K j p hp]
    exact squareRootLowPrimeFreshIncrement_eq_neg_deletion_add_badMass
      hR hp hpR
  · exact squareRootLowPrimePrimeDeletionCount_nonneg R K j p

/-- Actual fresh primes in an arithmetic interval. -/
def squareRootLowPrimeFreshPrimeSet (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter Nat.Prime

/-- Total forced deletion count over a prime interval. -/
def squareRootLowPrimeGlobalDeletionCount
    (R K j L U : ℕ) : ℕ :=
  ∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
    squareRootLowPrimePrimeDeletionCount R K j p

/-- **Global one-sided decomposition.**  Summing actual fresh-prime steps does
not create a new defect at every prime: the negative terms form one natural
deletion count and the obstruction is the already-defined globally owned
proper-parent mass. -/
theorem squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_ownedMass
    {R K j L U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        squareRootLowPrimeFreshIncrement R K j p) =
      -((squareRootLowPrimeGlobalDeletionCount R K j L U : ℕ) : ℂ) +
        squareRootLowPrimeGlobalProperParentBadMass R K j L U := by
  unfold squareRootLowPrimeGlobalDeletionCount
    squareRootLowPrimeGlobalProperParentBadMass
    squareRootLowPrimeFreshPrimeSet
  calc
    (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
        squareRootLowPrimeFreshIncrement R K j p) =
      ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
        (-((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
          squareRootLowPrimeProperParentBadMass R K j p) := by
            apply Finset.sum_congr rfl
            intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hpIoc, hpPrime⟩
            exact squareRootLowPrimeFreshIncrement_eq_neg_deletion_add_badMass
              hR hpPrime ((Finset.mem_Ioc.mp hpIoc).2.trans_lt hUR)
    _ = (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          -((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ)) +
        ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          squareRootLowPrimeProperParentBadMass R K j p := by
            rw [Finset.sum_add_distrib]
    _ = -(∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          ((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ)) +
        ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          squareRootLowPrimeProperParentBadMass R K j p := by
            rw [Finset.sum_neg_distrib]
    _ = -((∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
        ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
          squareRootLowPrimeProperParentBadMass R K j p := by
            push_cast
            rfl

/-- The same global decomposition expressed as the sum of accepted running
imbalance steps. -/
theorem squareRootLowPrimeRunningImbalance_step_sum_eq_neg_globalDeletion_add_ownedMass
    {R K j L U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        (squareRootLowPrimeRunningImbalance R K j (p - 1) -
          squareRootLowPrimeRunningImbalance R K j p)) =
      -((squareRootLowPrimeGlobalDeletionCount R K j L U : ℕ) : ℂ) +
        squareRootLowPrimeGlobalProperParentBadMass R K j L U := by
  calc
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        (squareRootLowPrimeRunningImbalance R K j (p - 1) -
          squareRootLowPrimeRunningImbalance R K j p)) =
      ∑ p ∈ squareRootLowPrimeFreshPrimeSet L U,
        squareRootLowPrimeFreshIncrement R K j p := by
          apply Finset.sum_congr rfl
          intro p hp
          exact squareRootLowPrimeRunningImbalance_step_eq_freshIncrement
            R K j p (Finset.mem_filter.mp hp).2
    _ = -((squareRootLowPrimeGlobalDeletionCount R K j L U : ℕ) : ℂ) +
        squareRootLowPrimeGlobalProperParentBadMass R K j L U :=
      squareRootLowPrimeFreshIncrement_sum_eq_neg_globalDeletion_add_ownedMass
        hR hUR

end RHLean.Proof
