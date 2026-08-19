import Mathlib
import RHLean.Proof.PrimeCombVisualizationRecurrence

/-!
# Sequential fresh-prime state transition

The prime-comb argument is intrinsically sequential.  A fresh prime is not a
weight in a completed global sum: it is an operation on an existing frame.
This file keeps that operation visible.

For a frozen old prime universe `S`, a fresh coordinate `p`, and cutoff `X`,
the newly created `p`-face is split before any summation is collapsed:

* the empty parent creates the first-hit prime seat `p`, of signed mass `-1`
  when `p <= X`;
* every nonempty reachable old parent creates one fresh child, with the
  opposite Boolean-cube sign;
* unreachable parents create no child below the cutoff.

Thus one fresh-prime step has the exact state form

`new state = old state - reachable proper-parent mass + first-hit boundary mass`.

The second section ties this face-level identity to the literal animation.
There, first-hit proper multiples are score-neutral, square collisions are
killed, and later touches flip.  Consequently the displayed prefix state obeys
an exact one-prime recurrence before any telescoping over primes is attempted.

No estimate and no global averaging statement occurs here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## Fresh-face channels before aggregation -/

/-- Signed contribution of the child created from one old parent face `t` by
adjoining the fresh coordinate `p`.  The child is present only when its product
fits below `X`. -/
def frozenFreshPrimeChildContribution
    (p X : ℕ) (t : Finset ℕ) : ℤ :=
  if p * primeFaceProduct t ≤ X then
    booleanCubeSign (insert p t)
  else
    0

/-- The empty parent is the first-hit prime seat itself.  Its child sign is
`-1`; if the prime is already beyond the cutoff the boundary contribution is
zero. -/
def frozenPrimeUniverseFirstHitBoundaryMass (p X : ℕ) : ℤ :=
  if p ≤ X then -1 else 0

/-- Parentwise first-hit contribution.  Exactly the empty parent carries the
first-hit boundary seat. -/
def frozenFreshPrimeFirstHitContribution
    (p X : ℕ) (t : Finset ℕ) : ℤ :=
  if t = ∅ then frozenPrimeUniverseFirstHitBoundaryMass p X else 0

/-- Signed old-parent contribution on the genuine later-touch channel.  The
parent must be nonempty and its fresh `p`-child must fit below the cutoff. -/
def frozenFreshPrimeReachableParentContribution
    (p X : ℕ) (t : Finset ℕ) : ℤ :=
  if t ≠ ∅ ∧ p * primeFaceProduct t ≤ X then
    booleanCubeSign t
  else
    0

/-- **Local sequential child law.**  For one old parent face, the fresh child
is either the first-hit prime seat (empty parent), or the opposite-signed child
of one reachable nonempty parent.  This is the pointwise statement that must be
preserved before summing over the frame. -/
theorem frozenFreshPrimeChildContribution_eq_firstHit_sub_reachableParent
    {S t : Finset ℕ} {p X : ℕ}
    (hp : p ∉ S) (ht : t ∈ S.powerset) :
    frozenFreshPrimeChildContribution p X t =
      frozenFreshPrimeFirstHitContribution p X t -
        frozenFreshPrimeReachableParentContribution p X t := by
  classical
  have hpt : p ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht hp
  have hsign :
      booleanCubeSign (insert p t) = -booleanCubeSign t := by
    unfold booleanCubeSign
    rw [Finset.card_insert_of_notMem hpt, pow_succ]
    ring
  by_cases ht0 : t = ∅
  · subst t
    by_cases hpX : p ≤ X
    · simp [frozenFreshPrimeChildContribution,
        frozenFreshPrimeFirstHitContribution,
        frozenFreshPrimeReachableParentContribution,
        frozenPrimeUniverseFirstHitBoundaryMass,
        primeFaceProduct, booleanCubeSign, hpX]
    · simp [frozenFreshPrimeChildContribution,
        frozenFreshPrimeFirstHitContribution,
        frozenFreshPrimeReachableParentContribution,
        frozenPrimeUniverseFirstHitBoundaryMass,
        primeFaceProduct, booleanCubeSign, hpX]
  · by_cases hfit : p * primeFaceProduct t ≤ X
    · simp [frozenFreshPrimeChildContribution,
        frozenFreshPrimeFirstHitContribution,
        frozenFreshPrimeReachableParentContribution,
        ht0, hfit, hsign]
    · simp [frozenFreshPrimeChildContribution,
        frozenFreshPrimeFirstHitContribution,
        frozenFreshPrimeReachableParentContribution,
        ht0, hfit]

/-- Total signed mass of the fresh `p`-face, still indexed by the old parents
that generated its children. -/
def frozenPrimeUniverseFreshPrimeFaceMass
    (S : Finset ℕ) (p X : ℕ) : ℤ :=
  ∑ t ∈ S.powerset, frozenFreshPrimeChildContribution p X t

/-- Total signed old-state mass on nonempty parents whose fresh `p`-children
are actually reachable below the cutoff. -/
def frozenPrimeUniverseReachableProperParentMass
    (S : Finset ℕ) (p X : ℕ) : ℤ :=
  ∑ t ∈ S.powerset,
    frozenFreshPrimeReachableParentContribution p X t

/-- The fresh face is exactly the first-hit boundary seat minus the reachable
proper-parent mass.  This is the aggregate corollary of the local child law,
not its replacement. -/
theorem frozenPrimeUniverseFreshPrimeFaceMass_eq_firstHit_sub_reachableParent
    {S : Finset ℕ} {p X : ℕ} (hp : p ∉ S) :
    frozenPrimeUniverseFreshPrimeFaceMass S p X =
      frozenPrimeUniverseFirstHitBoundaryMass p X -
        frozenPrimeUniverseReachableProperParentMass S p X := by
  classical
  unfold frozenPrimeUniverseFreshPrimeFaceMass
    frozenPrimeUniverseReachableProperParentMass
  calc
    (∑ t ∈ S.powerset, frozenFreshPrimeChildContribution p X t) =
        ∑ t ∈ S.powerset,
          (frozenFreshPrimeFirstHitContribution p X t -
            frozenFreshPrimeReachableParentContribution p X t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact
        frozenFreshPrimeChildContribution_eq_firstHit_sub_reachableParent
          hp ht
    _ = (∑ t ∈ S.powerset,
          frozenFreshPrimeFirstHitContribution p X t) -
        ∑ t ∈ S.powerset,
          frozenFreshPrimeReachableParentContribution p X t := by
      rw [Finset.sum_sub_distrib]
    _ = frozenPrimeUniverseFirstHitBoundaryMass p X -
        ∑ t ∈ S.powerset,
          frozenFreshPrimeReachableParentContribution p X t := by
      simp [frozenFreshPrimeFirstHitContribution]

/-- Splitting the inserted powerset into its old face and its fresh `p`-face
without collapsing the fresh face to a lower-cutoff mass. -/
theorem frozenPrimeUniverseMass_insert_eq_old_add_freshPrimeFace
    {S : Finset ℕ} {p X : ℕ} (hp : p ∉ S) :
    frozenPrimeUniverseMass (insert p S) X =
      frozenPrimeUniverseMass S X +
        frozenPrimeUniverseFreshPrimeFaceMass S p X := by
  classical
  rw [frozenPrimeUniverseMass_eq_cutoffSum,
    frozenPrimeUniverseMass_eq_cutoffSum]
  rw [Finset.sum_powerset_insert hp]
  congr 1
  unfold frozenPrimeUniverseFreshPrimeFaceMass
    frozenFreshPrimeChildContribution
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht hp
  have hprod :
      primeFaceProduct (insert p t) = p * primeFaceProduct t := by
    simp [primeFaceProduct, hpt]
  rw [hprod]

/-- **Sequential fresh-prime state transition.**  The state after adjoining
`p` is the old state, minus the signed mass of genuine reachable parents, plus
the first-hit boundary prime seat.

This is deliberately stronger in structure than the collapsed recurrence
`F_(S insert p)(X) = F_S(X) - F_S(X/p)`: it remembers which part is the
first-hit seat and which part comes from opposite-signed parent-child flips. -/
theorem frozenPrimeUniverseMass_insert_eq_old_sub_reachableParent_add_firstHit
    {S : Finset ℕ} {p X : ℕ} (hp : p ∉ S) :
    frozenPrimeUniverseMass (insert p S) X =
      frozenPrimeUniverseMass S X -
        frozenPrimeUniverseReachableProperParentMass S p X +
          frozenPrimeUniverseFirstHitBoundaryMass p X := by
  rw [frozenPrimeUniverseMass_insert_eq_old_add_freshPrimeFace hp,
    frozenPrimeUniverseFreshPrimeFaceMass_eq_firstHit_sub_reachableParent hp]
  ring

/-! ## Literal one-prime animation state -/

/-- Summing the already-proved pointwise operational recurrence gives the
prefix state after one literal animation step. -/
theorem primeCombAnimationStepPrefixMass_eq_insert
    (S : Finset ℕ) (p W : ℕ)
    (hpPrime : p.Prime)
    (hSPrime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    primeCombAnimationStepPrefixMass S p W =
      primeCombFramePrefixMass (insert p S) W := by
  unfold primeCombAnimationStepPrefixMass primeCombFramePrefixMass
  apply Finset.sum_congr rfl
  intro n _hn
  exact primeCombAnimationStepSite_eq_insert S p n hpPrime hSPrime hSlt

/-- **Displayed one-prime state recurrence.**  In the literal animation,
first-hit proper multiples are score-neutral, square collisions remove their
old score, and later touches reverse their old score.  Hence after one fresh
prime arrives,

`new prefix = old prefix - killed old mass - 2 * flipped old mass`.

No prime interval has been summed and no averaging has been performed. -/
theorem primeCombFramePrefixMass_insert_eq_old_sub_channels
    (S : Finset ℕ) (p W : ℕ)
    (hpPrime : p.Prime)
    (hSPrime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    primeCombFramePrefixMass (insert p S) W =
      primeCombFramePrefixMass S W -
        primeCombFrameKillChannelMass S p W -
          2 * primeCombFrameFlipChannelMass S p W := by
  have hdelta := primeCombAnimationStepDelta_eq_channels S p W
  rw [primeCombAnimationStepPrefixMass_eq_insert
    S p W hpPrime hSPrime hSlt] at hdelta
  unfold primeCombAnimationStepDelta at hdelta
  linear_combination hdelta

/-- The preceding theorem specialized to the actual increasing-prime walk.
This is the exact recurrence from the frame immediately before `p` to the frame
immediately after `p`. -/
theorem primeCombFramePrefixMass_primesUpTo_step
    (p W : ℕ) (hp : p.Prime) :
    primeCombFramePrefixMass (primesUpTo p) W =
      primeCombFramePrefixMass (primesUpTo (p - 1)) W -
        primeCombFrameKillChannelMass (primesUpTo (p - 1)) p W -
          2 * primeCombFrameFlipChannelMass (primesUpTo (p - 1)) p W := by
  have hSPrime : ∀ q ∈ primesUpTo (p - 1), q.Prime := by
    intro q hq
    exact prime_of_mem_primesUpTo hq
  have hSlt : ∀ q ∈ primesUpTo (p - 1), q < p := by
    intro q hq
    have hqPred := (mem_primesUpTo.mp hq).2
    have hp2 : 2 ≤ p := hp.two_le
    omega
  rw [primesUpTo_eq_insert_pred_of_prime hp]
  exact primeCombFramePrefixMass_insert_eq_old_sub_channels
    (primesUpTo (p - 1)) p W hp hSPrime hSlt

end RHLean.Proof
