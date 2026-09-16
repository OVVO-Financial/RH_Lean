import Mathlib
import «research.GLOBAL_RETURNED_CORE_TWO_PRIME_DIRICHLET_LOCAL_CONFLUENCE»
import «research.COVARIANCE_RECIPROCAL_OWNER_CONGESTION»

/-!
# Symmetric two-prime completed block Fubini

At block level the exact object is not a product of coarse one-step bounds.  For
a fixed parent and two owner primes `r,s`, the completed two-owner cube has four
literal terminal mixed insertions, corresponding to assigning each prime to one
of the two coordinates.  Reorientation is performed only by the canonical
unordered-pair map `covarianceOrderedPair`.

The one-owner child operation is insensitive to reorienting its parent.  Hence
the sequential `r`-then-`s` expansion is exactly this four-corner terminal set,
and so is the `s`-then-`r` expansion.  This is the exact finite Fubini statement
needed when intermediate one-step multiplicities differ.

Filtering by completed Dirichlet class keeps `clippedExcess` separate from
`outside`.  Cardinalities and reciprocal-energy sums then agree class by class,
with no `2/9` or `1/9` majorant.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Reorienting an unordered parent does not change its two literal one-owner
children. -/
theorem covarianceOwnerChildCandidates_orderedParent
    (q a b : ℕ) :
    covarianceOwnerChildCandidates q (covarianceOrderedPair a b) =
      covarianceOwnerChildCandidates q (a, b) := by
  by_cases hab : a < b
  · rw [covarianceOrderedPair_eq_of_lt hab]
  · have hpair : covarianceOrderedPair a b = (b, a) := by
      unfold covarianceOrderedPair
      simp [hab]
    rw [hpair]
    unfold covarianceOwnerChildCandidates
    rw [covarianceOrderedPair_comm (q * b) a,
      covarianceOrderedPair_comm b (q * a)]
    ext z
    simp [or_comm]

/-- The four terminal descendants obtained by assigning each of two owner
primes to either coordinate of a fixed parent. -/
def lowOwnerTwoPrimeCompletedChildCube
    (r s : ℕ) (parent : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  { covarianceOrderedPair ((r * s) * parent.1) parent.2,
    covarianceOrderedPair (r * parent.1) (s * parent.2),
    covarianceOrderedPair (s * parent.1) (r * parent.2),
    covarianceOrderedPair parent.1 ((r * s) * parent.2) }

/-- Sequential two-owner expansion using the literal one-owner child carrier. -/
def lowOwnerTwoPrimeSequentialChildCube
    (r s : ℕ) (parent : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (covarianceOwnerChildCandidates r parent).biUnion fun child =>
    covarianceOwnerChildCandidates s child

/-- **Exact two-step carrier Fubini.**  The sequential expansion is the canonical
completed four-corner carrier. -/
theorem lowOwnerTwoPrimeSequentialChildCube_eq_completed
    (r s : ℕ) (parent : ℕ × ℕ) :
    lowOwnerTwoPrimeSequentialChildCube r s parent =
      lowOwnerTwoPrimeCompletedChildCube r s parent := by
  rcases parent with ⟨a, b⟩
  unfold lowOwnerTwoPrimeSequentialChildCube
  change
    (({covarianceOrderedPair (r * a) b,
        covarianceOrderedPair a (r * b)} : Finset (ℕ × ℕ)).biUnion
      (fun child => covarianceOwnerChildCandidates s child)) =
      lowOwnerTwoPrimeCompletedChildCube r s (a, b)
  rw [Finset.biUnion_insert, Finset.singleton_biUnion]
  rw [covarianceOwnerChildCandidates_orderedParent s (r * a) b,
    covarianceOwnerChildCandidates_orderedParent s a (r * b)]
  unfold covarianceOwnerChildCandidates lowOwnerTwoPrimeCompletedChildCube
  have hleft : s * (r * a) = (r * s) * a := by
    rw [← Nat.mul_assoc, Nat.mul_comm s r]
  have hright : s * (r * b) = (r * s) * b := by
    rw [← Nat.mul_assoc, Nat.mul_comm s r]
  rw [hleft, hright]
  ext z
  simp

/-- The completed two-prime terminal cube is exactly symmetric in the two
owners. -/
theorem lowOwnerTwoPrimeCompletedChildCube_comm
    (r s : ℕ) (parent : ℕ × ℕ) :
    lowOwnerTwoPrimeCompletedChildCube r s parent =
      lowOwnerTwoPrimeCompletedChildCube s r parent := by
  ext z
  simp [lowOwnerTwoPrimeCompletedChildCube, Nat.mul_comm, Nat.mul_left_comm,
    or_comm, or_left_comm, or_assoc]

/-- **Block-level local confluence.**  The literal sequential child carrier is
independent of owner order. -/
theorem lowOwnerTwoPrimeSequentialChildCube_comm
    (r s : ℕ) (parent : ℕ × ℕ) :
    lowOwnerTwoPrimeSequentialChildCube r s parent =
      lowOwnerTwoPrimeSequentialChildCube s r parent := by
  rw [lowOwnerTwoPrimeSequentialChildCube_eq_completed,
    lowOwnerTwoPrimeSequentialChildCube_eq_completed,
    lowOwnerTwoPrimeCompletedChildCube_comm]

/-- Any terminal predicate selects exactly the same completed carrier in either
owner order. -/
theorem lowOwnerTwoPrimeCompletedChildCube_filter_comm
    (r s : ℕ) (parent : ℕ × ℕ) (keep : ℕ × ℕ → Prop)
    [DecidablePred keep] :
    (lowOwnerTwoPrimeCompletedChildCube r s parent).filter keep =
      (lowOwnerTwoPrimeCompletedChildCube s r parent).filter keep := by
  rw [lowOwnerTwoPrimeCompletedChildCube_comm]

/-- Exact path-independent terminal multiplicity for an arbitrary completed
filter. -/
theorem lowOwnerTwoPrimeCompletedChildCube_filter_card_comm
    (r s : ℕ) (parent : ℕ × ℕ) (keep : ℕ × ℕ → Prop)
    [DecidablePred keep] :
    ((lowOwnerTwoPrimeCompletedChildCube r s parent).filter keep).card =
      ((lowOwnerTwoPrimeCompletedChildCube s r parent).filter keep).card := by
  rw [lowOwnerTwoPrimeCompletedChildCube_filter_comm]

/-- Exact finite Fubini for arbitrary terminal weights on an arbitrary completed
filter. -/
theorem sum_lowOwnerTwoPrimeCompletedChildCube_filter_comm
    (r s : ℕ) (parent : ℕ × ℕ) (keep : ℕ × ℕ → Prop)
    [DecidablePred keep] (f : ℕ × ℕ → ℝ) :
    (∑ child ∈ (lowOwnerTwoPrimeCompletedChildCube r s parent).filter keep,
        f child) =
      ∑ child ∈ (lowOwnerTwoPrimeCompletedChildCube s r parent).filter keep,
        f child := by
  rw [lowOwnerTwoPrimeCompletedChildCube_filter_comm]

/-- Pair of completed Dirichlet classes of one terminal child. -/
def lowOwnerCompletedPairClass
    (R p : ℕ) (child : ℕ × ℕ) :
    LowOwnerCompletedSiteClass × LowOwnerCompletedSiteClass :=
  (lowOwnerCompletedSiteClass R p child.1,
    lowOwnerCompletedSiteClass R p child.2)

/-- Class-specific completed two-prime block.  In particular classes involving
`clippedExcess` remain distinct from the corresponding outside classes. -/
def lowOwnerTwoPrimeCompletedClassFiber
    (R p r s : ℕ) (parent : ℕ × ℕ)
    (cls : LowOwnerCompletedSiteClass × LowOwnerCompletedSiteClass) :
    Finset (ℕ × ℕ) :=
  (lowOwnerTwoPrimeCompletedChildCube r s parent).filter fun child =>
    lowOwnerCompletedPairClass R p child = cls

/-- Class-specific multiplicity is owner-order independent. -/
theorem lowOwnerTwoPrimeCompletedClassFiber_card_comm
    (R p r s : ℕ) (parent : ℕ × ℕ)
    (cls : LowOwnerCompletedSiteClass × LowOwnerCompletedSiteClass) :
    (lowOwnerTwoPrimeCompletedClassFiber R p r s parent cls).card =
      (lowOwnerTwoPrimeCompletedClassFiber R p s r parent cls).card := by
  unfold lowOwnerTwoPrimeCompletedClassFiber
  rw [lowOwnerTwoPrimeCompletedChildCube_comm]

/-- Exact sequential multiplicity, class by class. -/
theorem lowOwnerTwoPrimeSequentialClassFiber_card_comm
    (R p r s : ℕ) (parent : ℕ × ℕ)
    (cls : LowOwnerCompletedSiteClass × LowOwnerCompletedSiteClass) :
    ((lowOwnerTwoPrimeSequentialChildCube r s parent).filter fun child =>
        lowOwnerCompletedPairClass R p child = cls).card =
      ((lowOwnerTwoPrimeSequentialChildCube s r parent).filter fun child =>
        lowOwnerCompletedPairClass R p child = cls).card := by
  rw [lowOwnerTwoPrimeSequentialChildCube_comm]

/-- **Exact class-by-class reciprocal-energy Fubini.** -/
theorem sum_lowOwnerTwoPrimeCompletedClassFiber_energy_comm
    (R p r s : ℕ) (parent : ℕ × ℕ)
    (cls : LowOwnerCompletedSiteClass × LowOwnerCompletedSiteClass) :
    (∑ child ∈ lowOwnerTwoPrimeCompletedClassFiber R p r s parent cls,
        postRootCovarianceReciprocalPairEnergy child) =
      ∑ child ∈ lowOwnerTwoPrimeCompletedClassFiber R p s r parent cls,
        postRootCovarianceReciprocalPairEnergy child := by
  unfold lowOwnerTwoPrimeCompletedClassFiber
  rw [lowOwnerTwoPrimeCompletedChildCube_comm]

/-- **Exact sequential reciprocal-energy Fubini, class by class.**  This is the
block-level currency statement: different intermediate child counts cannot
change the final exact reciprocal-energy ledger. -/
theorem sum_lowOwnerTwoPrimeSequentialClassFiber_energy_comm
    (R p r s : ℕ) (parent : ℕ × ℕ)
    (cls : LowOwnerCompletedSiteClass × LowOwnerCompletedSiteClass) :
    (∑ child ∈ (lowOwnerTwoPrimeSequentialChildCube r s parent).filter
        (fun child => lowOwnerCompletedPairClass R p child = cls),
        postRootCovarianceReciprocalPairEnergy child) =
      ∑ child ∈ (lowOwnerTwoPrimeSequentialChildCube s r parent).filter
        (fun child => lowOwnerCompletedPairClass R p child = cls),
        postRootCovarianceReciprocalPairEnergy child := by
  rw [lowOwnerTwoPrimeSequentialChildCube_comm]

end RHLean.Proof