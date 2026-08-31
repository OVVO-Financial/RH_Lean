import Mathlib
import RHLean.Analysis.SquareRootTransportTopFibreNoGo

/-!
# Prime-deletion Hall obstruction on the square-root Mertens tail

The canonically oriented downcross carrier invites a graph-theoretic pairing:
connect opposite Mobius signs when one tail integer is obtained from the other
by adding or deleting one prime.  The actual crossing-prime deletion graph is a
subgraph of this more generous one-prime graph.

This module records the obstruction before attempting any Hall estimate.  Every
prime in the inert top half `(X_R / 2, X_R]`, where `X_R = R^2 - 1`, is an
isolated negative vertex even in the enlarged graph.  Hence every crossing-prime
deletion graph has Hall defect at least the cardinality of the complete top
prime fibre.

Thus a Hall-defect strategy confined to one-prime moves inside the Mertens tail
cannot have an RH-scale small unmatched set.  Any successful matching graph must
add genuinely nonlocal edges that can absorb the top-prime block.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

namespace CrossingPrimeDeletionGraph

/-- Negative nonzero-Mobius vertices in the square-root Mertens tail. -/
def squareRootTailNegativePart (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun n => μ n = -1

/-- Positive nonzero-Mobius vertices in the square-root Mertens tail. -/
def squareRootTailPositivePart (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun n => μ n = 1

/-- Enlarged one-prime adjacency on opposite signs in the Mertens tail.

The intended crossing-prime deletion graph is a subgraph: here we allow *any*
prime insertion/deletion which stays in the tail.  Proving isolation in this
supergraph is therefore stronger than proving it for the canonical crossing
move alone. -/
def OnePrimeTailAdjacent (R n m : ℕ) : Prop :=
  n ∈ squareRootTailNegativePart R ∧
    m ∈ squareRootTailPositivePart R ∧
      ∃ p : ℕ, p.Prime ∧ (n = p * m ∨ m = p * n)

/-- Positive neighbors of a set of negative tail vertices. -/
def onePrimeTailNeighbors (R : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (squareRootTailPositivePart R).filter fun m =>
    ∃ n ∈ S, OnePrimeTailAdjacent R n m

/-- Hall deficiency of one negative subset. -/
def onePrimeTailHallDefectAt (R : ℕ) (S : Finset ℕ) : ℕ :=
  S.card - (onePrimeTailNeighbors R S).card

/-- Maximum Hall deficiency over all negative subsets. -/
noncomputable def onePrimeTailHallDefect (R : ℕ) : ℕ :=
  ((squareRootTailNegativePart R).powerset.image
      (onePrimeTailHallDefectAt R)).max'
    (by
      refine ⟨onePrimeTailHallDefectAt R ∅, ?_⟩
      exact Finset.mem_image.mpr
        ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), rfl⟩)

/-- Top-half primes are genuine negative vertices of the Mertens tail. -/
theorem squareRootTopFibrePrimes_subset_negative
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTopFibrePrimes R ⊆ squareRootTailNegativePart R := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hqHalf, hqX⟩
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    -- `omega` treats `R ^ 2` and `R * R` as unrelated atoms, so present the
    -- endpoint in the same shape as the hypothesis before calling it.
    have hRR : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
    have hsq : squareRootEndpoint R = R * R - 1 := by
      unfold squareRootEndpoint
      rw [pow_two]
    rw [hsq]
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hmul
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨hhalf.trans_lt hqHalf, hqX⟩, ?_⟩
  simpa using ArithmeticFunction.moebius_apply_prime hqPrime

/-- **Top-prime isolation.**  A top-half prime has no opposite-sign neighbor
obtained by inserting or deleting one prime while remaining in the tail.

Deletion cannot factor the prime nontrivially.  Insertion cannot remain below
`X_R`, since every inserted prime is at least `2` and `q > X_R / 2`. -/
theorem squareRootTopFibrePrimes_neighbors_eq_empty
    (R : ℕ) (hR : 3 ≤ R) :
    onePrimeTailNeighbors R (squareRootTopFibrePrimes R) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmPos, hneighbor⟩
  rcases hneighbor with ⟨q, hqTop, hadj⟩
  rcases hadj with ⟨_hqNeg, _hmPos, p, hpPrime, hrel⟩
  have hmTail := (Finset.mem_filter.mp hmPos).1
  rcases Finset.mem_Ioc.mp hmTail with ⟨hRm, hmX⟩
  rcases Finset.mem_filter.mp hqTop with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hqHalf, _hqX⟩
  rcases hrel with hqeq | hmeq
  · have hmdvd : m ∣ q := by
      refine ⟨p, ?_⟩
      simpa [Nat.mul_comm] using hqeq
    rcases hqPrime.eq_one_or_self_of_dvd m hmdvd with hm1 | hmq
    · omega
    · subst m
      have hp2 : 2 ≤ p := hpPrime.two_le
      have hqpos : 0 < q := hqPrime.pos
      nlinarith
  · have hXlt2q : squareRootEndpoint R < 2 * q := by
      have h :=
        (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hqHalf
      simpa [Nat.mul_comm] using h
    have h2q_le_pq : 2 * q ≤ p * q := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hpPrime.two_le
    have hXltm : squareRootEndpoint R < m := by
      rw [hmeq]
      exact hXlt2q.trans_le h2q_le_pq
    omega

/-- The Hall deficiency witnessed by the top-prime set is exactly its full
cardinality. -/
theorem onePrimeTailHallDefectAt_topFibre
    (R : ℕ) (hR : 3 ≤ R) :
    onePrimeTailHallDefectAt R (squareRootTopFibrePrimes R) =
      (squareRootTopFibrePrimes R).card := by
  rw [onePrimeTailHallDefectAt,
    squareRootTopFibrePrimes_neighbors_eq_empty R hR]
  simp

/-- **Hall no-go.**  Even the enlarged one-prime graph has Hall defect at least
the entire inert top-prime population.  The canonical crossing-prime deletion
graph, having fewer edges, cannot do better on this witness. -/
theorem squareRootTopFibrePrimes_card_le_onePrimeTailHallDefect
    (R : ℕ) (hR : 3 ≤ R) :
    (squareRootTopFibrePrimes R).card ≤ onePrimeTailHallDefect R := by
  rw [← onePrimeTailHallDefectAt_topFibre R hR]
  unfold onePrimeTailHallDefect
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨squareRootTopFibrePrimes R, ?_, rfl⟩
  exact Finset.mem_powerset.mpr
    (squareRootTopFibrePrimes_subset_negative R hR)

end CrossingPrimeDeletionGraph

end RHLean.Proof
