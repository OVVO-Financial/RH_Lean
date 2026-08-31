import Mathlib
import RHLean.Proof.SquareRootLowPrimeStructuralKey
import RHLean.Proof.SquareRootLowPrimeHorizontalTerminalCoverage

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Schedule-generic displacement: if a terminal state still has its `p`-neighbor
in the original carrier, that neighbor was consumed at one concrete coordinate
in the strict prefix before `p`.  No numeric ordering of the prime labels is
needed here; the structural decrease is the shortening of the prefix. -/
theorem squareRootLowPrimeProcessedSeatTerminal_neighbor_has_prefix_blocker
    (pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
      (pre ++ p :: post) S)
    (hxHead : x ≠ none)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hneighbor : squareRootLowPrimeProcessedSeatExtend p x ∈ S) :
    ∃ pre' q post' z,
      pre = pre' ++ q :: post' ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre' S ∧
        ((squareRootLowPrimeProcessedSeatExtend p x ∈
              squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q
              (squareRootLowPrimeProcessedSeatExtend p x)) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            squareRootLowPrimeProcessedSeatExtend p x =
              squareRootLowPrimeProcessedSeatExtend q z)) := by
  have hxRewritten :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier post
        (squareRootLowPrimeProcessedSeatFrontierStep
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p) := by
    rw [squareRootLowPrimeProcessedSeatMatchingFrontier_append] at hx
    simpa [squareRootLowPrimeProcessedSeatMatchingFrontier] using hx
  have hxStep :
      x ∈ squareRootLowPrimeProcessedSeatFrontierStep
        (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' post _ hxRewritten
  have hneighborLost :
      squareRootLowPrimeProcessedSeatExtend p x ∉
        squareRootLowPrimeProcessedSeatMatchingFrontier pre S := by
    intro hneighborPre
    have hxPre := (Finset.mem_sdiff.mp hxStep).1
    have hxLower :
        x ∈ squareRootLowPrimeProcessedSeatPairLower
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
      mem_squareRootLowPrimeProcessedSeatPairLower.mpr
        ⟨hxPre, hxHead, hpFresh, hneighborPre⟩
    exact (Finset.mem_sdiff.mp hxStep).2
      (Finset.mem_union.mpr (Or.inl hxLower))
  rcases squareRootLowPrimeProcessedSeat_removed_has_owner
      pre S hneighbor hneighborLost with
    ⟨pre', q, post', hpreSplit, hpaired⟩
  rcases squareRootLowPrimeProcessedSeatPaired_has_partner hpaired with
    ⟨z, hz, hedge⟩
  exact ⟨pre', q, post', z, hpreSplit, hz, hedge⟩

/-- The same prefix-blocker statement for a genuine intrinsic terminal residual.
If the proposed child were absent from the original carrier, `p` would already
be its intrinsic first owner; therefore residuality forces the neighbor to be
present and the schedule-generic displacement theorem applies. -/
theorem squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_has_prefix_blocker
    (ps pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxResidual :
      x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual ps S)
    (hps : ps = pre ++ p :: post)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hlpf : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p) :
    ∃ pre' q post' z,
      pre = pre' ++ q :: post' ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre' S ∧
        ((squareRootLowPrimeProcessedSeatExtend p x ∈
              squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q
              (squareRootLowPrimeProcessedSeatExtend p x)) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            squareRootLowPrimeProcessedSeatExtend p x =
              squareRootLowPrimeProcessedSeatExtend q z)) := by
  have hxResidual' :
      x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S
        (squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S) := by
    simpa [squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual] using
      hxResidual
  have hxResidualData :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp hxResidual'
  have hxTargetData :
      x ≠ none ∧
        x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S :=
    Finset.mem_erase.mp hxResidualData.1
  have hxHead : x ≠ none := hxTargetData.1
  have hxTerminal :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S :=
    hxTargetData.2
  have hxS : x ∈ S :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps S hxTerminal
  have hpList : p ∈ ps := by
    rw [hps]
    simp
  have hnone :=
    (squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_none_iff ps S x).mp
      hxResidualData.2
  have hneighbor : squareRootLowPrimeProcessedSeatExtend p x ∈ S := by
    by_contra hmissing
    have hfall :
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p :=
      mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
        ⟨hxS, hxHead, hpFresh, hmissing, hlpf⟩
    exact hnone p hpList hfall
  have hxStage :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
        (pre ++ p :: post) S := by
    rw [← hps]
    exact hxTerminal
  exact squareRootLowPrimeProcessedSeatTerminal_neighbor_has_prefix_blocker
    pre post S hxStage hxHead hpFresh hneighbor

/-- A blocker found in the prefix has strictly smaller structural schedule rank.
This is the well-founded measure used by the terminal traversal. -/
theorem squareRootLowPrimeProcessedSeat_prefixBlocker_length_lt
    {pre pre' post' : List ℕ} {q : ℕ}
    (hsplit : pre = pre' ++ q :: post') :
    pre'.length < pre.length := by
  rw [hsplit, List.length_append, List.length_cons]
  omega

/-- Every blocker partner in a fresh-prime schedule remains in the same
`(shallowBase, seat)` fibre as the terminal state that exposed it.  This is the
key invariant needed by the recursive partial-packet traversal. -/
theorem squareRootLowPrimeProcessedSeat_prefixBlocker_structuralKey
    {K U p q : ℕ} {pre post pre' post' : List ℕ}
    {x z : SquareRootLowPrimeProcessedState}
    (hps : squareRootLowPrimeFreshPrimeList K U = pre ++ p :: post)
    (hpre : pre = pre' ++ q :: post')
    (hedge :
      (z = squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x)) ∨
        (squareRootLowPrimeProcessedSeatExtend p x =
          squareRootLowPrimeProcessedSeatExtend q z)) :
    squareRootLowPrimeProcessedSeatStructuralKey K z =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  have hpMem : p ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hps]
    simp
  have hqPre : q ∈ pre := by
    rw [hpre]
    simp
  have hqMem : q ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hps]
    simp [hqPre]
  have hpData := squareRootLowPrimeFreshPrimeList_prime_and_above hpMem
  have hqData := squareRootLowPrimeFreshPrimeList_prime_and_above hqMem
  rcases hedge with hforward | hback
  · rw [hforward,
      squareRootLowPrimeProcessedSeatStructuralKey_extend hqData.1 hqData.2,
      squareRootLowPrimeProcessedSeatStructuralKey_extend hpData.1 hpData.2]
  · have hkey := congrArg
      (squareRootLowPrimeProcessedSeatStructuralKey K) hback
    rw [squareRootLowPrimeProcessedSeatStructuralKey_extend hpData.1 hpData.2,
      squareRootLowPrimeProcessedSeatStructuralKey_extend hqData.1 hqData.2]
      at hkey
    exact hkey.symm

end RHLean.Proof
