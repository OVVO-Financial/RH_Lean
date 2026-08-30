import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalFailureRoot
import RHLean.Proof.SquareRootLowPrimeNoTogglePopulationBound
import RHLean.Proof.SquareRootLowPrimePartialPacketBoundary

/-!
# Tagged homes for the terminal no-liberty boundary

The final low-prime boundary is charged into four genuinely disjoint kinds of
home:

* one distinguished head;
* the already-compressed partial crossing packet;
* the born-exit frontier;
* canonical least-failure roots.

The nested `Sum` below is the literal tagged disjoint union.  This module proves
its root-scale cardinality budget.  It deliberately does not identify a raw
terminal seat with a home: that is the remaining alternating-rematching
injectivity theorem.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Canonical roots at most `R` which have at least one fresh failing prime. -/
def squareRootLowPrimeCanonicalLibertyFailureRoots
    (K U R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter fun n =>
    (squareRootLowPrimeFailurePrimeCandidates K U R n).Nonempty

@[simp] theorem mem_squareRootLowPrimeCanonicalLibertyFailureRoots
    {K U R n : ℕ} :
    n ∈ squareRootLowPrimeCanonicalLibertyFailureRoots K U R ↔
      0 < n ∧ n ≤ R ∧
        (squareRootLowPrimeFailurePrimeCandidates K U R n).Nonempty := by
  simp only [squareRootLowPrimeCanonicalLibertyFailureRoots,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnR⟩, hfail⟩
    exact ⟨by omega, hnR, hfail⟩
  · rintro ⟨hn, hnR, hfail⟩
    exact ⟨⟨by omega, hnR⟩, hfail⟩

/-- Every retained canonical home carries the failure-root data already used by
`SquareRootLowPrimeCanonicalFailureRoot`. -/
theorem squareRootLowPrimeCanonicalLibertyFailureRoot_data
    {K U R n : ℕ}
    (hn : n ∈ squareRootLowPrimeCanonicalLibertyFailureRoots K U R) :
    SquareRootLowPrimeCanonicalFailureRootData K U R n := by
  simpa [SquareRootLowPrimeCanonicalFailureRootData] using
    (mem_squareRootLowPrimeCanonicalLibertyFailureRoots.mp hn)

/-- Canonical failure-root homes cost at most one state per integer root. -/
theorem squareRootLowPrimeCanonicalLibertyFailureRoots_card_le_root
    (K U R : ℕ) :
    (squareRootLowPrimeCanonicalLibertyFailureRoots K U R).card ≤ R := by
  have hsub :
      squareRootLowPrimeCanonicalLibertyFailureRoots K U R ⊆
        Finset.Icc 1 R := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  calc
    (squareRootLowPrimeCanonicalLibertyFailureRoots K U R).card ≤
        (Finset.Icc 1 R).card := Finset.card_le_card hsub
    _ = R := by simp

/-- The final home type is a literal tagged disjoint union

`Head ⊔ PartialSeat ⊔ BornExit ⊔ FailureRoot`.

The tags make collisions between different boundary classes impossible by
construction. -/
abbrev SquareRootLowPrimeNoLibertyBoundaryHome :=
  Sum Unit (Sum ℕ (Sum (ℕ × ℕ) ℕ))

/-- The finite set of available terminal homes at the canonical low-prime
cutoff.  The partial component is the compressed packet itself, not its raw
prime population. -/
def squareRootLowPrimeNoLibertyBoundaryHomeSpace
    (R K j : ℕ) : Finset SquareRootLowPrimeNoLibertyBoundaryHome :=
  ({()} : Finset Unit).disjSum
    ((squareRootLowPrimePartialPacketBoundary R K j).disjSum
      ((squareRootLowPrimeBornNoSuccessorAtoms R K
          (squareRootBornPostTailLowPrimeCutoff R)).disjSum
        (squareRootLowPrimeCanonicalLibertyFailureRoots K
          (squareRootBornPostTailLowPrimeCutoff R) R)))

/-- Exact cardinality of the tagged home space. -/
theorem card_squareRootLowPrimeNoLibertyBoundaryHomeSpace
    (R K j : ℕ) :
    (squareRootLowPrimeNoLibertyBoundaryHomeSpace R K j).card =
      1 +
        (squareRootLowPrimePartialPacketBoundary R K j).card +
        (squareRootLowPrimeBornNoSuccessorAtoms R K
          (squareRootBornPostTailLowPrimeCutoff R)).card +
        (squareRootLowPrimeCanonicalLibertyFailureRoots K
          (squareRootBornPostTailLowPrimeCutoff R) R).card := by
  simp [squareRootLowPrimeNoLibertyBoundaryHomeSpace]
  omega

/-- **The four canonical home classes have total cardinality at most `4*R`.**

No analytic input enters: the packet costs `< K`, the born-exit edge costs
`2*R`, failure roots cost `R`, and `1 + K <= R` when `K < R`. -/
theorem squareRootLowPrimeNoLibertyBoundaryHomeSpace_card_le_four_root
    {R K j : ℕ} (hR : 1 ≤ R) (hKR : K < R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    (squareRootLowPrimeNoLibertyBoundaryHomeSpace R K j).card ≤ 4 * R := by
  have hpacket :=
    squareRootLowPrimePartialPacketBoundary_card_lt_depth
      (R := R) (K := K) (j := j) hV0 hVK
  have hborn :=
    squareRootLowPrimeBornNoSuccessorAtoms_card_le_two_root R K hR
  have hroots :=
    squareRootLowPrimeCanonicalLibertyFailureRoots_card_le_root K
      (squareRootBornPostTailLowPrimeCutoff R) R
  rw [card_squareRootLowPrimeNoLibertyBoundaryHomeSpace]
  omega

end RHLean.Proof
