import Mathlib
import RHLean.Proof.SquareRootLowPrimeFixedPartialPacketResidual
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome

/-!
# Sharper fixed-depth no-liberty boundary budget

At the certified fixed reciprocal depth `K = 18349`, the first crossing packet
has residual cardinality strictly below `21`.  Combining that exact finite fact
with the already-proved endpoint budgets gives

* Head: `1`;
* Partial: at most `20`;
* BornExit: at most `2*R`;
* RootEquality homes: exactly `R` available parent slots.

Hence the canonical home space, and therefore the actual tagged no-liberty
boundary, has cardinality at most `3*R + 21`.

This is only a target-side improvement.  It does not assume or manufacture the
still-open source-to-boundary classifier.
-/

noncomputable section

namespace RHLean.Proof

/-- Fixed-depth packet cardinality under the actual nonnegative residual bound. -/
theorem squareRootLowPrimePartialPacketBoundary18349_card_lt_twentyOne
    {R j : ℕ}
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j)
    (hV21 : squareRootCrossingLayerPartialPacketInt R 18349 j < 21) :
    (squareRootLowPrimePartialPacketBoundary R 18349 j).card < 21 := by
  rw [squareRootLowPrimePartialPacketBoundary_card]
  have hcast :
      (Int.toNat (squareRootCrossingLayerPartialPacketInt R 18349 j) : ℤ) =
        squareRootCrossingLayerPartialPacketInt R 18349 j :=
    Int.toNat_of_nonneg hV0
  have hltZ :
      (Int.toNat (squareRootCrossingLayerPartialPacketInt R 18349 j) : ℤ) < 21 := by
    rw [hcast]
    exact hV21
  exact_mod_cast hltZ

/-- **Fixed crossing target-home budget.** -/
theorem squareRootLowPrimeNoLibertyBoundaryHomeSpace18349_card_le_three_root_add_twentyOne
    {R j : ℕ} (hR : 1 ≤ R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j)
    (hV21 : squareRootCrossingLayerPartialPacketInt R 18349 j < 21) :
    (squareRootLowPrimeNoLibertyBoundaryHomeSpace R 18349 j).card ≤
      3 * R + 21 := by
  have hpacket :=
    squareRootLowPrimePartialPacketBoundary18349_card_lt_twentyOne hV0 hV21
  have hborn :=
    squareRootLowPrimeBornNoSuccessorAtoms_card_le_two_root R 18349 hR
  rw [card_squareRootLowPrimeNoLibertyBoundaryHomeSpace]
  omega

/-- **The actual fixed-depth tagged boundary inherits the sharper home budget.**
The only nontrivial home projection remains the already-proved injective Go
parent projection. -/
theorem squareRootLowPrimeProcessedSeatNoLibertyBoundary18349_card_le_three_root_add_twentyOne
    {R j : ℕ} (hR : 1 ≤ R)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j)
    (hV21 : squareRootCrossingLayerPartialPacketInt R 18349 j < 21) :
    (squareRootLowPrimeProcessedSeatNoLibertyBoundary
      R 18349 j (squareRootBornPostTailLowPrimeCutoff R)).card ≤
      3 * R + 21 := by
  let B := squareRootLowPrimeProcessedSeatNoLibertyBoundary
    R 18349 j (squareRootBornPostTailLowPrimeCutoff R)
  let H := squareRootLowPrimeNoLibertyBoundaryHomeSpace R 18349 j
  let home := squareRootLowPrimeNoLibertyBoundaryHome R 18349 j
  have hinj : Set.InjOn home B := by
    simpa [B, home] using
      squareRootLowPrimeNoLibertyBoundaryHome_injOn R 18349 j
  have himage : B.image home ⊆ H := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    simpa [B, H, home] using
      squareRootLowPrimeNoLibertyBoundaryHome_mem
        (R := R) (K := 18349) (j := j) hx
  have hcardImage : (B.image home).card = B.card :=
    Finset.card_image_iff.mpr hinj
  have hhome :=
    squareRootLowPrimeNoLibertyBoundaryHomeSpace18349_card_le_three_root_add_twentyOne
      hR hV0 hV21
  calc
    B.card = (B.image home).card := hcardImage.symm
    _ ≤ H.card := Finset.card_le_card himage
    _ ≤ 3 * R + 21 := by simpa [H] using hhome

/-- A genuine fixed crossing supplies a concrete layer index with the sharper
`3*R+21` target-side budget. -/
theorem squareRootPacketCrossing18349_exists_noLibertyBoundary_card_le_three_root_add_twentyOne
    {R : ℕ} (hR : 1 ≤ R) (hcross : SquareRootPacketCrossesAt R 18349) :
    ∃ j : ℕ,
      j ≤ squareRootReciprocalPrimeLayerCard R 18349 ∧
        0 ≤ squareRootCrossingLayerPartialPacketInt R 18349 j ∧
        squareRootCrossingLayerPartialPacketInt R 18349 j < 21 ∧
        (squareRootLowPrimeProcessedSeatNoLibertyBoundary
          R 18349 j (squareRootBornPostTailLowPrimeCutoff R)).card ≤
          3 * R + 21 := by
  rcases squareRootPacketCrossing18349_exists_partial_residual_lt_twentyOne
      hcross with ⟨j, hj, hV0, hV21⟩
  exact ⟨j, hj, hV0, hV21,
    squareRootLowPrimeProcessedSeatNoLibertyBoundary18349_card_le_three_root_add_twentyOne
      hR hV0 hV21⟩

end RHLean.Proof
