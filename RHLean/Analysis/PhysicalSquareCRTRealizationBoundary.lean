import Mathlib
import RHLean.Analysis.PhysicalSquareCRTTransfer

/-!
# Physical square-clock CRT realization and boundary control

This module tests the exact transfer exposed by `PhysicalSquareCRTTransfer`.
There are two distinct issues:

* the square clock cuts aligned finite-prime CRT periods at the two endpoints;
* even on a complete selected-prime CRT period, the actual Mobius `T` population
  may lose cells because of square hits from primes outside the selected set.

The first defect is elementary: for a fixed finite prime set with combined
period `M`, at most two aligned periods meet the ends of one square-block
transition interval.  Consequently the signed boundary mass is at most `6*M`.

The second defect is genuinely separate.  At `R = 243` the whole physical
transition carrier is exactly one aligned `11^2 = 121` period, so the geometric
CRT boundary is empty.  The selected-prime residue law nevertheless has its
certified `115 = 55 + 6*10` zero-free population while the actual Mobius
population deletes, for example, `k = 14762` because `4*k+1 = 59049` has a
`3^2` factor.  Thus complete square-clock CRT containment alone does not identify
the selected-prime law with the actual Mobius `T` law.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Geometric complete-period carrier, before imposing the actual Mobius
zero-free condition. -/
def physicalSquareCompleteCRTCarrier (P : Finset ℕ) (R : ℕ) : Finset ℕ :=
  (threeSlotSquareBlockTransitionCells R).filter fun k =>
    finitePrimeCRTOrbit P k ⊆ threeSlotSquareBlockTransitionCells R

/-- Purely geometric square-clock CRT boundary. -/
def physicalSquareCRTGeometricBoundaryCells
    (P : Finset ℕ) (R : ℕ) : Finset ℕ :=
  threeSlotSquareBlockTransitionCells R \
    physicalSquareCompleteCRTCarrier P R

/-- The actual `T` boundary from the preceding module is contained in the
purely geometric square-clock boundary. -/
theorem physicalSquareCRTBoundaryCells_subset_geometric
    (P : Finset ℕ) (R : ℕ) :
    physicalSquareCRTBoundaryCells P R ⊆
      physicalSquareCRTGeometricBoundaryCells P R := by
  intro k hk
  rcases Finset.mem_sdiff.mp hk with ⟨hkT, hkNotComplete⟩
  have hkGeom : k ∈ threeSlotSquareBlockTransitionCells R :=
    (Finset.mem_filter.mp hkT).1
  apply Finset.mem_sdiff.mpr
  refine ⟨hkGeom, ?_⟩
  intro hkCarrier
  apply hkNotComplete
  rcases Finset.mem_filter.mp hkCarrier with ⟨_, hOrbit⟩
  exact Finset.mem_filter.mpr ⟨hkT, hOrbit⟩

private theorem lower_div_four_iff (N k : ℕ) :
    (N + 2) / 4 ≤ k ↔ N ≤ 4 * k + 1 := by
  omega

private theorem upper_div_four_iff (N k : ℕ) :
    k < (N - 4) / 4 ↔ 4 * k + 7 < N := by
  omega

/-- First complete-cell index admitted by the square-block transition window. -/
def threeSlotSquareBlockLower (R : ℕ) : ℕ :=
  (R ^ 2 + 2) / 4

/-- Exclusive upper complete-cell index admitted by the square-block transition window. -/
def threeSlotSquareBlockUpper (R : ℕ) : ℕ :=
  ((R + 1) ^ 2 - 4) / 4

/-- The physical square-block transition carrier is literally one integer interval. -/
theorem threeSlotSquareBlockTransitionCells_eq_Ico (R : ℕ) :
    threeSlotSquareBlockTransitionCells R =
      Finset.Ico (threeSlotSquareBlockLower R) (threeSlotSquareBlockUpper R) := by
  ext k
  simp only [threeSlotSquareBlockTransitionCells, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Ico, threeSlotSquareBlockLower,
    threeSlotSquareBlockUpper]
  rw [lower_div_four_iff, upper_div_four_iff]
  omega

/-- The combined CRT period is always positive. -/
theorem finitePrimeCRTPeriod_pos (P : Finset ℕ) :
    0 < finitePrimeCRTPeriod P := by
  simp [finitePrimeCRTPeriod]

/-- If a cell is at least one CRT period from both interval endpoints, its whole
aligned CRT orbit lies inside the interval. -/
theorem finitePrimeCRTOrbit_subset_Ico_of_margin
    (P : Finset ℕ) {L U k : ℕ}
    (hleft : L + finitePrimeCRTPeriod P ≤ k)
    (hright : k + finitePrimeCRTPeriod P ≤ U) :
    finitePrimeCRTOrbit P k ⊆ Finset.Ico L U := by
  intro j hj
  let M := finitePrimeCRTPeriod P
  have hM : 0 < M := by
    simpa [M] using finitePrimeCRTPeriod_pos P
  have hjBounds := Finset.mem_Ico.mp hj
  have hmod : k % M < M := Nat.mod_lt k hM
  have hdecomp : (k / M) * M + k % M = k := by
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div k M
  have hstartL : L ≤ (k / M) * M := by
    change L + M ≤ k at hleft
    omega
  have hstartK : (k / M) * M ≤ k := Nat.div_mul_le_self k M
  have hendK : (k / M + 1) * M ≤ k + M := by
    rw [Nat.add_mul]
    simpa using Nat.add_le_add_right hstartK M
  apply Finset.mem_Ico.mpr
  constructor
  · exact hstartL.trans hjBounds.1
  · exact lt_of_lt_of_le hjBounds.2 (hendK.trans hright)

/-- At most two aligned CRT periods can meet the two endpoints of one physical
square-block transition interval. -/
theorem physicalSquareCRTGeometricBoundary_card_le_two_period
    (P : Finset ℕ) (R : ℕ) :
    (physicalSquareCRTGeometricBoundaryCells P R).card ≤
      2 * finitePrimeCRTPeriod P := by
  let L := threeSlotSquareBlockLower R
  let U := threeSlotSquareBlockUpper R
  let M := finitePrimeCRTPeriod P
  have hGeom : threeSlotSquareBlockTransitionCells R = Finset.Ico L U := by
    simpa [L, U] using threeSlotSquareBlockTransitionCells_eq_Ico R
  have hsubset :
      physicalSquareCRTGeometricBoundaryCells P R ⊆
        Finset.Ico L (L + M) ∪ Finset.Ico (U - M) U := by
    intro k hk
    rcases Finset.mem_sdiff.mp hk with ⟨hkGeom, hkNotComplete⟩
    have hkIco : k ∈ Finset.Ico L U := by
      rw [← hGeom]
      exact hkGeom
    by_cases hleft : L + M ≤ k
    · by_cases hright : k + M ≤ U
      · exfalso
        apply hkNotComplete
        apply Finset.mem_filter.mpr
        refine ⟨hkGeom, ?_⟩
        rw [hGeom]
        exact finitePrimeCRTOrbit_subset_Ico_of_margin P hleft hright
      · apply Finset.mem_union_right
        apply Finset.mem_Ico.mpr
        constructor
        · omega
        · exact hkIco.2
    · apply Finset.mem_union_left
      apply Finset.mem_Ico.mpr
      exact ⟨hkIco.1, by omega⟩
  calc
    (physicalSquareCRTGeometricBoundaryCells P R).card ≤
        (Finset.Ico L (L + M) ∪ Finset.Ico (U - M) U).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.Ico L (L + M)).card + (Finset.Ico (U - M) U).card :=
      Finset.card_union_le
    _ ≤ M + M := by
      simp only [Finset.card_Ico]
      omega
    _ = 2 * finitePrimeCRTPeriod P := by
      simp [M]

/-- The actual incomplete physical `T` population inherits the same two-period
cardinality bound. -/
theorem physicalSquareCRTBoundary_card_le_two_period
    (P : Finset ℕ) (R : ℕ) :
    (physicalSquareCRTBoundaryCells P R).card ≤
      2 * finitePrimeCRTPeriod P := by
  calc
    (physicalSquareCRTBoundaryCells P R).card ≤
        (physicalSquareCRTGeometricBoundaryCells P R).card :=
      Finset.card_le_card (physicalSquareCRTBoundaryCells_subset_geometric P R)
    _ ≤ 2 * finitePrimeCRTPeriod P :=
      physicalSquareCRTGeometricBoundary_card_le_two_period P R

/-- The physical degree-one cell observable has pointwise magnitude at most `3`. -/
theorem abs_physicalTCellValue_le_three (k : ℕ) :
    |physicalTCellValue k| ≤ 3 := by
  simp only [physicalTCellValue, threeSlotDegreeOneValue_threeSlotState]
  rcases ArithmeticFunction.moebius_eq_or (4 * k + 1) with h1 | h1 | h1 <;>
    rcases ArithmeticFunction.moebius_eq_or (4 * k + 2) with h2 | h2 | h2 <;>
      rcases ArithmeticFunction.moebius_eq_or (4 * k + 3) with h3 | h3 | h3 <;>
        simp [h1, h2, h3]

private theorem abs_physicalTCellValue_sum_le_three_mul_card (S : Finset ℕ) :
    |∑ k ∈ S, physicalTCellValue k| ≤ 3 * (S.card : ℤ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      calc
        |physicalTCellValue a + ∑ k ∈ S, physicalTCellValue k| ≤
            |physicalTCellValue a| + |∑ k ∈ S, physicalTCellValue k| :=
          abs_add _ _
        _ ≤ 3 + 3 * (S.card : ℤ) :=
          add_le_add (abs_physicalTCellValue_le_three a) ih
        _ = 3 * ((S.card + 1 : ℕ) : ℤ) := by
          push_cast
          ring

/-- Quantitative square-clock boundary control.  For fixed finite prime set `P`,
the incomplete-period signed mass is uniformly bounded independently of the
square stage `R`. -/
theorem abs_boundaryT_le_six_mul_period
    (P : Finset ℕ) (R : ℕ) :
    |boundaryT P R| ≤ 6 * (finitePrimeCRTPeriod P : ℤ) := by
  have hsum :=
    abs_physicalTCellValue_sum_le_three_mul_card
      (physicalSquareCRTBoundaryCells P R)
  have hcardNat := physicalSquareCRTBoundary_card_le_two_period P R
  have hcardInt :
      ((physicalSquareCRTBoundaryCells P R).card : ℤ) ≤
        2 * (finitePrimeCRTPeriod P : ℤ) := by
    exact_mod_cast hcardNat
  unfold boundaryT
  calc
    |∑ k ∈ physicalSquareCRTBoundaryCells P R, physicalTCellValue k| ≤
        3 * ((physicalSquareCRTBoundaryCells P R).card : ℤ) := hsum
    _ ≤ 3 * (2 * (finitePrimeCRTPeriod P : ℤ)) := by
      exact mul_le_mul_of_nonneg_left hcardInt (by norm_num)
    _ = 6 * (finitePrimeCRTPeriod P : ℤ) := by ring

/-! ## The first generic complete period: local law versus actual Mobius law -/

/-- Selected-prime zero-free cells on complete aligned `11^2` carriers. -/
def physicalSquareElevenLocalZeroFreeCells (R : ℕ) : Finset ℕ :=
  (physicalSquareCompleteCRTCarrier ({11} : Finset ℕ) R).filter fun k =>
    tSquareZeroFreeAt 11 k

/-- Selected-prime no-flip cells on complete aligned `11^2` carriers. -/
def physicalSquareElevenLocalNoFlipCells (R : ℕ) : Finset ℕ :=
  (physicalSquareCompleteCRTCarrier ({11} : Finset ℕ) R).filter fun k =>
    tSquareZeroFreeAt 11 k ∧ tNoFlipAt 11 k

/-- Selected-prime singleton-flip cells on complete aligned `11^2` carriers. -/
def physicalSquareElevenLocalSingletonFlipCells
    (R : ℕ) (i : Fin 6) : Finset ℕ :=
  (physicalSquareCompleteCRTCarrier ({11} : Finset ℕ) R).filter fun k =>
    tSquareZeroFreeAt 11 k ∧ tSingletonFlipAt 11 i k

/-- At `R = 243`, the physical transition carrier is exactly one aligned
`11^2 = 121` period. -/
theorem physicalSquareCompleteCRTCarrier_eleven_243_card :
    (physicalSquareCompleteCRTCarrier ({11} : Finset ℕ) 243).card = 121 := by
  native_decide

/-- The complete physical carrier realizes the certified selected-prime
zero-free count law. -/
theorem physicalSquareElevenLocalZeroFreeCells_243_card :
    (physicalSquareElevenLocalZeroFreeCells 243).card = 115 := by
  native_decide

/-- The complete physical carrier realizes the certified selected-prime
no-flip count law. -/
theorem physicalSquareElevenLocalNoFlipCells_243_card :
    (physicalSquareElevenLocalNoFlipCells 243).card = 55 := by
  native_decide

/-- Every selected-prime singleton-flip class has the certified size `10`. -/
theorem physicalSquareElevenLocalSingletonFlipCells_243_card (i : Fin 6) :
    (physicalSquareElevenLocalSingletonFlipCells 243 i).card = 10 := by
  fin_cases i <;> native_decide

/-- There is no geometric square-clock boundary at the first aligned generic
period. -/
theorem physicalSquareCRTGeometricBoundaryCells_eleven_243_eq_empty :
    physicalSquareCRTGeometricBoundaryCells ({11} : Finset ℕ) 243 = ∅ := by
  native_decide

/-- Consequently the actual `T` square-clock boundary is also empty at this
stage. -/
theorem physicalSquareCRTBoundaryCells_eleven_243_eq_empty :
    physicalSquareCRTBoundaryCells ({11} : Finset ℕ) 243 = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro k hk
  have hkGeom :=
    physicalSquareCRTBoundaryCells_subset_geometric ({11} : Finset ℕ) 243 hk
  rw [physicalSquareCRTGeometricBoundaryCells_eleven_243_eq_empty] at hkGeom
  simp at hkGeom

@[simp] theorem boundaryT_eleven_243_eq_zero :
    boundaryT ({11} : Finset ℕ) 243 = 0 := by
  simp [boundaryT, physicalSquareCRTBoundaryCells_eleven_243_eq_empty]

private theorem moebius_59049_eq_zero : μ 59049 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  have hunit := hsq 3 (by norm_num : 3 * 3 ∣ 59049)
  rw [Nat.isUnit_iff] at hunit
  norm_num at hunit

/-- The first cell of this complete `11^2` period is locally zero-free for prime
`11`. -/
theorem fourteenSevenSixTwo_mem_eleven_local_243 :
    14762 ∈ physicalSquareElevenLocalZeroFreeCells 243 := by
  native_decide

/-- The same cell is absent from the actual Mobius `T` population: its first
physical coordinate is `59049`, which has a `3^2` factor. -/
theorem fourteenSevenSixTwo_not_mem_actual_complete_eleven_243 :
    14762 ∉ physicalSquareCompleteCRTCells ({11} : Finset ℕ) 243 := by
  intro hk
  have hkT : 14762 ∈ physicalSquareTTransitionCells 243 :=
    physicalSquareCompleteCRTCells_subset ({11} : Finset ℕ) 243 hk
  have hstates := (Finset.mem_filter.mp hkT).2
  rcases hstates with ⟨hsrc, _hdst⟩
  change
    chiA (threeSlotState 14762) ≠ 0 ∧
      chiB (threeSlotState 14762) ≠ 0 ∧
        chiC (threeSlotState 14762) ≠ 0 at hsrc
  have ha := hsrc.1
  rw [chiA_threeSlotState] at ha
  have harg : 4 * 14762 + 1 = 59049 := by norm_num
  rw [harg, moebius_59049_eq_zero] at ha
  exact ha rfl

/-- Complete selected-prime CRT containment does not by itself realize the
actual Mobius `T` law, even when the square-clock boundary is empty. -/
theorem actual_complete_eleven_243_ne_selectedPrime_law :
    physicalSquareCompleteCRTCells ({11} : Finset ℕ) 243 ≠
      physicalSquareElevenLocalZeroFreeCells 243 := by
  intro h
  apply fourteenSevenSixTwo_not_mem_actual_complete_eleven_243
  rw [h]
  exact fourteenSevenSixTwo_mem_eleven_local_243

end RHLean.Analysis
