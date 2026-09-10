import Mathlib
import RHLean.Analysis.OutsidePrimeCompleteDeletionFirstMoment
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm

/-!
# Six-offset q-square transport for the physical deletion channel

The fixed-owner magnitude estimate in `OutsidePrimeCompleteDeletionFirstMoment`
forgets which of the six physical affine sites was hit.  This file keeps that
information and records the exact quotient map

`d = (4*k+a)/q^2`,

with inverse source cell `(q^2*d-a)/4` on the contact locus.  In particular the
selected-prime degree-one field is transported by *pullback to the source cell*;
it is not replaced by the ordinary Mobius weight of `d`.

The final finite certificate records the smallest obstruction to that literal
replacement.  On one complete `{11}` / `3^2` super-period the actual least-owner
`q=3` selected-sign channel has signed mass `2280`, whereas the corresponding
plain rough Mobius daughter through `2` has mass `0`.

Thus the local contact bijection and the complementary CRT tensor theorem from
#638 survive, but a physical q-owner channel is not itself a Go daughter.  Any
energy recurrence has to retain this affine pullback field (or reassemble the
owners globally before taking a norm).
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Integer form of the selected degree-one observable. -/
def selectedDegreeOneProjectionInt (P : Finset ℕ) (k : ℕ) : ℤ :=
  selectedPrimeSign P (tActiveForm (0 : Fin 3) k) -
    selectedPrimeSign P (tActiveForm (1 : Fin 3) k) +
      selectedPrimeSign P (tActiveForm (2 : Fin 3) k)

@[simp] theorem selectedDegreeOneProjection_eq_intCast
    (P : Finset ℕ) (k : ℕ) :
    selectedDegreeOneProjection P k =
      ((selectedDegreeOneProjectionInt P k : ℤ) : ℝ) := by
  rfl

/-- Daughter integer produced by a q-square contact at physical offset `a`. -/
def qSquareOffsetDaughter (q a k : ℕ) : ℕ :=
  (4 * k + a) / (q * q)

/-- Source cell reconstructed from a tagged q-square daughter. -/
def qSquareOffsetSourceCell (q a d : ℕ) : ℕ :=
  (q * q * d - a) / 4

/-- On the contact locus the quotient is exact. -/
theorem qSquareOffsetDaughter_exact
    {q a k : ℕ} (hdiv : q * q ∣ 4 * k + a) :
    q * q * qSquareOffsetDaughter q a k = 4 * k + a := by
  unfold qSquareOffsetDaughter
  exact Nat.mul_div_cancel' hdiv

/-- The tagged affine substitution reconstructs the original physical cell. -/
theorem qSquareOffsetSourceCell_daughter
    {q a k : ℕ} (hdiv : q * q ∣ 4 * k + a) :
    qSquareOffsetSourceCell q a (qSquareOffsetDaughter q a k) = k := by
  have hexact := qSquareOffsetDaughter_exact hdiv
  unfold qSquareOffsetSourceCell
  have hsub :
      q * q * qSquareOffsetDaughter q a k - a = 4 * k := by
    omega
  rw [hsub]
  omega

/-- The six-offset carrier is exactly the union of tagged q-square contacts. -/
theorem mem_physicalSquareHitCells_iff
    {K q k : ℕ} (hq : q.Prime) :
    k ∈ physicalSquareHitCells K q ↔
      k < K ∧ physicalSquarePrimeAtEdge k q := by
  constructor
  · intro hk
    unfold physicalSquareHitCells at hk
    rcases Finset.mem_biUnion.mp hk with ⟨a, ha, hka⟩
    rcases Finset.mem_filter.mp hka with ⟨hkK, hdiv⟩
    refine ⟨Finset.mem_range.mp hkK, hq, a, ha, ?_⟩
    simpa [pow_two] using hdiv
  · rintro ⟨hkK, hhit⟩
    exact mem_physicalSquareHitCells_of_squarePrimeAtEdge hkK hhit

/-- If `q` is the least square-prime owner, no smaller prime can hit any of the
six physical offsets.  This is the exact earlier-square exclusion needed by the
complementary field. -/
theorem outsidePrimeLeastDeletionChannel_no_earlier_square
    {P O : Finset ℕ} {q k p : ℕ}
    (hk : k ∈ outsidePrimeLeastDeletionChannelCells P O q)
    (hp : p.Prime) (hpq : p < q) :
    ¬ physicalSquarePrimeAtEdge k p := by
  intro hpHit
  rcases Finset.mem_filter.mp hk with ⟨hkDel, howner⟩
  have hne := outsidePrimeDeletion_leastSquare_ne_none hkDel
  cases hleast : physicalLeastOddSquarePrime k with
  | none => exact (hne hleast).elim
  | some r =>
      have hrq : r = q := by
        simpa [hleast] using howner
      have hle : r ≤ p := physicalLeastOddSquarePrime_le hleast hpHit
      omega

/-- Every q-owned deleted cell supplies an actual tagged contact among the six
physical offsets. -/
theorem outsidePrimeLeastDeletionChannel_exists_offset
    {P O : Finset ℕ} {q k : ℕ}
    (hk : k ∈ outsidePrimeLeastDeletionChannelCells P O q) :
    ∃ a ∈ physicalTransitionActiveOffsets,
      q * q ∣ 4 * k + a := by
  rcases Finset.mem_filter.mp hk with ⟨hkDel, howner⟩
  have hne := outsidePrimeDeletion_leastSquare_ne_none hkDel
  cases hleast : physicalLeastOddSquarePrime k with
  | none => exact (hne hleast).elim
  | some r =>
      have hrq : r = q := by
        simpa [hleast] using howner
      subst r
      rcases physicalLeastOddSquarePrime_some_spec hleast with
        ⟨_hq, a, ha, hdiv⟩
      exact ⟨a, ha, by simpa [pow_two] using hdiv⟩

/-- The exact transported selected field attached to a tagged daughter.  The
source-cell pullback is the feature that a literal Go identification omits. -/
def selectedDegreeOneOffsetDaughterField
    (P : Finset ℕ) (q a d : ℕ) : ℤ :=
  selectedDegreeOneProjectionInt P (qSquareOffsetSourceCell q a d)

/-- On every contact, transporting the selected field to the daughter and then
pulling it back recovers the original physical weight exactly. -/
theorem selectedDegreeOneOffsetDaughterField_contact
    (P : Finset ℕ) {q a k : ℕ}
    (hdiv : q * q ∣ 4 * k + a) :
    selectedDegreeOneOffsetDaughterField P q a
        (qSquareOffsetDaughter q a k) =
      selectedDegreeOneProjectionInt P k := by
  rw [selectedDegreeOneOffsetDaughterField,
    qSquareOffsetSourceCell_daughter hdiv]

/-! ## The q=3 complete-orbit obstruction to a literal Go daughter -/

/-- Computable six-offset `{11}`-selected q=3 contact population on one complete
period `4 * 3^2 * 11^2 = 4356`. -/
def elevenThreeCompleteSelectedDeletionCells : Finset ℕ :=
  (physicalSquareHitCells 4356 3).filter (tSquareZeroFreeAt 11)

/-- Its signed selected-prime degree-one mass, kept over `ℤ` so the complete
finite certificate is kernel-executable. -/
def elevenThreeCompleteSelectedDeletionMass : ℤ :=
  ∑ k ∈ elevenThreeCompleteSelectedDeletionCells,
    selectedDegreeOneProjectionInt ({11} : Finset ℕ) k

/-- The complete population has 2760 cells. -/
theorem elevenThreeCompleteSelectedDeletionCells_card :
    elevenThreeCompleteSelectedDeletionCells.card = 2760 := by
  native_decide

/-- **Finite counterexample to literal fixed-owner Go identification.** -/
theorem elevenThreeCompleteSelectedDeletionMass_eq_2280 :
    elevenThreeCompleteSelectedDeletionMass = 2280 := by
  native_decide

/-- For q=3, a 3-square hit is automatically the least odd square-prime owner. -/
theorem physicalLeastOddSquarePrime_eq_some_three_iff (k : ℕ) :
    physicalLeastOddSquarePrime k = some 3 ↔
      physicalSquarePrimeAtEdge k 3 := by
  constructor
  · exact physicalLeastOddSquarePrime_some_spec
  · intro hthree
    have hne : physicalLeastOddSquarePrime k ≠ none := by
      intro hnone
      have hno := (physicalLeastOddSquarePrime_eq_none_iff k).mp hnone
      exact hno ⟨3, hthree⟩
    cases hleast : physicalLeastOddSquarePrime k with
    | none => exact (hne hleast).elim
    | some p =>
        have hpHit := physicalLeastOddSquarePrime_some_spec hleast
        have hpLe : p ≤ 3 := physicalLeastOddSquarePrime_le hleast hthree
        have hpPrime : p.Prime := hpHit.1
        have hpOdd : p % 2 = 1 := physicalSquarePrimeAtEdge_odd hpHit
        have hthreeLe : 3 ≤ p := by
          have hpTwo : 2 ≤ p := hpPrime.two_le
          omega
        have hp : p = 3 := by omega
        simpa [hp] using hleast

/-- The computable population above is literally the repository's least-owner
q=3 deletion carrier for `{11}` on the same complete prefix. -/
theorem outsidePrimeLeastDeletionChannelCells_eleven_three_4356 :
    outsidePrimeLeastDeletionChannelCells
        ({11} : Finset ℕ) (Finset.range 4356) 3 =
      elevenThreeCompleteSelectedDeletionCells := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkDel, howner⟩
    rcases (mem_outsidePrimeDeletionCells_iff.mp hkDel) with
      ⟨hkRange, hselected, _hnotActual⟩
    have hne := outsidePrimeDeletion_leastSquare_ne_none hkDel
    cases hleast : physicalLeastOddSquarePrime k with
    | none => exact (hne hleast).elim
    | some p =>
        have hp3 : p = 3 := by
          simpa [hleast] using howner
        subst p
        have hhit : physicalSquarePrimeAtEdge k 3 :=
          physicalLeastOddSquarePrime_some_spec hleast
        apply Finset.mem_filter.mpr
        constructor
        · exact (mem_physicalSquareHitCells_iff (K := 4356)
            (q := 3) (k := k) (by norm_num)).2
              ⟨Finset.mem_range.mp hkRange, hhit⟩
        · simpa [outsidePrimeSelectedZeroFreeAt] using hselected
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkSquare, h11zero⟩
    rcases (mem_physicalSquareHitCells_iff (K := 4356)
        (q := 3) (k := k) (by norm_num)).1 hkSquare with
      ⟨hklt, hthree⟩
    have hleast : physicalLeastOddSquarePrime k = some 3 :=
      (physicalLeastOddSquarePrime_eq_some_three_iff k).2 hthree
    have hselected :
        outsidePrimeSelectedZeroFreeAt ({11} : Finset ℕ) k := by
      simpa [outsidePrimeSelectedZeroFreeAt] using h11zero
    have hnotActual : ¬ outsidePrimeActualZeroFreeAt k := by
      intro hactual
      have hedge :
          threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
            threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates := by
        exact ⟨
          (isThreeSlotNonzeroState_iff_mem_physicalThreeSlotNonzeroStates _).mp
            hactual.1,
          (isThreeSlotNonzeroState_iff_mem_physicalThreeSlotNonzeroStates _).mp
            hactual.2⟩
      have hnone : physicalLeastOddSquarePrime k = none :=
        (physicalLeastOddSquarePrime_eq_none_iff_nonzeroEdge k).2 hedge
      rw [hleast] at hnone
      simp at hnone
    apply Finset.mem_filter.mpr
    constructor
    · exact mem_outsidePrimeDeletionCells_iff.mpr
        ⟨Finset.mem_range.mpr hklt, hselected, hnotActual⟩
    · simp [hleast]

/-- The ordinary q=3 rough daughter at cutoff 2 is `mu(1)+mu(2)=0`. -/
theorem roughCofactorMobiusPrefixMass_three_two_eq_zero :
    RHLean.Proof.roughCofactorMobiusPrefixMass 3 2 = 0 := by
  rw [RHLean.Proof.roughCofactorMobiusPrefixMass_eq_cofactorMobiusPrefixMass
    (by norm_num : 2 < 3)]
  norm_num [RHLean.Proof.cofactorMobiusPrefixMass,
    RHLean.Proof.canonicalMoebiusWeight,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- Consequently the actual q=3 selected-sign source cannot be identified with
that plain rough daughter, even on a complete least-owner super-period. -/
theorem elevenThree_selectedMass_ne_plainRoughDaughter :
    ((elevenThreeCompleteSelectedDeletionMass : ℤ) : ℂ) ≠
      RHLean.Proof.roughCofactorMobiusPrefixMass 3 2 := by
  rw [elevenThreeCompleteSelectedDeletionMass_eq_2280,
    roughCofactorMobiusPrefixMass_three_two_eq_zero]
  norm_num

end RHLean.Analysis
