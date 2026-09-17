import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_FULL_ORBIT_RECURSION»

/-!
# The raw-parent inert survivor is genuinely untouched by the current owner

After completing every raw-parent orbit occurring under a greatest-owner fibre,
the exact descending recursion leaves an explicit `r`-inert survivor.  For the
actual descending chronology `r > p`, this packet contains no hidden double-r
corner: if both coordinates contained `r`, stripping `r` from one endpoint
would produce a physical r-crossing child in the same `(p,sig)` cell, so the
orientation-preserving stripped pair would already occur in the raw-parent
orbit set.

Hence every inert pair is r-free in both coordinates, stripping r fixes the
pair pointwise, and every fresh prime still separating the pair is strictly
smaller than r.  The inert term is therefore literal persistence to lower
owners, not a new same-scale boundary or energy error.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Inert means the current descending owner is absent.**  Above the first
owner p, an r-inert same-branch pair cannot have r in both coordinates. -/
theorem lowOwnerFirstOwnerRawParentOrbitInert_not_dvd_owner
    {R p r : ℕ} {sig : Finset ℕ} {mn : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hinert : mn ∈
      lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
        (lowOwnerRevealedPrimesAbove R r) r) :
    ¬ r ∣ mn.1 ∧ ¬ r ∣ mn.2 := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hinert with ⟨hcell, hnotRaw⟩
  rcases Finset.mem_filter.mp hcell with ⟨hsame, hmBase, hnBase⟩
  rcases Finset.mem_filter.mp hsame with ⟨_hprod, hsigAbove, hdivIff⟩
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with
    ⟨hnSq, hnPos⟩
  have hnotM : ¬ r ∣ m := by
    intro hrm
    have hrn : r ∣ n := hdivIff.mp hrm
    let un := squarefreePrimeFamilyParent r n
    have hunBase : un ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
      dsimp [un]
      exact lowOwnerFirstOwner_primeParent_mem_same_base hp hr hpr hnBase
    have hunCar := (Finset.mem_filter.mp hunBase).1
    have hunPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hunCar).2
    have hrun : ¬ r ∣ un := by
      dsimp [un]
      exact squarefreePrimeFamilyParent_not_dvd hr hnSq
    have hnEq : r * un = n := by
      dsimp [un, squarefreePrimeFamilyParent]
      rw [if_pos hrn]
      exact Nat.mul_div_cancel' hrn
    have hsigMoved :
        lowOwnerRevealedPrimeSignature
            (lowOwnerRevealedPrimesAbove R r) m =
          lowOwnerRevealedPrimeSignature
            (lowOwnerRevealedPrimesAbove R r) un := by
      calc
        lowOwnerRevealedPrimeSignature
            (lowOwnerRevealedPrimesAbove R r) m =
            lowOwnerRevealedPrimeSignature
              (lowOwnerRevealedPrimesAbove R r) n := hsigAbove
        _ = lowOwnerRevealedPrimeSignature
              (lowOwnerRevealedPrimesAbove R r) (r * un) := by rw [hnEq]
        _ = lowOwnerRevealedPrimeSignature
              (lowOwnerRevealedPrimesAbove R r) un :=
          lowOwnerRevealedPrimeSignature_mul_owner_eq_above hr hunPos
    have hcross : (m, un) ∈
        lowOwnerRevealedCrossPairCarrier R
          (lowOwnerRevealedPrimesAbove R r) r := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hmCar, hunCar⟩,
          ⟨hsigMoved, Or.inl ⟨hrm, hrun⟩⟩⟩
    have hcellCross : (m, un) ∈
        lowOwnerFirstOwnerCellRevealedCrossCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r :=
      Finset.mem_filter.mpr ⟨hcross, hmBase, hunBase⟩
    have hownerChild : (m, un) ∈
        lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r := by
      rw [← lowOwnerFirstOwnerCellRevealedCrossCarrier_above_eq_polarizationGreatestOwner
        hr]
      exact hcellCross
    have hrunParent : squarefreePrimeFamilyParent r un = un := by
      simp [squarefreePrimeFamilyParent, hrun]
    have hrawEq :
        lowOwnerFirstOwnerPolarizationRawParent r (m, un) =
          lowOwnerFirstOwnerPolarizationRawParent r (m, n) := by
      unfold lowOwnerFirstOwnerPolarizationRawParent
      simp only
      rw [hrunParent]
      dsimp [un]
    have hrawMem :
        lowOwnerFirstOwnerPolarizationRawParent r (m, n) ∈
          lowOwnerFirstOwnerPolarizationRawParentSet R p sig r := by
      rw [← hrawEq]
      exact Finset.mem_image.mpr ⟨(m, un), hownerChild, rfl⟩
    exact hnotRaw hrawMem
  have hnotN : ¬ r ∣ n := by
    intro hrn
    exact hnotM (hdivIff.mpr hrn)
  exact ⟨hnotM, hnotN⟩

/-- Therefore stripping the current owner fixes every inert pair pointwise. -/
theorem lowOwnerFirstOwnerRawParentOrbitInert_rawParent_eq_self
    {R p r : ℕ} {sig : Finset ℕ} {mn : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hinert : mn ∈
      lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
        (lowOwnerRevealedPrimesAbove R r) r) :
    lowOwnerFirstOwnerPolarizationRawParent r mn = mn := by
  have hfree :=
    lowOwnerFirstOwnerRawParentOrbitInert_not_dvd_owner hp hr hpr hinert
  rcases mn with ⟨m, n⟩
  simp [lowOwnerFirstOwnerPolarizationRawParent,
    squarefreePrimeFamilyParent, hfree.1, hfree.2]

/-- **Strict chronological descent of the inert packet.**  Every fresh prime
that still separates an inert pair is strictly below the current owner r. -/
theorem lowOwnerFirstOwnerRawParentOrbitInert_fresh_lt_owner
    {R p r q : ℕ} {sig : Finset ℕ} {mn : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hinert : mn ∈
      lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
        (lowOwnerRevealedPrimesAbove R r) r)
    (hqFresh : q ∈ squarefreePairFreshPrimeSet mn.1 mn.2) :
    q < r := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hinert with ⟨hcell, _hnotRaw⟩
  rcases Finset.mem_filter.mp hcell with ⟨hsame, hmBase, hnBase⟩
  rcases Finset.mem_filter.mp hsame with ⟨_hprod, hsigAbove, _hdivIff⟩
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
  have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
  rcases freshPrime_of_nonzeroPhysicalPair hmCar hnCar hqFresh with
    ⟨hqPrime, hqX⟩
  have hfree :=
    lowOwnerFirstOwnerRawParentOrbitInert_not_dvd_owner hp hr hpr hinert
  by_contra hnotlt
  have hrq : r ≤ q := Nat.le_of_not_gt hnotlt
  by_cases hqr : q = r
  · subst q
    have hxor :=
      (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
        hr hmPos hnPos).1 hqFresh
    rcases hxor with h | h
    · exact hfree.1 h.1
    · exact hfree.2 h.1
  · have hrqStrict : r < q := by omega
    have hsameFace :=
      revealedAbove_signature_eq_implies_face_eq
        hsigAbove hqPrime hrqStrict hqX
    unfold squarefreePairFreshPrimeSet at hqFresh
    rcases Finset.mem_union.mp hqFresh with hleft | hright
    · rcases Finset.mem_sdiff.mp hleft with ⟨hqm, hqn⟩
      exact hqn (hsameFace.mp hqm)
    · rcases Finset.mem_sdiff.mp hright with ⟨hqn, hqm⟩
      exact hqm (hsameFace.mpr hqn)

end RHLean.Proof
