import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_FULL_ORBIT_RECURSION»
import «research.GLOBAL_RETURNED_CORE_STOKES_BOUNDARY_IDENTIFICATION»

/-!
# Raw-parent carrier as a revealed prefix star

For a fixed first-owner cell `(p,sig)` and descending greatest owner `r`, the
orientation-preserving raw parents have a simple intrinsic description.
They are exactly the pairs `(a,b)` such that

* `a,b` lie in the same p-free base cell;
* after all primes strictly above `r` have been revealed, `a,b` are in the same
  branch;
* neither coordinate is divisible by `r`;
* at least one mixed r-child remains on the physical clock:
  `r*a <= X_R` or `r*b <= X_R`.

Thus the raw-parent carrier is a literal two-sided prefix star inside every
already-revealed branch.  This is the carrier statement needed to factor signed
threshold four-corner sums before any Cauchy--Schwarz estimate.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Intrinsic prefix-star description of the raw-parent carrier. -/
def lowOwnerFirstOwnerRawParentPrefixStar
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerFirstOwnerBaseFiber R p sig).product
      (lowOwnerFirstOwnerBaseFiber R p sig)).filter fun parent =>
    lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R r) parent.1 =
      lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R r) parent.2 ∧
    ¬ r ∣ parent.1 ∧
    ¬ r ∣ parent.2 ∧
    (r * parent.1 ≤ squareRootEndpoint R ∨
      r * parent.2 ≤ squareRootEndpoint R)

/-- Every occurring raw parent lies in the intrinsic prefix star. -/
theorem lowOwnerFirstOwnerPolarizationRawParentSet_subset_prefixStar
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    lowOwnerFirstOwnerPolarizationRawParentSet R p sig r ⊆
      lowOwnerFirstOwnerRawParentPrefixStar R p sig r := by
  intro parent hparent
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨_hr, _hpr, haBase, hbBase, hra, hrb⟩
  have hsigAbove :=
    lowOwnerFirstOwnerPolarizationRawParent_revealedAbove_eq hp hparent
  rcases Finset.mem_image.mp hparent with ⟨child, hchild, hrawEq⟩
  have hfixed : child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        R p sig r parent :=
    Finset.mem_filter.mpr ⟨hchild, hrawEq⟩
  have hphysical :
      r * parent.1 ≤ squareRootEndpoint R ∨
        r * parent.2 ≤ squareRootEndpoint R := by
    rcases lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed hfixed with
      hleft | hright
    · have hprod :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hchild).1).1
      have hmBase := (Finset.mem_product.mp hprod).1
      have hmCar := (Finset.mem_filter.mp hmBase).1
      have hmX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmCar).1).2
      left
      simpa [hleft] using hmX
    · have hprod :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hchild).1).1
      have hnBase := (Finset.mem_product.mp hprod).2
      have hnCar := (Finset.mem_filter.mp hnBase).1
      have hnX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnCar).1).2
      right
      simpa [hright] using hnX
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨haBase, hbBase⟩,
      ⟨hsigAbove, hra, hrb, hphysical⟩⟩

/-- A prefix-star parent with a physical left mixed child produces an actual
r-owner child. -/
private theorem lowOwnerFirstOwnerPrefixStar_leftChild_mem_ownerFiber
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hstar : parent ∈ lowOwnerFirstOwnerRawParentPrefixStar R p sig r)
    (hleft : r * parent.1 ≤ squareRootEndpoint R) :
    (r * parent.1, parent.2) ∈
      lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r := by
  rcases Finset.mem_filter.mp hstar with
    ⟨hprod, hsigAbove, hra, hrb, _hphysical⟩
  rcases Finset.mem_product.mp hprod with ⟨haBase, hbBase⟩
  have hraBase : r * parent.1 ∈ lowOwnerFirstOwnerBaseFiber R p sig :=
    lowOwnerFirstOwner_mul_larger_prime_mem_same_base_of_le
      hp hr hpr hra haBase hleft
  have haCar := (Finset.mem_filter.mp haBase).1
  have hbCar := (Finset.mem_filter.mp hbBase).1
  have hraCar := (Finset.mem_filter.mp hraBase).1
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
  have hsigMoved :
      lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) (r * parent.1) =
        lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) parent.2 := by
    calc
      lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) (r * parent.1) =
        lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) parent.1 :=
        lowOwnerRevealedPrimeSignature_mul_owner_eq_above hr haPos
      _ = lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) parent.2 := hsigAbove
  have hrLeft : r ∣ r * parent.1 := ⟨parent.1, rfl⟩
  have hcross : (r * parent.1, parent.2) ∈
      lowOwnerRevealedCrossPairCarrier R
        (lowOwnerRevealedPrimesAbove R r) r := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hraCar, hbCar⟩,
        ⟨hsigMoved, Or.inl ⟨hrLeft, hrb⟩⟩⟩
  have howner :
      IsSquarefreePairGreatestFreshPrimeOwner
        r (r * parent.1) parent.2 :=
    descendingCrossPair_greatestFreshOwner hr hcross
  have hne : r * parent.1 ≠ parent.2 := by
    intro heq
    apply hrb
    exact ⟨parent.1, heq.symm⟩
  unfold lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
    lowOwnerFirstOwnerBaseOffDiagonalPairCarrier
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hraBase, hbBase⟩, hne⟩,
      howner⟩

/-- Symmetric construction from a physical right mixed child. -/
private theorem lowOwnerFirstOwnerPrefixStar_rightChild_mem_ownerFiber
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hstar : parent ∈ lowOwnerFirstOwnerRawParentPrefixStar R p sig r)
    (hright : r * parent.2 ≤ squareRootEndpoint R) :
    (parent.1, r * parent.2) ∈
      lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r := by
  rcases Finset.mem_filter.mp hstar with
    ⟨hprod, hsigAbove, hra, hrb, _hphysical⟩
  rcases Finset.mem_product.mp hprod with ⟨haBase, hbBase⟩
  have hrbBase : r * parent.2 ∈ lowOwnerFirstOwnerBaseFiber R p sig :=
    lowOwnerFirstOwner_mul_larger_prime_mem_same_base_of_le
      hp hr hpr hrb hbBase hright
  have haCar := (Finset.mem_filter.mp haBase).1
  have hbCar := (Finset.mem_filter.mp hbBase).1
  have hrbCar := (Finset.mem_filter.mp hrbBase).1
  have hbPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar).2
  have hsigMoved :
      lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) parent.1 =
        lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) (r * parent.2) := by
    calc
      lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) parent.1 =
        lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) parent.2 := hsigAbove
      _ = lowOwnerRevealedPrimeSignature
          (lowOwnerRevealedPrimesAbove R r) (r * parent.2) :=
        (lowOwnerRevealedPrimeSignature_mul_owner_eq_above hr hbPos).symm
  have hrRight : r ∣ r * parent.2 := ⟨parent.2, rfl⟩
  have hcross : (parent.1, r * parent.2) ∈
      lowOwnerRevealedCrossPairCarrier R
        (lowOwnerRevealedPrimesAbove R r) r := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haCar, hrbCar⟩,
        ⟨hsigMoved, Or.inr ⟨hrRight, hra⟩⟩⟩
  have howner :
      IsSquarefreePairGreatestFreshPrimeOwner
        r parent.1 (r * parent.2) :=
    descendingCrossPair_greatestFreshOwner hr hcross
  have hne : parent.1 ≠ r * parent.2 := by
    intro heq
    apply hra
    exact ⟨parent.2, heq⟩
  unfold lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
    lowOwnerFirstOwnerBaseOffDiagonalPairCarrier
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haBase, hrbBase⟩, hne⟩,
      howner⟩

/-- Every intrinsic prefix-star parent actually occurs as a raw parent. -/
theorem lowOwnerFirstOwnerRawParentPrefixStar_subset_rawParentSet
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRawParentPrefixStar R p sig r ⊆
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r := by
  intro parent hstar
  have hphysical := (Finset.mem_filter.mp hstar).2.2.2
  rcases hphysical with hleft | hright
  · have hchild :=
      lowOwnerFirstOwnerPrefixStar_leftChild_mem_ownerFiber
        hp hr hpr hstar hleft
    unfold lowOwnerFirstOwnerPolarizationRawParentSet
    refine Finset.mem_image.mpr ⟨(r * parent.1, parent.2), hchild, ?_⟩
    unfold lowOwnerFirstOwnerPolarizationRawParent
      squarefreePrimeFamilyParent
    have hdata := (Finset.mem_filter.mp hstar).2
    have hrb : ¬ r ∣ parent.2 := hdata.2.2.1
    simp [hrb, Nat.mul_div_cancel_left parent.1 hr.pos]
  · have hchild :=
      lowOwnerFirstOwnerPrefixStar_rightChild_mem_ownerFiber
        hp hr hpr hstar hright
    unfold lowOwnerFirstOwnerPolarizationRawParentSet
    refine Finset.mem_image.mpr ⟨(parent.1, r * parent.2), hchild, ?_⟩
    unfold lowOwnerFirstOwnerPolarizationRawParent
      squarefreePrimeFamilyParent
    have hdata := (Finset.mem_filter.mp hstar).2
    have hra : ¬ r ∣ parent.1 := hdata.2.1
    simp [hra, Nat.mul_div_cancel_left parent.2 hr.pos]

/-- **Exact prefix-star carrier identification.** -/
theorem lowOwnerFirstOwnerPolarizationRawParentSet_eq_prefixStar
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerPolarizationRawParentSet R p sig r =
      lowOwnerFirstOwnerRawParentPrefixStar R p sig r := by
  apply Finset.Subset.antisymm
  · exact lowOwnerFirstOwnerPolarizationRawParentSet_subset_prefixStar hp
  · exact lowOwnerFirstOwnerRawParentPrefixStar_subset_rawParentSet hp hr hpr

end RHLean.Proof
