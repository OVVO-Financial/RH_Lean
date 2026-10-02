import Mathlib
import «research.VF_MID_ODD_FRACTIONAL_CLUSTER»

/-!
# Cross-owner injectivity of the recursive VF child descent

The #848 owner split already shows that every genuinely recursive least-prime
owner satisfies

  p^3 < (R+1)^2.

This file combines that cubic condition with the physical square-band width.
For R >= 7, any child m stripped from such an owner must satisfy

  2R < m < R^2.

The lower bound is decisive.  If two distinct owners p < q produced the same
child m, then the two parent sites p*m and q*m would be separated by at least
m >= 2R+1, while both are required to lie in the same open square band, whose
integer span is only 2R.  Hence distinct recursive owner fibres have disjoint
child carriers.

This is a genuine global injectivity statement across recursive owners, not
only the within-fibre injectivity proved earlier.
-/

noncomputable section

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- A rough child of a parity-late recursive owner is already beyond twice the
square index once R >= 7. -/
theorem vfMidLateRecursiveOwner_roughChild_gt_two_mul
    {R p m : ℕ} (hR : 7 ≤ R)
    (hp : p ∈ vfMidSquareBandLateRecursiveOwners R)
    (hm : m ∈ vfMidSquareBandOwnerRoughChildren R p) :
    2 * R < m := by
  have hrec : p ^ 3 < (R + 1) ^ 2 :=
    (Finset.mem_filter.mp hp).2
  rcases Finset.mem_filter.mp hm with ⟨_hmIcc, hdata⟩
  have hlo : R ^ 2 < p * m := hdata.1
  by_contra hnot
  have hmle : m ≤ 2 * R := by omega
  have hpmle : p * m ≤ p * (2 * R) :=
    Nat.mul_le_mul_left p hmle
  have hRp : R < 2 * p := by
    by_contra hnotRp
    have h2ple : 2 * p ≤ R := by omega
    have hbound : p * (2 * R) ≤ R ^ 2 := by
      calc
        p * (2 * R) = (2 * p) * R := by ring
        _ ≤ R * R := Nat.mul_le_mul_right R h2ple
        _ = R ^ 2 := by ring
    omega
  have hRp1 : R + 1 ≤ 2 * p := by omega
  have h8 : 8 ≤ R + 1 := by omega
  have hscale :
      8 * (R + 1) ^ 2 ≤ (R + 1) ^ 3 := by
    calc
      8 * (R + 1) ^ 2 ≤
          (R + 1) * (R + 1) ^ 2 :=
        Nat.mul_le_mul_right ((R + 1) ^ 2) h8
      _ = (R + 1) ^ 3 := by ring
  have hcube :
      (R + 1) ^ 3 ≤ (2 * p) ^ 3 :=
    Nat.pow_le_pow_left hRp1 3
  have hscaled :
      8 * (R + 1) ^ 2 ≤ 8 * p ^ 3 := by
    calc
      8 * (R + 1) ^ 2 ≤ (R + 1) ^ 3 := hscale
      _ ≤ (2 * p) ^ 3 := hcube
      _ = 8 * p ^ 3 := by ring
  have hterminal : (R + 1) ^ 2 ≤ p ^ 3 := by omega
  exact (Nat.not_lt_of_ge hterminal) hrec

/-- The same lower bound on the repository's stripped-child carrier. -/
theorem vfMidLateRecursiveOwner_child_gt_two_mul
    {R p m : ℕ} (hR : 7 ≤ R)
    (hp : p ∈ vfMidSquareBandLateRecursiveOwners R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    2 * R < m := by
  have hpLate : p ∈ vfMidSquareBandLateOwnerPrimes 2 R :=
    (Finset.mem_filter.mp hp).1
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (Finset.mem_filter.mp hpLate).1
  have heq :=
    vfMidSquareBandCompositeOwnerChildren_eq_rough
      (by omega : 3 ≤ R) hpOwner
  apply vfMidLateRecursiveOwner_roughChild_gt_two_mul hR hp
  rw [← heq]
  exact hm

/-- Recursive children stay strictly below the parent square scale. -/
theorem vfMidLateRecursiveOwner_child_lt_square
    {R p m : ℕ} (hR : 7 ≤ R)
    (_hp : p ∈ vfMidSquareBandLateRecursiveOwners R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    m < R ^ 2 :=
  vfMidSquareBandCompositeOwnerChildren_lt_square (by omega) hm

/-- **Cross-owner uniqueness.** Two parity-late recursive owners in the same
square band cannot strip to the same child. -/
theorem vfMidLateRecursiveOwner_child_owner_unique
    {R p q m : ℕ} (hR : 7 ≤ R)
    (hp : p ∈ vfMidSquareBandLateRecursiveOwners R)
    (hq : q ∈ vfMidSquareBandLateRecursiveOwners R)
    (hmP : m ∈ vfMidSquareBandCompositeOwnerChildren R p)
    (hmQ : m ∈ vfMidSquareBandCompositeOwnerChildren R q) :
    p = q := by
  have hmgt :=
    vfMidLateRecursiveOwner_child_gt_two_mul hR hp hmP
  have hpLate : p ∈ vfMidSquareBandLateOwnerPrimes 2 R :=
    (Finset.mem_filter.mp hp).1
  have hqLate : q ∈ vfMidSquareBandLateOwnerPrimes 2 R :=
    (Finset.mem_filter.mp hq).1
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (Finset.mem_filter.mp hpLate).1
  have hqOwner : q ∈ vfMidSquareBandOwnerPrimes R :=
    (Finset.mem_filter.mp hqLate).1
  have heqP :=
    vfMidSquareBandCompositeOwnerChildren_eq_rough
      (by omega : 3 ≤ R) hpOwner
  have heqQ :=
    vfMidSquareBandCompositeOwnerChildren_eq_rough
      (by omega : 3 ≤ R) hqOwner
  have hmPRough : m ∈ vfMidSquareBandOwnerRoughChildren R p := by
    rw [← heqP]
    exact hmP
  have hmQRough : m ∈ vfMidSquareBandOwnerRoughChildren R q := by
    rw [← heqQ]
    exact hmQ
  rcases Finset.mem_filter.mp hmPRough with ⟨_hmPIcc, hP⟩
  rcases Finset.mem_filter.mp hmQRough with ⟨_hmQIcc, hQ⟩
  rcases hP with ⟨hPLow, hPHigh, _hPRough⟩
  rcases hQ with ⟨hQLow, hQHigh, _hQRough⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hstep : (p + 1) * m ≤ q * m :=
      Nat.mul_le_mul_right m (by omega)
    have hadd : p * m + m ≤ q * m := by
      simpa [Nat.add_mul] using hstep
    have hwidth : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by
      ring
    omega
  · have hstep : (q + 1) * m ≤ p * m :=
      Nat.mul_le_mul_right m (by omega)
    have hadd : q * m + m ≤ p * m := by
      simpa [Nat.add_mul] using hstep
    have hwidth : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by
      ring
    omega

/-- **Pairwise disjoint recursive child carriers.** Distinct recursive owners
have disjoint stripped-child sets for every R >= 7. -/
theorem vfMidLateRecursiveOwner_children_disjoint
    {R p q : ℕ} (hR : 7 ≤ R)
    (hp : p ∈ vfMidSquareBandLateRecursiveOwners R)
    (hq : q ∈ vfMidSquareBandLateRecursiveOwners R)
    (hpq : p ≠ q) :
    Disjoint
      (vfMidSquareBandCompositeOwnerChildren R p)
      (vfMidSquareBandCompositeOwnerChildren R q) := by
  rw [Finset.disjoint_left]
  intro m hmP hmQ
  exact hpq
    (vfMidLateRecursiveOwner_child_owner_unique
      hR hp hq hmP hmQ)

end RHLean.Analysis
