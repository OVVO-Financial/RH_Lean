import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_FOUR_CORNER_OCCUPANCY»
import «research.GLOBAL_RETURNED_CORE_VIRTUAL_OWNER_CORNER_CLASSIFICATION»

/-!
# Complete the raw-parent owner fibre by Dirichlet-zero virtual corners

For one greatest-owner raw parent `(a,b)` the actual physical owner fibre is a
subset of the two literal mixed corners

  `(r*a,b)`, `(a,r*b)`.

The preceding owner-transfer theorem proves that both virtual siblings carry the
same greatest owner `r`, even when one sibling lies beyond the physical clock.
The Dirichlet extension then supplies the missing fact needed for a signed rank
splice: a virtual sibling belongs to the physical fibre exactly when its moved
coordinate is still at most `X_R`; otherwise its polarization atom is exactly
zero.

Consequently the sum on the *actual* physical owner fibre equals the sum of the
two virtual mixed-corner atoms with no error term.  The existing owner-cube
identity may therefore be applied literally, giving

  owner fibre = next polarization - parent - double child.

This is an exact signed identity.  No square, norm, absolute value, inherited
energy, or boundary majorant is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Local copy of the physical base-cell closure needed below.  Keeping it here
avoids importing the later Stokes boundary layer into the raw-parent chain. -/
private theorem lowOwnerRawParent_mul_larger_prime_mem_same_base_of_le
    {R p r n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hrn : ¬ r ∣ n)
    (hn : n ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hupper : r * n ≤ squareRootEndpoint R) :
    r * n ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
  rcases Finset.mem_filter.mp hn with ⟨hnCar, hnData⟩
  rcases Finset.mem_filter.mp hnCar with ⟨hnIcc, hmuN⟩
  have hnOne : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
  have hnPos : 0 < n := Nat.succ_le_iff.mp hnOne
  have hmuRN : realMoebiusStep (r * n) ≠ 0 := by
    rw [realMoebiusStep_mul_prime_eq_neg hr hrn]
    exact neg_ne_zero.mpr hmuN
  have hrnCar : r * n ∈ lowOwnerNonzeroMobiusCarrier R := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.succ_le_iff.mpr (Nat.mul_pos hr.pos hnPos), hupper⟩,
        hmuRN⟩
  have hsig : squarefreeLowerPrimeSignature p (r * n) = sig := by
    rw [squarefreeLowerPrimeSignature_mul_larger_prime hr hpr hnPos, hnData.1]
  have hpnotr : ¬ p ∣ r := by
    intro hdiv
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hdiv
    exact (ne_of_lt hpr) heq
  have hpfree : ¬ p ∣ r * n := by
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with h | h
    · exact hpnotr h
    · exact hnData.2 h
  exact Finset.mem_filter.mpr ⟨hrnCar, ⟨hsig, hpfree⟩⟩

/-- Stripping `r` from the left virtual mixed corner returns the raw parent. -/
theorem lowOwnerFirstOwnerPolarizationRawParent_leftMixed_eq
    {r : ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime) (hrb : ¬ r ∣ parent.2) :
    lowOwnerFirstOwnerPolarizationRawParent
        r (r * parent.1, parent.2) = parent := by
  rcases parent with ⟨a, b⟩
  simp [lowOwnerFirstOwnerPolarizationRawParent,
    squarefreePrimeFamilyParent, hrb,
    Nat.mul_div_cancel_left a hr.pos]

/-- Stripping `r` from the right virtual mixed corner returns the raw parent. -/
theorem lowOwnerFirstOwnerPolarizationRawParent_rightMixed_eq
    {r : ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ parent.1) :
    lowOwnerFirstOwnerPolarizationRawParent
        r (parent.1, r * parent.2) = parent := by
  rcases parent with ⟨a, b⟩
  simp [lowOwnerFirstOwnerPolarizationRawParent,
    squarefreePrimeFamilyParent, hra,
    Nat.mul_div_cancel_left b hr.pos]

/-- The left virtual mixed sibling is physical exactly while its moved
coordinate remains on the square-root clock. -/
theorem mem_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_leftMixed_iff
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    (r * parent.1, parent.2) ∈
        lowOwnerFirstOwnerPolarizationFixedRawParentFiber
          R p sig r parent ↔
      r * parent.1 ≤ squareRootEndpoint R := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, hpr, haBase, hbBase, hra, hrb⟩
  have howners :=
    lowOwnerFirstOwnerPolarizationRawParent_mixedCorners_have_owner hp hparent
  constructor
  · intro hmem
    have hgreatest := (Finset.mem_filter.mp hmem).1
    have hoff := (Finset.mem_filter.mp hgreatest).1
    have hprod := (Finset.mem_filter.mp hoff).1
    have hleftBase := (Finset.mem_product.mp hprod).1
    have hleftCar := (Finset.mem_filter.mp hleftBase).1
    have hleftIcc := (Finset.mem_filter.mp hleftCar).1
    exact (Finset.mem_Icc.mp hleftIcc).2
  · intro hupper
    have hleftBase : r * parent.1 ∈
        lowOwnerFirstOwnerBaseFiber R p sig :=
      lowOwnerRawParent_mul_larger_prime_mem_same_base_of_le
        hp hr hpr hra haBase hupper
    have hprod : (r * parent.1, parent.2) ∈
        (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig) :=
      Finset.mem_product.mpr ⟨hleftBase, hbBase⟩
    have hne : r * parent.1 ≠ parent.2 := by
      intro heq
      have hfresh := howners.1.1
      rw [heq] at hfresh
      simp [squarefreePairFreshPrimeSet] at hfresh
    have hoff : (r * parent.1, parent.2) ∈
        lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig :=
      Finset.mem_filter.mpr ⟨hprod, hne⟩
    have hgreatest : (r * parent.1, parent.2) ∈
        lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r :=
      Finset.mem_filter.mpr ⟨hoff, howners.1⟩
    exact Finset.mem_filter.mpr
      ⟨hgreatest,
        lowOwnerFirstOwnerPolarizationRawParent_leftMixed_eq hr hrb⟩

/-- The right virtual mixed sibling is physical exactly while its moved
coordinate remains on the square-root clock. -/
theorem mem_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_rightMixed_iff
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    (parent.1, r * parent.2) ∈
        lowOwnerFirstOwnerPolarizationFixedRawParentFiber
          R p sig r parent ↔
      r * parent.2 ≤ squareRootEndpoint R := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, hpr, haBase, hbBase, hra, hrb⟩
  have howners :=
    lowOwnerFirstOwnerPolarizationRawParent_mixedCorners_have_owner hp hparent
  constructor
  · intro hmem
    have hgreatest := (Finset.mem_filter.mp hmem).1
    have hoff := (Finset.mem_filter.mp hgreatest).1
    have hprod := (Finset.mem_filter.mp hoff).1
    have hrightBase := (Finset.mem_product.mp hprod).2
    have hrightCar := (Finset.mem_filter.mp hrightBase).1
    have hrightIcc := (Finset.mem_filter.mp hrightCar).1
    exact (Finset.mem_Icc.mp hrightIcc).2
  · intro hupper
    have hrightBase : r * parent.2 ∈
        lowOwnerFirstOwnerBaseFiber R p sig :=
      lowOwnerRawParent_mul_larger_prime_mem_same_base_of_le
        hp hr hpr hrb hbBase hupper
    have hprod : (parent.1, r * parent.2) ∈
        (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig) :=
      Finset.mem_product.mpr ⟨haBase, hrightBase⟩
    have hne : parent.1 ≠ r * parent.2 := by
      intro heq
      have hfresh := howners.2.1
      rw [← heq] at hfresh
      simp [squarefreePairFreshPrimeSet] at hfresh
    have hoff : (parent.1, r * parent.2) ∈
        lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig :=
      Finset.mem_filter.mpr ⟨hprod, hne⟩
    have hgreatest : (parent.1, r * parent.2) ∈
        lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r :=
      Finset.mem_filter.mpr ⟨hoff, howners.2⟩
    exact Finset.mem_filter.mpr
      ⟨hgreatest,
        lowOwnerFirstOwnerPolarizationRawParent_rightMixed_eq hr hra⟩

/-- **Physical fibre equals the two virtual mixed atoms after Dirichlet zero
extension.**  A missing sibling contributes exactly zero, rather than a new
boundary population. -/
theorem sum_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_eq_virtualMixed
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    (∑ child ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        R p sig r parent,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p child) =
      lowOwnerFirstOwnerDirichletPolarizationAtom
        R p (r * parent.1, parent.2) +
      lowOwnerFirstOwnerDirichletPolarizationAtom
        R p (parent.1, r * parent.2) := by
  let F : Finset (ℕ × ℕ) :=
    lowOwnerFirstOwnerPolarizationFixedRawParentFiber R p sig r parent
  let L : ℕ × ℕ := (r * parent.1, parent.2)
  let U : ℕ × ℕ := (parent.1, r * parent.2)
  change (∑ child ∈ F,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p child) =
    lowOwnerFirstOwnerDirichletPolarizationAtom R p L +
      lowOwnerFirstOwnerDirichletPolarizationAtom R p U
  have hLiff : L ∈ F ↔ r * parent.1 ≤ squareRootEndpoint R := by
    dsimp [F, L]
    exact mem_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_leftMixed_iff
      hp hparent
  have hUiff : U ∈ F ↔ r * parent.2 ≤ squareRootEndpoint R := by
    dsimp [F, U]
    exact mem_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_rightMixed_iff
      hp hparent
  have hsub : F ⊆ ({L, U} : Finset (ℕ × ℕ)) := by
    intro child hchild
    rcases lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed
      hchild with h | h
    · subst child
      simp [L, U]
    · subst child
      simp [L, U]
  by_cases hL : r * parent.1 ≤ squareRootEndpoint R
  · have hLmem : L ∈ F := hLiff.mpr hL
    by_cases hU : r * parent.2 ≤ squareRootEndpoint R
    · have hUmem : U ∈ F := hUiff.mpr hU
      have hset : F = ({L, U} : Finset (ℕ × ℕ)) := by
        apply Finset.Subset.antisymm hsub
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hLmem
        · exact hUmem
      rw [hset]
      have hne : L ≠ U := by
        intro heq
        have howners :=
          lowOwnerFirstOwnerPolarizationRawParent_mixedCorners_have_owner
            hp hparent
        have hfresh := howners.1.1
        change r * parent.1 = parent.1 ∧ parent.2 = r * parent.2 at heq
        rw [heq.1, heq.2] at hfresh
        simp [squarefreePairFreshPrimeSet] at hfresh
      simp [hne]
    · have hUnot : U ∉ F := (not_congr hUiff).mpr hU
      have hset : F = ({L} : Finset (ℕ × ℕ)) := by
        apply Finset.Subset.antisymm
        · intro z hz
          have hz' := hsub hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
          rcases hz' with rfl | rfl
          · simp
          · exact False.elim (hUnot hz)
        · intro z hz
          simp only [Finset.mem_singleton] at hz
          subst z
          exact hLmem
      have hUout : squareRootEndpoint R < r * parent.2 :=
        Nat.lt_of_not_ge hU
      have hUzero :
          lowOwnerFirstOwnerDirichletPolarizationAtom R p U = 0 := by
        dsimp [U]
        exact lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_second_outside
          hp.one_le hUout
      rw [hset]
      simp [hUzero]
  · have hLnot : L ∉ F := (not_congr hLiff).mpr hL
    have hLout : squareRootEndpoint R < r * parent.1 :=
      Nat.lt_of_not_ge hL
    have hLzero :
        lowOwnerFirstOwnerDirichletPolarizationAtom R p L = 0 := by
      dsimp [L]
      exact lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_first_outside
        hp.one_le hLout
    by_cases hU : r * parent.2 ≤ squareRootEndpoint R
    · have hUmem : U ∈ F := hUiff.mpr hU
      have hset : F = ({U} : Finset (ℕ × ℕ)) := by
        apply Finset.Subset.antisymm
        · intro z hz
          have hz' := hsub hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
          rcases hz' with rfl | rfl
          · exact False.elim (hLnot hz)
          · simp
        · intro z hz
          simp only [Finset.mem_singleton] at hz
          subst z
          exact hUmem
      rw [hset]
      simp [hLzero]
    · have hUnot : U ∉ F := (not_congr hUiff).mpr hU
      have hset : F = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hz' := hsub hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
        rcases hz' with rfl | rfl
        · exact hLnot hz
        · exact hUnot hz
      have hUout : squareRootEndpoint R < r * parent.2 :=
        Nat.lt_of_not_ge hU
      have hUzero :
          lowOwnerFirstOwnerDirichletPolarizationAtom R p U = 0 := by
        dsimp [U]
        exact lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_second_outside
          hp.one_le hUout
      rw [hset]
      simp [hLzero, hUzero]

/-- **Exact lower-rank splice on one raw parent.**  After completing missing
mixed siblings by Dirichlet zero, the actual owner fibre is the existing
mixed-child rank telescope: next polarization minus the two same-branch atoms. -/
theorem sum_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_eq_next_sub_sameBranches
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    (∑ child ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        R p sig r parent,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p child) =
      realMoebiusStep parent.1 * realMoebiusStep parent.2 *
          lowOwnerDirichletNextPolarizationScalar
            R p r parent.1 parent.2 -
        lowOwnerFirstOwnerDirichletPolarizationAtom R p parent -
        lowOwnerFirstOwnerDirichletPolarizationAtom
          R p (r * parent.1, r * parent.2) := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, _hpr, _haBase, _hbBase, hra, hrb⟩
  rw [sum_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_eq_virtualMixed
    hp hparent]
  exact lowOwnerDirichletPolarization_mixedChildren_eq_next_sub_sameBranches
    (R := R) (p := p) hr hra hrb

/-- **Aggregate signed owner-fibre splice.**  The full physical greatest-owner
packet is now reassembled raw-parent by raw-parent into one next-polarization
term and the two lower-rank same-branch atoms. -/
theorem sum_lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_eq_next_sub_sameBranches
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ child ∈
      lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p child) =
      ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        (realMoebiusStep parent.1 * realMoebiusStep parent.2 *
            lowOwnerDirichletNextPolarizationScalar
              R p r parent.1 parent.2 -
          lowOwnerFirstOwnerDirichletPolarizationAtom R p parent -
          lowOwnerFirstOwnerDirichletPolarizationAtom
            R p (r * parent.1, r * parent.2)) := by
  rw [sum_lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_eq_rawParents]
  apply Finset.sum_congr rfl
  intro parent hparent
  exact
    sum_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_eq_next_sub_sameBranches
      hp hparent

end RHLean.Proof
