import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_VIRTUAL_CUBE_SPLICE»
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_FRESH_PRIME_DESCENT»

/-!
# Complete raw-parent four-corner orbits and expose the exact rank recursion

The virtual-cube splice completes the two mixed corners of every occurring
raw-parent orbit by Dirichlet zero extension.  This file completes the matching
even half before any inequality is introduced.

For an occurring raw parent `(a,b)` under greatest owner `r`:

* every fresh coordinate of `(a,b)` is strictly smaller than `r`;
* consequently `(a,b)` is in the post-`r` same-branch survivor;
* the double corner `(r*a,r*b)` is in that survivor exactly while both moved
  coordinates remain on the physical clock, and otherwise its Dirichlet
  polarization atom is zero.

Hence the physical even fibre equals the two virtual even atoms, just as the
owner fibre already equals the two virtual mixed atoms.  Adding them gives the
literal full four-corner polarization identity.  After raw-parent Fubini, the
descending filtration therefore becomes

  polarization before r = sum(next polarization on raw parents) + inert.

The parent and double-child same-branch terms cancel *exactly*.  No norm,
absolute value, square, energy gate, or Mertens estimate appears here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Every fresh coordinate left on an occurring raw parent is strictly below
its greatest owner. -/
theorem lowOwnerFirstOwnerPolarizationRawParent_fresh_lt_owner
    {R p r q : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hqFresh : q ∈
      squarefreePairFreshPrimeSet parent.1 parent.2) :
    q < r := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, _hpr, haBase, hbBase, hra, hrb⟩
  have haCar := (Finset.mem_filter.mp haBase).1
  have hbCar := (Finset.mem_filter.mp hbBase).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar with
    ⟨_haSq, haPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar with
    ⟨_hbSq, hbPos⟩
  have hqPrime := (freshPrime_of_nonzeroPhysicalPair haCar hbCar hqFresh).1
  have hqr : q ≠ r := by
    intro hqr
    subst q
    have hxor :=
      (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
        hr haPos hbPos).1 hqFresh
    rcases hxor with h | h
    · exact hra h.1
    · exact hrb h.1
  have howner :=
    (lowOwnerFirstOwnerPolarizationRawParent_mixedCorners_have_owner
      hp hparent).1
  have hqMixed : q ∈
      squarefreePairFreshPrimeSet (r * parent.1) parent.2 := by
    have hiff :=
      mem_freshPrimeSet_stripped_iff_of_ne
        hr hqPrime hqr (Nat.mul_pos hr.pos haPos) hbPos
    apply hiff.mp
    simpa [squarefreePrimeFamilyParent, hrb,
      Nat.mul_div_cancel_left parent.1 hr.pos] using hqFresh
  have hqle := howner.2 q hqMixed
  omega

/-- Above the current greatest owner, the two coordinates of an occurring raw
parent have identical revealed prime signatures. -/
theorem lowOwnerFirstOwnerPolarizationRawParent_revealedAbove_eq
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R r) parent.1 =
      lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R r) parent.2 := by
  ext q
  by_cases hqAbove : q ∈ lowOwnerRevealedPrimesAbove R r
  · rcases Finset.mem_filter.mp hqAbove with ⟨_hqUpTo, hrq⟩
    simp only [lowOwnerRevealedPrimeSignature, Finset.mem_inter,
      hqAbove, and_true]
    constructor
    · intro hqa
      by_contra hqb
      have hqFresh : q ∈
          squarefreePairFreshPrimeSet parent.1 parent.2 := by
        unfold squarefreePairFreshPrimeSet
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_sdiff.mpr ⟨hqa, hqb⟩))
      have hlt :=
        lowOwnerFirstOwnerPolarizationRawParent_fresh_lt_owner
          hp hparent hqFresh
      omega
    · intro hqb
      by_contra hqa
      have hqFresh : q ∈
          squarefreePairFreshPrimeSet parent.1 parent.2 := by
        unfold squarefreePairFreshPrimeSet
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨hqb, hqa⟩))
      have hlt :=
        lowOwnerFirstOwnerPolarizationRawParent_fresh_lt_owner
          hp hparent hqFresh
      omega
  · simp [lowOwnerRevealedPrimeSignature, hqAbove]

/-- Multiplying by the current owner does not alter any strictly-higher
revealed coordinate. -/
theorem lowOwnerRevealedPrimeSignature_mul_owner_eq_above
    {R r n : ℕ} (hr : r.Prime) (hn : 0 < n) :
    lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R r) (r * n) =
      lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R r) n := by
  ext q
  by_cases hqAbove : q ∈ lowOwnerRevealedPrimesAbove R r
  · rcases Finset.mem_filter.mp hqAbove with ⟨hqUpTo, hrq⟩
    have hqPrime := (mem_primesUpTo.mp hqUpTo).1
    have hqr : q ≠ r := ne_of_gt hrq
    have hqNotDvdR : ¬ q ∣ r := by
      intro hdiv
      have heq : q = r := (Nat.prime_dvd_prime_iff_eq hqPrime hr).mp hdiv
      exact hqr heq
    have hrnPos : 0 < r * n := Nat.mul_pos hr.pos hn
    simp only [lowOwnerRevealedPrimeSignature, Finset.mem_inter,
      hqAbove, and_true]
    rw [prime_mem_squarefreePrimeFace_iff_dvd_public hqPrime hrnPos,
      prime_mem_squarefreePrimeFace_iff_dvd_public hqPrime hn]
    constructor
    · intro hdiv
      rcases hqPrime.dvd_mul.mp hdiv with hqrDvd | hqn
      · exact False.elim (hqNotDvdR hqrDvd)
      · exact hqn
    · intro hqn
      exact dvd_mul_of_dvd_right hqn r
  · simp [lowOwnerRevealedPrimeSignature, hqAbove]

/-- An occurring raw parent is fixed by stripping the owner again. -/
theorem lowOwnerFirstOwnerPolarizationRawParent_eq_self
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    lowOwnerFirstOwnerPolarizationRawParent r parent = parent := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨_hr, _hpr, _haBase, _hbBase, hra, hrb⟩
  rcases parent with ⟨a, b⟩
  simp [lowOwnerFirstOwnerPolarizationRawParent,
    squarefreePrimeFamilyParent, hra, hrb]

/-- Stripping the owner from both coordinates of the double corner returns the
same raw parent. -/
theorem lowOwnerFirstOwnerPolarizationRawParent_double_eq
    {r : ℕ} {parent : ℕ × ℕ} (hr : r.Prime) :
    lowOwnerFirstOwnerPolarizationRawParent
        r (r * parent.1, r * parent.2) = parent := by
  rcases parent with ⟨a, b⟩
  simp [lowOwnerFirstOwnerPolarizationRawParent,
    squarefreePrimeFamilyParent,
    Nat.mul_div_cancel_left a hr.pos,
    Nat.mul_div_cancel_left b hr.pos]

/-- The raw parent itself is always the zero-owner even corner of its own
post-owner orbit. -/
theorem lowOwnerFirstOwnerPolarizationRawParent_mem_evenFixedFiber
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    parent ∈ lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
      R p sig (lowOwnerRevealedPrimesAbove R r) r parent := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨_hr, _hpr, haBase, hbBase, hra, hrb⟩
  have haCar := (Finset.mem_filter.mp haBase).1
  have hbCar := (Finset.mem_filter.mp hbBase).1
  have hsig :=
    lowOwnerFirstOwnerPolarizationRawParent_revealedAbove_eq hp hparent
  have hsame : parent ∈ lowOwnerRevealedSameBranchPairCarrier R
      (lowOwnerRevealedPrimesAbove R r) r := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haCar, hbCar⟩,
        ⟨hsig, by simp [hra, hrb]⟩⟩
  have hcell : parent ∈
      lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig
        (lowOwnerRevealedPrimesAbove R r) r :=
    Finset.mem_filter.mpr ⟨hsame, ⟨haBase, hbBase⟩⟩
  have hraw := lowOwnerFirstOwnerPolarizationRawParent_eq_self hp hparent
  have heven : parent ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier
      R p sig (lowOwnerRevealedPrimesAbove R r) r := by
    exact Finset.mem_filter.mpr ⟨hcell, by simpa [hraw] using hparent⟩
  exact Finset.mem_filter.mpr ⟨heven, hraw⟩

/-- Local physical closure under multiplying by a larger fresh prime. -/
private theorem lowOwnerFullOrbit_mul_larger_prime_mem_same_base_of_le
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

/-- The double even corner is physically present exactly while both moved
coordinates remain inside the square-root clock. -/
theorem mem_lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_double_iff
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    (r * parent.1, r * parent.2) ∈
        lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
          R p sig (lowOwnerRevealedPrimesAbove R r) r parent ↔
      r * parent.1 ≤ squareRootEndpoint R ∧
        r * parent.2 ≤ squareRootEndpoint R := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, hpr, haBase, hbBase, hra, hrb⟩
  constructor
  · intro hmem
    have heven := (Finset.mem_filter.mp hmem).1
    have hcell := (Finset.mem_filter.mp heven).1
    rcases (Finset.mem_filter.mp hcell).2 with ⟨haMovedBase, hbMovedBase⟩
    have haMovedCar := (Finset.mem_filter.mp haMovedBase).1
    have hbMovedCar := (Finset.mem_filter.mp hbMovedBase).1
    have haIcc := (Finset.mem_filter.mp haMovedCar).1
    have hbIcc := (Finset.mem_filter.mp hbMovedCar).1
    exact ⟨(Finset.mem_Icc.mp haIcc).2, (Finset.mem_Icc.mp hbIcc).2⟩
  · rintro ⟨haX, hbX⟩
    have haMovedBase : r * parent.1 ∈
        lowOwnerFirstOwnerBaseFiber R p sig :=
      lowOwnerFullOrbit_mul_larger_prime_mem_same_base_of_le
        hp hr hpr hra haBase haX
    have hbMovedBase : r * parent.2 ∈
        lowOwnerFirstOwnerBaseFiber R p sig :=
      lowOwnerFullOrbit_mul_larger_prime_mem_same_base_of_le
        hp hr hpr hrb hbBase hbX
    have haCar := (Finset.mem_filter.mp haBase).1
    have hbCar := (Finset.mem_filter.mp hbBase).1
    have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
    have hbPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar).2
    have hsigParent :=
      lowOwnerFirstOwnerPolarizationRawParent_revealedAbove_eq hp hparent
    have hsigDouble :
        lowOwnerRevealedPrimeSignature
            (lowOwnerRevealedPrimesAbove R r) (r * parent.1) =
          lowOwnerRevealedPrimeSignature
            (lowOwnerRevealedPrimesAbove R r) (r * parent.2) := by
      calc
        lowOwnerRevealedPrimeSignature
            (lowOwnerRevealedPrimesAbove R r) (r * parent.1) =
            lowOwnerRevealedPrimeSignature
              (lowOwnerRevealedPrimesAbove R r) parent.1 :=
          lowOwnerRevealedPrimeSignature_mul_owner_eq_above hr haPos
        _ = lowOwnerRevealedPrimeSignature
              (lowOwnerRevealedPrimesAbove R r) parent.2 := hsigParent
        _ = lowOwnerRevealedPrimeSignature
              (lowOwnerRevealedPrimesAbove R r) (r * parent.2) :=
          (lowOwnerRevealedPrimeSignature_mul_owner_eq_above hr hbPos).symm
    have haMovedCar := (Finset.mem_filter.mp haMovedBase).1
    have hbMovedCar := (Finset.mem_filter.mp hbMovedBase).1
    have hsame : (r * parent.1, r * parent.2) ∈
        lowOwnerRevealedSameBranchPairCarrier R
          (lowOwnerRevealedPrimesAbove R r) r := by
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haMovedCar, hbMovedCar⟩,
          ⟨hsigDouble, ?_⟩⟩
      constructor
      · intro _h
        exact ⟨parent.2, rfl⟩
      · intro _h
        exact ⟨parent.1, rfl⟩
    have hcell : (r * parent.1, r * parent.2) ∈
        lowOwnerFirstOwnerCellRevealedSameBranchCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r :=
      Finset.mem_filter.mpr ⟨hsame, ⟨haMovedBase, hbMovedBase⟩⟩
    have hraw := lowOwnerFirstOwnerPolarizationRawParent_double_eq
      (parent := parent) hr
    have heven : (r * parent.1, r * parent.2) ∈
        lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r := by
      exact Finset.mem_filter.mpr
        ⟨hcell, by rw [hraw]; exact hparent⟩
    exact Finset.mem_filter.mpr ⟨heven, hraw⟩

/-- **Even virtual completion.**  The physical even raw-parent fibre equals the
base plus double virtual atoms; when the double corner is clipped its Dirichlet
atom is literally zero. -/
theorem sum_lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_eq_virtualEven
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    (∑ child ∈ lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
        R p sig (lowOwnerRevealedPrimesAbove R r) r parent,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p child) =
      lowOwnerFirstOwnerDirichletPolarizationAtom R p parent +
        lowOwnerFirstOwnerDirichletPolarizationAtom
          R p (r * parent.1, r * parent.2) := by
  let E := lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
    R p sig (lowOwnerRevealedPrimesAbove R r) r parent
  let D : ℕ × ℕ := (r * parent.1, r * parent.2)
  change (∑ child ∈ E,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p child) =
    lowOwnerFirstOwnerDirichletPolarizationAtom R p parent +
      lowOwnerFirstOwnerDirichletPolarizationAtom R p D
  have hPmem : parent ∈ E := by
    dsimp [E]
    exact lowOwnerFirstOwnerPolarizationRawParent_mem_evenFixedFiber hp hparent
  have hDiff :=
    mem_lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_double_iff hp hparent
  have hsub : E ⊆ ({parent, D} : Finset (ℕ × ℕ)) := by
    intro child hchild
    have hchild' := hchild
    dsimp [E] at hchild'
    rcases lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_child_even
      hchild' with h | h
    · subst child
      simp
    · subst child
      simp [D]
  by_cases hDphys :
      r * parent.1 ≤ squareRootEndpoint R ∧
        r * parent.2 ≤ squareRootEndpoint R
  · have hDmem : D ∈ E := by
      dsimp [D, E]
      exact hDiff.mpr hDphys
    have hset : E = ({parent, D} : Finset (ℕ × ℕ)) := by
      apply Finset.Subset.antisymm hsub
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hPmem
      · exact hDmem
    rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
      ⟨hr, _hpr, haBase, _hbBase, _hra, _hrb⟩
    have haCar := (Finset.mem_filter.mp haBase).1
    have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
    have hlt : parent.1 < r * parent.1 := by
      have h2a : parent.1 < 2 * parent.1 := by omega
      have h2r : 2 * parent.1 ≤ r * parent.1 :=
        Nat.mul_le_mul_right parent.1 hr.two_le
      exact h2a.trans_le h2r
    have hne : parent ≠ D := by
      intro hEq
      have hfirst := congrArg Prod.fst hEq
      dsimp [D] at hfirst
      exact (ne_of_lt hlt) hfirst
    rw [hset]
    simp [D, hne]
  · have hDnot : D ∉ E := by
      intro hmem
      have hmem' := hmem
      dsimp [D, E] at hmem'
      exact hDphys (hDiff.mp hmem')
    have hset : E = ({parent} : Finset (ℕ × ℕ)) := by
      apply Finset.Subset.antisymm
      · intro z hz
        have hz' := hsub hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
        rcases hz' with h | h
        · subst z
          simp
        · subst z
          exact False.elim (hDnot hz)
      · intro z hz
        simp only [Finset.mem_singleton] at hz
        subst z
        exact hPmem
    have hDzero :
        lowOwnerFirstOwnerDirichletPolarizationAtom R p D = 0 := by
      by_cases haX : r * parent.1 ≤ squareRootEndpoint R
      · have hbX : ¬ r * parent.2 ≤ squareRootEndpoint R := by
          intro h
          exact hDphys ⟨haX, h⟩
        exact lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_second_outside
          hp.one_le (Nat.lt_of_not_ge hbX)
      · exact lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_first_outside
          hp.one_le (Nat.lt_of_not_ge haX)
    rw [hset]
    simp [D, hDzero]

/-- **One raw-parent full-orbit collapse.**  Mixed owner fibre plus even survivor
is exactly the next polarization atom. -/
theorem lowOwnerFirstOwnerRawParent_fullOrbit_eq_nextPolarization
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    (∑ child ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        R p sig r parent,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p child) +
      (∑ child ∈ lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
          R p sig (lowOwnerRevealedPrimesAbove R r) r parent,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p child) =
      realMoebiusStep parent.1 * realMoebiusStep parent.2 *
        lowOwnerDirichletNextPolarizationScalar
          R p r parent.1 parent.2 := by
  rw [sum_lowOwnerFirstOwnerPolarizationFixedRawParentFiber_eq_next_sub_sameBranches
      hp hparent,
    sum_lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_eq_virtualEven
      hp hparent]
  ring

/-- **Aggregate raw-parent full-orbit collapse.** -/
theorem sum_lowOwnerFirstOwner_ownerFiber_add_orbitEven_eq_nextPolarization
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ child ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p child) +
      (∑ child ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p child) =
      ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        realMoebiusStep parent.1 * realMoebiusStep parent.2 *
          lowOwnerDirichletNextPolarizationScalar
            R p r parent.1 parent.2 := by
  rw [sum_lowOwnerFirstOwnerOwnerFiber_add_orbitEven_eq_rawParentOrbits]
  apply Finset.sum_congr rfl
  intro parent hparent
  exact lowOwnerFirstOwnerRawParent_fullOrbit_eq_nextPolarization hp hparent

/-- **Exact descending rank recursion.**  After completing the current raw
parent orbits, the parent and double-child same-branch masses disappear
algebraically.  The only survivor outside the strictly lower-rank next
polarization is the explicitly named inert carrier. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_next_add_inert
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) (hr : r.Prime) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        realMoebiusStep parent.1 * realMoebiusStep parent.2 *
          lowOwnerDirichletNextPolarizationScalar
            R p r parent.1 parent.2) +
      ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  have hdesc :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_orbitEven_add_inert_add_ownerFiber
      (R := R) (p := p) (r := r) (sig := sig) hr
  have hcollapse :=
    sum_lowOwnerFirstOwner_ownerFiber_add_orbitEven_eq_nextPolarization
      (R := R) (p := p) (r := r) (sig := sig) hp
  rw [hdesc]
  calc
    (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
        (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
        ∑ mn ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn =
      ((∑ mn ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
        (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn)) +
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertCarrier R p sig
          (lowOwnerRevealedPrimesAbove R r) r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by ring
    _ = _ := by rw [hcollapse]

end RHLean.Proof
