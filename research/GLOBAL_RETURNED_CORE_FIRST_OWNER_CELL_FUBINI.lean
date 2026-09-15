import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_CELLS»

/-!
# Exact first-owner cell Fubini predicate

The actual AMP Gram is already partitioned by the unique least fresh prime.
This file identifies that intrinsic owner predicate with the lower-signature
cell coordinates used by `GLOBAL_RETURNED_CORE_FIRST_OWNER_CELLS`.

On nonzero Moebius support, a prime `p` is the first separation owner exactly
when the two sites agree in every prime coordinate below `p` and `p` divides
exactly one of them.  Thus the first-owner Gram has no hidden pair class between
the intrinsic owner projector and the p-free / p-divisible cell split.

This is a carrier theorem only.  No norm, triangle inequality, Mertens bound,
or independence assumption is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Membership in the nonzero AMP carrier gives squarefree positive support. -/
theorem lowOwnerNonzeroMobiusCarrier_squarefree_pos
    {R n : ℕ} (hn : n ∈ lowOwnerNonzeroMobiusCarrier R) :
    Squarefree n ∧ 0 < n := by
  rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnmu⟩
  have hsq : Squarefree n := squarefree_of_realMoebiusStep_ne_zero hnmu
  have hpos : 0 < n := (Finset.mem_Icc.mp hnIcc).1
  exact ⟨hsq, hpos⟩

/-- **Exact cell characterization of the intrinsic first owner.**

On the actual nonzero AMP carrier, `p` is the unique first fresh-prime owner
iff the two sites have the same lower-prime signature and lie on opposite
`p`-divisibility branches.  This is the finite Fubini predicate needed to
regroup the global first-owner Gram by lower-signature cells. -/
theorem isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
    {R p m n : ℕ} (hp : p.Prime)
    (hm : m ∈ lowOwnerNonzeroMobiusCarrier R)
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hmn : m ≠ n) :
    IsSquarefreePairFreshPrimeOwner p m n ↔
      squarefreeLowerPrimeSignature p m =
          squarefreeLowerPrimeSignature p n ∧
        ((p ∣ m ∧ ¬ p ∣ n) ∨ (p ∣ n ∧ ¬ p ∣ m)) := by
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hm with ⟨hmsq, hmpos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hn with ⟨hnsq, hnpos⟩
  constructor
  · intro howner
    have hsig :=
      squarefreeLowerPrimeSignature_eq_of_firstOwner hmsq hnsq hmn howner
    have hcanon := squarefreePairFreshPrimeOwner_isOwner hmsq hnsq hmn
    have hp_le : p ≤ squarefreePairFreshPrimeOwner m n :=
      howner.2 _ hcanon.1
    have hcanon_le : squarefreePairFreshPrimeOwner m n ≤ p :=
      hcanon.2 _ howner.1
    have hpEq : p = squarefreePairFreshPrimeOwner m n := by omega
    have hxor0 :=
      squarefreePairFreshPrimeOwner_dvd_xor hmsq hnsq hmn hmpos hnpos
    have hxor :
        (p ∣ m ∧ ¬ p ∣ n) ∨ (p ∣ n ∧ ¬ p ∣ m) := by
      simpa [hpEq] using hxor0
    exact ⟨hsig, hxor⟩
  · rintro ⟨hsig, hxor⟩
    exact firstOwner_of_lowerSignature_eq_and_dvd_xor
      hp hmpos hnpos hsig hxor

/-- A first-owner pair therefore lands in exactly the two opposite branches of
one lower-signature cell.  The statement is deliberately orientation-free:
the numerical order used by the unordered Gram may put either branch first. -/
theorem firstOwner_pair_mem_opposite_cellFibers
    {R p m n : ℕ} (hp : p.Prime)
    (hm : m ∈ lowOwnerNonzeroMobiusCarrier R)
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hmn : m ≠ n)
    (howner : IsSquarefreePairFreshPrimeOwner p m n) :
    let sig := squarefreeLowerPrimeSignature p m
    (m ∈ lowOwnerFirstOwnerBaseFiber R p sig ∧
        n ∈ lowOwnerFirstOwnerChildFiber R p sig) ∨
      (n ∈ lowOwnerFirstOwnerBaseFiber R p sig ∧
        m ∈ lowOwnerFirstOwnerChildFiber R p sig) := by
  have hcell :=
    (isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
      hp hm hn hmn).mp howner
  rcases hcell with ⟨hsig, hxor⟩
  dsimp only
  rcases hxor with hmnXor | hnmXor
  · right
    constructor
    · exact Finset.mem_filter.mpr ⟨hn, ⟨hsig.symm, hmnXor.2⟩⟩
    · exact Finset.mem_filter.mpr ⟨hm, ⟨rfl, hmnXor.1⟩⟩
  · left
    constructor
    · exact Finset.mem_filter.mpr ⟨hm, ⟨rfl, hnmXor.2⟩⟩
    · exact Finset.mem_filter.mpr ⟨hn, ⟨hsig.symm, hnmXor.1⟩⟩

/-- Conversely, opposite branches of one occupied lower-signature cell are
precisely first-owner pairs.  This is the reverse half needed for an exact
cellwise regrouping rather than a one-sided support inclusion. -/
theorem opposite_cellFibers_firstOwner
    {R p m n : ℕ} (hp : p.Prime) (sig : Finset ℕ)
    (hm : m ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hn : n ∈ lowOwnerFirstOwnerChildFiber R p sig) :
    IsSquarefreePairFreshPrimeOwner p m n := by
  rcases Finset.mem_filter.mp hm with ⟨hmCar, hmb⟩
  rcases Finset.mem_filter.mp hn with ⟨hnCar, hnc⟩
  have hmpos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
  have hnpos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
  have hsig : squarefreeLowerPrimeSignature p m =
      squarefreeLowerPrimeSignature p n := by
    rw [hmb.1, hnc.1]
  exact firstOwner_of_lowerSignature_eq_and_dvd_xor
    hp hmpos hnpos hsig (Or.inr ⟨hnc.2, hmb.2⟩)

end RHLean.Proof
