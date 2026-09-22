import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_FILTRATION»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_GREATEST_OWNER_FUBINI»

/-!
# Global descending greatest-owner Fubini for an arbitrary signed site

The revealed-prime filtration already identifies

  Cross(primesAbove r, r)

with the pairs whose greatest fresh prime coordinate is r.  This file removes
all cell-specific bookkeeping and proves the global finite partition directly
on the common nonzero-Mobius clock.

For any signed site v,

  E_v(empty)
    = diagonal(v)
      + sum_r Cross_v(primesAbove r, r).

Every off-diagonal physical pair is charged exactly once.  The diagonal is
nonnegative.  No norm, Cauchy--Schwarz estimate, owner multiplicity bound, or
arithmetic hypothesis enters.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Full physical ordered pair carrier with the diagonal removed. -/
def lowOwnerGlobalOffDiagonalPairCarrier
    (R : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun mn =>
    mn.1 ≠ mn.2

/-- Physical diagonal pair carrier. -/
def lowOwnerGlobalDiagonalPairCarrier
    (R : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun mn =>
    mn.1 = mn.2

/-- Global off-diagonal fibre with unique greatest fresh owner r. -/
def lowOwnerGlobalGreatestOwnerPairFiber
    (R r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerGlobalOffDiagonalPairCarrier R).filter fun mn =>
    IsSquarefreePairGreatestFreshPrimeOwner r mn.1 mn.2

/-- Every global physical off-diagonal pair has a greatest fresh owner on the
physical prime clock. -/
theorem lowOwnerGlobalOffDiagonalPair_has_greatestOwner
    {R m n : ℕ}
    (hmn : (m, n) ∈ lowOwnerGlobalOffDiagonalPairCarrier R) :
    ∃ r ∈ primesUpTo (squareRootEndpoint R),
      IsSquarefreePairGreatestFreshPrimeOwner r m n := by
  rcases Finset.mem_filter.mp hmn with ⟨hpair, hne⟩
  rcases Finset.mem_product.mp hpair with ⟨hmCar, hnCar⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with
    ⟨hmSq, _hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with
    ⟨hnSq, _hnPos⟩
  have hleast := squarefreePairFreshPrimeOwner_isOwner hmSq hnSq hne
  let S := squarefreePairFreshPrimeSet m n
  have hSnonempty : S.Nonempty :=
    ⟨squarefreePairFreshPrimeOwner m n, hleast.1⟩
  let r := S.max' hSnonempty
  have hrFresh : r ∈ S := Finset.max'_mem S hSnonempty
  have hrMax : ∀ q ∈ S, q ≤ r := by
    intro q hq
    exact Finset.le_max' S q hq
  have howner : IsSquarefreePairGreatestFreshPrimeOwner r m n :=
    ⟨hrFresh, hrMax⟩
  have hrData := freshPrime_of_nonzeroPhysicalPair hmCar hnCar hrFresh
  exact ⟨r, mem_primesUpTo.mpr hrData, howner⟩

/-- Greatest-owner fibres are pairwise disjoint. -/
theorem lowOwnerGlobalGreatestOwnerPairFiber_pairwiseDisjoint
    (R : ℕ) :
    Set.PairwiseDisjoint (↑(primesUpTo (squareRootEndpoint R)))
      (lowOwnerGlobalGreatestOwnerPairFiber R) := by
  intro r _hr s _hs hrs
  change Disjoint
    (lowOwnerGlobalGreatestOwnerPairFiber R r)
    (lowOwnerGlobalGreatestOwnerPairFiber R s)
  rw [Finset.disjoint_left]
  intro mn hmr hms
  have hro := (Finset.mem_filter.mp hmr).2
  have hso := (Finset.mem_filter.mp hms).2
  exact hrs (squarefreePairGreatestFreshPrimeOwner_unique hro hso)

/-- The global greatest-owner fibres cover exactly the off-diagonal carrier. -/
theorem lowOwnerGlobalGreatestOwnerPairFiber_biUnion
    (R : ℕ) :
    (primesUpTo (squareRootEndpoint R)).biUnion
        (lowOwnerGlobalGreatestOwnerPairFiber R) =
      lowOwnerGlobalOffDiagonalPairCarrier R := by
  ext mn
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨r, _hr, hmn⟩
    exact (Finset.mem_filter.mp hmn).1
  · intro hmn
    rcases mn with ⟨m, n⟩
    rcases lowOwnerGlobalOffDiagonalPair_has_greatestOwner hmn with
      ⟨r, hr, howner⟩
    exact Finset.mem_biUnion.mpr
      ⟨r, hr, Finset.mem_filter.mpr ⟨hmn, howner⟩⟩

/-- On a physical prime owner, the greatest-owner fibre is exactly the
descending revealed-coordinate crossing carrier. -/
theorem lowOwnerGlobalGreatestOwnerPairFiber_eq_descendingCross
    {R r : ℕ} (hr : r ∈ primesUpTo (squareRootEndpoint R)) :
    lowOwnerGlobalGreatestOwnerPairFiber R r =
      lowOwnerRevealedCrossPairCarrier R
        (lowOwnerRevealedPrimesAbove R r) r := by
  have hrPrime := (mem_primesUpTo.mp hr).1
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hoff, howner⟩
    have hprod := (Finset.mem_filter.mp hoff).1
    rcases Finset.mem_product.mp hprod with ⟨hm, hn⟩
    exact
      (mem_descendingCrossPair_iff_greatestFreshOwner hrPrime).2
        ⟨hm, hn, howner⟩
  · intro h
    rcases (mem_descendingCrossPair_iff_greatestFreshOwner hrPrime).1 h with
      ⟨hm, hn, howner⟩
    have hne : m ≠ n := by
      intro hmn
      subst n
      have hfresh := howner.1
      simp [squarefreePairFreshPrimeSet] at hfresh
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hm, hn⟩, hne⟩, howner⟩

/-- **Global unique-owner signed Fubini.**

For any signed pair weight, the entire off-diagonal common-clock carrier is the
disjoint sum of the descending crossing packets. -/
theorem sum_lowOwnerGlobalOffDiagonal_eq_descendingCrossFibers
    (R : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerGlobalOffDiagonalPairCarrier R, f mn) =
      ∑ r ∈ primesUpTo (squareRootEndpoint R),
        ∑ mn ∈ lowOwnerRevealedCrossPairCarrier R
            (lowOwnerRevealedPrimesAbove R r) r,
          f mn := by
  rw [← lowOwnerGlobalGreatestOwnerPairFiber_biUnion R]
  rw [Finset.sum_biUnion
    (lowOwnerGlobalGreatestOwnerPairFiber_pairwiseDisjoint R)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [lowOwnerGlobalGreatestOwnerPairFiber_eq_descendingCross hr]

/-- Diagonal mass of an arbitrary signed site. -/
def lowOwnerGlobalDiagonalPairMassWith
    (R : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ mn ∈ lowOwnerGlobalDiagonalPairCarrier R,
    v mn.1 * v mn.2

/-- The arbitrary-site diagonal mass is nonnegative. -/
theorem lowOwnerGlobalDiagonalPairMassWith_nonneg
    (R : ℕ) (v : ℕ → ℝ) :
    0 ≤ lowOwnerGlobalDiagonalPairMassWith R v := by
  unfold lowOwnerGlobalDiagonalPairMassWith
  apply Finset.sum_nonneg
  intro mn hmn
  have heq := (Finset.mem_filter.mp hmn).2
  rw [heq]
  exact sq_nonneg (v mn.2)

/-- Empty revealed state is the full ordered carrier, split into diagonal and
off-diagonal parts. -/
theorem lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_offDiagonal
    (R : ℕ) (v : ℕ → ℝ) :
    lowOwnerRevealedPairMassWith R ∅ v =
      lowOwnerGlobalDiagonalPairMassWith R v +
        ∑ mn ∈ lowOwnerGlobalOffDiagonalPairCarrier R,
          v mn.1 * v mn.2 := by
  let P :=
    (lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)
  have hpart :=
    Finset.sum_filter_add_sum_filter_not
      (s := P) (p := fun mn : ℕ × ℕ => mn.1 = mn.2)
      (f := fun mn : ℕ × ℕ => v mn.1 * v mn.2)
  unfold lowOwnerRevealedPairMassWith
    lowOwnerGlobalDiagonalPairMassWith
    lowOwnerGlobalDiagonalPairCarrier
    lowOwnerGlobalOffDiagonalPairCarrier
    lowOwnerRevealedPairCarrier
    lowOwnerRevealedPrimeSignature
  simpa [P] using hpart.symm

/-- The physical diagonal carrier is the image of the one-dimensional clock. -/
theorem lowOwnerGlobalDiagonalPairCarrier_eq_image
    (R : ℕ) :
    lowOwnerGlobalDiagonalPairCarrier R =
      (lowOwnerNonzeroMobiusCarrier R).image (fun n => (n, n)) := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hprod, heq⟩
    rcases Finset.mem_product.mp hprod with ⟨hm, _hn⟩
    dsimp only at heq
    subst n
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨n, hn, hmn⟩
    have hpair : (m, n) = (n, n) := hmn
    have hmEq : m = n := congrArg Prod.fst hpair
    subst m
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hn, hn⟩, rfl⟩

/-- Diagonal mass is the one-dimensional sum of site squares. -/
theorem lowOwnerGlobalDiagonalPairMassWith_eq_sum_sq
    (R : ℕ) (v : ℕ → ℝ) :
    lowOwnerGlobalDiagonalPairMassWith R v =
      ∑ n ∈ lowOwnerNonzeroMobiusCarrier R, v n ^ 2 := by
  unfold lowOwnerGlobalDiagonalPairMassWith
  rw [lowOwnerGlobalDiagonalPairCarrier_eq_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _hn
    ring
  · intro a _ha b _hb hab
    exact congrArg Prod.fst hab

/-- At the empty revealed state the arbitrary-site pair mass is literally the
square of its one-dimensional amplitude. -/
theorem lowOwnerRevealedPairMassWith_empty_eq_sum_sq
    (R : ℕ) (v : ℕ → ℝ) :
    lowOwnerRevealedPairMassWith R ∅ v =
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier R, v n) ^ 2 := by
  unfold lowOwnerRevealedPairMassWith lowOwnerRevealedPairCarrier
    lowOwnerRevealedPrimeSignature
  simp only [Finset.inter_empty]
  simp only [ite_true]
  let S := lowOwnerNonzeroMobiusCarrier R
  change
    (∑ mn ∈ S.product S, v mn.1 * v mn.2) =
      (∑ n ∈ S, v n) ^ 2
  calc
    (∑ mn ∈ S.product S, v mn.1 * v mn.2) =
      ∑ m ∈ S, ∑ n ∈ S, v m * v n := by
        simpa only using
          (Finset.sum_product
            (s := S) (t := S)
            (f := fun mn : ℕ × ℕ => v mn.1 * v mn.2))
    _ = (∑ m ∈ S, v m) * (∑ n ∈ S, v n) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _hm
        rw [Finset.mul_sum]
    _ = (∑ n ∈ S, v n) ^ 2 := by ring

/-- **Global descending energy decomposition for an arbitrary signed site.**

Every off-diagonal term is paid exactly once by its greatest fresh owner. -/
theorem lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_descendingCross
    (R : ℕ) (v : ℕ → ℝ) :
    lowOwnerRevealedPairMassWith R ∅ v =
      lowOwnerGlobalDiagonalPairMassWith R v +
        ∑ r ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerRevealedCrossPairMassWith R
            (lowOwnerRevealedPrimesAbove R r) r v := by
  rw [lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_offDiagonal]
  unfold lowOwnerRevealedCrossPairMassWith
  rw [sum_lowOwnerGlobalOffDiagonal_eq_descendingCrossFibers]

/-- Consequently the total signed descending crossing mass is bounded above by
the unrevealed energy, solely because the terminal diagonal is nonnegative. -/
theorem sum_lowOwnerDescendingCrossPairMassWith_le_emptyEnergy
    (R : ℕ) (v : ℕ → ℝ) :
    (∑ r ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerRevealedCrossPairMassWith R
        (lowOwnerRevealedPrimesAbove R r) r v) ≤
      lowOwnerRevealedPairMassWith R ∅ v := by
  have h :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_descendingCross R v
  have hd := lowOwnerGlobalDiagonalPairMassWith_nonneg R v
  linarith

end RHLean.Proof
