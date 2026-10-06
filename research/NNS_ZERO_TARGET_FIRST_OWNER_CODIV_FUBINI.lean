import Mathlib
import «research.GLOBAL_RETURNED_CORE_GLOBAL_FIRST_OWNER_SITE_FUBINI»
import «research.GLOBAL_RETURNED_CORE_STOKES_ZERO_TARGET_COVARIANCE»
import «research.LOW_OWNER_RETURNED_CORE_ZERO_TARGET_GRAM»

/-!
# NNS zero-target Co/Div first-owner Fubini

The global least-owner carrier is already an exact disjoint partition of every
off-diagonal pair on the common nonzero-Mobius clock.  This file applies that
carrier theorem separately to the two nonnegative NNS zero-target ledgers.

For an arbitrary signed site v, both

  Co(v)  and  Div(v)

are decomposed exactly into the physical diagonal plus the disjoint least-owner
fibres.  No normalization, subtraction, absolute-value estimate, reciprocal
weight, or inequality is introduced.

This is the denominator-safe Fubini needed before changing PM degree on a
homogeneous fixed-owner/fixed-parent fibre.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Co-partial mass on one global least-owner fibre for an arbitrary signed
site. -/
def lowOwnerGlobalFirstOwnerCoPartialMassWith
    (R p : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ mn ∈ lowOwnerGlobalFirstOwnerPairFiber R p,
    zeroTargetCoPartialPair (v mn.1) (v mn.2)

/-- Divergent mass on one global least-owner fibre for an arbitrary signed
site. -/
def lowOwnerGlobalFirstOwnerDivergentMassWith
    (R p : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ mn ∈ lowOwnerGlobalFirstOwnerPairFiber R p,
    zeroTargetDivergentPair (v mn.1) (v mn.2)

/-- The exact least-owner partition works for an arbitrary pair observable, not
only the signed product observable used by the original global site Fubini. -/
theorem sum_lowOwnerGlobalOffDiagonal_eq_firstOwnerFibersWith
    (R : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerGlobalOffDiagonalPairCarrier R, f mn) =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ mn ∈ lowOwnerGlobalFirstOwnerPairFiber R p, f mn := by
  rw [← lowOwnerGlobalFirstOwnerPairFiber_biUnion R]
  rw [Finset.sum_biUnion
    (lowOwnerGlobalFirstOwnerPairFiber_pairwiseDisjoint R)]
  rfl

/-- Off-diagonal co-partial mass is exactly the disjoint sum of its least-owner
fibres. -/
theorem sum_lowOwnerGlobalOffDiagonalCoPartial_eq_firstOwnerFibers
    (R : ℕ) (v : ℕ → ℝ) :
    (∑ mn ∈ lowOwnerGlobalOffDiagonalPairCarrier R,
      zeroTargetCoPartialPair (v mn.1) (v mn.2)) =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerCoPartialMassWith R p v := by
  exact sum_lowOwnerGlobalOffDiagonal_eq_firstOwnerFibersWith
    R (fun mn => zeroTargetCoPartialPair (v mn.1) (v mn.2))

/-- Off-diagonal divergent mass is exactly the disjoint sum of its least-owner
fibres. -/
theorem sum_lowOwnerGlobalOffDiagonalDivergent_eq_firstOwnerFibers
    (R : ℕ) (v : ℕ → ℝ) :
    (∑ mn ∈ lowOwnerGlobalOffDiagonalPairCarrier R,
      zeroTargetDivergentPair (v mn.1) (v mn.2)) =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerDivergentMassWith R p v := by
  exact sum_lowOwnerGlobalOffDiagonal_eq_firstOwnerFibersWith
    R (fun mn => zeroTargetDivergentPair (v mn.1) (v mn.2))

/-- Exact diagonal co-partial mass.  Self pairs carry their full square in Co. -/
theorem lowOwnerGlobalDiagonalCoPartialMass_eq_sum_sq
    (R : ℕ) (v : ℕ → ℝ) :
    (∑ mn ∈ lowOwnerGlobalDiagonalPairCarrier R,
      zeroTargetCoPartialPair (v mn.1) (v mn.2)) =
      ∑ n ∈ lowOwnerNonzeroMobiusCarrier R, v n ^ 2 := by
  rw [lowOwnerGlobalDiagonalPairCarrier_eq_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _hn
    simp
  · intro a _ha b _hb hab
    exact congrArg Prod.fst hab

/-- Exact diagonal divergent mass.  Self pairs carry no divergent mass. -/
theorem lowOwnerGlobalDiagonalDivergentMass_eq_zero
    (R : ℕ) (v : ℕ → ℝ) :
    (∑ mn ∈ lowOwnerGlobalDiagonalPairCarrier R,
      zeroTargetDivergentPair (v mn.1) (v mn.2)) = 0 := by
  apply Finset.sum_eq_zero
  intro mn hmn
  have heq := (Finset.mem_filter.mp hmn).2
  rw [heq]
  simp

/-- **Denominator-safe Co Fubini.**

The complete zero-target co-partial Gram on the common clock is its exact
diagonal square mass plus the disjoint least-owner fibre masses. -/
theorem zeroTargetCoPartialGram_lowOwner_eq_diagonal_add_firstOwners
    (R : ℕ) (v : ℕ → ℝ) :
    zeroTargetCoPartialGram (lowOwnerNonzeroMobiusCarrier R) v =
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier R, v n ^ 2) +
        ∑ p ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerGlobalFirstOwnerCoPartialMassWith R p v := by
  let S := lowOwnerNonzeroMobiusCarrier R
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := S.product S)
      (p := fun mn : ℕ × ℕ => mn.1 = mn.2)
      (f := fun mn : ℕ × ℕ =>
        zeroTargetCoPartialPair (v mn.1) (v mn.2))
  have hprod :
      zeroTargetCoPartialGram S v =
        ∑ mn ∈ S.product S,
          zeroTargetCoPartialPair (v mn.1) (v mn.2) := by
    unfold zeroTargetCoPartialGram
    symm
    simpa only using
      (Finset.sum_product
        (s := S) (t := S)
        (f := fun mn : ℕ × ℕ =>
          zeroTargetCoPartialPair (v mn.1) (v mn.2)))
  rw [hprod]
  have hsplit' :
      (∑ mn ∈ S.product S,
        zeroTargetCoPartialPair (v mn.1) (v mn.2)) =
      (∑ mn ∈ lowOwnerGlobalDiagonalPairCarrier R,
        zeroTargetCoPartialPair (v mn.1) (v mn.2)) +
      (∑ mn ∈ lowOwnerGlobalOffDiagonalPairCarrier R,
        zeroTargetCoPartialPair (v mn.1) (v mn.2)) := by
    unfold lowOwnerGlobalDiagonalPairCarrier
      lowOwnerGlobalOffDiagonalPairCarrier
    dsimp [S] at hsplit ⊢
    exact hsplit.symm
  rw [hsplit',
    lowOwnerGlobalDiagonalCoPartialMass_eq_sum_sq,
    sum_lowOwnerGlobalOffDiagonalCoPartial_eq_firstOwnerFibers]

/-- **Denominator-safe Div Fubini.**

The complete zero-target divergent Gram has no diagonal contribution and is
exactly the disjoint sum of its least-owner fibre masses. -/
theorem zeroTargetDivergentGram_lowOwner_eq_sum_firstOwners
    (R : ℕ) (v : ℕ → ℝ) :
    zeroTargetDivergentGram (lowOwnerNonzeroMobiusCarrier R) v =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerDivergentMassWith R p v := by
  let S := lowOwnerNonzeroMobiusCarrier R
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := S.product S)
      (p := fun mn : ℕ × ℕ => mn.1 = mn.2)
      (f := fun mn : ℕ × ℕ =>
        zeroTargetDivergentPair (v mn.1) (v mn.2))
  have hprod :
      zeroTargetDivergentGram S v =
        ∑ mn ∈ S.product S,
          zeroTargetDivergentPair (v mn.1) (v mn.2) := by
    unfold zeroTargetDivergentGram
    symm
    simpa only using
      (Finset.sum_product
        (s := S) (t := S)
        (f := fun mn : ℕ × ℕ =>
          zeroTargetDivergentPair (v mn.1) (v mn.2)))
  rw [hprod]
  have hsplit' :
      (∑ mn ∈ S.product S,
        zeroTargetDivergentPair (v mn.1) (v mn.2)) =
      (∑ mn ∈ lowOwnerGlobalDiagonalPairCarrier R,
        zeroTargetDivergentPair (v mn.1) (v mn.2)) +
      (∑ mn ∈ lowOwnerGlobalOffDiagonalPairCarrier R,
        zeroTargetDivergentPair (v mn.1) (v mn.2)) := by
    unfold lowOwnerGlobalDiagonalPairCarrier
      lowOwnerGlobalOffDiagonalPairCarrier
    dsimp [S] at hsplit ⊢
    exact hsplit.symm
  rw [hsplit',
    lowOwnerGlobalDiagonalDivergentMass_eq_zero,
    zero_add,
    sum_lowOwnerGlobalOffDiagonalDivergent_eq_firstOwnerFibers]

/-- The Co+Div denominator therefore Fubinis without ever subtracting the two
ledgers. -/
theorem zeroTargetTotalGram_lowOwner_eq_diagonal_add_firstOwners
    (R : ℕ) (v : ℕ → ℝ) :
    zeroTargetCoPartialGram (lowOwnerNonzeroMobiusCarrier R) v +
        zeroTargetDivergentGram (lowOwnerNonzeroMobiusCarrier R) v =
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier R, v n ^ 2) +
        ∑ p ∈ primesUpTo (squareRootEndpoint R),
          (lowOwnerGlobalFirstOwnerCoPartialMassWith R p v +
            lowOwnerGlobalFirstOwnerDivergentMassWith R p v) := by
  rw [zeroTargetCoPartialGram_lowOwner_eq_diagonal_add_firstOwners,
    zeroTargetDivergentGram_lowOwner_eq_sum_firstOwners,
    ← Finset.sum_add_distrib]
  ring

end RHLean.Proof
