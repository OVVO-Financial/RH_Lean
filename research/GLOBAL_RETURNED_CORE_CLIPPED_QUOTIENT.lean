import Mathlib
import «research.ZERO_TARGET_CLIPPED_OWNER_ENERGY_CONTRACTION»

/-!
# The clipped first-separation exit is a one-child quotient cut

The companion-clipped predicate is not an arbitrary boundary condition.  For a
prime owner `p`, once the admitted mixed child `p*a` lies below `W`, clipping of
the companion `p*b` is exactly the statement that the lower endpoint `W/p`
lies between the two stripped parent coordinates.

On the literal fixed-owner covariance fibre this also removes one of the two
possible mixed children: the candidate containing `p*b` cannot lie in the
physical prefix.  Hence the clipped fibre has multiplicity at most one.

These are carrier facts only; no norm or cancellation estimate is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The clipped companion is exactly a quotient cut. -/
theorem criticalClippedCompanion_iff_quotientCut
    {W p a b : ℕ} (hp : p.Prime) (hpaW : p * a ≤ W) :
    W < p * b ↔ a ≤ W / p ∧ W / p < b := by
  constructor
  · intro hclip
    constructor
    · apply (Nat.le_div_iff_mul_le hp.pos).2
      simpa [Nat.mul_comm] using hpaW
    · apply (Nat.div_lt_iff_lt_mul hp.pos).2
      simpa [Nat.mul_comm] using hclip
  · rintro ⟨_haQ, hbQ⟩
    have h := (Nat.div_lt_iff_lt_mul hp.pos).1 hbQ
    simpa [Nat.mul_comm] using h

private theorem covarianceOrderedPair_max_eq (a b : ℕ) :
    max (covarianceOrderedPair a b).1 (covarianceOrderedPair a b).2 =
      max a b := by
  unfold covarianceOrderedPair
  split <;> simp [Nat.max_comm]

/-- On a companion-clipped owner, only the mixed child obtained by multiplying
the smaller parent coordinate can remain inside the physical prefix. -/
theorem postRootCovarianceFixedOwnerChildFiber_subset_singleton_of_clipped
    {W p : ℕ} {parent : ℕ × ℕ}
    (hclip : W < p * parent.2) :
    postRootCovarianceFixedOwnerChildFiber W parent p ⊆
      {covarianceOrderedPair (p * parent.1) parent.2} := by
  intro mn hmn
  have hcand :=
    postRootCovarianceFixedOwnerChildFiber_subset_candidates W parent p hmn
  rcases Finset.mem_filter.mp hmn with ⟨hownerFilter, _hparent⟩
  rcases Finset.mem_filter.mp hownerFilter with ⟨hweightFilter, _howner⟩
  rcases Finset.mem_filter.mp hweightFilter with ⟨hrec, _hweight⟩
  rcases Finset.mem_filter.mp hrec with ⟨hremainder, _hparentNe⟩
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hremainder).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨_hm1, hmW, _hn1, hnW, _hmnlt⟩
  unfold covarianceOwnerChildCandidates at hcand
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcand
  rcases hcand with hfirst | hsecond
  · exact Finset.mem_singleton.mpr hfirst
  · exfalso
    have hmaxW : max mn.1 mn.2 ≤ W := max_le hmW hnW
    have hpbW : p * parent.2 ≤ W := by
      calc
        p * parent.2 ≤ max parent.1 (p * parent.2) := Nat.le_max_right _ _
        _ = max (covarianceOrderedPair parent.1 (p * parent.2)).1
            (covarianceOrderedPair parent.1 (p * parent.2)).2 :=
              (covarianceOrderedPair_max_eq parent.1 (p * parent.2)).symm
        _ = max mn.1 mn.2 := by rw [hsecond]
        _ ≤ W := hmaxW
    exact (Nat.not_lt_of_ge hpbW) hclip

/-- The genuinely clipped fixed-owner fibre has multiplicity at most one, not
the generic two-child bound used by the unrestricted owner graph. -/
theorem postRootCovarianceFixedOwnerChildFiber_card_le_one_of_clipped
    {W p : ℕ} {parent : ℕ × ℕ}
    (hclip : W < p * parent.2) :
    (postRootCovarianceFixedOwnerChildFiber W parent p).card ≤ 1 := by
  have hcard := Finset.card_le_card
    (postRootCovarianceFixedOwnerChildFiber_subset_singleton_of_clipped hclip)
  simpa using hcard

/-- Multiplicity form of the one-child clipped fibre bound. -/
theorem postRootCovarianceFixedOwnerChildMultiplicity_le_one_of_clipped
    {W p : ℕ} {parent : ℕ × ℕ}
    (hclip : W < p * parent.2) :
    postRootCovarianceFixedOwnerChildMultiplicity W parent p ≤ 1 := by
  unfold postRootCovarianceFixedOwnerChildMultiplicity
  exact postRootCovarianceFixedOwnerChildFiber_card_le_one_of_clipped hclip

end RHLean.Proof
