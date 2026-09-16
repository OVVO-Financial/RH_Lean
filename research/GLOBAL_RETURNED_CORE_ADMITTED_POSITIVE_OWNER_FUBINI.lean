import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_SECTOR_FUBINI»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_RANK_BASE»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_PARENT_FUBINI»

/-!
# Admitted polarization: diagonal plus unique-owner positive-lag Fubini

The admitted/admitted polarization is symmetric.  Therefore its ordered square
splits exactly into a diagonal and twice the positive-lag carrier.  The diagonal
is nonpositive by the rank-zero theorem.

The positive-lag carrier is then Fubini-reindexed twice, with equalities only:

1. by its unique greatest remaining fresh owner `r`;
2. inside that owner fibre, by its stripped ordered parent.

Thus every live admitted pair is charged exactly once to one `(r,parent)` block.
No owner labels are collapsed and no local `2/9` estimate is used in the Fubini.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem sum_product_symmetric_eq_diag_add_two_pos
    (s : Finset ℕ) (f : ℕ × ℕ → ℝ)
    (hsym : ∀ a b, f (a, b) = f (b, a)) :
    (∑ ab ∈ s.product s, f ab) =
      (∑ a ∈ s, f (a, a)) +
        2 * (∑ ab ∈ (s.product s).filter (fun ab => ab.1 < ab.2), f ab) := by
  let diagTerm : ℕ × ℕ → ℝ := fun ab =>
    if ab.1 = ab.2 then f ab else 0
  let ltTerm : ℕ × ℕ → ℝ := fun ab =>
    if ab.1 < ab.2 then f ab else 0
  let gtTerm : ℕ × ℕ → ℝ := fun ab =>
    if ab.2 < ab.1 then f ab else 0
  have hpoint : ∀ ab : ℕ × ℕ,
      f ab = diagTerm ab + ltTerm ab + gtTerm ab := by
    intro ab
    rcases lt_trichotomy ab.1 ab.2 with hlt | heq | hgt
    · simp [diagTerm, ltTerm, gtTerm, hlt, ne_of_lt hlt,
        not_lt_of_ge (Nat.le_of_lt hlt)]
    · subst ab.2
      simp [diagTerm, ltTerm, gtTerm]
    · simp [diagTerm, ltTerm, gtTerm, hgt, ne_of_gt hgt,
        not_lt_of_ge (Nat.le_of_lt hgt)]
  have hsplit :
      (∑ ab ∈ s.product s, f ab) =
        (∑ ab ∈ s.product s, diagTerm ab) +
        (∑ ab ∈ s.product s, ltTerm ab) +
        (∑ ab ∈ s.product s, gtTerm ab) := by
    calc
      (∑ ab ∈ s.product s, f ab) =
          ∑ ab ∈ s.product s,
            (diagTerm ab + ltTerm ab) + gtTerm ab := by
              apply Finset.sum_congr rfl
              intro ab _hab
              rw [hpoint]
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdiag :
      (∑ ab ∈ s.product s, diagTerm ab) =
        ∑ a ∈ s, f (a, a) := by
    calc
      (∑ ab ∈ s.product s, diagTerm ab) =
          ∑ a ∈ s, ∑ b ∈ s,
            if a = b then f (a, b) else 0 := by
              simpa [diagTerm] using
                (Finset.sum_product
                  (s := s) (t := s)
                  (f := fun ab : ℕ × ℕ => diagTerm ab))
      _ = ∑ a ∈ s, f (a, a) := by
        apply Finset.sum_congr rfl
        intro a ha
        calc
          (∑ b ∈ s, if a = b then f (a, b) else 0) =
              ∑ b ∈ s, if b = a then f (a, a) else 0 := by
                apply Finset.sum_congr rfl
                intro b _hb
                by_cases hba : b = a
                · subst b
                  simp
                · have hab : ¬ a = b := by exact fun h => hba h.symm
                  simp [hba, hab]
          _ = f (a, a) := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro b hb hba
              simp [hba]
            · exact fun hnot => (hnot ha).elim
  have hlt :
      (∑ ab ∈ s.product s, ltTerm ab) =
        ∑ ab ∈ (s.product s).filter (fun ab => ab.1 < ab.2), f ab := by
    rw [Finset.sum_filter]
    rfl
  have hgt :
      (∑ ab ∈ s.product s, gtTerm ab) =
        ∑ ab ∈ (s.product s).filter (fun ab => ab.1 < ab.2), f ab := by
    have hswap :
        (∑ ab ∈ s.product s, gtTerm ab) =
          ∑ a ∈ s, ∑ b ∈ s,
            if a < b then f (b, a) else 0 := by
      calc
        (∑ ab ∈ s.product s, gtTerm ab) =
            ∑ a ∈ s, ∑ b ∈ s,
              if b < a then f (a, b) else 0 := by
                simpa [gtTerm] using
                  (Finset.sum_product
                    (s := s) (t := s)
                    (f := fun ab : ℕ × ℕ => gtTerm ab))
        _ = ∑ b ∈ s, ∑ a ∈ s,
              if b < a then f (a, b) else 0 := by
                rw [Finset.sum_comm]
        _ = ∑ a ∈ s, ∑ b ∈ s,
              if a < b then f (b, a) else 0 := by rfl
    rw [hswap]
    have hsymSum :
        (∑ a ∈ s, ∑ b ∈ s,
          if a < b then f (b, a) else 0) =
        ∑ a ∈ s, ∑ b ∈ s,
          if a < b then f (a, b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hab : a < b
      · simp [hab, hsym]
      · simp [hab]
    rw [hsymSum]
    symm
    calc
      (∑ ab ∈ (s.product s).filter (fun ab => ab.1 < ab.2), f ab) =
          ∑ ab ∈ s.product s,
            if ab.1 < ab.2 then f ab else 0 := Finset.sum_filter _ _
      _ = ∑ a ∈ s, ∑ b ∈ s,
            if a < b then f (a, b) else 0 := by
              simpa only using
                (Finset.sum_product
                  (s := s) (t := s)
                  (f := fun ab : ℕ × ℕ =>
                    if ab.1 < ab.2 then f ab else 0))
  rw [hsplit, hdiag, hlt, hgt]
  ring

/-- Exact admitted polarization split into rank-zero diagonal and positive lag. -/
theorem lowOwnerFirstOwnerAdmittedPolarizationMass_eq_diag_add_two_positive
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerAdmittedPolarizationMass R p sig =
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a)) +
      2 * (∑ ab ∈ lowOwnerFirstOwnerAdmittedPositivePairCarrier R p sig,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) := by
  unfold lowOwnerFirstOwnerAdmittedPolarizationMass
    lowOwnerFirstOwnerAdmittedPositivePairCarrier
  exact sum_product_symmetric_eq_diag_add_two_pos
    (lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (lowOwnerFirstOwnerDirichletPolarizationAtom R p)
    (lowOwnerFirstOwnerDirichletPolarizationAtom_comm R p)

/-- Dropping only the nonpositive rank-zero diagonal leaves twice the positive
unique-owner carrier. -/
theorem lowOwnerFirstOwnerAdmittedPolarizationMass_le_two_positive
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerAdmittedPolarizationMass R p sig ≤
      2 * (∑ ab ∈ lowOwnerFirstOwnerAdmittedPositivePairCarrier R p sig,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) := by
  rw [lowOwnerFirstOwnerAdmittedPolarizationMass_eq_diag_add_two_positive]
  have hdiag :
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro a ha
    exact lowOwnerFirstOwnerDirichletPolarizationAtom_diag_nonpos
      (Finset.mem_filter.mp ha).1
  linarith

/-- **Exact two-stage signed Fubini on the live positive-lag admitted sector.**
Owner labels and stripped parents are both retained. -/
theorem sum_lowOwnerFirstOwnerAdmittedPositive_eq_owner_parent_blocks
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ ab ∈ lowOwnerFirstOwnerAdmittedPositivePairCarrier R p sig,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) =
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ parent ∈ lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r,
          ∑ child ∈ lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
              R p sig r parent,
            lowOwnerFirstOwnerDirichletPolarizationAtom R p child := by
  rw [sum_lowOwnerFirstOwnerAdmittedPositive_eq_sum_greatestOwnerFibers
    hp (lowOwnerFirstOwnerDirichletPolarizationAtom R p)]
  apply Finset.sum_congr rfl
  intro r _hr
  exact sum_lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_eq_sum_parentFibers
    R p sig r (lowOwnerFirstOwnerDirichletPolarizationAtom R p)

/-- Aggregate admitted sector reduced to the owner-labelled parent blocks with
no owner collapse. -/
theorem lowOwnerFirstOwnerAdmittedPolarizationMass_le_owner_parent_blocks
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerAdmittedPolarizationMass R p sig ≤
      2 * (∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ parent ∈ lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r,
          ∑ child ∈ lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
              R p sig r parent,
            lowOwnerFirstOwnerDirichletPolarizationAtom R p child) := by
  rw [← sum_lowOwnerFirstOwnerAdmittedPositive_eq_owner_parent_blocks hp]
  exact lowOwnerFirstOwnerAdmittedPolarizationMass_le_two_positive R p sig

end RHLean.Proof
