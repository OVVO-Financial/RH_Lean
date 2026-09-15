import Mathlib
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_UNIQUE_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_RANK_BASE»

/-!
# Full signed cell telescope as a unique-owner polarization ledger

The cell telescope is already the ordered sum of Dirichlet polarization atoms
on the full p-free base square.  Because the atom is symmetric, that square is
exactly diagonal plus twice positive lag.  The diagonal is nonpositive, while
the positive-lag carrier has the unique greatest-owner Fubini from the preceding
file.

This is the outer finite signed Fubini required by the assembly constraints.  It
contains admitted and clipped sites in one state; no clipped square or separate
clipped-energy estimate occurs.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem sum_symmetric_square_eq_diag_add_two_positive
    (s : Finset ℕ) (f : ℕ × ℕ → ℝ)
    (hsym : ∀ a b, f (a, b) = f (b, a)) :
    (∑ ab ∈ s.product s, f ab) =
      (∑ a ∈ s, f (a, a)) +
      2 * (∑ ab ∈ (s.product s).filter (fun ab => ab.1 < ab.2), f ab) := by
  let off := (s.product s).filter fun ab => ab.1 ≠ ab.2
  have hpartition :
      (∑ ab ∈ s.product s, f ab) =
        (∑ ab ∈ (s.product s).filter (fun ab => ab.1 = ab.2), f ab) +
        ∑ ab ∈ off, f ab := by
    dsimp [off]
    simpa only [not_not] using
      (Finset.sum_filter_add_sum_filter_not
        (s := s.product s) (p := fun ab => ab.1 = ab.2) (f := f)).symm
  have hdiag :
      (∑ ab ∈ (s.product s).filter (fun ab => ab.1 = ab.2), f ab) =
        ∑ a ∈ s, f (a, a) := by
    calc
      (∑ ab ∈ (s.product s).filter (fun ab => ab.1 = ab.2), f ab) =
          ∑ a ∈ s, ∑ b ∈ s, if a = b then f (a, b) else 0 := by
            rw [Finset.sum_filter]
            simpa only using
              (Finset.sum_product
                (s := s) (t := s)
                (f := fun ab : ℕ × ℕ => if ab.1 = ab.2 then f ab else 0))
      _ = ∑ a ∈ s, f (a, a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_eq_single a]
        · simp
        · intro b hb hba
          simp [hba]
        · exact fun hnot => (hnot ha).elim
  let pos := (s.product s).filter fun ab => ab.1 < ab.2
  let neg := (s.product s).filter fun ab => ab.2 < ab.1
  have hoff_partition :
      (∑ ab ∈ off, f ab) = (∑ ab ∈ pos, f ab) + ∑ ab ∈ neg, f ab := by
    have hdisj : Disjoint pos neg := by
      rw [Finset.disjoint_left]
      intro ab hp hn
      have hp' := (Finset.mem_filter.mp hp).2
      have hn' := (Finset.mem_filter.mp hn).2
      omega
    have hunion : off = pos ∪ neg := by
      ext ab
      dsimp [off, pos, neg]
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union]
      constructor
      · rintro ⟨hprod, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨hprod, hlt⟩
        · exact Or.inr ⟨hprod, hgt⟩
      · rintro (⟨hprod, hlt⟩ | ⟨hprod, hgt⟩)
        · exact ⟨hprod, ne_of_lt hlt⟩
        · exact ⟨hprod, ne_of_gt hgt⟩
    rw [hunion, Finset.sum_union hdisj]
  have hneg_eq_pos : (∑ ab ∈ neg, f ab) = ∑ ab ∈ pos, f ab := by
    let swap : ℕ × ℕ → ℕ × ℕ := fun ab => (ab.2, ab.1)
    have hbij : Set.BijOn swap (↑neg) (↑pos) := by
      constructor
      · intro ab hab
        dsimp [neg, pos, swap] at hab ⊢
        rcases Finset.mem_filter.mp hab with ⟨hprod, hlt⟩
        rcases Finset.mem_product.mp hprod with ⟨ha, hb⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hlt⟩
      · intro x hx y hy hxy
        rcases x with ⟨x1, x2⟩
        rcases y with ⟨y1, y2⟩
        simp [swap] at hxy
        simp [hxy]
      · intro ab hab
        rcases ab with ⟨a, b⟩
        dsimp [pos, neg, swap] at hab ⊢
        rcases Finset.mem_filter.mp hab with ⟨hprod, hlt⟩
        rcases Finset.mem_product.mp hprod with ⟨ha, hb⟩
        refine ⟨(b, a), ?_, by simp⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hlt⟩
    have hsum := Finset.sum_bij
      (fun ab _hab => swap ab)
      (fun ab hab => hbij.1 hab)
      (fun ab _hab => by simpa [swap] using hsym ab.1 ab.2)
      (fun a1 ha1 a2 ha2 heq => hbij.2.1 ha1 ha2 heq)
      (fun b hb => by
        rcases hbij.2.2 hb with ⟨a, ha, hab⟩
        exact ⟨a, ha, hab⟩)
    simpa [swap] using hsum
  rw [hpartition, hdiag, hoff_partition, hneg_eq_pos]
  dsimp [pos]
  ring

/-- **Exact cell-level unique-owner ledger.** -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_diagonal_add_ownerFibers
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a)) +
      2 * (∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ ab ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber
            R p sig r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) := by
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_sum_dirichletPolarizationAtoms hp]
  have hsplit := sum_symmetric_square_eq_diag_add_two_positive
    (lowOwnerFirstOwnerBaseFiber R p sig)
    (lowOwnerFirstOwnerDirichletPolarizationAtom R p)
    (lowOwnerFirstOwnerDirichletPolarizationAtom_comm R p)
  rw [hsplit]
  congr 1
  rw [sum_lowOwnerFirstOwnerBasePositive_eq_sum_polarizationOwnerFibers
    hp (lowOwnerFirstOwnerDirichletPolarizationAtom R p)]

/-- The only inequality in the outer Fubini is dropping the favorable diagonal. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_le_two_ownerFibers
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig ≤
      2 * (∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ ab ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber
            R p sig r,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p ab) := by
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_diagonal_add_ownerFibers hp]
  have hdiag := sum_lowOwnerFirstOwnerDirichletPolarizationAtom_diagonal_nonpos
    R p sig
  linarith

end RHLean.Proof
