import Mathlib
import RHLean.Proof.SurvivorPrimeFaceFrontier
import RHLean.Proof.SurvivorResiduePrimeToggle

/-!
# Residue-conditioned survivor prime-face frontiers

The survivor residue covariance route groups active canonical source pairs by the
signed height residue `q^2-c^2 mod s`.  Independently, the prime-face route
cancels the alternating Mobius cube in a selected cofactor-prime coordinate.

This module connects those two exact mechanisms.

If a selected prime coordinate `ell` satisfies `ell^2 = 1 mod s`, inserting
`ell` into a cofactor prime face preserves the survivor height residue while
reversing the Boolean/Mobius sign.  Therefore the usual one-coordinate
truncated-cube cancellation works *inside each individual residue fibre*.
Only residue-conditioned first-failure frontiers survive.

At modulus `2`, the fixed pivot `ell = 3` is square-one.  Hence every upper-prime
face with `q >= 5` admits the same residue-preserving cancellation coordinate.
No analytic estimate is introduced here.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Alternating mass of an admissible prime-face population after restricting to
one signed-height residue class. -/
noncomputable def residueConditionedCubeAlternatingSum
    (modulus q : ℕ) (r : ZMod modulus)
    (ambient : Finset ℕ) (admissible : Finset ℕ → Prop) : ℤ := by
  classical
  exact ∑ u ∈ ambient.powerset,
    if admissible u ∧
        survivorHeightResidue modulus (primeFaceProduct u) q = r then
      booleanCubeSign u
    else 0

/-- Residue-conditioned alternating mass on one first-failure boundary. -/
noncomputable def residueConditionedFirstFailureBoundaryAlternatingSum
    (modulus q : ℕ) (r : ZMod modulus)
    (ambient : Finset ℕ) (ell : ℕ)
    (admissible : Finset ℕ → Prop) : ℤ := by
  classical
  exact ∑ u ∈ firstFailureBoundary ambient ell admissible,
    if survivorHeightResidue modulus (primeFaceProduct u) q = r then
      booleanCubeSign u
    else 0

/-- One-coordinate truncated-cube cancellation remains exact after conditioning
on a survivor height residue, provided the selected coordinate is square-one
modulo the residue modulus. -/
theorem residueConditionedCubeAlternatingSum_eq_firstFailureBoundary
    (modulus q : ℕ) (r : ZMod modulus)
    {ambient : Finset ℕ} {ell : ℕ} {admissible : Finset ℕ → Prop}
    (hell : ell ∈ ambient)
    (hdown : CubeDownwardClosed admissible)
    (hsq : (ell : ZMod modulus) ^ 2 = 1) :
    residueConditionedCubeAlternatingSum modulus q r ambient admissible =
      residueConditionedFirstFailureBoundaryAlternatingSum
        modulus q r ambient ell admissible := by
  classical
  have hdecomp : ambient = insert ell (ambient.erase ell) := by
    exact (Finset.insert_erase hell).symm
  unfold residueConditionedCubeAlternatingSum
  calc
    (∑ u ∈ ambient.powerset,
        if admissible u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) =
      ∑ u ∈ (insert ell (ambient.erase ell)).powerset,
        if admissible u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0 := by
          rw [← hdecomp]
    _ =
      (∑ u ∈ (ambient.erase ell).powerset,
        if admissible u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) +
      ∑ u ∈ (ambient.erase ell).powerset,
        if admissible (insert ell u) ∧
            survivorHeightResidue modulus
              (primeFaceProduct (insert ell u)) q = r then
          booleanCubeSign (insert ell u)
        else 0 := by
          rw [Finset.sum_powerset_insert (Finset.notMem_erase ell ambient)]
    _ =
      ∑ u ∈ (ambient.erase ell).powerset,
        ((if admissible u ∧
              survivorHeightResidue modulus (primeFaceProduct u) q = r then
            booleanCubeSign u
          else 0) +
        (if admissible (insert ell u) ∧
              survivorHeightResidue modulus
                (primeFaceProduct (insert ell u)) q = r then
            booleanCubeSign (insert ell u)
          else 0)) := by
            rw [Finset.sum_add_distrib]
    _ =
      ∑ u ∈ (ambient.erase ell).powerset,
        if admissible u ∧ ¬ admissible (insert ell u) ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0 := by
          apply Finset.sum_congr rfl
          intro u hu
          have hfresh : ell ∉ u :=
            Finset.notMem_of_mem_powerset_of_notMem
              hu (Finset.notMem_erase ell ambient)
          have hres :=
            survivor_primeFace_residue_iff_insert_of_sq_eq_one
              modulus ell q u r hfresh hsq
          by_cases hchild : admissible (insert ell u)
          · have hparent : admissible u :=
              hdown u (insert ell u) (Finset.subset_insert ell u) hchild
            by_cases hr :
                survivorHeightResidue modulus (primeFaceProduct u) q = r
            · have hrChild :
                  survivorHeightResidue modulus
                    (primeFaceProduct (insert ell u)) q = r := hres.mpr hr
              simp [hchild, hparent, hr, hrChild, booleanCubeSign,
                Finset.card_insert_of_notMem, hfresh, pow_succ]
            · have hrChild :
                  survivorHeightResidue modulus
                    (primeFaceProduct (insert ell u)) q ≠ r := by
                intro h
                exact hr (hres.mp h)
              simp [hchild, hparent, hr, hrChild]
          · by_cases hparent : admissible u
            · by_cases hr :
                  survivorHeightResidue modulus (primeFaceProduct u) q = r
              · simp [hchild, hparent, hr]
              · simp [hchild, hparent, hr]
            · simp [hchild, hparent]
    _ = residueConditionedFirstFailureBoundaryAlternatingSum
          modulus q r ambient ell admissible := by
      unfold residueConditionedFirstFailureBoundaryAlternatingSum
        firstFailureBoundary
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hparent : admissible u
      · by_cases hchild : admissible (insert ell u)
        · simp [hparent, hchild]
        · by_cases hr :
            survivorHeightResidue modulus (primeFaceProduct u) q = r
          · simp [hparent, hchild, hr]
          · simp [hparent, hchild, hr]
      · simp [hparent]

/-- Residue-conditioned alternating mass of the complete survivor high selector
in one distinguished-prime face cube. -/
noncomputable def survivorPrimeFaceResidueHighAlternatingMass
    (Λ : ℝ) (t q modulus : ℕ) (r : ZMod modulus) : ℤ :=
  residueConditionedCubeAlternatingSum modulus q r
    (survivorPrimeFaceAmbient q) (survivorPrimeFaceHigh Λ t q)

/-- The V-shaped survivor selector decomposes inside each residue fibre into the
same transport, product, and below-smooth pieces as in the unconditioned cube. -/
theorem survivorPrimeFaceResidueHigh_alternatingMass_decomposition
    (Λ : ℝ) (t q modulus : ℕ) (r : ZMod modulus) (hΛ : 0 ≤ Λ) :
    survivorPrimeFaceResidueHighAlternatingMass Λ t q modulus r =
      residueConditionedCubeAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) (survivorPrimeFaceTransportPrefix Λ t q) +
      residueConditionedCubeAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) (survivorPrimeFaceProductPrefix t q) -
      residueConditionedCubeAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) (survivorPrimeFaceBelowSmoothPrefix Λ t q) := by
  classical
  unfold survivorPrimeFaceResidueHighAlternatingMass
    residueConditionedCubeAlternatingSum
  calc
    (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceHigh Λ t q u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) =
      ∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        ((if survivorPrimeFaceTransportPrefix Λ t q u ∧
              survivorHeightResidue modulus (primeFaceProduct u) q = r then
            booleanCubeSign u
          else 0) +
        (if survivorPrimeFaceProductPrefix t q u ∧
              survivorHeightResidue modulus (primeFaceProduct u) q = r then
            booleanCubeSign u
          else 0) -
        (if survivorPrimeFaceBelowSmoothPrefix Λ t q u ∧
              survivorHeightResidue modulus (primeFaceProduct u) q = r then
            booleanCubeSign u
          else 0)) := by
            apply Finset.sum_congr rfl
            intro u _hu
            by_cases hr :
                survivorHeightResidue modulus (primeFaceProduct u) q = r
            · have hind :=
                survivorPrimeFaceHigh_indicator_decomposition Λ t q u hΛ
              unfold survivorPrimeFaceIndicator at hind
              have hscaled := congrArg (fun z : ℤ => z * booleanCubeSign u) hind
              simpa [hr, add_mul, sub_mul] using hscaled
            · simp [hr]
    _ =
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceTransportPrefix Λ t q u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) +
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceProductPrefix t q u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) -
      (∑ u ∈ (survivorPrimeFaceAmbient q).powerset,
        if survivorPrimeFaceBelowSmoothPrefix Λ t q u ∧
            survivorHeightResidue modulus (primeFaceProduct u) q = r then
          booleanCubeSign u
        else 0) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- **Residue-fibre three-frontier cancellation.**  A square-one selected prime
coordinate cancels every interior parent/child pair inside the same survivor
height residue. -/
theorem survivorPrimeFaceResidueHigh_alternatingMass_eq_threeFrontiers
    (Λ : ℝ) (t q modulus ell : ℕ) (r : ZMod modulus)
    (hΛ : 0 ≤ Λ)
    (hell : ell ∈ survivorPrimeFaceAmbient q)
    (hsq : (ell : ZMod modulus) ^ 2 = 1) :
    survivorPrimeFaceResidueHighAlternatingMass Λ t q modulus r =
      residueConditionedFirstFailureBoundaryAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) ell
        (survivorPrimeFaceTransportPrefix Λ t q) +
      residueConditionedFirstFailureBoundaryAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) ell
        (survivorPrimeFaceProductPrefix t q) -
      residueConditionedFirstFailureBoundaryAlternatingSum modulus q r
        (survivorPrimeFaceAmbient q) ell
        (survivorPrimeFaceBelowSmoothPrefix Λ t q) := by
  rw [survivorPrimeFaceResidueHigh_alternatingMass_decomposition
    Λ t q modulus r hΛ]
  rw [residueConditionedCubeAlternatingSum_eq_firstFailureBoundary
      modulus q r hell (survivorPrimeFaceTransportPrefix_downward Λ t q) hsq,
    residueConditionedCubeAlternatingSum_eq_firstFailureBoundary
      modulus q r hell (survivorPrimeFaceProductPrefix_downward t q) hsq,
    residueConditionedCubeAlternatingSum_eq_firstFailureBoundary
      modulus q r hell (survivorPrimeFaceBelowSmoothPrefix_downward Λ t q) hsq]

/-- At parity modulus `2`, the single pivot prime `3` works in every face with
upper coordinate at least `5`.  Thus all such residue fibres collapse to three
first-failure frontiers at one common coordinate. -/
theorem survivorPrimeFaceParityHigh_alternatingMass_eq_threeFrontiers_at_three
    (Λ : ℝ) (t q : ℕ) (r : ZMod 2)
    (hΛ : 0 ≤ Λ) (hq : 5 ≤ q) :
    survivorPrimeFaceResidueHighAlternatingMass Λ t q 2 r =
      residueConditionedFirstFailureBoundaryAlternatingSum 2 q r
        (survivorPrimeFaceAmbient q) 3
        (survivorPrimeFaceTransportPrefix Λ t q) +
      residueConditionedFirstFailureBoundaryAlternatingSum 2 q r
        (survivorPrimeFaceAmbient q) 3
        (survivorPrimeFaceProductPrefix t q) -
      residueConditionedFirstFailureBoundaryAlternatingSum 2 q r
        (survivorPrimeFaceAmbient q) 3
        (survivorPrimeFaceBelowSmoothPrefix Λ t q) := by
  apply survivorPrimeFaceResidueHigh_alternatingMass_eq_threeFrontiers
    Λ t q 2 3 r hΛ
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · norm_num

end RHLean.Proof
