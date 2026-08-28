import Mathlib
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence
import RHLean.Proof.SquareRootLowPrimeGoFourthPowerCutoff
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope

/-!
# Recursive Go descent through the unique smaller prime owner

The square-dilated Go residual is a frozen predecessor cube.  When its cutoff
has not yet fallen below the owner prime `q`, split at the completed lower
prefix `q - 1`.  The remaining rough/smooth window is exactly the difference
of two fresh-prime upper-column telescopes.

Algebraically this gives

`F_{q^-}(y) = M(q-1) - sum_{r<q prime} (F_{r^-}(y/r) - F_{r^-}((q-1)/r))`.

The prime coordinate in every summand is strictly smaller than `q`; the
underlying recurrence is the same fresh-prime Euler recurrence already used by
the wall telescope.

After the weighted-liberty flattening, the apparently prime-count weighted
second-boundary defect admits the same treatment.  For one fixed liberty prime
`r < q`, the surviving parents are exactly one interval in the frozen
predecessor cube through `r-1`.  Thus one whole `r`-slice is a difference of
two frozen predecessor states; the prime-count weight disappears before any
norm or estimate is taken.

No norm, PNT input, or asymptotic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- At its own predecessor cutoff, the frozen prime universe is already the
complete ordinary Mertens prefix. -/
theorem frozenPrimeUniverseMass_pred_eq_mertensSummatoryInt
    {q : ℕ} (_hq : q.Prime) :
    frozenPrimeUniverseMass (primesUpTo (q - 1)) (q - 1) =
      mertensSummatoryInt (q - 1) := by
  unfold frozenPrimeUniverseMass mertensSummatoryInt
  exact truncatedPrimeCube_eq_moebiusPrefix (q - 1)

/-- **Recursive Go law.**  An unfinished frozen predecessor state at owner `q`
is the completed lower-scale Mertens state through `q-1` minus disjoint
smaller-prime boundary strips.  Each strip is itself the difference between two
frozen predecessor states belonging to a prime `r < q`.

This is the signed recursion to use before taking any norm. -/
theorem frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips
    {q y : ℕ} (hq : q.Prime) (hqy : q ≤ y) :
    frozenPrimeUniverseMass (primesUpTo (q - 1)) y =
      mertensSummatoryInt (q - 1) -
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1)) (y / r) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  have hqTwo : 2 ≤ q := hq.two_le
  have hyOne : 1 ≤ y := by omega
  have hpredOne : 1 ≤ q - 1 := by omega
  have hy := frozenPrimeUniverse_upperColumn_telescope y (q - 1) hyOne
  have hpred :=
    frozenPrimeUniverse_upperColumn_telescope (q - 1) (q - 1) hpredOne
  rw [frozenPrimeUniverseMass_pred_eq_mertensSummatoryInt hq] at hpred
  rw [Finset.sum_sub_distrib, hy, hpred]
  ring

/-- Every recursive Go owner in the preceding law is strictly smaller than the
current owner. -/
theorem mem_primesUpTo_pred_lt_owner
    {q r : ℕ} (hr : r ∈ primesUpTo (q - 1)) :
    r < q := by
  have hrData := mem_primesUpTo.mp hr
  have hrTwo : 2 ≤ r := hrData.1.two_le
  have hrq := hrData.2
  omega

/-- Square-residual specialization of the recursive Go law.  In the unfinished
region `q <= floor(X/q^2)`, the residual is a completed `M(q-1)` state plus only
strictly descending owner strips. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_mertensPred_sub_smallerOwnerStrips
    {q X : ℕ} (hq : q.Prime)
    (hunfinished : q ≤ X / (q * q)) :
    squareRootLowPrimeGoWallSquareResidual q X =
      mertensSummatoryInt (q - 1) -
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1))
              ((X / (q * q)) / r) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  exact frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips
    hq hunfinished

/-! ## Weighted liberty slices are frozen predecessor strips -/

/-- Generic arithmetic form of a frozen predecessor cube: it is exactly the
Möbius mass of squarefree cofactors whose canonical largest prime is below the
fresh owner `r`. -/
theorem frozenPrimeUniverseMass_eq_goSmoothCofactorSum
    {r Y : ℕ} (hr : r.Prime) :
    frozenPrimeUniverseMass (primesUpTo (r - 1)) Y =
      ∑ d ∈ squareRootLowPrimeGoSmoothCofactors r Y, μ d := by
  have h :=
    squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum
      (q := r) (X := (r * r) * Y) hr
  have hrrPos : 0 < r * r := Nat.mul_pos hr.pos hr.pos
  have hcut : (r * r) * Y / (r * r) = Y :=
    Nat.mul_div_right Y hrrPos
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff, hcut, hcut] at h
  simpa using h

/-- Total lower cutoff for one `r`-liberty slice.  The minimum makes the
subtraction identity total even when the physical cutoff has already passed the
whole parent range. -/
def squareRootLowPrimeGoDefectSliceLowerCutoff
    (q X r : ℕ) : ℕ :=
  min (q - 1) (X / (q * q) / r)

/-- **Exact support flattening at fixed `r`.**  In unfinished territory the
old birth inequality is implied by the physical second-contact inequality.
Therefore the #483 defect parents at fixed `q,r` are literally the upper frozen
smooth prefix minus its lower physical prefix. -/
theorem squareRootLowPrimeGoSecondBoundaryDefectParents_eq_smooth_sdiff
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X) :
    squareRootLowPrimeGoSecondBoundaryDefectParents q X r =
      squareRootLowPrimeGoSmoothCofactors r (q - 1) \
        squareRootLowPrimeGoSmoothCofactors r
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r) := by
  classical
  have hq2Pos : 0 < q * q := Nat.mul_pos hq.pos hq.pos
  have hqleCut : q ≤ X / (q * q) := by
    apply (Nat.le_div_iff_mul_le hq2Pos).2
    calc
      q * (q * q) = q ^ 3 := by ring
      _ ≤ X := hcube
  ext d
  constructor
  · intro hd
    rcases mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd with
      ⟨hfull, hphysical⟩
    rcases mem_squareRootLowPrimeGoFullBirthBoundaryParents.mp hfull with
      ⟨hd1, hdq, hsq, hrough, _hbirth⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨hd1, hdq, hsq, hrough⟩, ?_⟩
    intro hlower
    have hdLower :=
      (mem_squareRootLowPrimeGoSmoothCofactors.mp hlower).2.1
    have hLowerLe :
        squareRootLowPrimeGoDefectSliceLowerCutoff q X r ≤
          X / (q * q) / r := by
      unfold squareRootLowPrimeGoDefectSliceLowerCutoff
      exact min_le_right _ _
    exact (Nat.not_lt_of_ge (hdLower.trans hLowerLe)) hphysical
  · intro hd
    rcases Finset.mem_sdiff.mp hd with ⟨hupper, hnotLower⟩
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hupper with
      ⟨hd1, hdq, hsq, hrough⟩
    have hphysical : X / (q * q) / r < d := by
      by_contra hnot
      have hdPhys : d ≤ X / (q * q) / r := Nat.le_of_not_gt hnot
      have hdLower :
          d ≤ squareRootLowPrimeGoDefectSliceLowerCutoff q X r := by
        unfold squareRootLowPrimeGoDefectSliceLowerCutoff
        exact le_min hdq hdPhys
      exact hnotLower
        (mem_squareRootLowPrimeGoSmoothCofactors.mpr
          ⟨hd1, hdLower, hsq, hrough⟩)
    have hbirthMul : q - 1 < d * r := by
      have hcutMul : X / (q * q) < d * r :=
        (Nat.div_lt_iff_lt_mul hr.pos).1 hphysical
      omega
    have hbirth : (q - 1) / r < d :=
      (Nat.div_lt_iff_lt_mul hr.pos).2 hbirthMul
    apply mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mpr
    exact ⟨mem_squareRootLowPrimeGoFullBirthBoundaryParents.mpr
      ⟨hd1, hdq, hsq, hrough, hbirth⟩, hphysical⟩

/-- The lower smooth prefix is contained in the full fixed-owner parent prefix. -/
theorem squareRootLowPrimeGoDefectSliceLower_subset_upper
    (q X r : ℕ) :
    squareRootLowPrimeGoSmoothCofactors r
        (squareRootLowPrimeGoDefectSliceLowerCutoff q X r) ⊆
      squareRootLowPrimeGoSmoothCofactors r (q - 1) := by
  intro d hd
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hd with
    ⟨hd1, hdLower, hsq, hrough⟩
  apply mem_squareRootLowPrimeGoSmoothCofactors.mpr
  refine ⟨hd1, ?_, hsq, hrough⟩
  exact hdLower.trans (by
    unfold squareRootLowPrimeGoDefectSliceLowerCutoff
    exact min_le_left _ _)

/-- The Möbius mass of one fixed `r` defect slice is exactly one difference of
frozen predecessor states.  The prime-count multiplicity has disappeared. -/
theorem squareRootLowPrimeGoSecondBoundaryDefect_moebiusSum_eq_frozenStrip
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X) :
    (∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r, μ d) =
      frozenPrimeUniverseMass (primesUpTo (r - 1)) (q - 1) -
        frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r) := by
  rw [squareRootLowPrimeGoSecondBoundaryDefectParents_eq_smooth_sdiff
    hq hr hrq hcube]
  have hsub := squareRootLowPrimeGoDefectSliceLower_subset_upper q X r
  have hsum := Finset.sum_sdiff hsub (f := fun d => μ d)
  have hUpper :=
    frozenPrimeUniverseMass_eq_goSmoothCofactorSum
      (r := r) (Y := q - 1) hr
  have hLower :=
    frozenPrimeUniverseMass_eq_goSmoothCofactorSum
      (r := r) (Y := squareRootLowPrimeGoDefectSliceLowerCutoff q X r) hr
  rw [← hUpper, ← hLower] at hsum
  omega

/-- Source-signed mass of one fixed interior-prime liberty slice. -/
def squareRootLowPrimeGoDefectPrimeSliceSourceMass
    (q X r : ℕ) : ℤ :=
  ∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r, μ (q * d)

/-- **One liberty prime = one signed frozen strip.**  Every source in the slice
has the common outer fresh-prime sign flip, so the actual source mass is the
negative of the frozen predecessor strip. -/
theorem squareRootLowPrimeGoDefectPrimeSliceSourceMass_eq_neg_frozenStrip
    {q X r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r < q)
    (hcube : q ^ 3 ≤ X) :
    squareRootLowPrimeGoDefectPrimeSliceSourceMass q X r =
      -(frozenPrimeUniverseMass (primesUpTo (r - 1)) (q - 1) -
        frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r)) := by
  unfold squareRootLowPrimeGoDefectPrimeSliceSourceMass
  calc
    (∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r,
        μ (q * d)) =
      ∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r,
        -μ d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact squareRootLowPrimeGoFullBirthBoundary_parentSourceWeight_eq_neg
        hq hr hrq
        (mem_squareRootLowPrimeGoSecondBoundaryDefectParents.mp hd).1
    _ = -(∑ d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents q X r,
        μ d) := by
      rw [Finset.sum_neg_distrib]
    _ = -(frozenPrimeUniverseMass (primesUpTo (r - 1)) (q - 1) -
        frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootLowPrimeGoDefectSliceLowerCutoff q X r)) := by
      rw [squareRootLowPrimeGoSecondBoundaryDefect_moebiusSum_eq_frozenStrip
        hq hr hrq hcube]

end RHLean.Proof
