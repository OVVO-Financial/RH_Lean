import Mathlib
import RHLean.Analysis.AlpogeSharpASKCollar

/-!
# Alpoge sharp ASK: EXACT affine / signed width covariance / positive collar

Unlike a principal-only Jensen estimate, this identity applies to the full
physical site kernel: *any* nonnegative Frobenius/inertia site weights v(g),
any site-dependent widths, and every real prime-power threshold z=a/n.

The source equals one affine baseline at c, minus a SINGLE signed width
response, plus a NONNEGATIVE, cutoff-localized collar remainder. This is
the correct source-faithful place to seek Alpoge's nonlocal partner/height
gain. No cancellation or RH-strength bound is assumed or proved.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- At the reference width c take the actual lower-side sharp ASK
slope -1 when z>c and the upper-side slope zero when z<=c. -/
def alpogeASKLinearWidthShift (z c w : ℝ) : ℝ :=
  if c < z then w - c else 0

/-- Difference from the affine tangent at reference width c. Convexity
makes it NONNEGATIVE. It only sees width cutoff crossings, so carries
no generic global Lipschitz charge. -/
def alpogeASKSharpCollarRemainder (z c w : ℝ) : ℝ :=
  alpogeASKPos z w - alpogeASKPos z c +
    alpogeASKLinearWidthShift z c w

/-- Exact affine-plus-collar decomposition, pointwise for every width. -/
theorem alpogeASKPos_eq_tangent_add_collar
    (z c w : ℝ) :
    alpogeASKPos z w =
      alpogeASKPos z c -
        alpogeASKLinearWidthShift z c w +
        alpogeASKSharpCollarRemainder z c w := by
  unfold alpogeASKSharpCollarRemainder
  ring

/-- For a threshold strictly above the reference, the collar return is
exactly the positive crossing w-z. -/
theorem alpogeASKSharpCollarRemainder_eq_of_ref_lt
    (z c w : ℝ) (hcz : c < z) :
    alpogeASKSharpCollarRemainder z c w =
      max (w - z) 0 := by
  unfold alpogeASKSharpCollarRemainder
    alpogeASKLinearWidthShift alpogeASKPos
  have hzc : 0 ≤ z - c := by linarith
  simp only [hcz, ite_true]
  rw [max_eq_left hzc]
  by_cases hwz : w ≤ z
  · have hzw : 0 ≤ z - w := by linarith
    have hwzz : w - z ≤ (0 : ℝ) := by linarith
    rw [max_eq_left hzw, max_eq_right hwzz]
    ring
  · have hzw : z - w ≤ (0 : ℝ) := by linarith
    have hwzz : (0 : ℝ) ≤ w - z := by linarith
    rw [max_eq_right hzw, max_eq_left hwzz]
    ring

/-- For a threshold not above the reference, the collar return is
exactly the positive crossing z-w. -/
theorem alpogeASKSharpCollarRemainder_eq_of_ref_ge
    (z c w : ℝ) (hzc : z ≤ c) :
    alpogeASKSharpCollarRemainder z c w =
      max (z - w) 0 := by
  unfold alpogeASKSharpCollarRemainder
    alpogeASKLinearWidthShift alpogeASKPos
  have hcnot : ¬ c < z := not_lt_of_ge hzc
  have hzc0 : z - c ≤ (0 : ℝ) := by linarith
  simp only [hcnot, ite_false]
  rw [max_eq_right hzc0]
  ring

/-- The unconditionally positive residual of the exact tangent split. -/
theorem alpogeASKSharpCollarRemainder_nonneg
    (z c w : ℝ) :
    0 ≤ alpogeASKSharpCollarRemainder z c w := by
  by_cases hcz : c < z
  · rw [alpogeASKSharpCollarRemainder_eq_of_ref_lt z c w hcz]
    exact le_max_right _ _
  · rw [alpogeASKSharpCollarRemainder_eq_of_ref_ge
        z c w (le_of_not_gt hcz)]
    exact le_max_right _ _

/-- Below the entire site width range, the sharp collar is absent. -/
theorem alpogeASKSharpCollarRemainder_zero_below
    (z b c w : ℝ) (hbc : b ≤ c) (hbw : b ≤ w)
    (hz : z ≤ b) :
    alpogeASKSharpCollarRemainder z c w = 0 := by
  have hzc : z ≤ c := le_trans hz hbc
  rw [alpogeASKSharpCollarRemainder_eq_of_ref_ge z c w hzc]
  have hzw : z - w ≤ (0 : ℝ) := by linarith
  rw [max_eq_right hzw]

/-- Strictly above the entire width range, the sharp collar is absent. -/
theorem alpogeASKSharpCollarRemainder_zero_above
    (z B c w : ℝ) (hcB : c ≤ B) (hwB : w ≤ B)
    (hz : B < z) :
    alpogeASKSharpCollarRemainder z c w = 0 := by
  have hcz : c < z := lt_of_le_of_lt hcB hz
  rw [alpogeASKSharpCollarRemainder_eq_of_ref_lt z c w hcz]
  have hwz : w - z ≤ (0 : ℝ) := by linarith
  rw [max_eq_right hwz]

/-- The full positive physical site source, not assumed to be the
principal character. The native Frobenius/inertia projector at
prime powers is a legitimate nonnegative coefficient v. -/
def alpogeASKPhysicalSiteMass {ι : Type*}
    (S : Finset ι) (v : ι → ℝ) (w : ι → ℝ)
    (z : ℝ) : ℝ :=
  ∑ g ∈ S, v g * alpogeASKPos z (w g)

/-- The only FIRST-ORDER width interaction in the complete physical
site source. It may be signed, and must not be thrown away. -/
def alpogeASKPhysicalWidthCovariance {ι : Type*}
    (S : Finset ι) (v : ι → ℝ) (w : ι → ℝ)
    (z c : ℝ) : ℝ :=
  ∑ g ∈ S, v g * alpogeASKLinearWidthShift z c (w g)

/-- Remaining nonnegative, cutoff-localized physical site payment. -/
def alpogeASKPhysicalCollarCost {ι : Type*}
    (S : Finset ι) (v : ι → ℝ) (w : ι → ℝ)
    (z c : ℝ) : ℝ :=
  ∑ g ∈ S, v g * alpogeASKSharpCollarRemainder z c (w g)

/-- Exact signed identity for the ENTIRE physical site source.
The width-character covariance is retained with the correct negative
sign, and the collar remainder is NOT bounded before recombination. -/
theorem alpogeASKPhysicalMass_eq_affine_sub_cov_add_collar
    {ι : Type*} (S : Finset ι)
    (v w : ι → ℝ) (z c : ℝ) :
    alpogeASKPhysicalSiteMass S v w z =
      (∑ g ∈ S, v g) * alpogeASKPos z c -
        alpogeASKPhysicalWidthCovariance S v w z c +
        alpogeASKPhysicalCollarCost S v w z c := by
  unfold alpogeASKPhysicalSiteMass
    alpogeASKPhysicalWidthCovariance alpogeASKPhysicalCollarCost
  calc
    (∑ g ∈ S, v g * alpogeASKPos z (w g)) =
        ∑ g ∈ S,
          (v g * alpogeASKPos z c -
            v g * alpogeASKLinearWidthShift z c (w g) +
            v g * alpogeASKSharpCollarRemainder z c (w g)) := by
          apply Finset.sum_congr rfl
          intro g _hg
          rw [alpogeASKPos_eq_tangent_add_collar z c (w g)]
          ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_mul]
        
/-- The collar cost on the COMPLETE physical kernel is nonnegative,
provided the actual site Fourier detector is nonnegative. -/
theorem alpogeASKPhysicalCollarCost_nonneg
    {ι : Type*} (S : Finset ι)
    (v w : ι → ℝ) (z c : ℝ)
    (hv : ∀ g ∈ S, 0 ≤ v g) :
    0 ≤ alpogeASKPhysicalCollarCost S v w z c := by
  unfold alpogeASKPhysicalCollarCost
  apply Finset.sum_nonneg
  intro g hg
  exact mul_nonneg (hv g hg)
    (alpogeASKSharpCollarRemainder_nonneg z c (w g))

/-- All signed covariance remains visible; away from the width
crossing collar there is no positive remainder at all. -/
theorem alpogeASKPhysicalCollarCost_zero_outside
    {ι : Type*} (S : Finset ι)
    (v w : ι → ℝ) (z c b B : ℝ)
    (hbc : b ≤ c) (hcB : c ≤ B)
    (hwidth : ∀ g ∈ S, b ≤ w g ∧ w g ≤ B)
    (hout : z ≤ b ∨ B < z) :
    alpogeASKPhysicalCollarCost S v w z c = 0 := by
  unfold alpogeASKPhysicalCollarCost
  apply Finset.sum_eq_zero
  intro g hg
  rcases hout with hl | hr
  · rw [alpogeASKSharpCollarRemainder_zero_below
      z b c (w g) hbc (hwidth g hg).1 hl]
    ring
  · rw [alpogeASKSharpCollarRemainder_zero_above
      z B c (w g) hcB (hwidth g hg).2 hr]
    ring

end RHLean.Analysis
