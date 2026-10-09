import Mathlib
import «research.VF_MID_SEVEN_EIGHTHS_OWNER_ABEL»

/-!
# Genuine completed-square VF weights in the Mellin spectral coordinate

For a distinct-prime semiprime n=p*q, the strict OPEN
square-block indicator has an ordinary Perron/Mellin
representation without square-boundary ambiguity.

The ORIGINAL per-odd-seat reference w_R=VF_midBandMass(R)/R
stays attached to each completed square block. The
Mellin numerator is

  K(A,B;s) = Σ_(A<=R<B) w_R ((R+1)^(2s) - R^(2s)).

This module proves the exact FINITE COMPLEX Abel identity
turning K into only two boundary phases and the signed
original-weight variation. It is a concrete bridge into
the analytic prime-pair Dirichlet series, not an analytic
prime distribution theorem or a Sector Six contraction.

Perron inversion and any contour shift are NOT proved here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Complex-valued completed-square Abel identity. Uses w(B)
as the terminal coefficient, so A=B requires no exception. -/
theorem vfSevenEighthsComplexWeightedIncrementAbel
    (E w : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ R ∈ Finset.Ico A B,
      w R * (E (R + 1) - E R)) =
    w B * E B - w A * E A +
      ∑ R ∈ Finset.Ico A B,
        (w R - w (R + 1)) * E (R + 1) := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp
  | succ B hAB ih =>
      rw [Finset.sum_Ico_succ_top hAB,
          Finset.sum_Ico_succ_top hAB, ih]
      ring

/-- At a positive root R, this is (R²)^s on the positive
real logarithmic branch. It is entire in the spectral
variable s, and all square boundaries are explicit. -/
def vfSevenEighthsSquareMellinPhase (s : ℂ) (R : ℕ) : ℂ :=
  Complex.exp (s * (Real.log ((R : ℝ) ^ 2) : ℂ))

/-- The ORIGINAL VF physical per-odd-site weight embedded
into the complex Mellin coefficient ring. -/
def vfSevenEighthsMellinOriginalWeight (R : ℕ) : ℂ :=
  ((vfMidBandMass R / (R : ℝ)) : ℂ)

/-- Finite physical Mellin numerator for ALL completed squares. -/
def vfSevenEighthsCompletedSquareMellinKernel
    (s : ℂ) (A B : ℕ) : ℂ :=
  ∑ R ∈ Finset.Ico A B,
    vfSevenEighthsMellinOriginalWeight R *
      (vfSevenEighthsSquareMellinPhase s (R + 1) -
       vfSevenEighthsSquareMellinPhase s R)

/-- Original VF square-block Mellin kernel equals TWO endpoint
phases plus signed variation in its actual original weights. -/
theorem vfSevenEighthsCompletedSquareMellinKernel_abel
    (s : ℂ) (A B : ℕ) (hAB : A ≤ B) :
    vfSevenEighthsCompletedSquareMellinKernel s A B =
    vfSevenEighthsMellinOriginalWeight B *
        vfSevenEighthsSquareMellinPhase s B -
    vfSevenEighthsMellinOriginalWeight A *
        vfSevenEighthsSquareMellinPhase s A +
    ∑ R ∈ Finset.Ico A B,
      (vfSevenEighthsMellinOriginalWeight R -
       vfSevenEighthsMellinOriginalWeight (R + 1)) *
        vfSevenEighthsSquareMellinPhase s (R + 1) := by
  unfold vfSevenEighthsCompletedSquareMellinKernel
  exact vfSevenEighthsComplexWeightedIncrementAbel
    (vfSevenEighthsSquareMellinPhase s)
    vfSevenEighthsMellinOriginalWeight
    A B hAB

end RHLean.Analysis
