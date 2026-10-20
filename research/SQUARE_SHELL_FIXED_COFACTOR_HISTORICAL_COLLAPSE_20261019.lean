import Mathlib
import «research.SQUARE_SHELL_TRAPEZOID_FINITE_COFACTOR_20261018»

/-!
# Translated finite prime-cofactor chronology collapses to two broad walls

The original R=317 / R=1027 historical transport has substantial
cancellation within each *fixed cofactor* across many square shells.
This module imports the corrected half-open translated wall functions
and proves that summing prime-count differences across ANY consecutive
history interval leaves only the two exterior cofactor quotient walls.

It works for arbitrary F : Nat -> Real (in particular the genuine
prime count, a floor-Li model, or their discrepancy). It carries actual
Mobius(c) with no sign averaging. The entire low-c source at fixed
cofactor cutoff C telescopes EXACTLY.

No PNT, RH, 5/6, Li error estimate, or signed bilinear estimate is
asserted. The high-c physical source with c<=r is distinct and requires
the existing admitted-product factor-order equivalence to apply a
cofactor-dependent lower/root boundary.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

private theorem shellCofactor_history_telescope
    (G : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b, (G (r + 1) - G r)) = G b - G a := by
  rw [Finset.sum_Ico_eq_sub _ hab,
      Finset.sum_range_sub G b, Finset.sum_range_sub G a]
  abel

/-- Literal floor-prime extension difference on the shifted half-open shell.
F may be actual pi, integer Li, or their signed discrepancy. -/
def shellCofactorShiftedPrimeIncrement
    (F : ℕ → ℝ) (c r T k : ℕ) : ℝ :=
  F (shellTrapezoidUpper r T k / c) -
    F (shellTrapezoidLower r T k / c)

/-- The right quotient wall of r is the left wall of r+1. -/
theorem shellCofactorShiftedWalls_adjoin
    (r T k : ℕ) :
    shellTrapezoidUpper r T k =
      shellTrapezoidLower (r + 1) T k := by
  rfl

/-- **Historical fixed-c exact telescope** for all real prime-count models.
The earlier short prime windows are not independently estimated. -/
theorem shellCofactorShiftedPrimeIncrement_sum_eq_broadInterval
    (F : ℕ → ℝ) (c a b T k : ℕ) (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b,
       shellCofactorShiftedPrimeIncrement F c r T k) =
      F (shellTrapezoidLower b T k / c) -
        F (shellTrapezoidLower a T k / c) := by
  have h := shellCofactor_history_telescope
    (fun r => F (shellTrapezoidLower r T k / c)) hab
  unfold shellCofactorShiftedPrimeIncrement
  simpa only [shellCofactorShiftedWalls_adjoin] using! h

/-- The *fixed-cofactor population* carries genuine Mobius signs.
The cutoff C is held fixed across the history; moving physical owner
admissibility is not silently added. -/
def shellCofactorHistoricalSignedPopulation
    (F : ℕ → ℝ) (a b T k C : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 C,
    shellTrapezoidMu c *
      (∑ r ∈ Finset.Ico a b,
        shellCofactorShiftedPrimeIncrement F c r T k)

/-- **Signed** fixed-cofactor history collapses to one broad interval
for EACH c, preserving exactly the cofactor multiplicities. -/
theorem shellCofactorHistoricalSignedPopulation_eq_boundary
    (F : ℕ → ℝ) (a b T k C : ℕ) (hab : a ≤ b) :
    shellCofactorHistoricalSignedPopulation F a b T k C =
      ∑ c ∈ Finset.Icc 1 C, shellTrapezoidMu c *
        (F (shellTrapezoidLower b T k / c) -
         F (shellTrapezoidLower a T k / c)) := by
  unfold shellCofactorHistoricalSignedPopulation
  apply Finset.sum_congr rfl
  intro c hc
  rw [shellCofactorShiftedPrimeIncrement_sum_eq_broadInterval F c a b T k hab]

/-- The same equality remains exact AFTER averaging 2T+1 shifts:
smoothing changes only the TWO exterior quotient walls, not the
internal arithmetic prime-event counts. -/
theorem shellCofactorHistoricalSignedMean_eq_boundaryMean
    (F : ℕ → ℝ) (a b T C : ℕ) (hab : a ≤ b) :
    shellTrapezoidMean T
      (fun k => shellCofactorHistoricalSignedPopulation F a b T k C) =
      shellTrapezoidMean T
        (fun k => ∑ c ∈ Finset.Icc 1 C,
          shellTrapezoidMu c *
            (F (shellTrapezoidLower b T k / c) -
             F (shellTrapezoidLower a T k / c))) := by
  unfold shellTrapezoidMean
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact shellCofactorHistoricalSignedPopulation_eq_boundary
    F a b T k C hab

/-- The signed PNT error remains the genuine actual-minus-model boundary,
not zero after the telescope. This is the independent analytic channel
which the R=317 / R=1027 cofactor cancellations expose but do NOT bound. -/
theorem shellCofactorHistoricalError_eq_signedBoundary
    (piActual piModel : ℕ → ℝ) (a b T k C : ℕ) (hab : a ≤ b) :
    shellCofactorHistoricalSignedPopulation
      (fun n => piActual n - piModel n) a b T k C =
      ∑ c ∈ Finset.Icc 1 C, shellTrapezoidMu c *
        ((piActual (shellTrapezoidLower b T k / c) -
          piModel (shellTrapezoidLower b T k / c)) -
         (piActual (shellTrapezoidLower a T k / c) -
          piModel (shellTrapezoidLower a T k / c))) := by
  exact shellCofactorHistoricalSignedPopulation_eq_boundary
    (fun n => piActual n - piModel n) a b T k C hab

#print axioms shellCofactorShiftedPrimeIncrement_sum_eq_broadInterval
#print axioms shellCofactorHistoricalSignedPopulation_eq_boundary
#print axioms shellCofactorHistoricalSignedMean_eq_boundaryMean
#print axioms shellCofactorHistoricalError_eq_signedBoundary

end RHLean.Analysis
