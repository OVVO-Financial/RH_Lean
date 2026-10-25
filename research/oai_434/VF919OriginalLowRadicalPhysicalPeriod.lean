import OAI.NumberTheory.DirichletL.Detector.PhysicalPoisson
import OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor

/-!
# Actual OpenAI physical numerator: short radical period

The original Poisson routine constructs a period from
generator * A * s. The ACTUAL multiplicative ideal-row factor
depends on the numerator modulo radical(A), even when A=I*J^3.

These two theorems replace that oversized source period by the ideal
  (generator) * radical(A) * (s)
for the original calibratedNumerator times sexticGauss, preserving all
nonunit masks and true calibration. No harmonic analysis is assumed.
-/

namespace OAI
noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

/-- Source-exact radical-conductor reduction for the true calibrated
numerator, without discarding any original calibration character. -/
theorem calibratedNumerator_congr_shortRadical
    (C : CalibrationData) (A m n : O)
    (h : m - n ∈ (Ideal.span {C.generator} : Ideal O) *
                       (Ideal.span {A} : Ideal O).radical) :
    calibratedNumerator C A m = calibratedNumerator C A n := by
  have hg : m - n ∈ (Ideal.span {C.generator} : Ideal O) :=
    Ideal.mul_le_left h
  have ha : m - n ∈ (Ideal.span {A} : Ideal O).radical :=
    Ideal.mul_le_right h
  have hm :
      Ideal.Quotient.mk (Ideal.span {C.generator}) m =
        Ideal.Quotient.mk (Ideal.span {C.generator}) n :=
    Ideal.Quotient.eq.mpr hg
  unfold calibratedNumerator CalibrationData.residueMonoid
  simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, hm, idealRowHom_congr_radical (Ideal.span {A}) m n ha]

/-- EXACT short period for the original calibrated low-Gaussian m-factor
  calibratedNumerator(C,A,m) * sexticGauss(s,-m).
The period is g * rad(A) * s, NOT the overly large g * A * s. -/
theorem calibratedLowGaussFactor_congr_shortRadical
    (C : CalibrationData) (A s m n : O) (hs : s ≠ 0)
    (h : m - n ∈
      ((Ideal.span {C.generator} : Ideal O) *
        (Ideal.span {A} : Ideal O).radical) * Ideal.span {s}) :
    calibratedNumerator C A m * sexticGauss s hs (-m) =
      calibratedNumerator C A n * sexticGauss s hs (-n) := by
  have hnum : m - n ∈
        (Ideal.span {C.generator} : Ideal O) *
          (Ideal.span {A} : Ideal O).radical :=
    Ideal.mul_le_left h
  have hsm : m - n ∈ (Ideal.span {s} : Ideal O) :=
    Ideal.mul_le_right h
  have hsneg : -m - (-n) ∈ (Ideal.span {s} : Ideal O) := by
    have hh : -(m - n) ∈ (Ideal.span {s} : Ideal O) :=
      (Ideal.span {s}).neg_mem hsm
    simpa only [neg_sub] using hh
  rw [calibratedNumerator_congr_shortRadical C A m n hnum,
    sexticGauss_frequency_congr s hs (-m) (-n) hsneg]

#print axioms calibratedNumerator_congr_shortRadical
#print axioms calibratedLowGaussFactor_congr_shortRadical

end SevenEighths.ProbePhysical
end
end OAI
