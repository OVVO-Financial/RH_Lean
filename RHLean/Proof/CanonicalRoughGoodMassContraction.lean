import Mathlib
import RHLean.Proof.CanonicalRoughQuantitativeContraction

/-!
# PNT-style good-mass decrement for canonical rough contraction

This file tightens exactly one existing mechanism.  The quantitative rough
Euler theorem currently bounds every transported physical defect layer by the
single worst scaled value

`Delta = max_p p * ||D_p||`,

which gives `||Ledger|| <= (1 - P) * Delta`.  That max-floor step discards the
feature that drives the native Selberg--Erdos PNT contraction: a positive amount
of reciprocal Euler mass may live on layers whose actual error is strictly
smaller than the ambient envelope.

For an ambient scaled-defect envelope `alpha` and a lower threshold `beta`, the
transported good mass below is exactly the reciprocal Euler mass of those
chronological steps satisfying

`p * ||D_p|| <= beta`,

with every later/smaller step multiplied by all earlier/larger Euler factors it
has already inherited.  The resulting ledger estimate is

`||Ledger|| <= (1 - P) * alpha - (alpha - beta) * GoodMass`.

Hence, if the terminal compressed mode is also bounded by `alpha`, the complete
compressed profile satisfies

`||Profile|| <= alpha - (alpha - beta) * GoodMass`.

This is the direct good-fibre compensation law used by the native PNT proof,
now on the already-existing RH-critical reciprocal contraction.  No new carrier,
reindexing, support estimate, or coordinate system is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Euler-transported reciprocal mass of physical steps whose *actual scaled
signed defect* is at most `beta`.  The recursion has exactly the same transport
orientation as `squareRootCanonicalRoughTransportedDefectLedger`: the head is
the earlier/larger prime, so it multiplies all good mass generated later. -/
def squareRootCanonicalRoughGoodDefectEulerMass
    (R : ℕ) (beta : ℝ) : List CanonicalRoughPhysicalEulerStep → ℝ
  | [] => 0
  | step :: steps =>
      (if (step.1 : ℝ) *
          ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤ beta then
        1 / (step.1 : ℝ)
      else 0) +
      canonicalRoughEulerFactor step.1 *
        squareRootCanonicalRoughGoodDefectEulerMass R beta steps

/-- The transported good mass is nonnegative on a genuine-prime step list. -/
theorem squareRootCanonicalRoughGoodDefectEulerMass_nonneg
    (R : ℕ) (beta : ℝ) (steps : List CanonicalRoughPhysicalEulerStep)
    (hprime : ∀ step ∈ steps, step.1.Prime) :
    0 ≤ squareRootCanonicalRoughGoodDefectEulerMass R beta steps := by
  induction steps with
  | nil => simp [squareRootCanonicalRoughGoodDefectEulerMass]
  | cons step steps ih =>
      have hp : step.1.Prime := hprime step (by simp)
      have htailPrime : ∀ s ∈ steps, s.1.Prime := by
        intro s hs
        exact hprime s (by simp [hs])
      have ha0 : 0 ≤ canonicalRoughEulerFactor step.1 :=
        canonicalRoughEulerFactor_nonneg hp
      have htail0 := ih htailPrime
      by_cases hgood :
          (step.1 : ℝ) *
              ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤ beta
      · simp only [squareRootCanonicalRoughGoodDefectEulerMass, if_pos hgood]
        exact add_nonneg (by positivity) (mul_nonneg ha0 htail0)
      · simp only [squareRootCanonicalRoughGoodDefectEulerMass, if_neg hgood,
          zero_add]
        exact mul_nonneg ha0 htail0

/-- **PNT-style good-mass improvement of the transported defect ledger.**

Assume only the existing ambient scaled signed-defect envelope
`p * ||D_p|| <= alpha`.  Every layer which in fact satisfies the better bound
`p * ||D_p|| <= beta` earns back its Euler-transported reciprocal mass.  Thus
the old `(1-P) * alpha` floor is sharpened by the exact decrement
`(alpha-beta) * GoodMass`.
-/
theorem squareRootCanonicalRoughTransportedDefectLedger_norm_le_goodMass
    (R : ℕ) (steps : List CanonicalRoughPhysicalEulerStep)
    (alpha beta : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta ≤ alpha)
    (hprime : ∀ step ∈ steps, step.1.Prime)
    (henv : ∀ step ∈ steps,
      (step.1 : ℝ) *
        ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤ alpha) :
    ‖squareRootCanonicalRoughTransportedDefectLedger R steps‖ ≤
      (1 - canonicalRoughEulerProduct steps) * alpha -
        (alpha - beta) *
          squareRootCanonicalRoughGoodDefectEulerMass R beta steps := by
  induction steps with
  | nil =>
      simp [squareRootCanonicalRoughTransportedDefectLedger,
        canonicalRoughEulerProduct,
        squareRootCanonicalRoughGoodDefectEulerMass]
  | cons step steps ih =>
      have hp : step.1.Prime := hprime step (by simp)
      have htailPrime : ∀ s ∈ steps, s.1.Prime := by
        intro s hs
        exact hprime s (by simp [hs])
      have htailEnv : ∀ s ∈ steps,
          (s.1 : ℝ) *
            ‖squareRootCanonicalRoughPhysicalStepDefect R s‖ ≤ alpha := by
        intro s hs
        exact henv s (by simp [hs])
      have htail := ih htailPrime htailEnv
      have ha0 : 0 ≤ canonicalRoughEulerFactor step.1 :=
        canonicalRoughEulerFactor_nonneg hp
      have hpPos : 0 < (step.1 : ℝ) := by
        exact_mod_cast hp.pos
      have hmul :
          ‖(canonicalRoughEulerFactor step.1 : ℂ) *
              squareRootCanonicalRoughTransportedDefectLedger R steps‖ =
            canonicalRoughEulerFactor step.1 *
              ‖squareRootCanonicalRoughTransportedDefectLedger R steps‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ha0]
      by_cases hgood :
          (step.1 : ℝ) *
              ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤ beta
      · have hdefect :
            ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤
              beta / (step.1 : ℝ) := by
          apply (le_div_iff₀ hpPos).2
          simpa [mul_comm] using hgood
        simp only [squareRootCanonicalRoughTransportedDefectLedger]
        calc
          ‖(canonicalRoughEulerFactor step.1 : ℂ) *
                squareRootCanonicalRoughTransportedDefectLedger R steps +
              squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤
            ‖(canonicalRoughEulerFactor step.1 : ℂ) *
                squareRootCanonicalRoughTransportedDefectLedger R steps‖ +
              ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ :=
            norm_add_le _ _
          _ = canonicalRoughEulerFactor step.1 *
                ‖squareRootCanonicalRoughTransportedDefectLedger R steps‖ +
              ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ := by
            rw [hmul]
          _ ≤ canonicalRoughEulerFactor step.1 *
                ((1 - canonicalRoughEulerProduct steps) * alpha -
                  (alpha - beta) *
                    squareRootCanonicalRoughGoodDefectEulerMass R beta steps) +
              beta / (step.1 : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_left htail ha0) hdefect
          _ = (1 - canonicalRoughEulerFactor step.1 *
                canonicalRoughEulerProduct steps) * alpha -
              (alpha - beta) *
                (1 / (step.1 : ℝ) +
                  canonicalRoughEulerFactor step.1 *
                    squareRootCanonicalRoughGoodDefectEulerMass R beta steps) := by
            unfold canonicalRoughEulerFactor
            ring
          _ = (1 - canonicalRoughEulerProduct (step :: steps)) * alpha -
              (alpha - beta) *
                squareRootCanonicalRoughGoodDefectEulerMass
                  R beta (step :: steps) := by
            simp [canonicalRoughEulerProduct,
              squareRootCanonicalRoughGoodDefectEulerMass, hgood]
      · have hhead := henv step (by simp)
        have hdefect :
            ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤
              alpha / (step.1 : ℝ) := by
          apply (le_div_iff₀ hpPos).2
          simpa [mul_comm] using hhead
        simp only [squareRootCanonicalRoughTransportedDefectLedger]
        calc
          ‖(canonicalRoughEulerFactor step.1 : ℂ) *
                squareRootCanonicalRoughTransportedDefectLedger R steps +
              squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤
            ‖(canonicalRoughEulerFactor step.1 : ℂ) *
                squareRootCanonicalRoughTransportedDefectLedger R steps‖ +
              ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ :=
            norm_add_le _ _
          _ = canonicalRoughEulerFactor step.1 *
                ‖squareRootCanonicalRoughTransportedDefectLedger R steps‖ +
              ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ := by
            rw [hmul]
          _ ≤ canonicalRoughEulerFactor step.1 *
                ((1 - canonicalRoughEulerProduct steps) * alpha -
                  (alpha - beta) *
                    squareRootCanonicalRoughGoodDefectEulerMass R beta steps) +
              alpha / (step.1 : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_left htail ha0) hdefect
          _ = (1 - canonicalRoughEulerFactor step.1 *
                canonicalRoughEulerProduct steps) * alpha -
              (alpha - beta) *
                (canonicalRoughEulerFactor step.1 *
                  squareRootCanonicalRoughGoodDefectEulerMass R beta steps) := by
            unfold canonicalRoughEulerFactor
            ring
          _ = (1 - canonicalRoughEulerProduct (step :: steps)) * alpha -
              (alpha - beta) *
                squareRootCanonicalRoughGoodDefectEulerMass
                  R beta (step :: steps) := by
            simp [canonicalRoughEulerProduct,
              squareRootCanonicalRoughGoodDefectEulerMass, hgood]

/-- **Strict good-mass contraction of the complete compressed profile.**

If the terminal compressed mode is also bounded by the same ambient envelope
`alpha`, then the Euler product and the baseline part of the defect ledger add
back to exactly `alpha`.  What remains is precisely the PNT-style good-mass
decrement `(alpha-beta) * GoodMass`. -/
theorem squareRootCanonicalRoughCompressedProfile_norm_le_goodMass
    (R : ℕ) (steps : List CanonicalRoughPhysicalEulerStep)
    (z : ℂ) (alpha beta : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta ≤ alpha)
    (hprime : ∀ step ∈ steps, step.1.Prime)
    (hz : ‖z‖ ≤ alpha)
    (henv : ∀ step ∈ steps,
      (step.1 : ℝ) *
        ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤ alpha) :
    ‖(canonicalRoughEulerProduct steps : ℂ) * z +
        squareRootCanonicalRoughTransportedDefectLedger R steps‖ ≤
      alpha - (alpha - beta) *
        squareRootCanonicalRoughGoodDefectEulerMass R beta steps := by
  have hP0 := canonicalRoughEulerProduct_nonneg steps hprime
  have hledger :=
    squareRootCanonicalRoughTransportedDefectLedger_norm_le_goodMass
      R steps alpha beta halpha hbeta hba hprime henv
  calc
    ‖(canonicalRoughEulerProduct steps : ℂ) * z +
        squareRootCanonicalRoughTransportedDefectLedger R steps‖ ≤
      ‖(canonicalRoughEulerProduct steps : ℂ) * z‖ +
        ‖squareRootCanonicalRoughTransportedDefectLedger R steps‖ :=
      norm_add_le _ _
    _ = canonicalRoughEulerProduct steps * ‖z‖ +
        ‖squareRootCanonicalRoughTransportedDefectLedger R steps‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP0]
    _ ≤ canonicalRoughEulerProduct steps * alpha +
        ((1 - canonicalRoughEulerProduct steps) * alpha -
          (alpha - beta) *
            squareRootCanonicalRoughGoodDefectEulerMass R beta steps) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hz hP0) hledger
    _ = alpha - (alpha - beta) *
        squareRootCanonicalRoughGoodDefectEulerMass R beta steps := by ring

/-- A positive amount of genuinely good Euler mass gives a strict contraction
below the ambient envelope. -/
theorem squareRootCanonicalRoughCompressedProfile_norm_lt_of_goodMass_pos
    (R : ℕ) (steps : List CanonicalRoughPhysicalEulerStep)
    (z : ℂ) (alpha beta : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta < alpha)
    (hprime : ∀ step ∈ steps, step.1.Prime)
    (hz : ‖z‖ ≤ alpha)
    (henv : ∀ step ∈ steps,
      (step.1 : ℝ) *
        ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤ alpha)
    (hgoodMass :
      0 < squareRootCanonicalRoughGoodDefectEulerMass R beta steps) :
    ‖(canonicalRoughEulerProduct steps : ℂ) * z +
        squareRootCanonicalRoughTransportedDefectLedger R steps‖ < alpha := by
  have hle := squareRootCanonicalRoughCompressedProfile_norm_le_goodMass
    R steps z alpha beta halpha hbeta hba.le hprime hz henv
  have hdrop :
      0 < (alpha - beta) *
        squareRootCanonicalRoughGoodDefectEulerMass R beta steps :=
    mul_pos (sub_pos.mpr hba) hgoodMass
  linarith

/-- **Cubic PNT-form corollary.**  With the optimized native-PNT threshold
`beta = 2*alpha/3`, any lower bound

`c * alpha^2 <= GoodMass`

produces the cubic decrement

`alpha -> alpha - (c/3) * alpha^3`.

The remaining hard arithmetic input is therefore exactly the same kind of input
as in the native PNT proof: prove positive quadratic good reciprocal mass. -/
theorem squareRootCanonicalRoughCompressedProfile_cubic_step_of_goodMass
    (R : ℕ) (steps : List CanonicalRoughPhysicalEulerStep)
    (z : ℂ) (alpha c : ℝ)
    (halpha : 0 ≤ alpha) (hc : 0 ≤ c)
    (hprime : ∀ step ∈ steps, step.1.Prime)
    (hz : ‖z‖ ≤ alpha)
    (henv : ∀ step ∈ steps,
      (step.1 : ℝ) *
        ‖squareRootCanonicalRoughPhysicalStepDefect R step‖ ≤ alpha)
    (hgoodMass :
      c * alpha ^ 2 ≤
        squareRootCanonicalRoughGoodDefectEulerMass
          R (2 * alpha / 3) steps) :
    ‖(canonicalRoughEulerProduct steps : ℂ) * z +
        squareRootCanonicalRoughTransportedDefectLedger R steps‖ ≤
      alpha - (c / 3) * alpha ^ 3 := by
  have hbeta : 0 ≤ 2 * alpha / 3 := by positivity
  have hba : 2 * alpha / 3 ≤ alpha := by nlinarith
  have hle := squareRootCanonicalRoughCompressedProfile_norm_le_goodMass
    R steps z alpha (2 * alpha / 3) halpha hbeta hba hprime hz henv
  have hcoef : 0 ≤ alpha - 2 * alpha / 3 := by nlinarith
  have hgain := mul_le_mul_of_nonneg_left hgoodMass hcoef
  calc
    ‖(canonicalRoughEulerProduct steps : ℂ) * z +
        squareRootCanonicalRoughTransportedDefectLedger R steps‖ ≤
      alpha - (alpha - 2 * alpha / 3) *
        squareRootCanonicalRoughGoodDefectEulerMass
          R (2 * alpha / 3) steps := hle
    _ ≤ alpha - (alpha - 2 * alpha / 3) * (c * alpha ^ 2) := by
      linarith
    _ = alpha - (c / 3) * alpha ^ 3 := by ring

end RHLean.Proof
