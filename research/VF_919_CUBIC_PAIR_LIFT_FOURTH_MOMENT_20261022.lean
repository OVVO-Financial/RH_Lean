import Mathlib

/-!
# Cubic prime-pair lifting: fourth moment before physical weighting

These are exact finite identities for the genuine two-index cubic
character expression, prior to taking norms. The implied prime-ideal
product reindex, de Faveri n=3 large sieve, row-test admission, and
physical source coefficients are NOT assumed or hidden here.

The proof target is the original OAI a=3/4 high row: apply a cubic
sieve to the squared cubic harmonic over pair ideals, use its fourth
moment with an independent physical window fourth moment, then
return to the original normalized detector.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Pair-lift BEFORE any triangle inequality: full ordered prime pairs,
including p=q, retain their actual phases. This is the algebraic
input to grouping pairs by the product ideal p*q. -/
theorem vf919CubicPrimePairLift
    {κ : Type*} [DecidableEq κ]
    (primes : Finset κ) (alpha chi : κ → ℂ) :
    (∑ p ∈ primes, alpha p * chi p) ^ 2 =
      ∑ p ∈ primes, ∑ q ∈ primes,
        (alpha p * alpha q) * (chi p * chi q) := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- The true fourth power of the original coherent cubic harmonic
is the SECOND moment of the complete pair-lift. There is no
claim that independent character phases average to zero. -/
theorem vf919CubicFourthMoment_eq_pairMoment
    {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (primes : Finset κ)
    (alpha : κ → ℂ) (chi : ι → κ → ℂ) :
    (∑ u ∈ rows, ‖∑ p ∈ primes, alpha p * chi u p‖ ^ 4) =
    ∑ u ∈ rows, ‖∑ p ∈ primes, ∑ q ∈ primes,
      (alpha p * alpha q) * (chi u p * chi u q)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro u hu
  calc
    ‖∑ p ∈ primes, alpha p * chi u p‖ ^ 4 =
      ‖(∑ p ∈ primes, alpha p * chi u p) ^ 2‖ ^ 2 := by
        rw [norm_pow]
        ring
    _ = _ := by
      rw [vf919CubicPrimePairLift primes alpha (chi u)]

/-- Native weighted fourth-to-second moment inequality. Applying this
to the actual OAI physical weight W(u) and cubic head H(u) needs no
artificial lower bound on the size of each Fiber.rows. -/
theorem vf919PhysicalWindowCubicFourthHolder
    {ι : Type*}
    (rows : Finset ι) (W H : ι → ℂ) :
    (∑ u ∈ rows, ‖W u‖ ^ 2 * ‖H u‖ ^ 2) ^ 2 ≤
      (∑ u ∈ rows, (‖W u‖ ^ 2) ^ 2) *
      (∑ u ∈ rows, (‖H u‖ ^ 2) ^ 2) := by
  exact Finset.sum_mul_sq_le_sq_mul_sq rows
    (fun u => ‖W u‖ ^ 2) (fun u => ‖H u‖ ^ 2)

/-- A genuinely source-directed consumer: a bound on the PHYSICAL
window 4th moment and an INDEPENDENT true cubic 4th moment pays the
weighted signed head without any per-fiber row-spread hypothesis.
Neither input is automatically true for arbitrary physical weights. -/
theorem vf919PhysicalWindowCubicFourthPayment
    {ι : Type*} (rows : Finset ι)
    (W H : ι → ℂ) (BW BH : ℝ)
    (hBW : 0 ≤ BW)
    (hWindow : (∑ u ∈ rows, (‖W u‖ ^ 2) ^ 2) ≤ BW)
    (hCubic : (∑ u ∈ rows, (‖H u‖ ^ 2) ^ 2) ≤ BH) :
    (∑ u ∈ rows, ‖W u‖ ^ 2 * ‖H u‖ ^ 2) ^ 2 ≤ BW * BH := by
  have hHnon : 0 ≤
      (∑ u ∈ rows, (‖H u‖ ^ 2) ^ 2) := by
    apply Finset.sum_nonneg
    intro u hu
    positivity
  exact (vf919PhysicalWindowCubicFourthHolder rows W H).trans
    (mul_le_mul hWindow hCubic hHnon hBW)

/-! ## Source-accurate sixth-free row cube-root cost and width gate -/

/-- Actual FreeRow rows are SIXTH-free; the pair-cubic fourth moment
must sum c^3 * u0 fibers. At U=P^(5/4) the cube-root counting term
GROWS like P^(1/6): the attractive cube-free P^(-1/12)
fourth-moment budget is not admissible for the original source.

At U=P^2 the worst actual term is P^(-1/3), and at the source
marked-width aperture U >= P^(9/2), it is P^(-1).
These are exponent equalities only, not a sieve or row admission. -/
theorem vf919ActualSixthFreePairFourthExponentArithmetic :
    (4 : ℝ) - 4 * (3 / 4) - (2 / 3) * (5 / 4) = 1 / 6 ∧
    (10 / 3 : ℝ) - 4 * (3 / 4) - (5 / 4) / 3 = -(1 / 12) ∧
    (4 : ℝ) - 4 * (3 / 4) - (2 / 3) * 2 = -(1 / 3) ∧
    (10 / 3 : ℝ) - 4 * (3 / 4) - 2 / 3 = -(1 / 3) ∧
    (4 : ℝ) - 4 * (3 / 4) - (2 / 3) * (9 / 2) = -2 ∧
    (10 / 3 : ℝ) - 4 * (3 / 4) - (9 / 2) / 3 = -(7 / 6) := by
  norm_num

/-- The ORIGINAL OAI marked-fourth width constraint:
2*m + 6*(3/4+2*Delta)*sum(selected widths) <= 1.
For m,Delta>=0, this forces the full selected width <=2/9. -/
theorem vf919ActualMarkedFourthWidthCap
    {Slot : Type*} (selected : Finset Slot)
    (width : Slot → ℝ) (m Delta : ℝ)
    (hm : 0 ≤ m) (hDelta : 0 ≤ Delta)
    (hw : ∀ s ∈ selected, 0 ≤ width s)
    (hGate : 2 * m + 6 * (3 / 4 + 2 * Delta) *
        (∑ s ∈ selected, width s) ≤ 1) :
    (∑ s ∈ selected, width s) ≤ (2 / 9 : ℝ) := by
  have hS : 0 ≤ (∑ s ∈ selected, width s) := by
    apply Finset.sum_nonneg
    intro s hs
    exact hw s hs
  have hDS : 0 ≤ Delta * (∑ s ∈ selected, width s) :=
    mul_nonneg hDelta hS
  nlinarith [hDS]

/-- Every actually selected slot is below the full width budget. -/
theorem vf919ActualSelectedSlotWidthCap
    {Slot : Type*} (selected : Finset Slot)
    (width : Slot → ℝ) (m Delta : ℝ) (s : Slot)
    (hm : 0 ≤ m) (hDelta : 0 ≤ Delta)
    (hw : ∀ t ∈ selected, 0 ≤ width t)
    (hGate : 2 * m + 6 * (3 / 4 + 2 * Delta) *
        (∑ t ∈ selected, width t) ≤ 1)
    (hs : s ∈ selected) :
    width s ≤ (2 / 9 : ℝ) := by
  have hSum := vf919ActualMarkedFourthWidthCap
    selected width m Delta hm hDelta hw hGate
  have hOne : width s ≤ (∑ t ∈ selected, width t) :=
    Finset.single_le_sum (fun t ht => hw t ht) hs
  linarith

/-- Original prime-slot P=U^width, so the actual marked-width gate
forces U >= P^(9/2). This is the aperture favorable to the
SIXTH-free pair-cubic sieve, rather than an invented U=P^(5/4). -/
theorem vf919SelectedPrimeAperture
    (U w : ℝ) (hU : 1 ≤ U) (hw : w ≤ 2 / 9) :
    (U ^ w) ^ (9 / 2 : ℝ) ≤ U := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    (U ^ w) ^ (9 / 2 : ℝ) = U ^ (w * (9 / 2 : ℝ)) := by
      rw [← Real.rpow_mul hUp.le]
    _ ≤ U ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
    _ = U := by rw [Real.rpow_one]

#print axioms vf919CubicPrimePairLift
#print axioms vf919CubicFourthMoment_eq_pairMoment
#print axioms vf919PhysicalWindowCubicFourthHolder
#print axioms vf919PhysicalWindowCubicFourthPayment
#print axioms vf919ActualSixthFreePairFourthExponentArithmetic
#print axioms vf919ActualMarkedFourthWidthCap
#print axioms vf919ActualSelectedSlotWidthCap
#print axioms vf919SelectedPrimeAperture

end RHLean.Analysis
