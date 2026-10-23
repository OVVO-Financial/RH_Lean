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

/-- Exact P^(5/4) and P^2 pair-modulus exponent budgets at a=3/4,
where the pair-coefficient diagonal has norm exponent 2-4a=-1
and the n=3 mixed term is (U*P^2)^(2/3). -/
theorem vf919CubicPairFourthExponentArithmetic :
    (2 : ℝ) - 4 * (3 / 4) +
        (2 / 3) * (5 / 4 + 2) - 5 / 4 = -(1 / 12 : ℝ) ∧
    (2 : ℝ) - 4 * (3 / 4) +
        (2 / 3) * (2 + 2) - 2 = -(1 / 3 : ℝ) ∧
    ((5 / 4 : ℝ) * (1 / 15)) / 2 = 1 / 24 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

#print axioms vf919CubicPrimePairLift
#print axioms vf919CubicFourthMoment_eq_pairMoment
#print axioms vf919PhysicalWindowCubicFourthHolder
#print axioms vf919PhysicalWindowCubicFourthPayment
#print axioms vf919CubicPairFourthExponentArithmetic

end RHLean.Analysis
