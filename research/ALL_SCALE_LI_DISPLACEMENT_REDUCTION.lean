import Mathlib
import RHLean.Proof.SquareRootLegalAncestryGramReduction
import «research.PRIME_FLIP_PNT_TELESCOPE»

/-!
# All-scale Li allocation and the exact prime-displacement remainder

This file records two layers without importing any unproved analytic estimate.

1. An abstract largest-prime recursion for a prime-frequency weight `w(q)`.
   Instantiating `w` with the repository's singleton Li increments
   `primeSievePNTDensity` gives the all-scale Li allocation model.  Two such
   recursions satisfy an exact triangular displacement identity.

2. At the physical square endpoint `X = R^2 - 1`, the already-compiled
   prime-flip PNT replacement error is rewritten in the coordinates aligned
   with `LowerMertensCriticalEnvelope`:

       sum_d D_{R,d} * (M(d) - 1),

   where `D_{R,d}` is the actual-prime-minus-Li discrepancy on the reciprocal
   quotient band.  The constant discrepancy mode has disappeared.  The same
   scalar is also identified with the existing Möbius-atom Abel telescope.

No PNT remainder estimate, RH hypothesis, or root-scale bound is asserted.
The final proposition names the remaining quantitative target.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Abstract all-scale prime-frequency recursion -/

/-- One largest-prime recursion step for a prime-frequency weight `w`.
The child cutoff `q-1` enforces strict largest-prime ordering. -/
def primeFrequencyStep
    (w : ℕ → ℂ) (S : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  1 - ∑ q ∈ Finset.Ioc 1 (min x y),
    w q * S (x / q) (q - 1)

/-- A state solves the complete largest-prime recursion for the weight `w`. -/
def IsPrimeFrequencyState
    (w : ℕ → ℂ) (S : ℕ → ℕ → ℂ) : Prop :=
  ∀ x y : ℕ, S x y = primeFrequencyStep w S x y

/-- Once the prime cutoff is above the physical endpoint, increasing it changes
nothing.  This is the saturation property needed for the square-root split. -/
def PrimeFrequencySaturated (S : ℕ → ℕ → ℂ) : Prop :=
  ∀ x y : ℕ, x ≤ y → S x y = S x x

/-- The repository's all-scale Li allocation uses the exact singleton
logarithmic-integral increments already used by the PNT centering layer. -/
def IsAllScaleLiState (S : ℕ → ℕ → ℂ) : Prop :=
  IsPrimeFrequencyState primeSievePNTDensity S

/-- The corresponding exact-prime recursion uses the ordinary prime indicator. -/
def IsAllScaleActualPrimeState (S : ℕ → ℕ → ℂ) : Prop :=
  IsPrimeFrequencyState primeSievePrimeIndicator S

/-- Exact Duhamel/Volterra identity for changing prime-frequency weights.
The first sum is the signed weight displacement; the second recursively
propagates the already-created state displacement to lower cutoffs. -/
theorem primeFrequencyState_sub_eq_signedDisplacement
    {wa wb : ℕ → ℂ} {A B : ℕ → ℕ → ℂ}
    (hA : IsPrimeFrequencyState wa A)
    (hB : IsPrimeFrequencyState wb B)
    (x y : ℕ) :
    A x y - B x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          (wa q - wb q) * A (x / q) (q - 1)) -
        ∑ q ∈ Finset.Ioc 1 (min x y),
          wb q * (A (x / q) (q - 1) - B (x / q) (q - 1)) := by
  rw [hA x y, hB x y]
  unfold primeFrequencyStep
  have hsum :
      (∑ q ∈ Finset.Ioc 1 (min x y), wa q * A (x / q) (q - 1)) -
          (∑ q ∈ Finset.Ioc 1 (min x y), wb q * B (x / q) (q - 1)) =
        (∑ q ∈ Finset.Ioc 1 (min x y),
          (wa q - wb q) * A (x / q) (q - 1)) +
        ∑ q ∈ Finset.Ioc 1 (min x y),
          wb q * (A (x / q) (q - 1) - B (x / q) (q - 1)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hsum]
  ring

/-- Specialization: actual-prime state minus all-scale Li state is driven only
by prime-indicator-minus-Li displacement and the lower triangular propagated
difference. -/
theorem actualPrimeState_sub_allScaleLiState
    {A L : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (hL : IsAllScaleLiState L)
    (x y : ℕ) :
    A x y - L x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          (primeSievePrimeIndicator q - primeSievePNTDensity q) *
            A (x / q) (q - 1)) -
        ∑ q ∈ Finset.Ioc 1 (min x y),
          primeSievePNTDensity q *
            (A (x / q) (q - 1) - L (x / q) (q - 1)) :=
  primeFrequencyState_sub_eq_signedDisplacement hA hL x y

/-! ## Exact square-root split in any saturated frequency model -/

/-- At `X = R^2 - 1`, every owner `q > R` has quotient `X/q < q`.
Thus a saturated largest-prime state reduces every upper child to its diagonal
value and the root/high split is exact. -/
theorem primeFrequencyState_squareRoot_split
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (R : ℕ) (hR : 2 ≤ R)
    (hS : IsPrimeFrequencyState w S)
    (hsat : PrimeFrequencySaturated S) :
    S (squareRootEndpoint R) (squareRootEndpoint R) =
      S (squareRootEndpoint R) R -
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          w q * S (squareRootEndpoint R / q) (squareRootEndpoint R / q) := by
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hfull := hS (squareRootEndpoint R) (squareRootEndpoint R)
  have hroot := hS (squareRootEndpoint R) R
  unfold primeFrequencyStep at hfull hroot
  rw [min_self] at hfull
  rw [min_eq_right hRX] at hroot
  have hhigh :
      (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          w q * S (squareRootEndpoint R / q) (q - 1)) =
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          w q * S (squareRootEndpoint R / q)
            (squareRootEndpoint R / q) := by
    apply Finset.sum_congr rfl
    intro q hq
    rcases Finset.mem_Ioc.mp hq with ⟨hRq, hqX⟩
    have hqpos : 0 < q := by omega
    have hXlt : squareRootEndpoint R < q * q := by
      unfold squareRootEndpoint
      nlinarith
    have hdivlt : squareRootEndpoint R / q < q := by
      apply (Nat.div_lt_iff_lt_mul hqpos).2
      simpa [Nat.mul_comm] using hXlt
    have hsatChild : squareRootEndpoint R / q ≤ q - 1 := by omega
    rw [hsat (squareRootEndpoint R / q) (q - 1) hsatChild]
  have hsplit :=
    Finset.sum_Ioc_consecutive
      (f := fun q : ℕ =>
        w q * S (squareRootEndpoint R / q) (q - 1))
      (by omega : 1 ≤ R) hRX
  rw [hfull, hroot, ← hhigh]
  linear_combination hsplit

/-- The assembled all-scale Li square-root model is literally its diagonal
state.  This is an exact model identity, not yet a quantitative bound. -/
theorem allScaleLiState_squareRoot_assembled_eq_diagonal
    {L : ℕ → ℕ → ℂ}
    (R : ℕ) (hR : 2 ≤ R)
    (hL : IsAllScaleLiState L)
    (hsat : PrimeFrequencySaturated L) :
    L (squareRootEndpoint R) R -
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          primeSievePNTDensity q *
            L (squareRootEndpoint R / q) (squareRootEndpoint R / q) =
      L (squareRootEndpoint R) (squareRootEndpoint R) := by
  symm
  exact primeFrequencyState_squareRoot_split R hR hL hsat

/-! ## Concrete square-endpoint prime-displacement remainder -/

/-- The reciprocal-band displacement after the constant mode has been removed.
These are exactly the coefficients naturally paired with the lower-envelope
coordinates `M(d)-1`. -/
def squareRootCenteredPrimeDisplacement (R : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (R - 1),
    primeSieveReciprocalPrimeDiscrepancy R (squareRootEndpoint R) d *
      (mertensSummatory d - 1)

/-- The chronological prime-flip replacement error is the negative centered
band sum.  In particular, the dangerous unweighted discrepancy mode is absent. -/
theorem squareRoot_primeFlipPNTError_eq_neg_centeredDisplacement
    (R : ℕ) (hR : 2 ≤ R) :
    primeFlipPNTError R (squareRootEndpoint R) =
      -squareRootCenteredPrimeDisplacement R := by
  rw [primeFlipPNTError_eq_reciprocalDiscrepancy]
  unfold primeSieveQuotientSupport squareRootCenteredPrimeDisplacement
  have htop :
      squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R (by omega)
  rw [htop]
  unfold primeFlipInheritedResponse
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The same centered remainder in the Abel-atom coordinates.  This is the
exact bridge between the `K`-aligned local-discrepancy form and the prefix
prime-discrepancy/Möbius-atom form. -/
theorem squareRoot_centeredPrimeDisplacement_eq_moebiusAtoms
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCenteredPrimeDisplacement R =
      (∑ d ∈ Finset.Icc 2 (R - 1),
          (((μ d : ℤ) : ℂ)) *
            primeSievePrimeDiscrepancy (squareRootEndpoint R / d)) -
        (mertensSummatory (R - 1) - 1) *
          primeSievePrimeDiscrepancy R := by
  have hcenter :=
    squareRoot_primeFlipPNTError_eq_neg_centeredDisplacement R hR
  have hatoms := squareRoot_primeFlipPNTError_eq_moebiusAtoms R hR
  calc
    squareRootCenteredPrimeDisplacement R =
        -primeFlipPNTError R (squareRootEndpoint R) := by
      rw [hcenter]
      ring
    _ = (∑ d ∈ Finset.Icc 2 (R - 1),
          (((μ d : ℤ) : ℂ)) *
            primeSievePrimeDiscrepancy (squareRootEndpoint R / d)) -
        (mertensSummatory (R - 1) - 1) *
          primeSievePrimeDiscrepancy R := by
      rw [hatoms]
      ring

/-- The remaining root-scale displacement theorem.  This is deliberately only
a proposition: proving it requires cancellation of the signed reciprocal-band
prime displacement against the lower Mertens response; no pointwise RH-sized
bound on `pi-Li` is assumed. -/
def SquareRootPrimeDisplacementRootBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖primeFlipPNTError R (squareRootEndpoint R)‖ ^ 2 ≤
        C * (R : ℝ) ^ 2 * K

/-- Equivalent statement directly on the centered reciprocal-band scalar. -/
def SquareRootCenteredPrimeDisplacementRootBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootCenteredPrimeDisplacement R‖ ^ 2 ≤
        C * (R : ℝ) ^ 2 * K

theorem squareRootPrimeDisplacementRootBounded_iff_centered :
    SquareRootPrimeDisplacementRootBoundedStatement ↔
      SquareRootCenteredPrimeDisplacementRootBoundedStatement := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R K hR hK
    have hb := hbound R K hR hK
    rw [squareRoot_primeFlipPNTError_eq_neg_centeredDisplacement R hR,
      norm_neg] at hb
    exact hb
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro R K hR hK
    have hb := hbound R K hR hK
    rw [squareRoot_primeFlipPNTError_eq_neg_centeredDisplacement R hR,
      norm_neg]
    exact hb

end RHLean.Analysis
