import Mathlib
import RHLean.Proof.SquareRootLegalAncestryGramReduction
import RHLean.Analysis.PrimeSieveDyadicCoherentAbel
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
  linear_combination -hsum

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
    have hXltRsq : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      have hpos : 0 < R ^ 2 := by positivity
      omega
    have hRsqLt : R ^ 2 < q ^ 2 :=
      Nat.pow_lt_pow_left hRq (by omega)
    have hXlt : squareRootEndpoint R < q * q := by
      simpa [pow_two] using hXltRsq.trans hRsqLt
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

/-! ## Dyadic coordinate split of the actual-minus-Li displacement

This is a coordinate change on the *actual* displacement above, not a new
analytic hypothesis.  The dyadic reciprocal decomposition already available
for the PNT error separates each reciprocal discrepancy into a block mean and
a mean-zero wavelet.  Because the displacement is weighted by `M(d)-1`, the
mean-zero wavelet loses the constant `-1` identically.  Hence its complete
contribution is exactly the repository's existing boundary-free Abel wavelet
channel. -/

/-- The complete mean-zero dyadic wavelet has zero mass on reciprocal support. -/
theorem sum_primeSieveDyadicWavelet_support_eq_zero
    (y x : ℕ) :
    (∑ d ∈ primeSieveQuotientSupport y x,
      primeSieveDyadicWavelet y x d) = 0 := by
  classical
  calc
    (∑ d ∈ primeSieveQuotientSupport y x,
        primeSieveDyadicWavelet y x d) =
      ∑ d ∈ primeSieveQuotientSupport y x,
        ∑ j ∈ primeSieveDyadicBlockIndices y x,
          primeSieveDyadicBlockWaveletMask y x j d := by
            apply Finset.sum_congr rfl
            intro d hd
            symm
            exact sum_primeSieveDyadicBlockWaveletMask_eq_wavelet hd
    _ = ∑ j ∈ primeSieveDyadicBlockIndices y x,
          ∑ d ∈ primeSieveQuotientSupport y x,
            primeSieveDyadicBlockWaveletMask y x j d := by
            rw [Finset.sum_comm]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          exact sum_primeSieveDyadicBlockWaveletMask_eq_zero hj

/-- The block-mean part of the centered actual-minus-Li displacement. -/
def squareRootCenteredDyadicCoherentDisplacement (R : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
    primeSieveDyadicBlockMean R (squareRootEndpoint R)
        (primeSieveDyadicIndex d) *
      (mertensSummatory d - 1)

/-- The mean-zero part of the centered actual-minus-Li displacement. -/
def squareRootCenteredDyadicWaveletDisplacement (R : ℕ) : ℂ :=
  ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
    primeSieveDyadicWavelet R (squareRootEndpoint R) d *
      (mertensSummatory d - 1)

/-- Exact coherent/wavelet split of the physical actual-minus-Li displacement. -/
theorem squareRootCenteredPrimeDisplacement_eq_dyadicCentered
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCenteredPrimeDisplacement R =
      squareRootCenteredDyadicCoherentDisplacement R +
        squareRootCenteredDyadicWaveletDisplacement R := by
  unfold squareRootCenteredPrimeDisplacement
    squareRootCenteredDyadicCoherentDisplacement
    squareRootCenteredDyadicWaveletDisplacement
    primeSieveQuotientSupport
  have htop :
      squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R (by omega)
  rw [htop, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [primeSieveReciprocalPrimeDiscrepancy_eq_dyadicMean_add_wavelet]
  ring

/-- **The constant coordinate disappears from the mean-zero channel.**

Since the wavelet has zero total mass, weighting it by `M(d)-1` is exactly
the same as weighting it by `M(d)`.  Thus this part of the actual transfer is
already the existing dyadic wavelet PNT error. -/
theorem squareRootCenteredDyadicWaveletDisplacement_eq_waveletPNTError
    (R : ℕ) :
    squareRootCenteredDyadicWaveletDisplacement R =
      primeSieveDyadicWaveletPNTError R (squareRootEndpoint R) := by
  have hzero :=
    sum_primeSieveDyadicWavelet_support_eq_zero R (squareRootEndpoint R)
  unfold squareRootCenteredDyadicWaveletDisplacement
    primeSieveDyadicWaveletPNTError
  calc
    (∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
        primeSieveDyadicWavelet R (squareRootEndpoint R) d *
          (mertensSummatory d - 1)) =
      ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
        (primeSieveDyadicWavelet R (squareRootEndpoint R) d *
            mertensSummatory d -
          primeSieveDyadicWavelet R (squareRootEndpoint R) d) := by
            apply Finset.sum_congr rfl
            intro d _hd
            ring
    _ = (∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
          primeSieveDyadicWavelet R (squareRootEndpoint R) d *
            mertensSummatory d) -
        ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
          primeSieveDyadicWavelet R (squareRootEndpoint R) d := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
          primeSieveDyadicWavelet R (squareRootEndpoint R) d *
            mertensSummatory d := by
            rw [hzero]
            ring

/-- **Actual-to-Li transfer with the wavelet already in a boundary-free Abel
coordinate.**  No endpoint Mertens term survives in the mean-zero channel.
The only part not absorbed by the existing Abel identity is the signed
block-mean coherent displacement. -/
theorem squareRootCenteredPrimeDisplacement_eq_coherent_add_boundaryFreeWavelet
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootCenteredPrimeDisplacement R =
      squareRootCenteredDyadicCoherentDisplacement R +
        ∑ j ∈ primeSieveDyadicBlockIndices R (squareRootEndpoint R),
          ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
            (((μ d : ℤ) : ℂ)) *
              primeSieveDyadicBlockAbelPotential
                R (squareRootEndpoint R) j d := by
  rw [squareRootCenteredPrimeDisplacement_eq_dyadicCentered R hR,
    squareRootCenteredDyadicWaveletDisplacement_eq_waveletPNTError,
    primeSieveDyadicWaveletPNTError_eq_boundaryFreeAbel]

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

/-! ## Exact Li allocation: the displacement channel is identically zero -/

/-- The theoretical exact-Li allocation hypothesis at the square endpoint.
It says that every reciprocal quotient band carries exactly its Li mass.
This is a model hypothesis, not a claim about the actual discrete primes. -/
def SquareRootExactLiAllocation (R : ℕ) : Prop :=
  ∀ d ∈ Finset.Icc 1 (R - 1),
    primeSieveReciprocalPrimeDiscrepancy R (squareRootEndpoint R) d = 0

/-- Under exact Li allocation, the centered prime-displacement scalar vanishes
term by term.  There is no prime-location error left to estimate inside the
theoretical Li model. -/
theorem squareRoot_centeredPrimeDisplacement_eq_zero_of_exactLiAllocation
    (R : ℕ) (hLi : SquareRootExactLiAllocation R) :
    squareRootCenteredPrimeDisplacement R = 0 := by
  unfold squareRootCenteredPrimeDisplacement
  apply Finset.sum_eq_zero
  intro d hd
  rw [hLi d hd, zero_mul]

/-- Under exact Li allocation, the complete chronological PNT replacement
error is exactly zero. -/
theorem squareRoot_primeFlipPNTError_eq_zero_of_exactLiAllocation
    (R : ℕ) (hR : 2 ≤ R) (hLi : SquareRootExactLiAllocation R) :
    primeFlipPNTError R (squareRootEndpoint R) = 0 := by
  rw [squareRoot_primeFlipPNTError_eq_neg_centeredDisplacement R hR,
    squareRoot_centeredPrimeDisplacement_eq_zero_of_exactLiAllocation R hLi,
    neg_zero]

/-- Exact Li allocation at every square-root stage. -/
def ExactLiAllocationAtAllSquareRoots : Prop :=
  ∀ R : ℕ, 2 ≤ R → SquareRootExactLiAllocation R

/-- With exact Li allocation, the displacement bound is automatic with constant
zero.  Hence the displacement theorem is not part of the intrinsic Li-model
bound: it belongs only to the later transfer back to actual primes. -/
theorem squareRootPrimeDisplacementRootBounded_of_exactLiAllocation
    (hLi : ExactLiAllocationAtAllSquareRoots) :
    SquareRootPrimeDisplacementRootBoundedStatement := by
  refine ⟨0, by norm_num, ?_⟩
  intro R K hR hK
  rw [squareRoot_primeFlipPNTError_eq_zero_of_exactLiAllocation R hR (hLi R hR)]
  simp

/-! ## Intrinsic all-scale Li target -/

/-- The pure all-scale Li square-root theorem.  No actual-prime indicator and
no prime-count discrepancy occurs in this statement.  This is the quantitative
question that remains *inside* the exact Li allocation model. -/
def AllScaleLiSquareRootBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℕ → ℕ → ℂ) (R : ℕ),
      IsAllScaleLiState L →
      PrimeFrequencySaturated L →
      2 ≤ R →
      ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ ^ 2 ≤
        C * (R : ℝ) ^ 2

/-- Equivalent assembled formulation of the intrinsic Li target at one scale:
the root-sector state minus the Li-weighted upper sector is exactly the
diagonal Li state, so any diagonal estimate transfers with no displacement
term. -/
theorem allScaleLiState_squareRoot_assembled_norm_sq_eq_diagonal
    {L : ℕ → ℕ → ℂ}
    (R : ℕ) (hR : 2 ≤ R)
    (hL : IsAllScaleLiState L)
    (hsat : PrimeFrequencySaturated L) :
    ‖L (squareRootEndpoint R) R -
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          primeSievePNTDensity q *
            L (squareRootEndpoint R / q) (squareRootEndpoint R / q)‖ ^ 2 =
      ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ ^ 2 := by
  rw [allScaleLiState_squareRoot_assembled_eq_diagonal R hR hL hsat]


end RHLean.Analysis
