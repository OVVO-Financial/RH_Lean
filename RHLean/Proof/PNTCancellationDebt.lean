import Mathlib
import RHLean.Analysis.SquareRootShallowReciprocalCrossing
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction

/-!
# PNT density and cancellation debt

This file separates two different quantities in the post-root reciprocal
transport.

* `pntRawCancellationExposure` is the unsigned seat exposure.  A prime in
  reciprocal layer `d` has exactly `d-1` candidate proper-multiple seats, so
  the raw layer exposure is `(d-1) * L_R(d)`.
* `pntCancellationDebt R d` is measured only after the already-compiled
  predecessor-dense cube contraction.  For each prime in layer `d`, the
  remaining signed object is the canonical first-jump residual.  We sum those
  residuals over the whole layer *before* taking absolute value, so cross-prime
  cancellation is preserved.

The PNT controls the arrival density `L_R(d)` at every fixed reciprocal depth.
It does not by itself bound the live first-jump debt.  The latter is isolated as
`PNTCancellationDebtPolylogBoundedStatement`.

A bookkeeping correction is important: because the raw exposure has the extra
factor `d-1`, summing fixed-depth PNT densities through `d < R` has a harmonic
factor.  Thus the natural full raw scale is quadratic in `R`, not
`R^2 / log R`.  Any root-scale saving must come from cancellation debt, not from
silently assigning the prime-arrival scale to the seat-exposure scale.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- Prime coordinates in reciprocal layer `d` at the square endpoint
`X_R = R^2 - 1`, with the post-root cutoff built into the interval. -/
def pntReciprocalLayerPrimes (R d : ℕ) : Finset ℕ :=
  (primeSieveReciprocalInterval R (squareRootEndpoint R) d).filter Nat.Prime

/-- Honest natural cardinality `L_R(d)` of one reciprocal prime layer. -/
def pntReciprocalLayerPrimeCount (R d : ℕ) : ℕ :=
  (pntReciprocalLayerPrimes R d).card

@[simp] theorem pntReciprocalLayerPrimeCount_eq_squareRoot
    (R d : ℕ) :
    pntReciprocalLayerPrimeCount R d =
      squareRootReciprocalPrimeLayerCard R d := by
  rfl

/-- The already-proved native PNT gives the exact fixed-depth arrival density
for `L_R(d)`. -/
theorem pntReciprocalLayerPrimeCount_mul_log_div_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun R : ℕ =>
        (pntReciprocalLayerPrimeCount R d : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop
      (𝓝 ((1 : ℝ) / (d : ℝ) -
        (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) := by
  simpa [pntReciprocalLayerPrimeCount] using
    squareRootReciprocalPrimeLayerCard_mul_log_div_tendsto d hd

/-- Raw unsigned seat exposure in one reciprocal layer. -/
def pntRawCancellationExposureLayer (R d : ℕ) : ℝ :=
  ((d - 1 : ℕ) : ℝ) * (pntReciprocalLayerPrimeCount R d : ℝ)

/-- Full raw unsigned seat exposure through all reciprocal depths below `R`. -/
def pntRawCancellationExposure (R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 R, pntRawCancellationExposureLayer R d

/-- Fixed-depth PNT density with the literal seat multiplicity attached. -/
theorem pntRawCancellationExposureLayer_mul_log_div_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun R : ℕ =>
        pntRawCancellationExposureLayer R d *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop
      (𝓝 (((d - 1 : ℕ) : ℝ) *
        ((1 : ℝ) / (d : ℝ) -
          (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
  have h := (tendsto_const_nhds :
      Tendsto (fun _R : ℕ => ((d - 1 : ℕ) : ℝ)) atTop
        (𝓝 (((d - 1 : ℕ) : ℝ)))).mul
    (pntReciprocalLayerPrimeCount_mul_log_div_tendsto d hd)
  simpa [pntRawCancellationExposureLayer, mul_assoc] using h

/-- Fixed finite-depth raw exposure.  Keeping `K` fixed is the regime in which
pointwise reciprocal-layer PNT limits may be summed directly. -/
def pntRawCancellationExposureThrough (R K : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 K, pntRawCancellationExposureLayer R d

/-- PNT density for every fixed finite raw-exposure packet.  No claim is made
here about the moving-depth sum `K = R-1`; that requires a uniform estimate. -/
theorem pntRawCancellationExposureThrough_mul_log_div_tendsto
    (K : ℕ) :
    Tendsto
      (fun R : ℕ =>
        pntRawCancellationExposureThrough R K *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop
      (𝓝 (∑ d ∈ Finset.Icc 1 K,
        ((d - 1 : ℕ) : ℝ) *
          ((1 : ℝ) / (d : ℝ) -
            (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
  have hsum :
      Tendsto
        (fun R : ℕ => ∑ d ∈ Finset.Icc 1 K,
          pntRawCancellationExposureLayer R d *
            Real.log (squareRootEndpoint R : ℝ) /
              (squareRootEndpoint R : ℝ))
        atTop
        (𝓝 (∑ d ∈ Finset.Icc 1 K,
          ((d - 1 : ℕ) : ℝ) *
            ((1 : ℝ) / (d : ℝ) -
              (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
    apply tendsto_finset_sum
    intro d hdMem
    have hd : 0 < d := (Finset.mem_Icc.mp hdMem).1
    exact pntRawCancellationExposureLayer_mul_log_div_tendsto d hd
  refine hsum.congr' ?_
  filter_upwards with R
  unfold pntRawCancellationExposureThrough
  rw [Finset.sum_mul]
  ring

/-- Signed first-jump residual attached to one post-root prime `q`.

This is not a generic remaining-seat count.  It is the exact residual left by
the compiled predecessor-dense square-root contraction of the predecessor cube
through `q-1`, at the actual reciprocal cutoff `floor(X_R/q)`. -/
def pntCancellationDebtForPrime (R q : ℕ) : ℤ :=
  predecessorFirstJumpFrozenWindowMass
    3 (Nat.sqrt R) (primesUpTo (q - 1))
    0 (squareRootEndpoint R / q)

/-- The per-prime debt is exactly the remainder in the existing signed
square-root contraction identity. -/
theorem pntPredecessorWindow_eq_sqrtContraction_add_debt
    (R q : ℕ)
    (hqroot : Nat.sqrt R < q)
    (hcut : squareRootEndpoint R / q ≤ R) :
    frozenPrimeUniverseWindowMass (primesUpTo (q - 1))
        0 (squareRootEndpoint R / q) =
      frozenPrimeUniverseWindowMass (primesUpTo (Nat.sqrt R))
        0 (squareRootEndpoint R / q) +
      pntCancellationDebtForPrime R q := by
  simpa [pntCancellationDebtForPrime] using
    frozenPrimeUniverseWindowMass_eq_sqrtContraction_add_firstJump
      R q 0 (squareRootEndpoint R / q) hqroot hcut

/-- Signed live debt of reciprocal layer `d`.  The prime contributions are
summed before any absolute value, preserving nonlocal cancellation inside the
layer. -/
def pntCancellationDebtLayerMass (R d : ℕ) : ℤ :=
  ∑ q ∈ pntReciprocalLayerPrimes R d,
    pntCancellationDebtForPrime R q

/-- Nonnegative live debt in one reciprocal layer, after signed aggregation. -/
def pntCancellationDebt (R d : ℕ) : ℝ :=
  |((pntCancellationDebtLayerMass R d : ℤ) : ℝ)|

/-- Total live first-jump cancellation debt below the square-root depth. -/
def pntTotalCancellationDebt (R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 R, pntCancellationDebt R d

/-- The proposed root-scale target: after all completed predecessor cubes have
been contracted, the total first-failure boundary is at most `R log R` up to a
constant. -/
def PNTCancellationDebtPolylogBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      pntTotalCancellationDebt R ≤
        C * (R : ℝ) * (Real.log (R : ℝ) + 1)

/-- Sharper candidate if the nested first-jump telescope ultimately removes the
logarithmic overlap completely. -/
def PNTCancellationDebtLinearBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      pntTotalCancellationDebt R ≤ C * (R : ℝ)

/-- Linear live-debt control would immediately imply the polylog target. -/
theorem pntCancellationDebtPolylogBounded_of_linear
    (h : PNTCancellationDebtLinearBoundedStatement) :
    PNTCancellationDebtPolylogBoundedStatement := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro R hR
  have hlog0 : 0 ≤ Real.log (R : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ R by omega))
  have hfactor : (1 : ℝ) ≤ Real.log (R : ℝ) + 1 := by linarith
  have hCR : 0 ≤ C * (R : ℝ) := by positivity
  calc
    pntTotalCancellationDebt R ≤ C * (R : ℝ) := hbound R hR
    _ ≤ (C * (R : ℝ)) * (Real.log (R : ℝ) + 1) := by
      exact le_mul_of_one_le_right hCR hfactor
    _ = C * (R : ℝ) * (Real.log (R : ℝ) + 1) := by ring

end RHLean.Proof
