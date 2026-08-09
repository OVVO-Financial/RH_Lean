import Mathlib
import RHLean.Arithmetic.PrimorialWheelMinimalTorus
import RHLean.Analysis.SquareWheelNesting
import RHLean.Analysis.SquareWheelZeroModeElimination

/-!
# Centered increment of the square-wheel nonzero response

The square-wheel nonzero response is the protected quantitative object of the
prime-wheel route.  At each complete-square sample its exact zero-mode split is

```text
R_k(X_n) = H_{k,n} + rho_{k,n} R_k(U_k),
```

where `H` is `squareWheelNonzeroSampleResponse` and
`rho = (X_n-L_k)/Q_k` in the Lean normalization.

For two consecutive complete-square samples inside the same primorial block,
this file differentiates that identity exactly.  Since

```text
X_n - X_{n-1} = 2n+1,
```

the zero-mode coefficient changes by `(2n+1)/Q_k`, while the residual
difference is the canonical square-block increment.  Hence

```text
H_{k,n} - H_{k,n-1}
  = Delta_n - ((2n+1)/Q_k) * R_k(U_k).
```

The endpoint term is genuinely rank one: every square increment in the block
is multiplied by a deterministic scalar and the same single endpoint residual.
No estimate, norm, or cancellation claim is introduced here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- Consecutive square-prefix endpoints have the manuscript gap `2n+1` when
indexed as `X_n-X_{n-1}`. -/
theorem squarePrefixEndpoint_eq_pred_add_gap
    (n : ℕ) (hn : 1 ≤ n) :
    squarePrefixEndpoint n =
      squarePrefixEndpoint (n - 1) + (2 * n + 1) := by
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have h := squarePrefixEndpoint_succ_eq_add_gap (n - 1)
  rw [hpred] at h
  calc
    squarePrefixEndpoint n =
        squarePrefixEndpoint (n - 1) + (2 * (n - 1) + 3) := h
    _ = squarePrefixEndpoint (n - 1) + (2 * n + 1) := by
      congr 1
      omega

/-- Once the previous square sample lies beyond the wheel anchor, the pinned
sample length increases by exactly the square gap. -/
theorem squareWheelSampleLength_eq_pred_add_gap
    (W : PrimeWheelFiniteSystem) (n : ℕ) (hn : 1 ≤ n)
    (hlower : W.lower ≤ squarePrefixEndpoint (n - 1)) :
    squareWheelSampleLength W n =
      squareWheelSampleLength W (n - 1) + (2 * n + 1) := by
  unfold squareWheelSampleLength
  have hgap := squarePrefixEndpoint_eq_pred_add_gap n hn
  rw [hgap]
  omega

/-- Exact rank-one coefficient derivative.  The difference of two consecutive
square-wheel sample ratios is the square gap divided by the common torus
modulus. -/
theorem squareWheelSampleRatio_sub_pred_eq_gap
    (W : PrimeWheelFiniteSystem) (n : ℕ) (hn : 1 ≤ n)
    (hlower : W.lower ≤ squarePrefixEndpoint (n - 1)) :
    squareWheelSampleRatio W n - squareWheelSampleRatio W (n - 1) =
      ((W.modulus : ℂ)⁻¹) * (((2 * n + 1 : ℕ) : ℂ)) := by
  unfold squareWheelSampleRatio
  rw [squareWheelSampleLength_eq_pred_add_gap W n hn hlower]
  push_cast
  ring

/-- The deterministic endpoint-drift term in one centered square-wheel
increment.  Its only arithmetic input varying with `n` is the square gap. -/
def primorialMinimalSquareWheelEndpointDrift (k n : ℕ) : ℂ :=
  ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    (((2 * n + 1 : ℕ) : ℂ))) *
      ((((primorialMinimalWheelSystem k).residual
        (primorialBlockUpper k) : ℤ) : ℂ))

/-- The centered square-block increment that is exactly the discrete derivative
of the protected nonzero response. -/
def primorialMinimalSquareWheelCenteredIncrement (k n : ℕ) : ℂ :=
  canonicalTotalIncrement n -
    primorialMinimalSquareWheelEndpointDrift k n

/-- **Exact centered `H` increment.**  If consecutive square samples lie in one
primorial block, the difference of the Lean nonzero responses is the canonical
square-block increment minus the rank-one endpoint drift. -/
theorem primorialMinimalSquareWheelNonzeroResponse_sub_pred_eq_centeredIncrement
    (k n : ℕ) (hn : 1 ≤ n)
    (hleftLower :
      primorialBlockLower k < squarePrefixEndpoint (n - 1))
    (hleftUpper :
      squarePrefixEndpoint (n - 1) ≤ primorialBlockUpper k)
    (hrightUpper :
      squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
        squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) (n - 1) =
      primorialMinimalSquareWheelCenteredIncrement k n := by
  have hgap := squarePrefixEndpoint_eq_pred_add_gap n hn
  have hrightLower : primorialBlockLower k < squarePrefixEndpoint n := by
    rw [hgap]
    omega
  have hdelta :=
    canonicalTotalIncrement_eq_primorialResidual_sub
      k n hn hleftLower.le hleftUpper hrightLower.le hrightUpper
  have hminRight :=
    primorialMinimalWheel_residual_eq_primorialWheel_residual
      k hrightUpper
  have hminLeft :=
    primorialMinimalWheel_residual_eq_primorialWheel_residual
      k hleftUpper
  rw [← hminRight, ← hminLeft] at hdelta
  have hsampleRight :=
    primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
      (primorialMinimalWheelSystem k) n hrightLower hrightUpper
  have hsampleLeft :=
    primeWheelResidual_squareEndpoint_eq_nonzero_add_zero
      (primorialMinimalWheelSystem k) (n - 1) hleftLower hleftUpper
  have hratio :=
    squareWheelSampleRatio_sub_pred_eq_gap
      (primorialMinimalWheelSystem k) n hn hleftLower.le
  unfold primorialMinimalSquareWheelCenteredIncrement
    primorialMinimalSquareWheelEndpointDrift
  calc
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
        squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) (n - 1) =
      (((((primorialMinimalWheelSystem k).residual
            (squarePrefixEndpoint n) : ℤ) : ℂ)) -
        ((((primorialMinimalWheelSystem k).residual
            (squarePrefixEndpoint (n - 1)) : ℤ) : ℂ))) -
        (squareWheelSampleRatio (primorialMinimalWheelSystem k) n -
          squareWheelSampleRatio
            (primorialMinimalWheelSystem k) (n - 1)) *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ)) := by
              rw [hsampleRight, hsampleLeft]
              ring
    _ = canonicalTotalIncrement n -
        (squareWheelSampleRatio (primorialMinimalWheelSystem k) n -
          squareWheelSampleRatio
            (primorialMinimalWheelSystem k) (n - 1)) *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ)) := by
              rw [← hdelta]
    _ = canonicalTotalIncrement n -
        (((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
          (((2 * n + 1 : ℕ) : ℂ))) *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ))) := by
              rw [hratio]

/-- Explicit, abbreviation-free form of the preceding theorem. -/
theorem primorialMinimalSquareWheelNonzeroResponse_sub_pred_eq_increment_sub_drift
    (k n : ℕ) (hn : 1 ≤ n)
    (hleftLower :
      primorialBlockLower k < squarePrefixEndpoint (n - 1))
    (hleftUpper :
      squarePrefixEndpoint (n - 1) ≤ primorialBlockUpper k)
    (hrightUpper :
      squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n -
        squareWheelNonzeroSampleResponse
          (primorialMinimalWheelSystem k) (n - 1) =
      canonicalTotalIncrement n -
        ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
          (((2 * n + 1 : ℕ) : ℂ))) *
          ((((primorialMinimalWheelSystem k).residual
            (primorialBlockUpper k) : ℤ) : ℂ)) := by
  simpa [primorialMinimalSquareWheelCenteredIncrement,
    primorialMinimalSquareWheelEndpointDrift] using
      primorialMinimalSquareWheelNonzeroResponse_sub_pred_eq_centeredIncrement
        k n hn hleftLower hleftUpper hrightUpper

end RHLean.Proof
