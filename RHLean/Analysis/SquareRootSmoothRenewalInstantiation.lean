import Mathlib
import RHLean.Analysis.PrimeWheelNearFarRenewalSquareEndpoint

/-!
# Square-root smooth / prime-wheel renewal instantiation

This module connects the original exact square-root decomposition

`M(X_t) = squareRootSmoothMass t - squareRootTransportMass t`

at `X_t = (t+1)^2-1` to the prime-wheel renewal coordinates of
`PrimeWheelNearFarRenewalSquareEndpoint`.

The key normalization fact is exact and structural: the original square-root
transport is one copy of the strict upper-prime Mertens transform.  Consequently
it is the full renewal `R_t` with only the possible boundary prime `t+1`
removed.  It is not, in general, the doubled proper-multiple mass
`2 * properFiberMass`.

We therefore record both:

* the literal canonical square-root identity
  `M(X_t) = smooth_t - R_t + boundary_t`; and
* the exact two-copy normalization mismatch needed to feed the existing
  doubled proper-fibre interface.

No PNT term, `Li` term, or separate absolute bound on `R_t` is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The square endpoint divided by its root coordinate is exactly the previous
integer: `floor(((t+1)^2-1)/(t+1)) = t`. -/
theorem squarePrefixEndpoint_div_succ_eq_root (t : ℕ) :
    squarePrefixEndpoint t / (t + 1) = t := by
  apply Nat.le_antisymm
  · exact squarePrefixEndpoint_div_le_root (by omega)
  · have hden : 0 < t + 1 := by omega
    apply (Nat.le_div_iff_mul_le hden).2
    have hsq : t * (t + 1) + 1 ≤ (t + 1) ^ 2 := by
      nlinarith [Nat.zero_le t]
    have hend := squarePrefixEndpoint_add_one t
    omega

/-- The only prime coordinate present in `(t,X_t]` but absent from the original
strict square-root transport range `(t+1,X_t]`. -/
def squareRootRenewalBoundary (t : ℕ) : ℂ :=
  if (t + 1).Prime then mertensSummatory t else 0

private theorem succ_le_squarePrefixEndpoint
    {t : ℕ} (ht : 1 ≤ t) :
    t + 1 ≤ squarePrefixEndpoint t := by
  have hsq : t + 2 ≤ (t + 1) ^ 2 := by
    nlinarith
  have hend := squarePrefixEndpoint_add_one t
  omega

/-- The full renewal is the possible `p=t+1` boundary fibre plus the strict
renewal used by the original square-root transport. -/
theorem primeWheelSquareRenewal_eq_boundary_add_strictRenewal
    (t : ℕ) (ht : 1 ≤ t) :
    primeWheelSquareRenewal t =
      squareRootRenewalBoundary t +
        ∑ p ∈ Finset.Ioc (t + 1) (squarePrefixEndpoint t),
          if p.Prime then mertensSummatory (squarePrefixEndpoint t / p) else 0 := by
  classical
  have hX : t + 1 ≤ squarePrefixEndpoint t := succ_le_squarePrefixEndpoint ht
  have hset :
      Finset.Ioc t (squarePrefixEndpoint t) =
        insert (t + 1) (Finset.Ioc (t + 1) (squarePrefixEndpoint t)) := by
    ext p
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    constructor
    · intro hp
      by_cases hpeq : p = t + 1
      · exact Or.inl hpeq
      · right
        constructor
        · omega
        · exact hp.2
    · rintro (hpeq | hp)
      · subst p
        exact ⟨by omega, hX⟩
      · exact ⟨by omega, hp.2⟩
  unfold primeWheelSquareRenewal squareRootRenewalBoundary
  rw [hset, Finset.sum_insert]
  · rw [squarePrefixEndpoint_div_succ_eq_root]
  · simp

/-- The original dynamic transport at square index `t` is literally the
prime-first transport at root cutoff `t+1`. -/
theorem squareRootTransportMass_eq_primeFirst_succ (t : ℕ) :
    squareRootTransportMass t = squareRootTransportPrimeFirst (t + 1) := by
  have hR : 1 ≤ t + 1 := by omega
  have h := squareRootTransportMass_pred_eq_cofactorFirst (t + 1) hR
  have hpred : t + 1 - 1 = t := by omega
  rw [hpred] at h
  calc
    squareRootTransportMass t = squareRootTransportCofactorFirst (t + 1) := h
    _ = squareRootTransportPrimeFirst (t + 1) :=
      squareRootTransportCofactorFirst_eq_primeFirst (t + 1)

/-- The original square-root transport is the strict-`t+1` renewal. -/
theorem squareRootTransportMass_eq_strictRenewal (t : ℕ) :
    squareRootTransportMass t =
      ∑ p ∈ Finset.Ioc (t + 1) (squarePrefixEndpoint t),
        if p.Prime then mertensSummatory (squarePrefixEndpoint t / p) else 0 := by
  rw [squareRootTransportMass_eq_primeFirst_succ,
    squareRootTransportPrimeFirst_succ_eq_strictRenewal]

/-- Exact boundary bridge from the original square-root transport to the full
prime-wheel renewal. -/
theorem squareRootTransportMass_eq_renewal_sub_boundary
    (t : ℕ) (ht : 1 ≤ t) :
    squareRootTransportMass t =
      primeWheelSquareRenewal t - squareRootRenewalBoundary t := by
  have hstrict := squareRootTransportMass_eq_strictRenewal t
  have hsplit := primeWheelSquareRenewal_eq_boundary_add_strictRenewal t ht
  calc
    squareRootTransportMass t =
        ∑ p ∈ Finset.Ioc (t + 1) (squarePrefixEndpoint t),
          if p.Prime then mertensSummatory (squarePrefixEndpoint t / p) else 0 := hstrict
    _ = primeWheelSquareRenewal t - squareRootRenewalBoundary t := by
      rw [hsplit]
      ring

/-- The literal canonical square-root instantiation: smooth background minus
one full renewal, with only the possible `p=t+1` boundary restored. -/
theorem squarePrefixMertens_eq_smooth_sub_renewal_add_boundary
    (t : ℕ) (ht : 1 ≤ t) :
    squarePrefixMertens t =
      squareRootSmoothMass t - primeWheelSquareRenewal t +
        squareRootRenewalBoundary t := by
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_eq_renewal_sub_boundary t ht]
  ring

/-- The root boundary itself is root-scale. -/
theorem norm_squareRootRenewalBoundary_le_root (t : ℕ) :
    ‖squareRootRenewalBoundary t‖ ≤ (t : ℝ) := by
  have hM := norm_mertensSummatory_sub_le 0 t (Nat.zero_le t)
  have hMt : ‖mertensSummatory t‖ ≤ (t : ℝ) := by
    simpa using hM
  by_cases hp : (t + 1).Prime
  · simpa [squareRootRenewalBoundary, hp] using hMt
  · simp [squareRootRenewalBoundary, hp]

/-- The exact obstruction to identifying the original one-copy square-root
transport with the doubled proper-multiple prime-wheel mass.  This is an
explicit signed structural term, not a boundary estimate. -/
def squareRootPrimeWheelTwoCopyMismatch (t : ℕ) : ℂ :=
  primeWheelSquareRenewal t -
    2 * primeWheelSquarePrimeCountMass t +
    squareRootRenewalBoundary t

/-- The two-copy mismatch is exactly `2*properFiberMass - transport`. -/
theorem two_properFiberMass_sub_transport_eq_twoCopyMismatch
    (t : ℕ) (ht : 1 ≤ t) :
    2 * primeWheelSquareProperFiberMass t - squareRootTransportMass t =
      squareRootPrimeWheelTwoCopyMismatch t := by
  rw [primeWheelSquareProperFiberMass_eq_renewal_sub_primeCount,
    squareRootTransportMass_eq_renewal_sub_boundary t ht]
  unfold squareRootPrimeWheelTwoCopyMismatch
  ring

/-- Equivalent form showing that the mismatch contains a full proper-fibre
component and therefore cannot be treated as merely the `p=t+1` boundary. -/
theorem twoCopyMismatch_eq_properFiber_sub_primeCount_add_boundary
    (t : ℕ) :
    squareRootPrimeWheelTwoCopyMismatch t =
      primeWheelSquareProperFiberMass t -
        primeWheelSquarePrimeCountMass t + squareRootRenewalBoundary t := by
  rw [primeWheelSquareProperFiberMass_eq_renewal_sub_primeCount]
  unfold squareRootPrimeWheelTwoCopyMismatch
  ring

/-- Canonical noncircular background that makes the existing doubled
proper-fibre interface exact.  It is the square-root smooth mass plus the
explicit one-copy/two-copy normalization mismatch. -/
def squareRootPrimeWheelCanonicalBackground (t : ℕ) : ℂ :=
  squareRootSmoothMass t + squareRootPrimeWheelTwoCopyMismatch t

/-- Exact dynamic identity required by the #387 interface, now instantiated
without defining the background from `M(X_t)` itself. -/
theorem squarePrefixMertens_eq_canonicalBackground_sub_twoProperFiber
    (t : ℕ) (ht : 1 ≤ t) :
    squarePrefixMertens t =
      squareRootPrimeWheelCanonicalBackground t -
        2 * primeWheelSquareProperFiberMass t := by
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_eq_renewal_sub_boundary t ht,
    primeWheelSquareProperFiberMass_eq_renewal_sub_primeCount]
  unfold squareRootPrimeWheelCanonicalBackground squareRootPrimeWheelTwoCopyMismatch
  ring

/-- The conditional centered-renewal interface is therefore fully instantiated,
but with the exact canonical background above rather than the bare smooth mass. -/
theorem squarePrefixMertens_eq_canonicalBackground_add_centeredRenewal
    (t : ℕ) (ht : 1 ≤ t) :
    squarePrefixMertens t =
      squareRootPrimeWheelCanonicalBackground t +
        2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t := by
  exact squarePrefixMertens_eq_background_add_centeredRenewal_of_properFiber
    t (squareRootPrimeWheelCanonicalBackground t)
    (squarePrefixMertens_eq_canonicalBackground_sub_twoProperFiber t ht)

/-- At the survivor threshold, the already-proved near/far decomposition now
has a genuine canonical background and retains its explicit `16*t` near error. -/
theorem exists_nearError_squarePrefixMertens_eq_canonicalBackground_add_farComb
    (t : ℕ) (ht : 55 ≤ t) :
    ∃ E : ℂ, ‖E‖ ≤ 16 * (t : ℝ) ∧
      squarePrefixMertens t =
        squareRootPrimeWheelCanonicalBackground t +
          primeWheelSquareFarCombMass t + E := by
  exact exists_nearError_squarePrefixMertens_eq_background_add_farComb
    t ht (squareRootPrimeWheelCanonicalBackground t)
    (squarePrefixMertens_eq_canonicalBackground_sub_twoProperFiber t (by omega))

/-- If a future structural theorem kills the explicit normalization mismatch,
then and only then does the desired bare-smooth two-copy centered formula follow
from this exact architecture. -/
theorem squarePrefixMertens_eq_smooth_add_centeredRenewal_of_twoCopyMismatch_eq_zero
    (t : ℕ) (ht : 1 ≤ t)
    (hzero : squareRootPrimeWheelTwoCopyMismatch t = 0) :
    squarePrefixMertens t =
      squareRootSmoothMass t +
        2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t := by
  have h := squarePrefixMertens_eq_canonicalBackground_add_centeredRenewal t ht
  simpa [squareRootPrimeWheelCanonicalBackground, hzero] using h

/-- The remaining square-root analytic target exposed by the exact bridge:
signed cancellation between the complete smooth square-kill background and the
lower-scale Mertens renewal.  The root boundary is already controlled above. -/
def SquareRootSmoothRenewalCancellationBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t →
        ‖squareRootSmoothMass t - primeWheelSquareRenewal t‖ ^ 2 ≤
          C * Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε)

end RHLean.Proof
