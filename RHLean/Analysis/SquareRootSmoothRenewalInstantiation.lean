import Mathlib
import RHLean.Analysis.MertensEnergyRHForward
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

Finally, the signed smooth-minus-renewal bound is shown to be equivalent to the
repository's square-prefix Mertens energy criterion, and hence sufficient for
Mathlib's formal Riemann hypothesis through the proved Mertens-energy forward
bridge.

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

/-- Corrected version of the proposed two-copy decomposition.  The bare smooth
background acquires the full structural two-copy mismatch, not just the root
boundary. -/
theorem squarePrefixMertens_eq_smooth_sub_twoProperFiber_add_twoCopyMismatch
    (t : ℕ) (ht : 1 ≤ t) :
    squarePrefixMertens t =
      squareRootSmoothMass t -
        2 * primeWheelSquareProperFiberMass t +
        squareRootPrimeWheelTwoCopyMismatch t := by
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_eq_renewal_sub_boundary t ht,
    primeWheelSquareProperFiberMass_eq_renewal_sub_primeCount]
  unfold squareRootPrimeWheelTwoCopyMismatch
  ring

/-- Algebraic adapter for the existing doubled proper-fibre interface.  This is
noncircular, but it is deliberately not called the pure pre-T background: its
correction term itself contains the renewal. -/
def squareRootPrimeWheelDoubledInterfaceBackground (t : ℕ) : ℂ :=
  squareRootSmoothMass t + squareRootPrimeWheelTwoCopyMismatch t

/-- Exact dynamic identity required by the #387 doubled interface. -/
theorem squarePrefixMertens_eq_doubledInterfaceBackground_sub_twoProperFiber
    (t : ℕ) (ht : 1 ≤ t) :
    squarePrefixMertens t =
      squareRootPrimeWheelDoubledInterfaceBackground t -
        2 * primeWheelSquareProperFiberMass t := by
  rw [squarePrefixMertens_eq_smooth_sub_twoProperFiber_add_twoCopyMismatch t ht]
  unfold squareRootPrimeWheelDoubledInterfaceBackground
  ring

/-- The conditional centered-renewal interface is fully instantiated by the
explicit algebraic adapter.  This theorem does not identify that adapter with
the pure square-root smooth background. -/
theorem squarePrefixMertens_eq_doubledInterfaceBackground_add_centeredRenewal
    (t : ℕ) (ht : 1 ≤ t) :
    squarePrefixMertens t =
      squareRootPrimeWheelDoubledInterfaceBackground t +
        2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t := by
  exact squarePrefixMertens_eq_background_add_centeredRenewal_of_properFiber
    t (squareRootPrimeWheelDoubledInterfaceBackground t)
    (squarePrefixMertens_eq_doubledInterfaceBackground_sub_twoProperFiber t ht)

/-- Expanded centered form, keeping the two-copy obstruction visible rather
than hiding it in the adapter background. -/
theorem squarePrefixMertens_eq_smooth_add_mismatch_add_centeredRenewal
    (t : ℕ) (ht : 1 ≤ t) :
    squarePrefixMertens t =
      squareRootSmoothMass t + squareRootPrimeWheelTwoCopyMismatch t +
        2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t := by
  simpa [squareRootPrimeWheelDoubledInterfaceBackground] using
    squarePrefixMertens_eq_doubledInterfaceBackground_add_centeredRenewal t ht

/-- At the survivor threshold, the already-proved near/far decomposition now
has an explicit doubled-interface background and retains the `16*t` near error. -/
theorem exists_nearError_squarePrefixMertens_eq_doubledInterfaceBackground_add_farComb
    (t : ℕ) (ht : 55 ≤ t) :
    ∃ E : ℂ, ‖E‖ ≤ 16 * (t : ℝ) ∧
      squarePrefixMertens t =
        squareRootPrimeWheelDoubledInterfaceBackground t +
          primeWheelSquareFarCombMass t + E := by
  exact exists_nearError_squarePrefixMertens_eq_background_add_farComb
    t ht (squareRootPrimeWheelDoubledInterfaceBackground t)
    (squarePrefixMertens_eq_doubledInterfaceBackground_sub_twoProperFiber t (by omega))

/-- The same near/far result with the smooth term and normalization mismatch
shown separately. -/
theorem exists_nearError_squarePrefixMertens_eq_smooth_add_mismatch_add_farComb
    (t : ℕ) (ht : 55 ≤ t) :
    ∃ E : ℂ, ‖E‖ ≤ 16 * (t : ℝ) ∧
      squarePrefixMertens t =
        squareRootSmoothMass t + squareRootPrimeWheelTwoCopyMismatch t +
          primeWheelSquareFarCombMass t + E := by
  simpa [squareRootPrimeWheelDoubledInterfaceBackground] using
    exists_nearError_squarePrefixMertens_eq_doubledInterfaceBackground_add_farComb t ht

/-- If a future structural theorem kills the explicit normalization mismatch,
then the desired bare-smooth two-copy centered formula follows. -/
theorem squarePrefixMertens_eq_smooth_add_centeredRenewal_of_twoCopyMismatch_eq_zero
    (t : ℕ) (ht : 1 ≤ t)
    (hzero : squareRootPrimeWheelTwoCopyMismatch t = 0) :
    squarePrefixMertens t =
      squareRootSmoothMass t +
        2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t := by
  have h := squarePrefixMertens_eq_smooth_add_mismatch_add_centeredRenewal t ht
  simpa [hzero] using h

/-- In fact, the desired bare-smooth two-copy centered identity is equivalent
to vanishing of the exact normalization mismatch. -/
theorem squarePrefixMertens_eq_smooth_add_centeredRenewal_iff_twoCopyMismatch_eq_zero
    (t : ℕ) (ht : 1 ≤ t) :
    (squarePrefixMertens t =
      squareRootSmoothMass t +
        2 * primeWheelSquarePrimeCountMass t -
        2 * primeWheelSquareRenewal t) ↔
      squareRootPrimeWheelTwoCopyMismatch t = 0 := by
  have hexact := squarePrefixMertens_eq_smooth_add_mismatch_add_centeredRenewal t ht
  constructor
  · intro hpure
    have hsame :
        squareRootSmoothMass t + squareRootPrimeWheelTwoCopyMismatch t +
            2 * primeWheelSquarePrimeCountMass t -
            2 * primeWheelSquareRenewal t =
          squareRootSmoothMass t +
            2 * primeWheelSquarePrimeCountMass t -
            2 * primeWheelSquareRenewal t :=
      hexact.symm.trans hpure
    linear_combination hsame
  · intro hzero
    simpa [hzero] using hexact

/-- The remaining square-root analytic target exposed by the exact bridge:
signed cancellation between the complete smooth square-kill background and the
lower-scale Mertens renewal.  The root boundary is already controlled above. -/
def SquareRootSmoothRenewalCancellationBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t →
        ‖squareRootSmoothMass t - primeWheelSquareRenewal t‖ ^ 2 ≤
          C * Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε)

private theorem norm_sq_add_le_two_local (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- The explicit boundary remains below the same critical square-prefix power
used by the signed cancellation statement. -/
private theorem norm_squareRootRenewalBoundary_sq_le_rpow
    (t : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ‖squareRootRenewalBoundary t‖ ^ 2 ≤
      Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε) := by
  have hb := norm_squareRootRenewalBoundary_le_root t
  have hbSq :
      ‖squareRootRenewalBoundary t‖ ^ 2 ≤ (t : ℝ) ^ 2 := by
    have hnorm : 0 ≤ ‖squareRootRenewalBoundary t‖ := norm_nonneg _
    have ht : 0 ≤ (t : ℝ) := by positivity
    nlinarith
  have hnat : t ^ 2 ≤ (t + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_succ t) 2
  have hsq :
      (t : ℝ) ^ 2 ≤ ((t + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hnat
  have hbase : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le t))
  have hexp : (2 : ℝ) ≤ 2 + ε := by linarith
  have hrpow :
      Real.rpow ((t + 1 : ℕ) : ℝ) (2 : ℝ) ≤
        Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  calc
    ‖squareRootRenewalBoundary t‖ ^ 2 ≤ (t : ℝ) ^ 2 := hbSq
    _ ≤ ((t + 1 : ℕ) : ℝ) ^ 2 := hsq
    _ = Real.rpow ((t + 1 : ℕ) : ℝ) (2 : ℝ) := by
      symm
      exact Real.rpow_natCast ((t + 1 : ℕ) : ℝ) 2
    _ ≤ Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε) := hrpow

/-- The signed smooth-minus-renewal estimate implies the repository's exact
square-prefix Mertens energy criterion.  The only loss is a harmless constant
from adding the root-scale boundary. -/
theorem squarePrefixEnergyBounded_of_smoothRenewalCancellation
    (hcancel : SquareRootSmoothRenewalCancellationBoundedStatement) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases hcancel ε hε with ⟨C, hC, hbound⟩
  have hC' : 0 ≤ 2 * C + 2 := by nlinarith
  refine ⟨2 * C + 2, hC', ?_⟩
  intro t
  by_cases ht0 : t = 0
  · subst t
    simpa [squarePrefixMertens, squarePrefixEndpoint] using hC'
  · have ht : 1 ≤ t := Nat.pos_of_ne_zero ht0
    have hD := hbound t ht
    have hB := norm_squareRootRenewalBoundary_sq_le_rpow t ε hε
    have hdecomp := squarePrefixMertens_eq_smooth_sub_renewal_add_boundary t ht
    calc
      ‖squarePrefixMertens t‖ ^ 2 =
          ‖(squareRootSmoothMass t - primeWheelSquareRenewal t) +
            squareRootRenewalBoundary t‖ ^ 2 := by rw [hdecomp]
      _ ≤ 2 * ‖squareRootSmoothMass t - primeWheelSquareRenewal t‖ ^ 2 +
            2 * ‖squareRootRenewalBoundary t‖ ^ 2 :=
        norm_sq_add_le_two_local _ _
      _ ≤ 2 * (C * Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε)) +
            2 * Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hD (by norm_num))
          (mul_le_mul_of_nonneg_left hB (by norm_num))
      _ = (2 * C + 2) * Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε) := by ring

/-- Conversely, square-prefix Mertens energy control bounds the same signed
smooth-minus-renewal object, because their difference is only the root-scale
boundary. -/
theorem smoothRenewalCancellation_of_squarePrefixEnergyBounded
    (hprefix : SquarePrefixEnergyBoundedStatement) :
    SquareRootSmoothRenewalCancellationBoundedStatement := by
  intro ε hε
  rcases hprefix ε hε with ⟨C, hC, hbound⟩
  have hC' : 0 ≤ 2 * C + 2 := by nlinarith
  refine ⟨2 * C + 2, hC', ?_⟩
  intro t ht
  have hM := hbound t
  have hB := norm_squareRootRenewalBoundary_sq_le_rpow t ε hε
  have hdecomp := squarePrefixMertens_eq_smooth_sub_renewal_add_boundary t ht
  have hrewrite :
      squareRootSmoothMass t - primeWheelSquareRenewal t =
        squarePrefixMertens t - squareRootRenewalBoundary t := by
    rw [hdecomp]
    ring
  calc
    ‖squareRootSmoothMass t - primeWheelSquareRenewal t‖ ^ 2 =
        ‖squarePrefixMertens t + (-squareRootRenewalBoundary t)‖ ^ 2 := by
      rw [hrewrite, sub_eq_add_neg]
    _ ≤ 2 * ‖squarePrefixMertens t‖ ^ 2 +
          2 * ‖-squareRootRenewalBoundary t‖ ^ 2 :=
      norm_sq_add_le_two_local _ _
    _ = 2 * ‖squarePrefixMertens t‖ ^ 2 +
          2 * ‖squareRootRenewalBoundary t‖ ^ 2 := by rw [norm_neg]
    _ ≤ 2 * (C * Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε)) +
          2 * Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hM (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))
    _ = (2 * C + 2) * Real.rpow ((t + 1 : ℕ) : ℝ) (2 + ε) := by ring

/-- The proposed signed cancellation is exactly the square-prefix critical
energy criterion, modulo the already-controlled root boundary. -/
theorem smoothRenewalCancellation_iff_squarePrefixEnergyBounded :
    SquareRootSmoothRenewalCancellationBoundedStatement ↔
      SquarePrefixEnergyBoundedStatement := by
  exact ⟨squarePrefixEnergyBounded_of_smoothRenewalCancellation,
    smoothRenewalCancellation_of_squarePrefixEnergyBounded⟩

/-- Via the existing square-sampling bridge, the same signed cancellation is
also equivalent to the full Mertens energy criterion. -/
theorem smoothRenewalCancellation_iff_mertensEnergyBounded :
    SquareRootSmoothRenewalCancellationBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  constructor
  · intro hcancel
    exact mertensEnergyBounded_of_squarePrefixEnergyBounded
      (squarePrefixEnergyBounded_of_smoothRenewalCancellation hcancel)
  · intro hM
    exact smoothRenewalCancellation_of_squarePrefixEnergyBounded
      (squarePrefixEnergyBounded_of_mertensEnergyBounded hM)

/-- **Terminal analytic reduction.**  Proving the signed smooth-minus-renewal
bound is sufficient for Mathlib's formal Riemann hypothesis, using the
repository's proved Mertens-energy continuation and functional-equation bridge. -/
theorem riemannHypothesis_of_smoothRenewalCancellation
    (hcancel : SquareRootSmoothRenewalCancellationBoundedStatement) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_mertensEnergy
    (smoothRenewalCancellation_iff_mertensEnergyBounded.mp hcancel)

end RHLean.Proof