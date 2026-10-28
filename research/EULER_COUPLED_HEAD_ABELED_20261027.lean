import Mathlib
import «research.EULER_COUPLED_HEAD_NO_DRIFT_20261027»

/-!
# Fully coupled historical Euler Abel identity

This completes the finite **head** algebra begun in #1040: endpoint
differences cancel integer quotient-window lengths BEFORE ABSOLUTE VALUES.
The full historical smooth drift -(R+1)/b * sum M(r_(q+1)) survives and is
recoupled to the complementary historical tail via the already certified
global Mobius inversion. No claim of a fixed eta or finite-C is made.

The indexed terminal E_Q is retained EVEN WHEN I_Q IS EMPTY.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Historical Mertens value at the right endpoint of a quotient bucket. -/
def eulerHeadMertensQ (R q : ℕ) : ℚ :=
  eulerHistoricalMertensQ (eulerBucketHigh R q)

/-- Original divisor-punch coefficient at q, zero unless q divides N. -/
def eulerHeadDivisorPunchQ (R q : ℕ) : ℚ :=
  if q ∣ R - 1 then eulerMuQ ((R - 1) / q) else 0

/-- The length of one adjacent quotient window in rational coordinates. -/
def eulerHeadWindowLengthQ (R q b : ℕ) : ℚ :=
  (eulerBucketJUpper R q b : ℚ) - (eulerBucketJLower R q b : ℚ)

/-- Genuine historical Mertens values on an unbroken hyperbola interval. -/
def eulerHeadWindowMassQ (R q b : ℕ) : ℚ :=
  ∑ m ∈ Finset.Ioc (eulerBucketJLower R q b)
    (eulerBucketJUpper R q b),
    eulerHistoricalMertensQ (eulerBucketY R b / m)

/-- Actual head source after the #1038 clipped/interior split, before
the q-Abel cancellation. The delta_q punch is retained explicitly. -/
def eulerCoupledHeadPreAbelQ (R Q b : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (Q - 1),
    (eulerBucketIndexedEndpointQ R (i + 1) b *
       (eulerHeadMertensQ R (i + 1) -
        eulerHeadMertensQ R (i + 2) -
        eulerHeadDivisorPunchQ R (i + 1)) +
     eulerHeadWindowMassQ R (i + 1) b -
     eulerHeadWindowLengthQ R (i + 1) b *
       eulerHeadMertensQ R (i + 2))

/-- Abel endpoint plus the complete smooth drift and original divisor punch. -/
def eulerCoupledHeadPostAbelQ (R Q b : ℕ) : ℚ :=
  eulerBucketIndexedEndpointQ R 1 b * eulerHeadMertensQ R 1 -
  eulerBucketIndexedEndpointQ R Q b * eulerHeadMertensQ R Q +
  ∑ i ∈ Finset.range (Q - 1),
    (eulerHeadWindowMassQ R (i + 1) b -
      ((R + 1 : ℕ) : ℚ) / (b : ℚ) * eulerHeadMertensQ R (i + 2) -
      eulerBucketIndexedEndpointQ R (i + 1) b *
        eulerHeadDivisorPunchQ R (i + 1))

/-- Elementary exact telescope over adjacent quotient endpoints. -/
private theorem eulerHeadFiniteTelescope (n : ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ Finset.range n, (f (i + 1) - f (i + 2))) =
      f 1 - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Any matched endpoint difference and window length telescope exactly;
this is the algebraic heart of the genuinely coupled Abel cancellation. -/
private theorem eulerHeadAbelAlgebra
    (n : ℕ) (E M D W V : ℕ → ℚ) (d : ℚ)
    (hE : ∀ q, E (q + 1) - E q = W q - d) :
    (∑ i ∈ Finset.range n,
       (E (i + 1) *
         (M (i + 1) - M (i + 2) - D (i + 1)) +
        V (i + 1) - W (i + 1) * M (i + 2))) =
      E 1 * M 1 - E (n + 1) * M (n + 1) +
      ∑ i ∈ Finset.range n,
        (V (i + 1) - d * M (i + 2) - E (i + 1) * D (i + 1)) := by
  have hterm (i : ℕ) :
      E (i + 1) * (M (i + 1) - M (i + 2) - D (i + 1)) +
        V (i + 1) - W (i + 1) * M (i + 2) =
      (E (i + 1) * M (i + 1) - E (i + 2) * M (i + 2)) +
        (V (i + 1) - d * M (i + 2) - E (i + 1) * D (i + 1)) := by
    have hnext : E (i + 2) = E (i + 1) + W (i + 1) - d := by
      have h := hE (i + 1)
      linarith
    rw [hnext]
    ring
  calc
    _ = ∑ i ∈ Finset.range n,
          ((E (i + 1) * M (i + 1) - E (i + 2) * M (i + 2)) +
            (V (i + 1) - d * M (i + 2) -
              E (i + 1) * D (i + 1))) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hterm i
    _ = (∑ i ∈ Finset.range n,
          (E (i + 1) * M (i + 1) - E (i + 2) * M (i + 2))) +
          ∑ i ∈ Finset.range n,
            (V (i + 1) - d * M (i + 2) -
              E (i + 1) * D (i + 1)) := by
          rw [Finset.sum_add_distrib]
    _ = E 1 * M 1 - E (n + 1) * M (n + 1) +
          ∑ i ∈ Finset.range n,
            (V (i + 1) - d * M (i + 2) -
              E (i + 1) * D (i + 1)) := by
          rw [eulerHeadFiniteTelescope n (fun j => E j * M j)]

/-- The exact endpoint-plus-strict-interior Abel identity from the genuine
historical quotient buckets; full drift is retained, not prematurely bounded. -/
theorem eulerCoupled_head_interior_abel
    (R Q b : ℕ) (hQ : 1 ≤ Q) :
    eulerCoupledHeadPreAbelQ R Q b = eulerCoupledHeadPostAbelQ R Q b := by
  let E : ℕ → ℚ := fun q => eulerBucketIndexedEndpointQ R q b
  let M : ℕ → ℚ := fun q => eulerHeadMertensQ R q
  let D : ℕ → ℚ := fun q => eulerHeadDivisorPunchQ R q
  let W : ℕ → ℚ := fun q => eulerHeadWindowLengthQ R q b
  let V : ℕ → ℚ := fun q => eulerHeadWindowMassQ R q b
  let d : ℚ := ((R + 1 : ℕ) : ℚ) / (b : ℚ)
  have hE (q : ℕ) : E (q + 1) - E q = W q - d := by
    simpa [E, W, d, eulerHeadWindowLengthQ] using
      eulerEndpoint_diff_eq_window_sub R q b
  have h := eulerHeadAbelAlgebra (Q - 1) E M D W V d hE
  have hnext : Q - 1 + 1 = Q := by omega
  simpa only [eulerCoupledHeadPreAbelQ, eulerCoupledHeadPostAbelQ,
    E, M, D, W, V, d, hnext] using h

/-- The same coupled identity with the global previously-certified
Mobius no-drift compensation written as the head/complementary-tail
exchange, preserving the terminal Q-indexed endpoint. -/
theorem eulerCoupled_head_interior_abel_no_drift
    (R Q b : ℕ) (hR : 2 ≤ R) (hQ : 1 ≤ Q)
    (hQN : Q ≤ R - 1) :
    eulerCoupledHeadPreAbelQ R Q b =
      eulerBucketIndexedEndpointQ R 1 b * eulerHeadMertensQ R 1 -
      eulerBucketIndexedEndpointQ R Q b * eulerHeadMertensQ R Q +
      (∑ i ∈ Finset.range (Q - 1),
        (eulerHeadWindowMassQ R (i + 1) b -
          eulerBucketIndexedEndpointQ R (i + 1) b *
            eulerHeadDivisorPunchQ R (i + 1))) -
      (((R + 1 : ℕ) : ℚ) / (b : ℚ)) *
        (1 - eulerHistoricalMertensQ (R - 1) -
          ∑ q ∈ Finset.Ioc Q (R - 1),
            eulerHistoricalMertensQ ((R - 1) / q)) := by
  rw [eulerCoupled_head_interior_abel R Q b hQ]
  unfold eulerCoupledHeadPostAbelQ
  have hsum_aux (n : ℕ) :
      (∑ i ∈ Finset.range n, eulerHeadMertensQ R (i + 2)) =
        ∑ q ∈ Finset.Ioc 1 (n + 1),
          eulerHistoricalMertensQ ((R - 1) / q) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ,
          Finset.sum_Ioc_succ_top (by omega : 1 ≤ n + 1), ih]
        simp [eulerHeadMertensQ, eulerBucketHigh]
  have hsum :
      (∑ i ∈ Finset.range (Q - 1), eulerHeadMertensQ R (i + 2)) =
        ∑ q ∈ Finset.Ioc 1 Q,
          eulerHistoricalMertensQ ((R - 1) / q) := by
    have hQeq : Q - 1 + 1 = Q := by omega
    simpa [hQeq] using hsum_aux (Q - 1)
  have hcancel := eulerAbelSmoothDriftQ_eq_compensated R Q b hR hQ hQN
  have hlinear :
      (∑ i ∈ Finset.range (Q - 1),
       (eulerHeadWindowMassQ R (i + 1) b -
        (((R + 1 : ℕ) : ℚ) / (b : ℚ)) *
          eulerHeadMertensQ R (i + 2) -
        eulerBucketIndexedEndpointQ R (i + 1) b *
          eulerHeadDivisorPunchQ R (i + 1))) =
      (∑ i ∈ Finset.range (Q - 1),
        (eulerHeadWindowMassQ R (i + 1) b -
          eulerBucketIndexedEndpointQ R (i + 1) b *
            eulerHeadDivisorPunchQ R (i + 1))) -
      (((R + 1 : ℕ) : ℚ) / (b : ℚ)) *
        (∑ i ∈ Finset.range (Q - 1),
          eulerHeadMertensQ R (i + 2)) := by
    simp_rw [Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [hlinear, hsum]
  linear_combination hcancel

#print axioms eulerCoupled_head_interior_abel
#print axioms eulerCoupled_head_interior_abel_no_drift

end RHLean.Proof
