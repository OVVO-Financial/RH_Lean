import Mathlib
import RHLean.Arithmetic.PrimorialTruncatedWheelBoundary
import RHLean.Arithmetic.PrimesUpToFrontier

/-!
# Finite Abel return in the prime coordinate

The truncated reciprocal Euler recurrence supplies a native `1/q` on the moving
`X/q` column, so the reciprocal-weighted upper column telescopes to a single
final boundary.  The literal physical fixed-`q` columns carry `mu(c)/c` and no
`1/q`, and for them the recurrence gives instead the exact unweighted law

```text
T_{q-}(X/q) - E_{q-} = q * (B_{q-}(X) - B_q(X)),
```

where `B_n(X) = T_{primesUpTo n}(X) - E_{primesUpTo n}` is the canonical
reciprocal boundary profile.  Summing over primes therefore produces a
*prime-weighted discrete variation* of the boundary, not one terminal boundary.

This file supplies the step that turns that variation back into a closed form.
The boundary profile is constant across composite cutoffs, because `primesUpTo`
does not move there, so the prime-indexed sum is really a sum over every cutoff,
and ordinary finite summation by parts gives

```text
sum_{q <= K, q prime} q * (B_{q-} - B_q) = sum_{n < K} B_n - K * B_K.
```

The architecture is therefore

```text
physical defects -> fixed-q shells -> transport telescope in p
  -> boundary profile in q -> finite Abel return in q.
```

The quantitative consequence is the point of the file.  A bound on the endpoint
`B_K(X)` alone does **not** control the physical aggregate: the Abel return also
carries the integrated profile `sum_{n < K} B_n(X)`, and the final estimate
below keeps both terms explicitly.  So the RH-critical object attached to the
physical columns is not `|T_{<=K}(X) - E_{<=K}|` on its own but the Abel
combination `sum_{n < K} B_n(X) - K * B_K(X)`.

The Abel step is proved first for an arbitrary profile that is stationary off
the primes, so it applies verbatim to any boundary family with that shape, and
is then specialized to the truncated wheel profile.  Nothing here is asymptotic.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## Abel summation against a profile that only moves at primes -/

/-- **Finite Abel transform of a discrete variation.**  For an arbitrary real
profile `B`, weighting each backward difference by its index and summing over an
initial segment returns the integrated profile minus the scaled endpoint.  No
primality is involved; this is pure summation by parts. -/
theorem sum_Icc_natCast_mul_boundaryDrop_eq_abel (B : ℕ → ℝ) (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) * (B (n - 1) - B n)) =
      (∑ n ∈ Finset.range K, B n) - (K : ℝ) * B K := by
  induction K with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0)]
      simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ K + 1), ih,
        Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- Primes below a cutoff sit inside the corresponding index segment. -/
theorem primesUpTo_subset_Icc_one (K : ℕ) : primesUpTo K ⊆ Finset.Icc 1 K := by
  intro q hq
  rcases mem_primesUpTo.mp hq with ⟨hqPrime, hqle⟩
  exact Finset.mem_Icc.mpr ⟨hqPrime.one_lt.le, hqle⟩

/-- A profile that does not move at composite cutoffs contributes nothing there,
so its prime-indexed variation is the full indexed variation. -/
theorem sum_primesUpTo_natCast_mul_boundaryDrop_eq_sum_Icc
    (B : ℕ → ℝ) (K : ℕ) (hstat : ∀ n, ¬ n.Prime → B n = B (n - 1)) :
    (∑ q ∈ primesUpTo K, (q : ℝ) * (B (q - 1) - B q)) =
      ∑ n ∈ Finset.Icc 1 K, (n : ℝ) * (B (n - 1) - B n) := by
  refine Finset.sum_subset (primesUpTo_subset_Icc_one K) ?_
  intro n hn hnot
  have hnle : n ≤ K := (Finset.mem_Icc.mp hn).2
  have hnp : ¬ n.Prime := by
    intro hp
    exact hnot (mem_primesUpTo.mpr ⟨hp, hnle⟩)
  rw [hstat n hnp]
  ring

/-- **Finite Abel return in the prime coordinate.**  For any profile stationary
off the primes, the prime-weighted discrete variation equals the integrated
profile minus the scaled endpoint. -/
theorem sum_primesUpTo_natCast_mul_boundaryDrop_eq_abel
    (B : ℕ → ℝ) (K : ℕ) (hstat : ∀ n, ¬ n.Prime → B n = B (n - 1)) :
    (∑ q ∈ primesUpTo K, (q : ℝ) * (B (q - 1) - B q)) =
      (∑ n ∈ Finset.range K, B n) - (K : ℝ) * B K := by
  rw [sum_primesUpTo_natCast_mul_boundaryDrop_eq_sum_Icc B K hstat,
    sum_Icc_natCast_mul_boundaryDrop_eq_abel B K]

/-! ## The canonical reciprocal boundary profile -/

/-- Canonical reciprocal boundary profile: the truncated signed reciprocal cube
on the prime prefix, measured against its own complete Euler contraction. -/
def primorialTruncatedWheelBoundaryProfile (X n : ℕ) : ℝ :=
  primorialTruncatedSignedReciprocalCube (primesUpTo n) X -
    primorialSignedContractionFactor (primesUpTo n)

theorem primorialTruncatedWheelBoundaryProfile_eq (X n : ℕ) :
    primorialTruncatedWheelBoundaryProfile X n =
      primorialTruncatedSignedReciprocalCube (primesUpTo n) X -
        primorialSignedContractionFactor (primesUpTo n) := rfl

/-- A composite cutoff adjoins no prime coordinate. -/
theorem primesUpTo_eq_pred_of_not_prime {n : ℕ} (hn : ¬ n.Prime) :
    primesUpTo n = primesUpTo (n - 1) := by
  ext q
  simp only [mem_primesUpTo]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    refine ⟨hqPrime, ?_⟩
    have hqne : q ≠ n := by
      rintro rfl
      exact hn hqPrime
    omega
  · rintro ⟨hqPrime, hqle⟩
    exact ⟨hqPrime, by omega⟩

/-- Hence the boundary profile is stationary off the primes. -/
theorem primorialTruncatedWheelBoundaryProfile_eq_of_not_prime
    (X : ℕ) {n : ℕ} (hn : ¬ n.Prime) :
    primorialTruncatedWheelBoundaryProfile X n =
      primorialTruncatedWheelBoundaryProfile X (n - 1) := by
  unfold primorialTruncatedWheelBoundaryProfile
  rw [primesUpTo_eq_pred_of_not_prime hn]

/-! ## The physical column aggregate in closed form -/

/-- **Abel return for the truncated wheel boundary.**  The prime-weighted
boundary drops produced by the literal unweighted physical columns sum to the
integrated boundary profile minus its scaled endpoint. -/
theorem primorialTruncatedBoundary_primeWeightedDrops_eq_abelReturn (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (q : ℝ) *
        (primorialTruncatedWheelBoundaryProfile X (q - 1) -
          primorialTruncatedWheelBoundaryProfile X q)) =
      (∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
        (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K :=
  sum_primesUpTo_natCast_mul_boundaryDrop_eq_abel
    (primorialTruncatedWheelBoundaryProfile X) K
    (fun _n hn => primorialTruncatedWheelBoundaryProfile_eq_of_not_prime X hn)

/-- The same statement with the profile written out, matching the shape in which
the unweighted-column law is stated on the truncated wheel telescope. -/
theorem primorialTruncatedBoundary_primeWeightedDrops_eq_abelReturn_unfolded
    (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (q : ℝ) *
        ((primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) X -
            primorialSignedContractionFactor (primesUpTo (q - 1))) -
          (primorialTruncatedSignedReciprocalCube (primesUpTo q) X -
            primorialSignedContractionFactor (primesUpTo q)))) =
      (∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
        (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K :=
  primorialTruncatedBoundary_primeWeightedDrops_eq_abelReturn X K

/-- **The quantitative seam.**  The Abel return carries two terms, so an
endpoint bound on `B_K` alone does not control the physical aggregate: the
integrated profile appears with full weight. -/
theorem abs_primorialTruncatedBoundaryAbelReturn_le (X K : ℕ) :
    |(∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
        (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K| ≤
      (∑ n ∈ Finset.range K, |primorialTruncatedWheelBoundaryProfile X n|) +
        (K : ℝ) * |primorialTruncatedWheelBoundaryProfile X K| := by
  have hsplit :
      |(∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n) -
          (K : ℝ) * primorialTruncatedWheelBoundaryProfile X K| ≤
        |∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n| +
          |(K : ℝ) * primorialTruncatedWheelBoundaryProfile X K| := by
    have h :=
      abs_add (∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n)
        (-((K : ℝ) * primorialTruncatedWheelBoundaryProfile X K))
    simpa [sub_eq_add_neg, abs_neg] using h
  have hsum :
      |∑ n ∈ Finset.range K, primorialTruncatedWheelBoundaryProfile X n| ≤
        ∑ n ∈ Finset.range K, |primorialTruncatedWheelBoundaryProfile X n| :=
    Finset.abs_sum_le_sum_abs _ _
  have hmul :
      |(K : ℝ) * primorialTruncatedWheelBoundaryProfile X K| =
        (K : ℝ) * |primorialTruncatedWheelBoundaryProfile X K| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg K)]
  rw [hmul] at hsplit
  linarith

end RHLean.Proof
