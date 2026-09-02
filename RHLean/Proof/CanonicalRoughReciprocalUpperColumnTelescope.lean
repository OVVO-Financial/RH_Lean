import Mathlib
import RHLean.Proof.CanonicalRoughTruncatedWheelManyPrimeTelescope

/-!
# Reciprocal upper-column telescope for final truncated-wheel boundaries

The many-prime transport theorem collapses every fixed-partner physical defect
ledger to one final truncated-wheel boundary

`T_P(N) - E_P`,

where `E_P = prod_{p in P} (1 - 1/p)`.  The remaining first-owner-style move
is to sum those partner columns before taking any norm.

For the chronological prime-prefix schedule, the exact weighted aggregate is

```text
sum_{q <= K, q prime} (1/q) * (T_{q^-}(X/q) - E_{q^-})
  = E_{<=K} - T_{<=K}(X).
```

Thus the complete signed partner aggregate is itself the negative of one final
truncated-wheel boundary.  This is the reciprocal analogue of the existing
integer upper-column telescope, proved directly from the same prime-by-prime
Euler recurrence and with no estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Composite successor cutoffs do not change the prime prefix. -/
theorem primesUpTo_succ_eq_of_not_prime_reciprocal
    (n : ℕ) (hnot : ¬ (n + 1).Prime) :
    primesUpTo (n + 1) = primesUpTo n := by
  ext q
  simp only [mem_primesUpTo]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    refine ⟨hqPrime, ?_⟩
    have hqne : q ≠ n + 1 := by
      intro hEq
      subst q
      exact hnot hqPrime
    omega
  · rintro ⟨hqPrime, hqle⟩
    exact ⟨hqPrime, by omega⟩

/-- **Reciprocal upper-column telescope.**

Each partner prime contributes its final truncated-wheel boundary with the
native reciprocal owner weight `1/q`.  Summing over a complete prime prefix
cancels both the moving truncated profile and the matching uniform Euler
contraction, leaving exactly the negative final boundary. -/
theorem primorialTruncatedBoundary_upperColumn_telescope
    (X K : ℕ) (hX : 1 ≤ X) :
    (∑ q ∈ primesUpTo K,
      (1 / (q : ℝ)) *
        (primorialTruncatedSignedReciprocalCube
            (primesUpTo (q - 1)) (X / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialSignedContractionFactor (primesUpTo K) -
        primorialTruncatedSignedReciprocalCube (primesUpTo K) X := by
  induction K with
  | zero =>
      have hzero : primesUpTo 0 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        have hdata := mem_primesUpTo.mp hq
        have htwo := hdata.1.two_le
        omega
      rw [hzero]
      simp [primorialSignedContractionFactor,
        primorialTruncatedSignedReciprocalCube_empty X hX]
  | succ K ih =>
      by_cases hq : (K + 1).Prime
      · have hnotMem : K + 1 ∉ primesUpTo K := by
          simp
        have hpred : K + 1 - 1 = K := by omega
        have hset :
            primesUpTo (K + 1) = insert (K + 1) (primesUpTo K) := by
          simpa [hpred] using insert_freshPrime_primesUpTo_pred_eq hq
        have htrunc :=
          primorialTruncatedSignedReciprocalCube_insert
            (P := primesUpTo K) (p := K + 1) (X := X) hnotMem hq
        have hfactor :
            primorialSignedContractionFactor (primesUpTo (K + 1)) =
              (1 - 1 / ((K + 1 : ℕ) : ℝ)) *
                primorialSignedContractionFactor (primesUpTo K) := by
          rw [hset]
          unfold primorialSignedContractionFactor
          rw [Finset.prod_insert hnotMem]
        calc
          (∑ q ∈ primesUpTo (K + 1),
              (1 / (q : ℝ)) *
                (primorialTruncatedSignedReciprocalCube
                    (primesUpTo (q - 1)) (X / q) -
                  primorialSignedContractionFactor
                    (primesUpTo (q - 1)))) =
            (1 / ((K + 1 : ℕ) : ℝ)) *
                (primorialTruncatedSignedReciprocalCube
                    (primesUpTo K) (X / (K + 1)) -
                  primorialSignedContractionFactor (primesUpTo K)) +
              ∑ q ∈ primesUpTo K,
                (1 / (q : ℝ)) *
                  (primorialTruncatedSignedReciprocalCube
                      (primesUpTo (q - 1)) (X / q) -
                    primorialSignedContractionFactor
                      (primesUpTo (q - 1))) := by
                rw [hset, Finset.sum_insert hnotMem, hpred]
          _ =
            (1 / ((K + 1 : ℕ) : ℝ)) *
                (primorialTruncatedSignedReciprocalCube
                    (primesUpTo K) (X / (K + 1)) -
                  primorialSignedContractionFactor (primesUpTo K)) +
              (primorialSignedContractionFactor (primesUpTo K) -
                primorialTruncatedSignedReciprocalCube
                  (primesUpTo K) X) := by rw [ih]
          _ = primorialSignedContractionFactor (primesUpTo (K + 1)) -
                primorialTruncatedSignedReciprocalCube
                  (primesUpTo (K + 1)) X := by
              rw [hfactor, hset, htrunc]
              ring
      · have hset := primesUpTo_succ_eq_of_not_prime_reciprocal K hq
        rw [hset, ih]

/-- The same identity in boundary-sign orientation. -/
theorem primorialTruncatedBoundary_upperColumn_telescope_boundary
    (X K : ℕ) (hX : 1 ≤ X) :
    (∑ q ∈ primesUpTo K,
      (1 / (q : ℝ)) *
        (primorialTruncatedSignedReciprocalCube
            (primesUpTo (q - 1)) (X / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      -(primorialTruncatedSignedReciprocalCube (primesUpTo K) X -
          primorialSignedContractionFactor (primesUpTo K)) := by
  rw [primorialTruncatedBoundary_upperColumn_telescope X K hX]
  ring

end RHLean.Proof
