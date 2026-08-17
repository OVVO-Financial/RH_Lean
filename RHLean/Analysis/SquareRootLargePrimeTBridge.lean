import Mathlib
import RHLean.Analysis.LargePrimeTTransport
import RHLean.Analysis.SquareRootTransportRealization

/-!
# Square-root realization bridge to large-prime T transport

The square-root transport realization already reindexes the actual high-largest-prime
population in the complete square prefix by canonical cofactor/prime pairs
`1 <= c < R < q`.

This module connects that realized arithmetic population directly to
`LargePrimeTransportData`. Consequently the generic large-prime Mobius sign-flip and
zero-preservation theorems apply to every member of the actual square-root transport
pair set, and the actual high-source mass can be rewritten through the same transport
interface.

No analytic estimate is used here. This is an exact bridge only; quantitative control
of the complementary population remains separate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Every cofactor/prime pair in the realized square-root transport population is
valid native large-prime transport data. -/
theorem squareRootTransportPair_largePrimeTransportData
    {R c q : ℕ}
    (hcq : (c, q) ∈ squareRootTransportPairSet R) :
    LargePrimeTransportData R c q := by
  rcases Finset.mem_filter.mp hcq with ⟨hbase, hdata⟩
  rcases Finset.mem_product.mp hbase with ⟨hc, hq⟩
  rcases Finset.mem_Ico.mp hc with ⟨hc1, hcR⟩
  rcases Finset.mem_Ioc.mp hq with ⟨hRq, _hqX⟩
  exact
    { c_pos := hc1
      c_lt_cutoff := hcR
      q_prime := hdata.1
      cutoff_lt_q := hRq }

/-- On every realized square-root transport pair, adjoining the large prime flips the
Mobius sign of the small cofactor. -/
theorem squareRootTransportPair_moebius_flip
    {R c q : ℕ}
    (hcq : (c, q) ∈ squareRootTransportPairSet R) :
    (μ (c * q) : ℤ) = -(μ c : ℤ) := by
  have h :=
    (squareRootTransportPair_largePrimeTransportData hcq).moebius_mul_eq_neg
  simpa [mul_comm] using h

/-- The realized square-root transport creates no new Mobius zero and removes no
inherited zero. -/
theorem squareRootTransportPair_moebius_zero_iff
    {R c q : ℕ}
    (hcq : (c, q) ∈ squareRootTransportPairSet R) :
    (μ (c * q) : ℤ) = 0 ↔ (μ c : ℤ) = 0 := by
  have h :=
    (squareRootTransportPair_largePrimeTransportData hcq).moebius_mul_eq_zero_iff
  simpa [mul_comm] using h

/-- Complex Mobius weights on a realized transport pair cancel the sign reversal:
`-mu(c*q) = mu(c)`. -/
theorem squareRootTransportPair_weight_flip
    {R c q : ℕ}
    (hcq : (c, q) ∈ squareRootTransportPairSet R) :
    -canonicalMoebiusWeight (c * q) = canonicalMoebiusWeight c := by
  have hμ := squareRootTransportPair_moebius_flip hcq
  unfold canonicalMoebiusWeight
  rw [hμ]
  simp

/-- The realized pair-source transport mass is exactly the sum of the small-cofactor
Mobius weights, proved through `LargePrimeTransportData`. -/
theorem squareRootTransportPairSourceMass_eq_largePrimeCofactorMass
    (R : ℕ) :
    squareRootTransportPairSourceMass R =
      ∑ cq ∈ squareRootTransportPairSet R, canonicalMoebiusWeight cq.1 := by
  classical
  unfold squareRootTransportPairSourceMass
  apply Finset.sum_congr rfl
  intro cq hcq
  exact squareRootTransportPair_weight_flip hcq

/-- Combining the existing exact source-to-pair reindexing with the native large-prime
transport law gives a direct bridge from the actual high-largest-prime square-prefix
population to its small cofactors. -/
theorem neg_squareRootHighTransportSourceMass_eq_largePrimeCofactorMass
    (R : ℕ) (hR : 1 ≤ R) :
    -(∑ m ∈ squareRootHighTransportSourceSet R, canonicalMoebiusWeight m) =
      ∑ cq ∈ squareRootTransportPairSet R, canonicalMoebiusWeight cq.1 := by
  calc
    -(∑ m ∈ squareRootHighTransportSourceSet R, canonicalMoebiusWeight m) =
        squareRootTransportPairSourceMass R := by
      rw [sum_squareRootHighTransportSourceSet_eq_pairProducts R hR]
      simp [squareRootTransportPairSourceMass]
    _ = ∑ cq ∈ squareRootTransportPairSet R, canonicalMoebiusWeight cq.1 :=
      squareRootTransportPairSourceMass_eq_largePrimeCofactorMass R

end RHLean.Analysis
