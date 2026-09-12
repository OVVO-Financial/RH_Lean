import Mathlib
import RHLean.Proof.StableFarWallOwnedCensus
import RHLean.Proof.CanonicalGapAncestryBridge

/-!
# Strict far-wall crossings renew only once

A strict `q^2` crossing on the far wall has already stripped the largest prime
`q` from a nonunit low cofactor `q*d`.  The returned stable-wall state is
`(d,p)`, with every prime factor of `d` strictly below `q` and with

`q*d*p <= X_R < q^2*d*p`.

If `d = 1`, the return is terminal.  If `d > 1`, strip its own largest prime
`r = P^+(d)` and write `d = r*e`.  Since `r < q`, the original pre-crossing
inequality immediately gives

`r^2*e*p = r*d*p < q*d*p <= X_R`.

Thus the returned nonunit state is automatically in the *descended* half at
its next canonical owner.  It cannot cross a second time.  The same
factorization also shows that its stable-wall weight is the negative of the
next child-far weight.  These are exact signed statements; no norm or estimate
is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- **Depth-one renewal.**  A nonunit strict crossing, after forgetting its
outer owner, is automatically descended at the returned cofactor's own
canonical largest-prime owner. -/
theorem lowWheelFarPrimeQ2Crossing_returned_nonUnit_descends
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (hd : 1 < d) :
    (canonicalLargestPrimeFactor d, (canonicalCofactor d, p)) ∈
      lowWheelFarPrimeQ2DescendedTriples R := by
  have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp ht).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
    ⟨hqPrime, hqR, _hd1, hpPrime, hpR, hdsq, hdq, hcut⟩
  let r := canonicalLargestPrimeFactor d
  let e := canonicalCofactor d
  have hrPrime : r.Prime := by
    dsimp [r]
    exact canonicalLargestPrimeFactor_prime hd
  have he1 : 1 ≤ e := by
    dsimp [e]
    exact canonicalCofactor_pos hd
  have hesq : Squarefree e := by
    dsimp [e]
    exact squarefree_canonicalCofactor hdsq hd
  have hrq : r < q := by
    simpa [r] using hdq
  have hrR : r < R := hrq.trans hqR
  have her : canonicalLargestPrimeFactor e < r := by
    dsimp [r, e]
    exact canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hd hdsq
  have hprod : r * e = d := by
    dsimp [r, e]
    simpa [Nat.mul_comm] using canonicalCofactor_mul_largestPrimeFactor hd
  have hnextCut : r * e * p ≤ squareRootEndpoint R := by
    rw [hprod]
    have hq1 : 1 ≤ q := hqPrime.one_le
    have hle : d * p ≤ q * (d * p) := by
      simpa using Nat.mul_le_mul_right (d * p) hq1
    exact hle.trans (by simpa [Nat.mul_assoc] using hcut)
  have hnextBase :
      (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    lowWheelFarPrimeLowCofactorTriple_mem_of_data
      hrPrime hrR he1 hpPrime hpR hesq her hnextCut
  apply Finset.mem_filter.mpr
  refine ⟨hnextBase, ?_⟩
  have hrleq : r ≤ q := Nat.le_of_lt hrq
  calc
    r * r * e * p = r * (r * e) * p := by ring
    _ = r * d * p := by rw [hprod]
    _ ≤ q * d * p := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (d * p) hrleq
    _ ≤ squareRootEndpoint R := hcut

/-- The returned nonunit state therefore lands in the literal next-owner
child-far slice consumed by the q-square recursion. -/
theorem lowWheelFarPrimeQ2Crossing_returned_nonUnit_mem_nextChildFarSlice
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (hd : 1 < d) :
    (canonicalCofactor d, p) ∈
      lowWheelFarPrimeQ2ChildFarSlice R (canonicalLargestPrimeFactor d) := by
  have hdesc := lowWheelFarPrimeQ2Crossing_returned_nonUnit_descends ht hd
  have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp ht).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
    ⟨_hqPrime, hqR, _hd1, _hpPrime, _hpR, hdsq, hdq, _hcut⟩
  have hrPrime : (canonicalLargestPrimeFactor d).Prime :=
    canonicalLargestPrimeFactor_prime hd
  have hrR : canonicalLargestPrimeFactor d < R := hdq.trans hqR
  have howner :
      (canonicalLargestPrimeFactor d, (canonicalCofactor d, p)) ∈
        lowWheelFarPrimeQ2DescendedOwnerTriples R (canonicalLargestPrimeFactor d) :=
    Finset.mem_filter.mpr ⟨hdesc, rfl⟩
  have himage :
      (canonicalCofactor d, p) ∈
        (lowWheelFarPrimeQ2DescendedOwnerTriples R
          (canonicalLargestPrimeFactor d)).image Prod.snd :=
    Finset.mem_image.mpr
      ⟨(canonicalLargestPrimeFactor d, (canonicalCofactor d, p)), howner, rfl⟩
  rw [lowWheelFarPrimeQ2DescendedOwner_image_eq_childFarSlice hrPrime hrR] at himage
  exact himage

/-- A returned strict crossing has no second strict crossing at its next
canonical owner. -/
theorem lowWheelFarPrimeQ2Crossing_returned_nonUnit_not_crossing
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (hd : 1 < d) :
    (canonicalLargestPrimeFactor d, (canonicalCofactor d, p)) ∉
      lowWheelFarPrimeQ2CrossingTriples R := by
  have hdesc := lowWheelFarPrimeQ2Crossing_returned_nonUnit_descends ht hd
  intro hcross
  have hle := (Finset.mem_filter.mp hdesc).2
  have hgt := (Finset.mem_filter.mp hcross).2
  omega

/-- Every strict crossing return is therefore either the unit terminal state or
one literal next-owner child-far state. -/
theorem lowWheelFarPrimeQ2Crossing_returned_terminal_or_nextChild
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R) :
    d = 1 ∨
      (canonicalCofactor d, p) ∈
        lowWheelFarPrimeQ2ChildFarSlice R (canonicalLargestPrimeFactor d) := by
  by_cases hdone : d = 1
  · exact Or.inl hdone
  · right
    have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp ht).1
    have hd1 := (lowWheelFarPrimeLowCofactorTriple_data hbase).2.2.1
    have hdgt : 1 < d := by omega
    exact lowWheelFarPrimeQ2Crossing_returned_nonUnit_mem_nextChildFarSlice ht hdgt

/-- **Pointwise signed cancellation currency.**  On a nonunit return, the
stable-wall cofactor weight is exactly the negative of the next child-far
cofactor weight.  This is the sign relation needed to cancel one renewal copy
against one descended child copy before any energy estimate. -/
theorem lowWheelFarPrimeQ2Crossing_returnedWeight_eq_neg_nextChildWeight
    {R q d p : ℕ}
    (ht : (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (hd : 1 < d) :
    lowWheelFullTaggedPhysicalWeight ((∅ : Finset ℕ), (d, p)) =
      -canonicalMoebiusWeight (canonicalCofactor d) := by
  have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp ht).1
  have hsq := (lowWheelFarPrimeLowCofactorTriple_data hbase).2.2.2.2.2.1
  have hmu := canonicalSignedParent_moebius hsq hd
  unfold lowWheelFullTaggedPhysicalWeight canonicalMoebiusWeight
  simp only [booleanCubeSign, Finset.card_empty, pow_zero, Int.cast_one, mul_one]
  rw [hmu]
  push_cast
  ring

end RHLean.Proof
