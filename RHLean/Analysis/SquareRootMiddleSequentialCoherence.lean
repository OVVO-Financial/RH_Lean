import Mathlib
import RHLean.Analysis.PrimeDilateCofactorPrimeWindows
import RHLean.Analysis.PrimeSieveAbelIdentity
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.PrimeCombVisualizationRecurrence

/-!
# Sequential coherence of the square-root middle section

The square-root middle section now has several exact coordinate systems in the
repository.  They are useful only if their distinct mechanisms remain visible.
This module composes the existing interfaces without replacing any of them:

* the harmonic quotient layers from `SquareRootPrimeCountGap`;
* the older reciprocal quotient fibres and prime-count/Li discrepancies from
  `PrimeSieveQuotientPNTError`;
* the Abel telescope from `PrimeSieveAbelIdentity`;
* the complete-square prime-dilate cofactor windows from
  `PrimeDilateCofactorPrimeWindows`;
* the local fresh-prime parent/child law and literal kill/flip recurrence from
  `PrimeCombVisualizationRecurrence`.

The resulting statements are all finite exact identities.  In particular:

* the `d = 2` harmonic layer is the already-existing reciprocal quotient fibre
  `(X/3,X/2]`, and its Mertens weight is exactly zero;
* the whole middle is the old reciprocal-prime-tail with only the inert `d = 1`
  top fibre removed;
* the swapped `mu(c) pi(X/c)` hyperbola exposes the exact
  `-pi(R) M(R-1)` edge, but this reindexing is not itself a contraction;
* the Abel discrepancy and the prime-dilate cofactor-window discrepancy are two
  exact coordinates of the same centered error;
* the aggregate middle/top readouts do not replace the sequential mechanism:
  a fresh prime still acts parent by parent, with first-hit and reachable-parent
  channels kept separate before any sum is taken.

The internal cofactor-prefix cancellation `mu(1)+mu(2)=0` is deliberately not
identified with the distinct source pairing `q <-> 2q`.  No interval-PNT
estimate, averaging claim, recursive square-root hierarchy, or RH-scale saving
is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

private theorem mertensSummatory_one_coherence : mertensSummatory 1 = 1 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]

/-- At the complete-square endpoint the generic quotient support ends exactly
at `R-1`:

`floor((R^2-1)/(R+1)) = R-1`.
-/
theorem squareRootQuotientSupportTop_eq_pred
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootEndpoint R / (R + 1) = R - 1 := by
  unfold squareRootEndpoint
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  have hfactor : (R - 1) * (R + 1) = R ^ 2 - 1 := by
    nlinarith
  rw [← hfactor]
  simpa using Nat.mul_div_right (R - 1) (by omega : 0 < R + 1)

/-- The harmonic tail at `j=2` is literally the middle Mertens tail from the
three-section decomposition. -/
@[simp] theorem squareRootMiddleHarmonicTail_two_eq_middle
    (R : ℕ) :
    squareRootMiddleHarmonicTail R 2 = squareRootMiddleMertensTail R := by
  rfl

/-- The new harmonic layer is not a second interval construction: it is exactly
the repository's pre-existing reciprocal quotient interval, with the prime
predicate applied. -/
theorem squareRootMiddleHarmonicLayerPrimes_eq_reciprocalInterval
    (R j : ℕ) :
    squareRootMiddleHarmonicLayerPrimes R j =
      (primeSieveReciprocalInterval R (squareRootEndpoint R) j).filter Nat.Prime := by
  classical
  ext q
  simp [squareRootMiddleHarmonicLayerPrimes,
    primeSieveReciprocalInterval, primeSieveReciprocalLower,
    primeSieveReciprocalUpper, max_lt_iff]
  omega

/-- Equivalently, for positive quotient index `j`, the harmonic layer is the
prime subset of the older literal quotient fibre `floor(X_R/q)=j`. -/
theorem squareRootMiddleHarmonicLayerPrimes_eq_quotientFiber
    (R j : ℕ) (hj : 0 < j) :
    squareRootMiddleHarmonicLayerPrimes R j =
      (primeSieveQuotientFiber R (squareRootEndpoint R) j).filter Nat.Prime := by
  rw [primeSieveQuotientFiber_eq_reciprocalInterval
    R (squareRootEndpoint R) j hj]
  exact squareRootMiddleHarmonicLayerPrimes_eq_reciprocalInterval R j

/-- The layer cardinality used by the harmonic peel is exactly the older
reciprocal-interval prime-count object. -/
theorem squareRootMiddleHarmonicLayer_card_eq_reciprocalPrimeCount
    (R j : ℕ) :
    ((squareRootMiddleHarmonicLayerPrimes R j).card : ℂ) =
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) j := by
  rw [squareRootMiddleHarmonicLayerPrimes_eq_reciprocalInterval,
    primeSieveReciprocalPrimeCount_eq_card]

/-- The one-layer peel written directly in the pre-existing quotient-fibre
language.  This is the same recurrence, not a new decomposition. -/
theorem squareRootMiddleHarmonicTail_peel_reciprocal
    (R j : ℕ) (hj : 2 ≤ j) (hjR : j < R) :
    squareRootMiddleHarmonicTail R j =
      mertensSummatory j *
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) j +
        squareRootMiddleHarmonicTail R (j + 1) := by
  rw [squareRootMiddleHarmonicTail_peel R j hj hjR,
    squareRootMiddleHarmonicLayer_card_eq_reciprocalPrimeCount]

/-- The reciprocal quotient fibre `d=1` is exactly the inert top-prime block. -/
theorem squareRootReciprocalPrimeCount_one_eq_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) 1 =
      ((squareRootTopFibrePrimes R).card : ℂ) := by
  have hpow : R ^ 2 = R * R := by ring
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 hmul
  have hinterval :
      primeSieveReciprocalInterval R (squareRootEndpoint R) 1 =
        Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R) := by
    unfold primeSieveReciprocalInterval primeSieveReciprocalLower
      primeSieveReciprocalUpper
    simp [max_eq_right hhalf]
  unfold squareRootTopFibrePrimes
  rw [primeSieveReciprocalPrimeCount_eq_card, hinterval]

/-- **The whole middle in the old quotient-fibre coordinates.**  The complete
reciprocal prime tail has quotient support `1,...,R-1`; removing the inert
`d=1` fibre leaves exactly the middle layers `2,...,R-1`.

Thus the harmonic peel from the merged middle theorem is an interface to the
older quotient-fibre machinery, not a competing hierarchy.
-/
theorem squareRootMiddleMertensTail_eq_reciprocalPrimeLayers
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      ∑ d ∈ Finset.Icc 2 (R - 1),
        primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
          mertensSummatory d := by
  classical
  have hsupport :
      squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R (by omega)
  have htransportRecip :
      squareRootTransportPrimeFirst R =
        primeSieveReciprocalPrimeTail R (squareRootEndpoint R) := by
    rw [squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)]
    rw [← primeSieveMertensPrimeTail_squareRootEndpoint R]
    exact primeSieveMertensPrimeTail_eq_reciprocalPrimeTail
      R (squareRootEndpoint R)
  unfold primeSieveReciprocalPrimeTail primeSieveQuotientSupport at htransportRecip
  rw [hsupport] at htransportRecip
  have hset :
      Finset.Icc 1 (R - 1) =
        ({1} : Finset ℕ) ∪ Finset.Icc 2 (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hdrest
    rw [Finset.mem_singleton] at hd1
    rcases Finset.mem_Icc.mp hdrest with ⟨hd2, _⟩
    omega
  rw [hset, Finset.sum_union hdisj] at htransportRecip
  simp [squareRootReciprocalPrimeCount_one_eq_topCard R hR,
    mertensSummatory_one_coherence] at htransportRecip
  have hsplit :=
    squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR
  calc
    squareRootMiddleMertensTail R =
        squareRootTransportPrimeFirst R -
          ((squareRootTopFibrePrimes R).card : ℂ) := by
      rw [hsplit]
      ring
    _ = ∑ d ∈ Finset.Icc 2 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d := by
      rw [htransportRecip]
      ring

private theorem sum_canonicalMoebiusWeight_three_to_pred_eq_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ c ∈ Finset.Icc 3 (R - 1), canonicalMoebiusWeight c) =
      mertensSummatory (R - 1) := by
  classical
  have hset :
      Finset.Icc 1 (R - 1) =
        ({1, 2} : Finset ℕ) ∪ Finset.Icc 3 (R - 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1, 2} : Finset ℕ) (Finset.Icc 3 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro c hc12 hcrest
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc12
    rcases Finset.mem_Icc.mp hcrest with ⟨hc3, _⟩
    omega
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  unfold cofactorMobiusPrefixMass
  rw [hset, Finset.sum_union hdisj]
  have h12 :
      (∑ c ∈ ({1, 2} : Finset ℕ), canonicalMoebiusWeight c) = 0 := by
    simp [canonicalMoebiusWeight,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  rw [h12, zero_add]

/-- The swapped hyperbola with the inert-style root edge made explicit:

`T_mid = sum_{3<=c<R} mu(c) pi(floor(X_R/c)) - pi(R) M(R-1)`.

This is exact bookkeeping.  The `c<R` support and the hyperbola reindexing do
not by themselves provide an analytic saving.
-/
theorem squareRootMiddleMertensTail_eq_swappedPrimeCounting_sub_rootEdge
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      (∑ c ∈ Finset.Icc 3 (R - 1),
        canonicalMoebiusWeight c *
          (Nat.primeCounting (squareRootEndpoint R / c) : ℂ)) -
        (Nat.primeCounting R : ℂ) * mertensSummatory (R - 1) := by
  rw [squareRootMiddleMertensTail_eq_swappedPrimeCounting R hR]
  have hsum := sum_canonicalMoebiusWeight_three_to_pred_eq_mertens R hR
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_mul, hsum]
  ring

/-- **Middle as the complete-square prime-dilate windows minus the inert top.**
For any fixed prime `p`, the older prime-dilate compression removes every
recursive Mertens weight from the full upper-prime transport.  Subtracting the
known `d=1` top block gives the present middle target exactly.
-/
theorem squareRootMiddleMertensTail_eq_primeDilateWindows_sub_topCard
    (p R : ℕ) (hp : p.Prime) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      squarePrimeDilateCofactorPrimeCountTransform p R -
        ((squareRootTopFibrePrimes R).card : ℂ) := by
  calc
    squareRootMiddleMertensTail R =
        squareRootTransportPrimeFirst R -
          ((squareRootTopFibrePrimes R).card : ℂ) := by
      rw [squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR]
      ring
    _ = squarePrimeDilateCofactorPrimeCountTransform p R -
          ((squareRootTopFibrePrimes R).card : ℂ) := by
      rw [squareRootTransportPrimeFirst_eq_squarePrimeDilateCofactorPrimeCountTransform
        p R hp (by omega)]

/-- **Abel and prime-dilate coherence.**  At the square endpoint, the older Abel
coordinate and the older parent/child cofactor-window coordinate are exactly
the same centered PNT error.  This is an identity between two prior interfaces,
not an estimate on either one.
-/
theorem squareRootAbelDiscrepancy_eq_primeDilateWindowDiscrepancy
    (p R : ℕ) (hp : p.Prime) (hR : 1 ≤ R) :
    primeSieveMoebiusDiscrepancySum R (squareRootEndpoint R) -
        primeSieveAbelBoundary R (squareRootEndpoint R) =
      squarePrimeDilateCofactorDiscrepancyTransform p R := by
  calc
    primeSieveMoebiusDiscrepancySum R (squareRootEndpoint R) -
        primeSieveAbelBoundary R (squareRootEndpoint R) =
      primeSievePNTError R (squareRootEndpoint R) :=
        (primeSievePNTError_eq_moebiusDiscrepancySum_sub_abelBoundary
          R (squareRootEndpoint R)).symm
    _ = squarePrimeDilateCofactorDiscrepancyTransform p R :=
      primeSievePNTError_squareRootEndpoint_eq_squarePrimeDilateCofactorDiscrepancyTransform
        p R hp (by omega)

/-! ## Sequential mechanism retained underneath the readouts -/

/-- The complete-square prime-sieve state before the upper primes act differs
from the final Mertens state by exactly twice the middle-plus-top transport.
Thus the harmonic and cofactor-window coordinates above are readouts of the
actual remaining sequential prime action. -/
theorem allPlusSquareRootPrimeCombMass_sub_mertens_eq_two_middle_add_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    allPlusSquareRootPrimeCombMass R - squarePrefixMertens (R - 1) =
      2 * (squareRootMiddleMertensTail R +
        ((squareRootTopFibrePrimes R).card : ℂ)) := by
  rw [allPlusSquareRootPrimeCombMass_sub_mertens_eq_two_transport R (by omega)]
  rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]
  rw [squareRootTransportCofactorFirst_eq_primeFirst]
  rw [squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR]

/-- Square-endpoint specialization of the local parentwise fresh-prime law.
The first-hit seat and the opposite-signed reachable parent remain separate
before any frame sum is taken. -/
theorem squareRootFreshPrimeChildContribution_eq_firstHit_sub_reachableParent
    {S t : Finset ℕ} {p R : ℕ}
    (hp : p ∉ S) (ht : t ∈ S.powerset) :
    frozenFreshPrimeChildContribution p (squareRootEndpoint R) t =
      frozenFreshPrimeFirstHitContribution p (squareRootEndpoint R) t -
        frozenFreshPrimeReachableParentContribution p (squareRootEndpoint R) t := by
  exact frozenFreshPrimeChildContribution_eq_firstHit_sub_reachableParent hp ht

/-- Square-endpoint specialization of the sequential fresh-prime state update.
This retains the old state, reachable proper-parent mass, and first-hit boundary
as three visible channels. -/
theorem squareRootFrozenPrimeUniverseMass_insert_eq_sequential_channels
    {S : Finset ℕ} {p R : ℕ} (hp : p ∉ S) :
    frozenPrimeUniverseMass (insert p S) (squareRootEndpoint R) =
      frozenPrimeUniverseMass S (squareRootEndpoint R) -
        frozenPrimeUniverseReachableProperParentMass S p (squareRootEndpoint R) +
          frozenPrimeUniverseFirstHitBoundaryMass p (squareRootEndpoint R) := by
  exact frozenPrimeUniverseMass_insert_eq_old_sub_reachableParent_add_firstHit hp

/-- The literal increasing-prime animation at the square endpoint: square
collisions delete old mass and later touches reverse old mass, producing the
factor `2` on the flip channel.  This remains the primitive step when the
harmonic layers are later accumulated. -/
theorem squareRootPrimeCombFramePrefixMass_primesUpTo_step
    (R p : ℕ) (hp : p.Prime) :
    primeCombFramePrefixMass (primesUpTo p) (squareRootEndpoint R) =
      primeCombFramePrefixMass (primesUpTo (p - 1)) (squareRootEndpoint R) -
        primeCombFrameKillChannelMass (primesUpTo (p - 1)) p
          (squareRootEndpoint R) -
          2 * primeCombFrameFlipChannelMass (primesUpTo (p - 1)) p
            (squareRootEndpoint R) := by
  exact primeCombFramePrefixMass_primesUpTo_step p (squareRootEndpoint R) hp

end RHLean.Proof
