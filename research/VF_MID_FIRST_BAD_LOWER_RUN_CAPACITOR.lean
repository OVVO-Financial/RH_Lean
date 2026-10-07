import Mathlib
import «research.VF_MID_FINAL_RAW_CLIPPED_TELESCOPE»
import «research.VF_MID_FAN_ESCAPE_CAPACITY_BILLS»
import «research.VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE»

/-!
# VF first-bad run capacitor in exact lower-prime coordinates

This file keeps the canonical run-level route in the literal signed VF
tracking currency.

For a subdoubling run [A,B), the already-proved frozen-run owner Fubini gives

  Tracking(A,B)
    = VFMass(A,B) - FrozenPrefixSupply(A,B)
      + LowerPrimeIntervalTransport(A,B),

where

  LowerPrimeIntervalTransport(A,B)
    = sum_{A < p < B, p prime} [pi(B^2/p) - pi(p)].

Thus the capacitor variables are not new analytic objects:

  Q_parent    = Tracking(A,B),
  Q_safe      = VFMass(A,B) - FrozenPrefixSupply(A,B),
  Q_recursive = LowerPrimeIntervalTransport(A,B).

The last term is an exact multiplicity-preserving lower-scale prime transport.
Every tagged child prime occurring in it lies strictly below A^2 and has
square-root scale strictly below A.  It is also nonnegative, because it is
literally a sum of child-population cardinalities.

Therefore this coordinate is the **lower-wall / composite-vacuum capacitor**.
It transports positive VF-minus-actual pressure to lower scales.  The
upper-wall / prime-cluster direction must be handled by the complementary
prime-survivor capacity ledger; it is not represented by pretending this
nonnegative transport can become negative.

The generic capacitor window applies without any pair/Gram conversion:
if Q_recursive <= H, the deterministic/frozen part Q_safe must remain inside
the rigid window [Q_parent-H,Q_parent+H].  Any upper capacity for Q_safe which
leaves that window forces Q_recursive to be positively supercritical.

No prime-gap estimate, independence hypothesis, fantasy-cone membership, norm,
or absolute-value decomposition is introduced here.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Deterministic/frozen-prefix part of the exact dyadic VF tracking ledger. -/
def vfMidDyadicFrozenSafeMass (A B : ℕ) : ℝ :=
  vfMidDyadicVFMass A B - vfMidDyadicPrefixSupply A A B

/-- Exact lower-scale actual-prime transport left after the frozen baseline. -/
def vfMidDyadicLowerPrimeIntervalTransport (A B : ℕ) : ℝ :=
  vfMidDyadicFrozenCompositePrimeIntervalSupply A B

/-- **Exact run capacitor equality in the actual VF currency.** -/
theorem vfMidDyadicVFTrackingDefect_eq_frozenSafe_add_lowerTransport
    {A B : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicVFTrackingDefect A B =
      vfMidDyadicFrozenSafeMass A B +
        vfMidDyadicLowerPrimeIntervalTransport A B := by
  rw [vfMidDyadicVFTrackingDefect_eq_vfMass_sub_prefix_add_lowerPrimeIntervals
    hA hAB hBA]
  rfl

/-- The recursive/lower transport is literally the already-proved
owner-first endpoint-gap sum. -/
theorem vfMidDyadicLowerPrimeIntervalTransport_eq_sum_endpointGaps
    {A B : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicLowerPrimeIntervalTransport A B =
      ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        ((Nat.primeCounting (B ^ 2 / p) : ℝ) -
          (Nat.primeCounting p : ℝ)) := by
  unfold vfMidDyadicLowerPrimeIntervalTransport
  exact vfMidDyadicFrozenCompositePrimeIntervalSupply_eq_sum_endpointGaps
    (by omega : 3 ≤ A) hAB hBA

/-- **First-bad run trigger already in capacitor coordinates.**

A first bad endpoint forces the exact parent tracking charge outside the wall
increment, with no change of currency. -/
theorem vfMidActualPrimeFirstBadAt_forces_frozenSafe_lowerTransportTrigger
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 4 ≤ A) (hABlt : A < B) (hBA : B ≤ 2 * A) :
    (K * vfMidSyntheticRadialScale B -
          K * vfMidSyntheticRadialScale A <
        vfMidDyadicFrozenSafeMass A B +
          vfMidDyadicLowerPrimeIntervalTransport A B) ∨
    (vfMidDyadicFrozenSafeMass A B +
          vfMidDyadicLowerPrimeIntervalTransport A B <
        K * vfMidSyntheticRadialScale A -
          K * vfMidSyntheticRadialScale B) := by
  have htrigger :=
    vfMidActualPrimeFirstBadAt_forces_signedSeatRunTrigger
      hfirst (by omega : 3 ≤ A) hABlt hBA
  have hrun :=
    vfMidDyadicVFTrackingDefect_eq_oddRunSeatMass
      (A := A) (B := B) (by omega : 2 ≤ A) hABlt.le
  have hcap :=
    vfMidDyadicVFTrackingDefect_eq_frozenSafe_add_lowerTransport
      hA hABlt.le hBA
  rw [← hrun, hcap] at htrigger
  exact htrigger

/-- **Rigid capacitor window in exact actual-prime run coordinates.**

If the complete lower-scale transport is not supercritical, the frozen safe
part must lie within H of the exact parent tracking charge. -/
theorem vfMidDyadicFrozenSafeMass_mem_trackingWindow_of_lowerTransport_abs_le
    {A B : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    {H : ℝ}
    (hrec : |vfMidDyadicLowerPrimeIntervalTransport A B| ≤ H) :
    vfMidDyadicVFTrackingDefect A B - H ≤
        vfMidDyadicFrozenSafeMass A B ∧
      vfMidDyadicFrozenSafeMass A B ≤
        vfMidDyadicVFTrackingDefect A B + H := by
  exact vfMidSafeMass_mem_parentWindow_of_recursive_abs_le
    (vfMidDyadicVFTrackingDefect_eq_frozenSafe_add_lowerTransport
      hA hAB hBA)
    hrec

/-- Positive-side capacitor tripwire. -/
theorem vfMidDyadicLowerPrimeIntervalTransport_gt_of_frozenSafeCapacity
    {A B : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    {cap H : ℝ}
    (hsafe : vfMidDyadicFrozenSafeMass A B ≤ cap)
    (hexcess : cap + H < vfMidDyadicVFTrackingDefect A B) :
    H < vfMidDyadicLowerPrimeIntervalTransport A B := by
  exact vfMidRecursiveResidual_gt_of_safeCapacity
    (vfMidDyadicVFTrackingDefect_eq_frozenSafe_add_lowerTransport
      hA hAB hBA)
    hsafe hexcess

/-- The lower-prime transport is nonnegative: it is exactly the
multiplicity-preserving population of stripped frozen-composite prime
children.  This fixes the sign of the lower-wall descent currency. -/
theorem vfMidDyadicLowerPrimeIntervalTransport_nonneg
    {A B : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    0 ≤ vfMidDyadicLowerPrimeIntervalTransport A B := by
  unfold vfMidDyadicLowerPrimeIntervalTransport
  rw [← vfMidDyadicFrozenCompositeOwnerChildSupply_eq_primeIntervalSupply
    hA hAB hBA]
  unfold vfMidDyadicFrozenCompositeOwnerChildSupply
  positivity

/-- Because the lower transport is nonnegative, an ordinary upper bound is
enough to invoke the two-sided capacitor window; no absolute-value estimate is
needed on this side. -/
theorem vfMidDyadicFrozenSafeMass_mem_trackingWindow_of_lowerTransport_le
    {A B : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    {H : ℝ}
    (hrec : vfMidDyadicLowerPrimeIntervalTransport A B ≤ H) :
    vfMidDyadicVFTrackingDefect A B - H ≤
        vfMidDyadicFrozenSafeMass A B ∧
      vfMidDyadicFrozenSafeMass A B ≤
        vfMidDyadicVFTrackingDefect A B + H := by
  have hnonneg :=
    vfMidDyadicLowerPrimeIntervalTransport_nonneg hA hAB hBA
  apply vfMidDyadicFrozenSafeMass_mem_trackingWindow_of_lowerTransport_abs_le
    hA hAB hBA
  simpa [abs_of_nonneg hnonneg] using hrec

/-- Every actual tagged prime child in the lower transport lies on a strictly
smaller square-root scale.  This packages the existing frozen-run geometry in
the same module as the capacitor trigger. -/
theorem vfMidDyadicLowerTransport_child_strictly_lower
    {A B R p q : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hR : R ∈ Finset.Ico A B)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R)
    (hq : q ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    q.Prime ∧ q < A ^ 2 ∧ Nat.sqrt q < A := by
  exact vfMidDyadicFrozenCompositeOwnerChild_prime_below_frozenSquare
    hA hAB hBA hR hp hq


/-! ## Already-proved no-persistence machinery feeds sector six

The scalar lower-prime capacitor above and the pair-level continuation ledger
live in different exact currencies and are not identified by analogy. At the
pair level, the existing signed-cell polarization has already removed the
interior persistence mechanism:

* the rank-zero diagonal is terminal/nonpositive;
* clipped/admitted transport is explicit boundary mass;
* the admitted positive-lag carrier is uniquely partitioned by greatest owner;
* continuation sectors one through five are nonrecursive;
* sector six is the only genuinely recursive remainder.

The exact signed-cell equality in the centered greatest-owner module puts that
already-proved no-persistence reduction into the same scalar capacitor algebra
used above.
-/

/-- **No-persistence capacitor tripwire.**

If the terminal/boundary side of one signed first-owner cell is bounded by
cap, while the complete signed cell exceeds cap + H, then sector six alone
must carry more than H. -/
theorem vfMidNoPersistenceCapacitor_forces_sectorSixDirichletMass
    {R p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) {cap H : ℝ}
    (hsafe :
      lowOwnerFirstOwnerNoPersistenceSafeDirichletMass R p sig ≤ cap)
    (hexcess :
      cap + H < lowOwnerFirstOwnerSignedCellTelescope R p sig) :
    H < lowOwnerFirstOwnerSectorSixRecursiveDirichletMass R p sig := by
  exact vfMidRecursiveResidual_gt_of_safeCapacity
    (lowOwnerFirstOwnerSignedCellTelescope_eq_noPersistenceSafe_add_sectorSix
      hp)
    hsafe hexcess

/-- If sector six remains inside [-H,H], the already-terminal/boundary mass is
forced into the exact parent window. This is the contrapositive form used when
a first-bad source cannot be absorbed without recursive descent. -/
theorem vfMidNoPersistenceSafeMass_mem_cellWindow_of_sectorSix_abs_le
    {R p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) {H : ℝ}
    (hrec :
      |lowOwnerFirstOwnerSectorSixRecursiveDirichletMass R p sig| ≤ H) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig - H ≤
        lowOwnerFirstOwnerNoPersistenceSafeDirichletMass R p sig ∧
      lowOwnerFirstOwnerNoPersistenceSafeDirichletMass R p sig ≤
        lowOwnerFirstOwnerSignedCellTelescope R p sig + H := by
  exact vfMidSafeMass_mem_parentWindow_of_recursive_abs_le
    (lowOwnerFirstOwnerSignedCellTelescope_eq_noPersistenceSafe_add_sectorSix
      hp)
    hrec

/-- Positive sector-six mass cannot be supported by an empty recursive
continuation carrier. Hence some greatest owner has a literal sector-six
pair. -/
theorem vfMidSectorSixDirichletMass_pos_has_recursivePair
    {R p : ℕ} {sig : Finset ℕ}
    (hpos : 0 < lowOwnerFirstOwnerSectorSixRecursiveDirichletMass R p sig) :
    ∃ r ∈ lowOwnerRevealedPrimesAbove R p,
      ∃ m n : ℕ,
        (m, n) ∈
          lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
            R p sig r := by
  by_contra hnone
  push_neg at hnone
  have hzero :
      lowOwnerFirstOwnerAdmittedPositiveSectorSixDirichletMass R p sig = 0 := by
    unfold lowOwnerFirstOwnerAdmittedPositiveSectorSixDirichletMass
    apply Finset.sum_eq_zero
    intro r hr
    unfold lowOwnerFirstOwnerGreatestOwnerSectorSixDirichletMass
    apply Finset.sum_eq_zero
    intro mn hmn
    rcases mn with ⟨m, n⟩
    exact (hnone r hr m n hmn).elim
  unfold lowOwnerFirstOwnerSectorSixRecursiveDirichletMass at hpos
  rw [hzero] at hpos
  norm_num at hpos

/-- **Capacitor overflow forces literal sector-six descent.**

Once the already-proved no-persistence/terminal sectors cannot absorb the
signed cell demand, the capacitor forces positive sector-six mass. A literal
sector-six pair therefore exists, and its existing continuation theorem
supplies a stripped parent in the strict recursive carrier with fresh-owner
rank reduced by one.

No new cancellation estimate or persistence hypothesis appears. -/
theorem vfMidNoPersistenceCapacitor_forces_sectorSixDescent
    {R p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) {cap H : ℝ}
    (hH : 0 ≤ H)
    (hsafe :
      lowOwnerFirstOwnerNoPersistenceSafeDirichletMass R p sig ≤ cap)
    (hexcess :
      cap + H < lowOwnerFirstOwnerSignedCellTelescope R p sig) :
    ∃ r ∈ lowOwnerRevealedPrimesAbove R p,
      ∃ m n : ℕ,
        (m, n) ∈
            lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
              R p sig r ∧
          squarefreePairPrimeOrderedParent r m n ∈
            postRootCovarianceRemainderRecursivePairCarrier
              (squareRootEndpoint R / r) ∧
          (squarefreePairFreshPrimeSet
              (squarefreePairPrimeOrderedParent r m n).1
              (squarefreePairPrimeOrderedParent r m n).2).card + 1 =
            (squarefreePairFreshPrimeSet m n).card ∧
          ∀ q ∈ squarefreePairFreshPrimeSet
              (squarefreePairPrimeOrderedParent r m n).1
              (squarefreePairPrimeOrderedParent r m n).2,
            q < r := by
  have hrec :
      H < lowOwnerFirstOwnerSectorSixRecursiveDirichletMass R p sig :=
    vfMidNoPersistenceCapacitor_forces_sectorSixDirichletMass
      hp hsafe hexcess
  have hpos :
      0 < lowOwnerFirstOwnerSectorSixRecursiveDirichletMass R p sig :=
    lt_of_le_of_lt hH hrec
  rcases vfMidSectorSixDirichletMass_pos_has_recursivePair hpos with
    ⟨r, hr, m, n, hmn⟩
  have hdata :=
    lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber_data
      hp hmn
  dsimp only at hdata
  exact ⟨r, hr, m, n, hmn, hdata⟩

end RHLean.Analysis
