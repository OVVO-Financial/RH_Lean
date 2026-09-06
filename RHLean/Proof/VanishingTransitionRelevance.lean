import Mathlib
import RHLean.Arithmetic.PrimorialTruncatedWheelBoundary
import RHLean.Proof.MutableSupportBound
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.LowWheelDoubleCubeTransport
import RHLean.Proof.PrimeCombReciprocalBandCancellation
import RHLean.Proof.TerminalAxiomAudit

/-!
# Vanishing transition relevance

This module formalizes the final deterministic asymptotic transfer.  A transition
support `U n` is measured on the linear scale of the square block by

```text
card (U n) / n.
```

If the settled complement has zero Möbius mass, PR #153 gives
`|Δ_n| <= card (U n)`.  Dividing by `n` shows that vanishing transition relevance
forces the normalized square-block discrepancy to vanish as well.

The arithmetic construction of the genuine severed transition support, and the
proof that its relevance vanishes, remain separate inputs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology
open Filter

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership

/-- Transition relevance on the natural linear scale of the square block. -/
def transitionRelevance (U : ℕ → Finset ℕ) (n : ℕ) : ℝ :=
  ((U n).card : ℝ) / (n : ℝ)

/-- Absolute square-block discrepancy normalized by the same linear scale. -/
def normalizedSquareBlockDiscrepancy (n : ℕ) : ℝ :=
  |(squareBlockMoebius n : ℝ)| / (n : ℝ)

/-- Epsilon/eventually formulation of vanishing transition relevance. -/
def TransitionRelevanceVanishes (U : ℕ → Finset ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, transitionRelevance U n ≤ ε

/-- Epsilon/eventually formulation of `Δ_n = o(n)`. -/
def SquareBlockDiscrepancyVanishes : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, normalizedSquareBlockDiscrepancy n ≤ ε

/-- Pointwise transfer: the normalized block discrepancy is bounded by transition
relevance whenever the settled complement has zero Möbius mass. -/
theorem normalizedSquareBlockDiscrepancy_le_transitionRelevance
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    {n : ℕ} (hn : 0 < n) :
    normalizedSquareBlockDiscrepancy n ≤ transitionRelevance U n := by
  have hInt : |squareBlockMoebius n| ≤ ((U n).card : ℤ) :=
    abs_squareBlockMoebius_le_mutable_card (hU n) (hinterior n)
  have hReal : |(squareBlockMoebius n : ℝ)| ≤ ((U n).card : ℝ) := by
    exact_mod_cast hInt
  unfold normalizedSquareBlockDiscrepancy transitionRelevance
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_le_div_iff_of_pos_right hnReal).2 hReal

/-- Vanishing transition relevance forces `Δ_n = o(n)` in epsilon/eventually
form.  No further cancellation estimate is used. -/
theorem squareBlockDiscrepancyVanishes_of_transitionRelevanceVanishes
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (hvanish : TransitionRelevanceVanishes U) :
    SquareBlockDiscrepancyVanishes := by
  intro ε hε
  have hrel := hvanish ε hε
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    omega
  filter_upwards [hrel, hpos] with n hnRel hnPos
  exact le_trans
    (normalizedSquareBlockDiscrepancy_le_transitionRelevance U hU hinterior hnPos)
    hnRel

/-! ## Ordered prime replication as deterministic Möbius transport

The fixed lower Möbius prefix is not resampled by post-root primes.  This
section identifies the user's cofactor-first response with the repository's
existing high transport and therefore with its exact dyadic compression.
-/

/-- Complete signed replication response of the fixed prefix at the square
endpoint `X_R = R^2 - 1`. -/
def orderedPrimeReplicationResponse (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    canonicalMoebiusWeight c *
      ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
        (Nat.primeCounting R : ℂ))

/-- The `c=1,2` channels cancel everything except the inert top-prime block. -/
theorem orderedPrimeReplication_firstTwo_eq_topCard
    (R : ℕ) :
    (∑ c ∈ ({1, 2} : Finset ℕ),
      canonicalMoebiusWeight c *
        ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
          (Nat.primeCounting R : ℂ))) =
      ((squareRootTopFibrePrimes R).card : ℂ) := by
  have hmu1 : canonicalMoebiusWeight 1 = 1 := by
    simp [canonicalMoebiusWeight]
  have hmu2 : canonicalMoebiusWeight 2 = -1 := by
    unfold canonicalMoebiusWeight
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  have htop := squareRootTopFibrePrimes_card_add_primeCounting_half R
  have htopC :
      ((squareRootTopFibrePrimes R).card : ℂ) +
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) =
        (Nat.primeCounting (squareRootEndpoint R) : ℂ) := by
    exact_mod_cast htop
  have htopDiff :
      (Nat.primeCounting (squareRootEndpoint R) : ℂ) -
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) =
        ((squareRootTopFibrePrimes R).card : ℂ) := by
    symm
    exact (eq_sub_iff_add_eq).2 htopC
  calc
    (∑ c ∈ ({1, 2} : Finset ℕ),
      canonicalMoebiusWeight c *
        ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
          (Nat.primeCounting R : ℂ))) =
        (Nat.primeCounting (squareRootEndpoint R) : ℂ) -
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) := by
      simp [hmu1, hmu2]
    _ = ((squareRootTopFibrePrimes R).card : ℂ) := htopDiff

/-- **Exact global identification.**  The full ordered replication response is
exactly the existing cofactor-first transport.  No iid or probabilistic input
appears. -/
theorem orderedPrimeReplicationResponse_eq_transport
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationResponse R = squareRootTransportCofactorFirst R := by
  classical
  let lowC : Finset ℕ := Finset.Icc 3 (R - 1)
  have hset :
      Finset.Ico 1 R = ({1, 2} : Finset ℕ) ∪ lowC := by
    ext c
    simp only [lowC, Finset.mem_Ico, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hdisj : Disjoint ({1, 2} : Finset ℕ) lowC := by
    rw [Finset.disjoint_left]
    intro c hc12 hclow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc12
    rcases Finset.mem_Icc.mp hclow with ⟨hc3, _hcTop⟩
    omega
  have hmiddle := squareRootMiddleMertensTail_eq_swappedPrimeCounting R hR
  unfold orderedPrimeReplicationResponse
  rw [hset, Finset.sum_union hdisj,
    orderedPrimeReplication_firstTwo_eq_topCard R]
  change ((squareRootTopFibrePrimes R).card : ℂ) +
      (∑ c ∈ Finset.Icc 3 (R - 1),
        canonicalMoebiusWeight c *
          ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
            (Nat.primeCounting R : ℂ))) = squareRootTransportCofactorFirst R
  rw [← hmiddle, squareRootTransportCofactorFirst_eq_primeFirst,
    squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR]
  ring

/-- **Global deterministic non-iid compression.**  The whole ordered prime
replication of the fixed Möbius prefix is exactly the repository's odd dyadic
boundary mass. -/
theorem orderedPrimeReplicationResponse_eq_dyadicBoundaryMass
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationResponse R =
      squareRootDyadicTransportBoundaryMass R := by
  rw [orderedPrimeReplicationResponse_eq_transport R hR,
    squareRootTransportCofactorFirst_eq_dyadicBoundaryMass]

/-! ## Iterated fresh-prime Euler finite differences

The post-root response is now reindexed through the *entire* deterministic
Möbius dependence of the fixed prefix.  In reciprocal coordinates a fresh
prime acts by `W(X) - W(X/p)`.  The cutoff travels with the shift, so no raw
seat outside the surviving Boolean face is introduced.
-/

/-- Prime-count response field above the fixed root cutoff. -/
def orderedPrimeWindowWeight (R x : ℕ) : ℂ :=
  (Nat.primeCounting x : ℂ) - (Nat.primeCounting R : ℂ)

/-- Truncated Boolean Euler finite difference in the reciprocal endpoint
coordinate. -/
def eulerFiniteDifferenceResponse
    (P : Finset ℕ) (B X : ℕ) (W : ℕ → ℂ) : ℂ :=
  ∑ t ∈ P.powerset,
    if primeFaceProduct t ≤ B then
      (booleanCubeSign t : ℂ) * W (X / primeFaceProduct t)
    else
      0

/-- **One fresh prime is one exact Boolean difference.** -/
theorem eulerFiniteDifferenceResponse_insert
    {P : Finset ℕ} {p B X : ℕ} (W : ℕ → ℂ)
    (hp : p ∉ P) (hpPrime : p.Prime) :
    eulerFiniteDifferenceResponse (insert p P) B X W =
      eulerFiniteDifferenceResponse P B X W -
        eulerFiniteDifferenceResponse P (B / p) (X / p) W := by
  classical
  unfold eulerFiniteDifferenceResponse
  rw [Finset.sum_powerset_insert hp]
  have hsecond :
      (∑ t ∈ P.powerset,
        if primeFaceProduct (insert p t) ≤ B then
          (booleanCubeSign (insert p t) : ℂ) *
            W (X / primeFaceProduct (insert p t))
        else 0) =
        -(∑ t ∈ P.powerset,
          if primeFaceProduct t ≤ B / p then
            (booleanCubeSign t : ℂ) *
              W ((X / p) / primeFaceProduct t)
          else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hpt : p ∉ t :=
      Finset.notMem_of_mem_powerset_of_notMem ht hp
    have hprod :
        primeFaceProduct (insert p t) = p * primeFaceProduct t := by
      simp [primeFaceProduct, hpt]
    have hsign :
        (booleanCubeSign (insert p t) : ℂ) =
          -(booleanCubeSign t : ℂ) := by
      unfold booleanCubeSign
      rw [Finset.card_insert_of_notMem hpt, pow_succ]
      push_cast
      ring
    have hcut :
        primeFaceProduct (insert p t) ≤ B ↔
          primeFaceProduct t ≤ B / p := by
      rw [hprod]
      constructor
      · intro hle
        apply (Nat.le_div_iff_mul_le hpPrime.pos).2
        simpa [Nat.mul_comm] using hle
      · intro hle
        have hmul := (Nat.le_div_iff_mul_le hpPrime.pos).1 hle
        simpa [Nat.mul_comm] using hmul
    have hdiv :
        X / primeFaceProduct (insert p t) =
          (X / p) / primeFaceProduct t := by
      rw [hprod, Nat.div_div_eq_div_mul]
    by_cases hle : primeFaceProduct t ≤ B / p
    · have hchild : primeFaceProduct (insert p t) ≤ B := hcut.mpr hle
      simp only [hchild, hle, if_true]
      rw [hsign, hdiv]
      ring
    · have hchild : ¬primeFaceProduct (insert p t) ≤ B := by
        intro h
        exact hle (hcut.mp h)
      simp [hchild, hle]
  rw [hsecond]
  ring

/-- The complete fixed-prefix ordered response as one truncated Euler cube. -/
def orderedPrimeReplicationEulerResponse (R : ℕ) : ℂ :=
  eulerFiniteDifferenceResponse
    (primesUpTo R) (R - 1) (squareRootEndpoint R)
    (orderedPrimeWindowWeight R)

/-- **No iid surrogate remains:** the lower Möbius prefix is literally one
truncated Boolean prime cube for the actual prime-count response weight. -/
theorem orderedPrimeReplicationResponse_eq_eulerFiniteDifference
    (R : ℕ) (hR : 1 ≤ R) :
    orderedPrimeReplicationResponse R =
      orderedPrimeReplicationEulerResponse R := by
  classical
  unfold orderedPrimeReplicationResponse orderedPrimeReplicationEulerResponse
  rw [canonicalMoebiusWeighted_Ico_eq_admissibleFaceSum
    R hR (fun c =>
      (Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
        (Nat.primeCounting R : ℂ))]
  rw [admissiblePrimeFaces_pred_eq_lowCube_filter_product_lt R hR]
  unfold eulerFiniteDifferenceResponse
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hlt : primeFaceProduct t < R
  · have hle : primeFaceProduct t ≤ R - 1 := by omega
    simp [hlt, hle, orderedPrimeWindowWeight]
  · have hnle : ¬primeFaceProduct t ≤ R - 1 := by omega
    simp [hlt, hnle]

/-- The finite-difference cube is exactly the existing high transport. -/
theorem orderedPrimeReplicationEulerResponse_eq_transport
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationEulerResponse R =
      squareRootTransportCofactorFirst R := by
  rw [← orderedPrimeReplicationResponse_eq_eulerFiniteDifference R (by omega)]
  exact orderedPrimeReplicationResponse_eq_transport R hR

/-- And therefore exactly the compiled dyadic boundary compression. -/
theorem orderedPrimeReplicationEulerResponse_eq_dyadicBoundaryMass
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationEulerResponse R =
      squareRootDyadicTransportBoundaryMass R := by
  rw [orderedPrimeReplicationEulerResponse_eq_transport R hR,
    squareRootTransportCofactorFirst_eq_dyadicBoundaryMass]

/-- The dual reciprocal-weighted convention is already native in the repo and
satisfies the exact `1 - (1/p) S_p` recurrence. -/
theorem reciprocalWeightedEulerFiniteDifference_insert
    {P : Finset ℕ} {p X : ℕ}
    (hp : p ∉ P) (hpPrime : p.Prime) :
    primorialTruncatedSignedReciprocalCube (insert p P) X =
      primorialTruncatedSignedReciprocalCube P X -
        (1 / (p : ℝ)) *
          primorialTruncatedSignedReciprocalCube P (X / p) :=
  primorialTruncatedSignedReciprocalCube_insert hp hpPrime

/-! ## Exact post-cancellation live exposure

The first-jump fibre below is *after* the predecessor-dense cube has already
collapsed to the smaller square-root universe.  Thus the exposure counts only
the exact first-failure boundary; it is not a generic remaining-seat count.
-/

/-- Signed first-jump aggregate with all state signs intact. -/
def signedLiveFirstJumpAggregate (R : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x

/-- Nonnegative live cancellation exposure.  The norm is taken only after each
exact first-failure predecessor fibre has been formed. -/
def liveCancellationExposure (R : ℕ) : ℝ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    ‖lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x‖

/-- Signed live mass is dominated by the post-cancellation exposure. -/
theorem norm_signedLiveFirstJumpAggregate_le_liveCancellationExposure
    (R : ℕ) :
    ‖signedLiveFirstJumpAggregate R‖ ≤ liveCancellationExposure R := by
  unfold signedLiveFirstJumpAggregate liveCancellationExposure
  exact norm_sum_le _ _

/-- **Exact remaining live-exposure theorem.**  This is stated on the compiled
first-failure carrier, not on Mertens and not on raw prime seats. -/
def LiveCancellationExposureBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      liveCancellationExposure R ≤
        C * (R : ℝ) * (Real.log (R : ℝ) + 1)

/-- The exposure theorem immediately controls the signed first-jump aggregate. -/
theorem signedLiveFirstJumpAggregate_polylog_of_liveExposure
    (h : LiveCancellationExposureBound) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 3 ≤ R →
        ‖signedLiveFirstJumpAggregate R‖ ≤
          C * (R : ℝ) * (Real.log (R : ℝ) + 1) := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro R hR
  exact (norm_signedLiveFirstJumpAggregate_le_liveCancellationExposure R).trans
    (hbound R hR)

/-- The exact square-root predecessor contraction isolates this signed live
aggregate as the only first-jump part of the oriented ledger. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sqrtDense_add_signedLive
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre R x) +
        signedLiveFirstJumpAggregate R := by
  simpa [signedLiveFirstJumpAggregate] using
    lowWheelCanonicalDowncrossOrientedLedger_eq_sqrtDense_add_firstJump R

/-! ## Canonical first-jump prime slices

The first-jump residual of every oriented state is already a disjoint signed
sum over its canonical first failing prime.  This section lifts that exact
partition to the global state carrier without taking norms.  It is the
correct object on which to attempt the next deterministic finite-difference
contraction.
-/

/-- A fixed finite prime universe containing every predecessor prime that can
occur in an oriented state at root `R`. -/
def firstJumpPrimeUniverse (R : ℕ) : Finset ℕ :=
  primesUpTo (squareRootEndpoint R)

/-- Signed contribution of one canonical first-jump prime to one oriented
state.  The state sign is kept outside the predecessor slice. -/
noncomputable def signedFirstJumpPrimeStateSlice
    (R p : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if h : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
      Nat.sqrt R < lowWheelCanonicalDowncrossPivot x then
    if hp : p ∈ primesUpTo (lowWheelCanonicalDowncrossPivot x - 1) then
      canonicalMoebiusWeight x.1 *
        ((predecessorFirstJumpFrozenWindowSliceMass
          3 (Nat.sqrt R)
          (primesUpTo (lowWheelCanonicalDowncrossPivot x - 1))
          (R / x.2)
          (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2)
          p : ℤ) : ℂ)
    else 0
  else 0

/-- Global signed mass owned by one canonical first-jump prime. -/
def signedFirstJumpPrimeSliceAggregate (R p : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    signedFirstJumpPrimeStateSlice R p x

/-- The local predecessor prime set of every actual oriented state is contained
in the common finite prime universe. -/
theorem predecessorPrimeSet_subset_firstJumpPrimeUniverse
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    primesUpTo (lowWheelCanonicalDowncrossPivot x - 1) ⊆
      firstJumpPrimeUniverse R := by
  classical
  rcases x with ⟨c, k⟩
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  have hne := hxData.2
  have hkPivot : k = lowWheelCanonicalDowncrossPivot (c, k) :=
    lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
  have hkMem := (Finset.mem_product.mp hxData.1).2
  have hkLe : k ≤ squareRootEndpoint R := (Finset.mem_Icc.mp hkMem).2
  intro p hp
  rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpLe⟩
  apply mem_primesUpTo.mpr
  refine ⟨hpPrime, ?_⟩
  omega

/-- For one actual state, the complete first-jump fibre is exactly the signed
sum of its canonical prime slices over the common universe. -/
theorem lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_primeSlices
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x =
      ∑ p ∈ firstJumpPrimeUniverse R,
        signedFirstJumpPrimeStateSlice R p x := by
  classical
  rcases x with ⟨c, k⟩
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  have hne := hxData.2
  by_cases hroot : Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k)
  · have hstate :
        (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty ∧
          Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k) :=
      ⟨hne, hroot⟩
    let S := primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1)
    let A := R / k
    let B := lowWheelCanonicalDowncrossOwnershipUpper R c k
    have hmass :=
      predecessorFirstJumpFrozenWindowMass_eq_sum_slices
        3 (Nat.sqrt R) S A B
    have hcast := congrArg (fun z : ℤ => (z : ℂ)) hmass
    push_cast at hcast
    unfold lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre
    rw [if_pos hstate]
    change canonicalMoebiusWeight c *
        ((predecessorFirstJumpFrozenWindowMass
          3 (Nat.sqrt R) S A B : ℤ) : ℂ) = _
    rw [hcast, Finset.mul_sum]
    have hsubset : S ⊆ firstJumpPrimeUniverse R := by
      simpa [S] using
        (predecessorPrimeSet_subset_firstJumpPrimeUniverse (R := R)
          (x := (c, k)) hx)
    calc
      (∑ p ∈ S,
          canonicalMoebiusWeight c *
            ((predecessorFirstJumpFrozenWindowSliceMass
              3 (Nat.sqrt R) S A B p : ℤ) : ℂ)) =
        ∑ p ∈ S, signedFirstJumpPrimeStateSlice R p (c, k) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [signedFirstJumpPrimeStateSlice, hstate, hp, S, A, B]
      _ = ∑ p ∈ firstJumpPrimeUniverse R,
          signedFirstJumpPrimeStateSlice R p (c, k) := by
          apply Finset.sum_subset hsubset
          intro p hpU hpNot
          simp [signedFirstJumpPrimeStateSlice, hstate, hpNot, S]
  · have hstate :
        ¬((lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty ∧
          Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k)) := by
      simp [hne, hroot]
    simp [lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre,
      signedFirstJumpPrimeStateSlice, hstate]

/-- **Exact global prime-slice Fubini.**  The signed live first-jump aggregate is
literally the sum of its canonical first-jump-prime aggregates.  No norm,
probability model, or PNT estimate occurs in this identity. -/
theorem signedLiveFirstJumpAggregate_eq_sum_primeSlices
    (R : ℕ) :
    signedLiveFirstJumpAggregate R =
      ∑ p ∈ firstJumpPrimeUniverse R,
        signedFirstJumpPrimeSliceAggregate R p := by
  classical
  unfold signedLiveFirstJumpAggregate signedFirstJumpPrimeSliceAggregate
  calc
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        ∑ p ∈ firstJumpPrimeUniverse R,
          signedFirstJumpPrimeStateSlice R p x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_primeSlices hx
    _ = ∑ p ∈ firstJumpPrimeUniverse R,
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
          signedFirstJumpPrimeStateSlice R p x := by
        rw [Finset.sum_comm]

/-- A canonical first-jump slice below the predecessor threshold is empty. -/
theorem predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_le_threshold
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ}
    (hp : p ≤ Y) :
    predecessorFirstJumpFrozenWindowSliceMass d Y S A B p = 0 := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
  apply Finset.sum_eq_zero
  intro t ht
  have hfirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp ht).2
  omega

/-- A canonical first-jump slice above the physical window endpoint is empty. -/
theorem predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ}
    (hBp : B < p) :
    predecessorFirstJumpFrozenWindowSliceMass d Y S A B p = 0 := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
  apply Finset.sum_eq_zero
  intro t ht
  have hslice := mem_predecessorFirstJumpFrozenWindowSlice.mp ht
  have hfirst := hslice.2
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hslice.1).1
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htPow, _hlo, hup⟩
  have hprodPos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset htPow
  have hpdvd : p ∣ primeFaceProduct t := by
    change p ∣ t.prod id
    exact Finset.dvd_prod_of_mem id hfirst.1
  have hple : p ≤ primeFaceProduct t := Nat.le_of_dvd hprodPos hpdvd
  omega

/-- Consequently a state slice is zero at primes at or below the root wall. -/
theorem signedFirstJumpPrimeStateSlice_eq_zero_of_le_root
    {R p : ℕ} {x : LowWheelCofactorQuotientState}
    (hp : p ≤ Nat.sqrt R) :
    signedFirstJumpPrimeStateSlice R p x = 0 := by
  classical
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_le_threshold hp]
    simp
  · rfl
  · rfl

/-- A state slice is also zero above the physical root endpoint `R`; the
ownership window itself is already contained in `[1,R]`. -/
theorem signedFirstJumpPrimeStateSlice_eq_zero_of_root_lt
    {R p : ℕ} {x : LowWheelCofactorQuotientState}
    (hRp : R < p) :
    signedFirstJumpPrimeStateSlice R p x = 0 := by
  classical
  rcases x with ⟨c, k⟩
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · have hupper : lowWheelCanonicalDowncrossOwnershipUpper R c k ≤ R := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_left _ _).trans (Nat.div_le_self _ _)
    have hBp : lowWheelCanonicalDowncrossOwnershipUpper R c k < p :=
      hupper.trans_lt hRp
    rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt hBp]
    simp
  · rfl
  · rfl

/-- The global prime slice vanishes below the root wall. -/
theorem signedFirstJumpPrimeSliceAggregate_eq_zero_of_le_root
    {R p : ℕ} (hp : p ≤ Nat.sqrt R) :
    signedFirstJumpPrimeSliceAggregate R p = 0 := by
  unfold signedFirstJumpPrimeSliceAggregate
  apply Finset.sum_eq_zero
  intro x _hx
  exact signedFirstJumpPrimeStateSlice_eq_zero_of_le_root hp

/-- The global prime slice vanishes above `R`. -/
theorem signedFirstJumpPrimeSliceAggregate_eq_zero_of_root_lt
    {R p : ℕ} (hp : R < p) :
    signedFirstJumpPrimeSliceAggregate R p = 0 := by
  unfold signedFirstJumpPrimeSliceAggregate
  apply Finset.sum_eq_zero
  intro x _hx
  exact signedFirstJumpPrimeStateSlice_eq_zero_of_root_lt hp

/-- The actual first-jump prime carrier is the post-root prime interval. -/
def signedFirstJumpPostRootPrimeSet (R : ℕ) : Finset ℕ :=
  frozenPrimeUniverseHighPrimeSet (Nat.sqrt R) R

/-- Only primes strictly between the square-root wall and `R` survive in the
global signed first-jump decomposition. -/
theorem signedLiveFirstJumpAggregate_eq_sum_postRootPrimeSlices
    (R : ℕ) (hR : 3 ≤ R) :
    signedLiveFirstJumpAggregate R =
      ∑ p ∈ signedFirstJumpPostRootPrimeSet R,
        signedFirstJumpPrimeSliceAggregate R p := by
  classical
  rw [signedLiveFirstJumpAggregate_eq_sum_primeSlices]
  have hRend : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    nlinarith
  have hsubset : signedFirstJumpPostRootPrimeSet R ⊆ firstJumpPrimeUniverse R := by
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    unfold firstJumpPrimeUniverse
    exact mem_primesUpTo.mpr ⟨hpData.1, hpData.2.2.trans hRend⟩
  symm
  apply Finset.sum_subset hsubset
  intro p hpU hpNot
  have hpPrime : p.Prime := (mem_primesUpTo.mp hpU).1
  by_cases hpLow : p ≤ Nat.sqrt R
  · exact signedFirstJumpPrimeSliceAggregate_eq_zero_of_le_root hpLow
  · have hpHigh : Nat.sqrt R < p := Nat.lt_of_not_ge hpLow
    have hpNotData : ¬(p.Prime ∧ Nat.sqrt R < p ∧ p ≤ R) := by
      simpa [signedFirstJumpPostRootPrimeSet,
        mem_frozenPrimeUniverseHighPrimeSet] using hpNot
    have hRp : R < p := by
      by_contra hnot
      have hpR : p ≤ R := Nat.le_of_not_gt hnot
      exact hpNotData ⟨hpPrime, hpHigh, hpR⟩
    exact signedFirstJumpPrimeSliceAggregate_eq_zero_of_root_lt hRp

/-- The desired signed live-boundary estimate, with the norm taken only after
all state and Möbius signs have been summed. -/
def PNTFiniteDifferenceLiveExposureBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖signedLiveFirstJumpAggregate R‖ ≤
        C * (R : ℝ) * (Real.log (R : ℝ) + 1)

/-- The remaining prime-local quantitative seam.  It asks the iterated Euler
finite differences to control one canonical high-prime slice at its natural
`R/p` seat scale, with one logarithmic overlap allowance. -/
def FirstJumpPrimeSliceFiniteDifferenceBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R p : ℕ, 3 ≤ R → p.Prime → Nat.sqrt R < p → p ≤ R →
      ‖signedFirstJumpPrimeSliceAggregate R p‖ ≤
        C * (((R / p : ℕ) : ℝ)) * (Real.log (R : ℝ) + 1)

end RHLean.Proof
