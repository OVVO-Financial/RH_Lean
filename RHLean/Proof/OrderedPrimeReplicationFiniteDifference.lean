import Mathlib
import RHLean.Arithmetic.PrimorialTruncatedWheelBoundary
import RHLean.Proof.LowWheelDoubleCubeTransport
import RHLean.Proof.TerminalAxiomAudit
import RHLean.Proof.VanishingTransitionRelevance

/-!
# Ordered prime replication as an iterated Euler finite difference

The post-root prime sector does not resample Möbius signs.  Once a squarefree
lower cofactor `c` is fixed, adjoining a fresh prime reverses its sign.  In the
reciprocal cutoff coordinate this is the literal Boolean difference

`W(X) - W(X / p)`.

Iterating over a finite prime set therefore produces one truncated Boolean cube.
The cutoff is part of the operator: after inserting `p`, both the physical
reciprocal endpoint and the admissible face-product cutoff divide by `p`.

This module makes that statement exact for the ordered prime-count replication
response already identified with the repository transport term.  No iid model,
probabilistic concentration, PNT estimate, or analytic cancellation estimate is
used in the identities below.

The repository also already contains the reciprocal-weighted dual operator
`primorialTruncatedSignedReciprocalCube`; its fresh-prime recurrence is

`D_(P union {p})(X) = D_P(X) - (1/p) D_P(X/p)`.

The present `eulerFiniteDifferenceResponse` is the unweighted version required
by the actual prime-count response.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

/-- Prime-count response field above the fixed root cutoff. -/
def orderedPrimeWindowWeight (R x : ℕ) : ℂ :=
  (Nat.primeCounting x : ℂ) - (Nat.primeCounting R : ℂ)

/-- Truncated Boolean Euler finite difference in the reciprocal endpoint
coordinate.  A face `t` contributes only while its squarefree product is at
most `B`; its reciprocal shift is `X / primeFaceProduct t`. -/
def eulerFiniteDifferenceResponse
    (P : Finset ℕ) (B X : ℕ) (W : ℕ → ℂ) : ℂ :=
  ∑ t ∈ P.powerset,
    if primeFaceProduct t ≤ B then
      (booleanCubeSign t : ℂ) * W (X / primeFaceProduct t)
    else
      0

/-- **One fresh prime is one exact Boolean difference.**  Inserting a fresh
prime `p` splits the Boolean cube into the old faces and the same faces with
`p` inserted.  The latter have opposite sign, reciprocal endpoint `X/p`, and
face-product cutoff `B/p`.

This is the exact unweighted `1 - S_p` law. -/
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

/-- The complete fixed-prefix ordered prime response written as one truncated
Euler Boolean cube. -/
def orderedPrimeReplicationEulerResponse (R : ℕ) : ℂ :=
  eulerFiniteDifferenceResponse
    (primesUpTo R) (R - 1) (squareRootEndpoint R)
    (orderedPrimeWindowWeight R)

/-- **The lower Möbius prefix is literally one Boolean prime cube.**  The
arbitrary-weight squarefree reindexing removes the fiction of independent
`+1/-1/0` draws: every nonzero cofactor is the unique product of one admissible
prime face, and its sign is exactly the Boolean parity of that face. -/
theorem orderedPrimeReplicationResponse_eq_eulerFiniteDifference
    (R : ℕ) (hR : 1 ≤ R) :
    orderedPrimeReplicationResponse R =
      orderedPrimeReplicationEulerResponse R := by
  classical
  unfold orderedPrimeReplicationResponse orderedPrimeReplicationEulerResponse
  rw [canonicalMoebiusWeighted_Ico_eq_admissibleFaceSum
    R hR (fun c => orderedPrimeWindowWeight R (squareRootEndpoint R / c))]
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

/-- Hence the finite-difference cube is not a surrogate: at square-root scale it
is exactly the already-compiled high transport. -/
theorem orderedPrimeReplicationEulerResponse_eq_transport
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationEulerResponse R =
      squareRootTransportCofactorFirst R := by
  rw [← orderedPrimeReplicationResponse_eq_eulerFiniteDifference R (by omega)]
  exact orderedPrimeReplicationResponse_eq_transport R hR

/-- The same global object after the already-compiled deterministic dyadic
compression. -/
theorem orderedPrimeReplicationEulerResponse_eq_dyadicBoundaryMass
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationEulerResponse R =
      squareRootDyadicTransportBoundaryMass R := by
  rw [orderedPrimeReplicationEulerResponse_eq_transport R hR,
    squareRootTransportCofactorFirst_eq_dyadicBoundaryMass]

/-- The repository's native reciprocal-weighted Boolean cube satisfies exactly
the weighted shift law `1 - (1/p) S_p`.  This wrapper records that this is the
dual weighted convention, not the weight convention of the ordered prime-count
response above. -/
theorem reciprocalWeightedEulerFiniteDifference_insert
    {P : Finset ℕ} {p X : ℕ}
    (hp : p ∉ P) (hpPrime : p.Prime) :
    primorialTruncatedSignedReciprocalCube (insert p P) X =
      primorialTruncatedSignedReciprocalCube P X -
        (1 / (p : ℝ)) *
          primorialTruncatedSignedReciprocalCube P (X / p) :=
  primorialTruncatedSignedReciprocalCube_insert hp hpPrime

/-! ## The exact post-cancellation live exposure -/

/-- Signed first-jump aggregate after all completed predecessor-cube
cancellation and the square-root dense contraction have already been performed.
No absolute value is taken inside this definition. -/
def signedLiveFirstJumpAggregate (R : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x

/-- Nonnegative live cancellation exposure.  Absolute values are taken only
*after* each exact first-failure predecessor fibre has been formed; raw seats or
raw prime arrivals are never counted independently here. -/
def liveCancellationExposure (R : ℕ) : ℝ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    ‖lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x‖

/-- The signed live first-jump aggregate is bounded by the exact post-cancellation
exposure. -/
theorem norm_signedLiveFirstJumpAggregate_le_liveCancellationExposure
    (R : ℕ) :
    ‖signedLiveFirstJumpAggregate R‖ ≤ liveCancellationExposure R := by
  unfold signedLiveFirstJumpAggregate liveCancellationExposure
  exact norm_sum_le _ _

/-- **Remaining live-exposure theorem.**  This is deliberately stated on the
exact first-failure fibres rather than on a generic remaining-seat set or on
Mertens itself. -/
def LiveCancellationExposureBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      liveCancellationExposure R ≤
        C * (R : ℝ) * (Real.log (R : ℝ) + 1)

/-- The live-exposure statement immediately bounds the signed first-jump
aggregate at root scale up to one logarithm. -/
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

/-- The first-jump term in the exact square-root contraction of the oriented
ledger is precisely the signed live aggregate above. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sqrtDense_add_signedLive
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedSqrtDenseStateFibre R x) +
        signedLiveFirstJumpAggregate R := by
  simpa [signedLiveFirstJumpAggregate] using
    lowWheelCanonicalDowncrossOrientedLedger_eq_sqrtDense_add_firstJump R

end RHLean.Proof
