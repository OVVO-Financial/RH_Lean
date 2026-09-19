import RHLean.Proof.PostRootPartnerReciprocalCompression
import RHLean.Proof.StableFarWallAdaptiveFourCornerBridge
import Mathlib
import RHLean.Proof.SquareRootLowPrimeRunningTelescope
import RHLean.Proof.SquareRootLowPrimePacketFreeMassTransfer
import RHLean.Proof.SquareRootLowPrimeResponseReentryBirthWitness
import RHLean.Proof.SquareRootLowPrimeResponseForestOthelloInvolution
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty
import RHLean.Proof.SquareRootLowPrimeCanonicalCreationResponseMap
import RHLean.Proof.SquareRootLowPrimeShallowProcessedCreationEquiv
import RHLean.Proof.SquareRootLowPrimeProcessedCreationResponseFixedClassification
import RHLean.Proof.SquareRootLowPrimeCanonicalMatchingInvolution
import RHLean.Proof.SquareRootLowPrimeEulerCreationResponseEnergyGate
import RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell
import RHLean.Proof.SquareRootLowPrimeGoFullFacePartner
import RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary
import RHLean.Proof.SquareRootLowPrimeDeepProcessedSeatBridge
import RHLean.Proof.SquareRootLowPrimeNoTogglePopulationBound

/-!
# Response re-entry routes canonically into the Go two-boundary shell

This file formalizes the arithmetic bridge exposed by the finite X=210 model.

A non-born processed seat can survive a first-owner fallout only through the
inherited response tail. If it later re-enters at a larger scheduled owner,
SquareRootLowPrimeResponseReentryBirthWitness produces a strictly larger newly
born prime. Read that newborn prime as the Go outer owner, the later scheduled
prime as the Go smaller owner, and retain the original cofactor as the Go
parent.

The birth witness is then exactly a member of the full Go birth boundary.
The existing two-boundary theorem splits that parent into:

* a physically completed second-contact terminal parent; or
* a genuine SecondBoundaryDefectParents occurrence.

The latter is already consumed by the full-face transport mate theorem, so this
bridge introduces no new estimate and never sends a completed second contact
(such as the X=210 example) into the hard carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A born re-entry witness is literally a full Go birth-boundary parent. -/
theorem squareRootLowPrimeReentryBirthBoundary_mem_goFullBirthBoundary
    {R p q c t : ℕ}
    (hc : 0 < c)
    (_hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hsq : Squarefree c)
    (htBirth : t ∈ squareRootBornPartnerBirthBoundary R c (q * c)) :
    c ∈ squareRootLowPrimeGoFullBirthBoundaryParents t q := by
  rcases mem_squareRootBornPartnerBirthBoundary.mp htBirth with
    ⟨htBorn, hct⟩
  rcases Finset.mem_filter.mp htBorn with
    ⟨_htRange, _htPrime, _hroughChild, htqc, _hprod⟩
  apply mem_squareRootLowPrimeGoFullBirthBoundaryParents.mpr
  refine ⟨by omega, ?_, hsq, hrough.trans hpq, ?_⟩
  · omega
  · apply (Nat.div_lt_iff_lt_mul hq.pos).2
    have htqc' : t ≤ c * q := by
      simpa [Nat.mul_comm] using htqc
    omega

/-- Every re-entry birth witness has exactly the two physical Go outcomes:
second contact already completed, or a genuine second-boundary defect. -/
theorem squareRootLowPrimeReentryBirthBoundary_goTerminal_or_secondBoundary
    {R X p q c t : ℕ}
    (hc : 0 < c)
    (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hsq : Squarefree c)
    (htBirth : t ∈ squareRootBornPartnerBirthBoundary R c (q * c)) :
    c ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
          t (X / (t * t)) q ∨
      c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents t X q := by
  have hfull :
      c ∈ squareRootLowPrimeGoFullBirthBoundaryParents t q :=
    squareRootLowPrimeReentryBirthBoundary_mem_goFullBirthBoundary
      hc hp hq hrough hpq hsq htBirth
  have hsplit :=
    squareRootLowPrimeGoFullBirthBoundaryParents_eq_terminal_union_defect
      t X q
  rw [hsplit] at hfull
  exact Finset.mem_union.mp hfull

/-- Dynamic processed-seat to Go-shell bridge. -/
theorem squareRootLowPrimeNonBornFalloutReentry_goTerminal_or_secondBoundary
    {R K j U p q c s : ℕ}
    (hR : 1 ≤ R) (hc : 0 < c)
    (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hqAlive : s < squareRootLowPrimeCombinedFreshResponse R K j (q * c)) :
    ∃ t,
      t.Prime ∧ q < t ∧ p * c < t ∧
        (c ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
              t (squareRootEndpoint R / (t * t)) q ∨
          c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
              t (squareRootEndpoint R) q) := by
  have hparent :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
    (mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall).1
  have hseat :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
  have hcProcessed :
      c ∈ squareRootLowPrimeProcessedSignedCofactors R U :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hseat).1
  have hcMuNe : μ c ≠ 0 := by
    exact (Finset.mem_filter.mp hcProcessed).2.2
  have hsq : Squarefree c :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hcMuNe
  obtain ⟨t, htBirth, hqt, hpct⟩ :=
    squareRootLowPrimeNonBornFalloutReentry_birthWitness
      hR hc hp hq hrough hpq hpU hUR hs hnb hfall hqAlive
  have htBorn := (mem_squareRootBornPartnerBirthBoundary.mp htBirth).1
  have htPrime : t.Prime := (Finset.mem_filter.mp htBorn).2.1
  have hsplit :=
    squareRootLowPrimeReentryBirthBoundary_goTerminal_or_secondBoundary
      (X := squareRootEndpoint R)
      hc hp hq hrough hpq hsq htBirth
  exact ⟨t, htPrime, hqt, hpct, hsplit⟩

/-- The hard branch is already consumed pointwise by the full-face Go mate. -/
theorem squareRootLowPrimeSecondBoundaryDefect_fullFace_cancel
    {R t q c : ℕ}
    (hR : 2 ≤ R)
    (ht : t.Prime) (hq : q.Prime) (hqt : q < t)
    (hcube : t ^ 3 ≤ squareRootEndpoint R)
    (hcDefect : c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
      t (squareRootEndpoint R) q) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource q t c) +
      lowWheelFullTaggedPhysicalWeight
        (lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoSecondBoundaryFullFaceSource q t c)) = 0 := by
  exact squareRootLowPrimeGoSecondBoundaryFullFaceSource_mate_cancel
    hR ht hq hqt hcube hcDefect

/-! ## Exact identification of the response-forest exit mass -/

/-- For every processed cutoff below the root, the response forest's born
frontier is exactly the `BornExit` carrier with the same child Möbius weight. -/
theorem squareRootLowPrimeBornFrontierChildMass_re_eq_bornExitBoundaryMassReal_of_lt
    {R K U : ℕ} (hUR : U < R) :
    (squareRootLowPrimeBornFrontierChildMass R K U).re =
      squareRootLowPrimeBornExitBoundaryMassReal R K U := by
  rw [squareRootLowPrimeBornNoSuccessorAtoms_eq_frontier hUR]
  unfold squareRootLowPrimeBornFrontierChildMass
    squareRootLowPrimeBornExitBoundaryMassReal
  simp [canonicalMoebiusWeight]

/-- At the canonical cutoff the response forest's born frontier is exactly the
`BornExit` carrier, with the same child Möbius weight.  This is an equality of
signed masses, not merely the previously compiled cardinality comparison. -/
theorem squareRootLowPrimeBornFrontierChildMass_re_eq_bornExitBoundaryMassReal
    {R K : ℕ} (hR : 2 ≤ R) :
    (squareRootLowPrimeBornFrontierChildMass R K
        (squareRootBornPostTailLowPrimeCutoff R)).re =
      squareRootLowPrimeBornExitBoundaryMassReal R K
        (squareRootBornPostTailLowPrimeCutoff R) := by
  have hcut : squareRootBornPostTailLowPrimeCutoff R < R := by
    unfold squareRootBornPostTailLowPrimeCutoff
    have hsqrtPos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 (by omega)
    omega
  rw [squareRootLowPrimeBornNoSuccessorAtoms_eq_frontier hcut]
  unfold squareRootLowPrimeBornFrontierChildMass
    squareRootLowPrimeBornExitBoundaryMassReal
  simp [canonicalMoebiusWeight]

/-- **Response-forest elimination of BornExit.**

After the complete response-forest involution, the born frontier is already
the `BornExit` mass on the target side, so it cancels from the mass-transfer
equation.  What remains is one exact signed Euler-characteristic seam between
the initial shallow state and the response root/post-root terms:

`T(K) - RootCofactor + OwnedCofactor + PostRootChild = 1 - V + RootEquality`.

No norm, cardinality bound, or asymptotic input occurs. -/
theorem squareRootLowPrimeMassTransfer_iff_responseForestRootShallowIdentity
    {R K j U : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R) :
    (squareRootLowPrimeRunningImbalanceReal R K j U =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) ↔
      (squareRootLowPrimeRunningImbalanceReal R K j K -
          (squareRootLowPrimeResponseRootCofactorMass R K U).re +
          (squareRootLowPrimeOwnedResponseCofactorMass R K U).re +
          (squareRootLowPrimePostRootChildMass R K U).re =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) := by
  have hforest :
      squareRootLowPrimeRunningImbalanceReal R K j K -
          squareRootLowPrimeRunningImbalanceReal R K j U =
        (squareRootLowPrimeResponseRootCofactorMass R K U).re -
          (squareRootLowPrimeOwnedResponseCofactorMass R K U).re -
          (squareRootLowPrimeBornFrontierChildMass R K U).re -
          (squareRootLowPrimePostRootChildMass R K U).re := by
    simpa using squareRootLowPrimeRunningImbalanceReal_sub_eq_responseForestBoundary
      (R := R) (K := K) (j := j) (U := U) hR hK hKU hUR
  have hborn :
      (squareRootLowPrimeBornFrontierChildMass R K U).re =
        squareRootLowPrimeBornExitBoundaryMassReal R K U :=
    squareRootLowPrimeBornFrontierChildMass_re_eq_bornExitBoundaryMassReal_of_lt
      hUR
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **Child-Euler form of the kill-shot seam.**  The complete owned response
cofactor mass is the disjoint sum of response roots and incoming internal-born
children.  Substituting that exact partition removes both cofactor terms from
the preceding criterion.  Mass transfer is therefore equivalent to one
identity involving only the initial shallow mass and the two response-child
populations. -/
theorem squareRootLowPrimeMassTransfer_iff_responseChildEulerIdentity
    {R K j U : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R) :
    (squareRootLowPrimeRunningImbalanceReal R K j U =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) ↔
      (squareRootLowPrimeRunningImbalanceReal R K j K +
          (squareRootLowPrimeBornInternalChildMass R K U).re +
          (squareRootLowPrimePostRootChildMass R K U).re =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) := by
  rw [squareRootLowPrimeMassTransfer_iff_responseForestRootShallowIdentity
    hR hK hKU hUR]
  have hsplit := congrArg Complex.re
    (squareRootLowPrimeOwnedResponseCofactorMass_eq_root_add_internal
      (R := R) (K := K) (U := U) hUR)
  simp only [map_add] at hsplit
  constructor <;> intro h <;> linarith

/-- Same criterion with `T(K)` replaced by the literal complete shallow
creation carrier.  This is the finite Euler-characteristic statement left to
close: shallow creation roots plus all internal/post-root response children
must equal head minus packet plus the exact root-equality boundary. -/
theorem squareRootLowPrimeMassTransfer_iff_creationResponseChildEulerIdentity
    {R K j U : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R) :
    (squareRootLowPrimeRunningImbalanceReal R K j U =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) ↔
      ((∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j,
          squareRootLowPrimeCreationWeightReal x) +
          (squareRootLowPrimeBornInternalChildMass R K U).re +
          (squareRootLowPrimePostRootChildMass R K U).re =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) := by
  rw [squareRootLowPrimeMassTransfer_iff_responseChildEulerIdentity
    hR hK hKU hUR]
  rw [squareRootLowPrimeCreationCarrierExact_realWeight_sum]

/-! ## Stable-far entry into the reciprocal Euler coordinate -/

/-- **Exact far-wall / reciprocal-defect exchange rate.**  For an actual
stable-far triple `(q,(d,p))`, write `c=q*d`.  The complete raw partner column
over `c` is exactly `p*c` times the reciprocal physical defect at the far
prime `p`.  Thus the surviving far wall is not external to the reciprocal
Euler machinery: it enters through its native signed defect coordinate with
the exact scaling restored. -/
theorem lowWheelFarPrimeLowCofactorTriple_partnerColumn_eq_scaledReciprocalDefect
    {R : ℕ} {t : ℕ × (ℕ × ℕ)} (hR : 2 ≤ R)
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R) :
    (∑ _r ∈ squareRootCanonicalRoughPrimePartnerSet R (t.1 * t.2.1),
        canonicalMoebiusWeight (t.1 * t.2.1)) =
      (t.2.2 : ℂ) *
        ((t.1 * t.2.1 : ℕ) : ℂ) *
          squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
            R (t.1 * t.2.1) t.2.2 := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hqPrime, _hqR, hd1, hpPrime, _hpR, _hdsq, _hdq, _hcut⟩
  have hcpos : 0 < t.1 * t.2.1 :=
    Nat.mul_pos hqPrime.pos (by omega)
  have hraw :
      canonicalMoebiusWeight (t.1 * t.2.1) *
          (((squareRootCanonicalRoughFreshLossBoundary
              R (t.1 * t.2.1) t.2.2).card : ℂ) -
            ((squareRootCanonicalRoughFreshBirthBoundary
              R (t.1 * t.2.1) t.2.2).card : ℂ)) =
        ∑ _r ∈ squareRootCanonicalRoughPrimePartnerSet R (t.1 * t.2.1),
          canonicalMoebiusWeight (t.1 * t.2.1) :=
    lowWheelFarPrimeLowCofactorTriple_farPrimeRawBoundary_eq_partnerIncidenceSum
      hR ht
  have hscale :
      (t.2.2 : ℂ) *
          (((t.1 * t.2.1 : ℕ) : ℂ) *
            squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect
              R (t.1 * t.2.1) t.2.2) =
        canonicalMoebiusWeight (t.1 * t.2.1) *
          (((squareRootCanonicalRoughFreshLossBoundary
              R (t.1 * t.2.1) t.2.2).card : ℂ) -
            ((squareRootCanonicalRoughFreshBirthBoundary
              R (t.1 * t.2.1) t.2.2).card : ℂ)) := by
    simpa using
      (natCast_mul_cofactorWeightedReciprocalDefect_eq_rawBoundary
        (R := R) (c := t.1 * t.2.1) (p := t.2.2)
        (fun _ => (1 : ℂ)) hcpos hpPrime)
  rw [← hraw] at hscale
  simpa [mul_assoc] using hscale.symm

/-! ## Channel Euler characteristic -/

/-- The complete shallow creation mass splits exactly into the distinguished
head and the born/high channel roots. -/
theorem squareRootLowPrimeCreationCarrierExact_realWeight_sum_eq_head_add_channels
    (R K j : ℕ) :
    (∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j,
        squareRootLowPrimeCreationWeightReal x) =
      1 +
        (∑ x ∈ squareRootLowPrimeShallowBornCreationStates R K,
          squareRootLowPrimeCreationWeightReal x) +
        (∑ x ∈ squareRootLowPrimeShallowHighCreationStates R K j,
          squareRootLowPrimeCreationWeightReal x) := by
  unfold squareRootLowPrimeCreationCarrierExact
  rw [Finset.sum_insert
      (none_not_mem_squareRootLowPrimeCreationSeats R K j),
    Finset.sum_union
      (squareRootLowPrimeShallowBornCreationStates_disjoint_high R K j)]
  simp [squareRootLowPrimeCreationWeightReal,
    squareRootLowPrimeCreationWeightComplex]

/-- **Two-channel form of the remaining exact seam.**  After response-forest
cancellation and removal of the head, mass transfer is equivalent to the sum
of two native Euler characteristics:

* shallow born roots plus internal-born response children;
* shallow high roots plus post-root response children.

Their total must be exactly `-V + RootEquality`. -/
theorem squareRootLowPrimeMassTransfer_iff_twoChannelEulerIdentity
    {R K j U : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R) :
    (squareRootLowPrimeRunningImbalanceReal R K j U =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) ↔
      ((∑ x ∈ squareRootLowPrimeShallowBornCreationStates R K,
            squareRootLowPrimeCreationWeightReal x) +
          (squareRootLowPrimeBornInternalChildMass R K U).re +
        ((∑ x ∈ squareRootLowPrimeShallowHighCreationStates R K j,
            squareRootLowPrimeCreationWeightReal x) +
          (squareRootLowPrimePostRootChildMass R K U).re) =
        -((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) := by
  rw [squareRootLowPrimeMassTransfer_iff_creationResponseChildEulerIdentity
    hR hK hKU hUR,
    squareRootLowPrimeCreationCarrierExact_realWeight_sum_eq_head_add_channels]
  constructor <;> intro h <;> linarith

/-! ## Canonical unmatched-frontier normal form -/

/-- **Exact first-Othello normal form.**  Specializing the generic
creation/response cancellation to the canonical least eligible owner gives
the terminal running state as the signed mass of the two unmatched frontiers.
No cardinality or norm estimate enters. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_canonicalUnmatchedFrontiers
    {R K j U : ℕ} (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      (∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j \
          squareRootLowPrimeMatchedCreationStates R K j U,
        squareRootLowPrimeCreationWeightReal x) +
      ∑ z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U \
          creationResponseMatchedImage
            (squareRootLowPrimeMatchedCreationStates R K j U)
            (squareRootLowPrimeCanonicalCreationToResponse R K j U),
        squareRootLowPrimeResponseSeatWeightReal z := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_creation_add_responseSeats
    hR hK hKU]
  exact creationResponse_sum_eq_unmatchedFrontiers
    (squareRootLowPrimeCreationCarrierExact R K j)
    (squareRootLowPrimeMatchedCreationStates R K j U)
    (squareRootLowPrimeOwnedResponseSeatCarrier R K j U)
    (squareRootLowPrimeCanonicalCreationToResponse R K j U)
    squareRootLowPrimeCreationWeightReal
    squareRootLowPrimeResponseSeatWeightReal
    (by
      intro x hx
      exact (mem_squareRootLowPrimeMatchedCreationStates.mp hx).1)
    (by
      intro x hx
      exact squareRootLowPrimeCanonicalCreationToResponse_mem hx)
    squareRootLowPrimeCanonicalCreationToResponse_injOn
    (by
      intro x hx
      exact squareRootLowPrimeCanonicalCreationToResponse_weight_cancel hx)

/-- **Mass transfer in first-Othello coordinates.**  The repository's remaining
closed-form identity is equivalent to an equality involving only the two
canonical unmatched frontiers.  Thus all chronological terminal-width
bookkeeping may be discarded once the first Othello normal form is installed. -/
theorem squareRootLowPrimeMassTransfer_iff_canonicalUnmatchedFrontierIdentity
    {R K j U : ℕ} (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) :
    (squareRootLowPrimeRunningImbalanceReal R K j U =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) ↔
      ((∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j \
            squareRootLowPrimeMatchedCreationStates R K j U,
          squareRootLowPrimeCreationWeightReal x) +
        ∑ z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U \
            creationResponseMatchedImage
              (squareRootLowPrimeMatchedCreationStates R K j U)
              (squareRootLowPrimeCanonicalCreationToResponse R K j U),
          squareRootLowPrimeResponseSeatWeightReal z =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_canonicalUnmatchedFrontiers
    hR hK hKU]

/-- **Canonical unmatched-frontier acceptance theorem.**  At the terminal
cutoff, an exact identity on the two first-Othello unmatched frontiers alone
implies the packet-free mass-transfer identity.  This is the proof target after
discarding the chronological terminal-width coordinates. -/
theorem squareRootLowPrimePacketFree_of_canonicalUnmatchedFrontierIdentity
    {R K j : ℕ}
    (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hKU : K ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hunmatched :
      (∑ x ∈ squareRootLowPrimeCreationCarrierExact R K j \
            squareRootLowPrimeMatchedCreationStates R K j
              (squareRootBornPostTailLowPrimeCutoff R),
          squareRootLowPrimeCreationWeightReal x) +
        ∑ z ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j
              (squareRootBornPostTailLowPrimeCutoff R) \
            creationResponseMatchedImage
              (squareRootLowPrimeMatchedCreationStates R K j
                (squareRootBornPostTailLowPrimeCutoff R))
              (squareRootLowPrimeCanonicalCreationToResponse R K j
                (squareRootBornPostTailLowPrimeCutoff R)),
          squareRootLowPrimeResponseSeatWeightReal z =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K
            (squareRootBornPostTailLowPrimeCutoff R) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) :
    (squareRootMatchedBornSmoothTransport R).re +
        (squareRootBornPostTailAboveCutoffResponse R K j
          (squareRootBornPostTailLowPrimeCutoff R)).re =
      1 + squareRootLowPrimeBornExitBoundaryMassReal R K
            (squareRootBornPostTailLowPrimeCutoff R) +
        squareRootLowPrimeRootEqualityBoundaryMassReal R := by
  have hmass :
      squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K
            (squareRootBornPostTailLowPrimeCutoff R) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R :=
    (squareRootLowPrimeMassTransfer_iff_canonicalUnmatchedFrontierIdentity
      (R := R) (K := K) (j := j)
      (U := squareRootBornPostTailLowPrimeCutoff R) (by omega) hK hKU).2
      hunmatched
  exact (squareRootLowPrimeMassTransfer_iff_packetFree R K j
    (squareRootBornPostTailLowPrimeCutoff R) hR hK hKR hj).1 hmass

/-! ## Exact transfer between the two Othello fixed sets -/

/-- **Move order is algebraically irrelevant.**  The chronological canonical
Euler mate and the creation/response mate are sign-reversing involutions on
the same processed-seat carrier.  Hence their fixed populations have exactly
the same signed mass.  The first fixed population is the canonical terminal
frontier, so no estimate of the alternating paths is required. -/
theorem squareRootLowPrimeCanonicalTerminal_mass_eq_creationResponseStableMass
    {R K j U : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ x ∈ finiteOthelloStablePart
          (squareRootLowPrimeProcessedSeatCarrier R K j U)
          (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U),
        squareRootLowPrimeProcessedSeatWeightReal x := by
  let S := squareRootLowPrimeProcessedSeatCarrier R K j U
  have hstable := sum_finiteOthelloStablePart_eq_of_two_involutions
    S
    (squareRootLowPrimeProcessedSeatCanonicalMate R K j U)
    (squareRootLowPrimeProcessedSeatCreationResponseMate R K j U)
    squareRootLowPrimeProcessedSeatWeightReal
    (fun x hx => squareRootLowPrimeProcessedSeatCanonicalMate_mem
      R K j U hx)
    (fun x hx => squareRootLowPrimeProcessedSeatCanonicalMate_involutive
      R K j U hx)
    (fun x hx hne => squareRootLowPrimeProcessedSeatCanonicalMate_weight_neg
      R K j U hx hne)
    (fun x hx => squareRootLowPrimeProcessedSeatCreationResponseMate_mem
      hR hK hKU hx)
    (fun x hx => squareRootLowPrimeProcessedSeatCreationResponseMate_involutive
      hR hK hKU hx)
    (fun x hx hne => squareRootLowPrimeProcessedSeatCreationResponseMate_weight_neg
      hR hK hKU hx hne)
  have hcanon :
      finiteOthelloStablePart S
          (squareRootLowPrimeProcessedSeatCanonicalMate R K j U) =
        squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U := by
    simpa [S, finiteOthelloStablePart, signMatchingFixedPart] using
      signMatchingFixedPart_processedSeatCanonicalMate_eq_terminalFrontier
        R K j U
  rw [hcanon] at hstable
  exact hstable

/-! ## Exact birth-growth conservation -/

/-- The combined response is born mass plus honest high response, so every
change along two owner children satisfies an exact integer conservation law:
born growth = combined-response growth + honest-high loss.

This is the equality behind the earlier one-sided re-entry charge. -/
theorem squareRootLowPrimeResponse_birthGrowth_eq_combinedGrowth_add_highLoss
    (R K j p q c : ℕ) :
    (squareRootBornPartnerCount R (q * c) : ℤ) -
        (squareRootBornPartnerCount R (p * c) : ℤ) =
      ((squareRootLowPrimeCombinedFreshResponse R K j (q * c) : ℕ) : ℤ) -
          ((squareRootLowPrimeCombinedFreshResponse R K j (p * c) : ℕ) : ℤ) +
        (((squareRootLowPrimeHonestHighResponse R K j (p * c) : ℕ) : ℤ) -
          ((squareRootLowPrimeHonestHighResponse R K j (q * c) : ℕ) : ℤ)) := by
  rw [squareRootLowPrimeCombinedFreshResponse_eq_born_add_honestHigh,
    squareRootLowPrimeCombinedFreshResponse_eq_born_add_honestHigh]
  push_cast
  ring

/-- Under the usual owner ordering the honest-high loss is nonnegative. -/
theorem squareRootLowPrimeResponse_highLoss_nonneg
    {R K j p q c : ℕ} (hc : 0 < c) (hp : 0 < p) (hpq : p < q) :
    (0 : ℤ) ≤
      ((squareRootLowPrimeHonestHighResponse R K j (p * c) : ℕ) : ℤ) -
        ((squareRootLowPrimeHonestHighResponse R K j (q * c) : ℕ) : ℤ) := by
  have hpc : 0 < p * c := Nat.mul_pos hp hc
  have hpqmul : p * c ≤ q * c :=
    Nat.mul_le_mul (Nat.le_of_lt hpq) (le_refl c)
  have hmono := squareRootLowPrimeHonestHighResponse_antitone
    (R := R) (K := K) (j := j) hpc hpqmul
  omega

/-! ## Re-entry closes inside the response forest -/

/-- **A scheduled non-born re-entry is already a response-forest event.**
The newborn prime supplied by the re-entry theorem is a literal born response
atom over the re-entered cofactor `q*c`.  It is therefore either internal to
the processed prime interval, where the response-forest Othello involution
cancels it against its arithmetic child, or it has crossed the owner cutoff and
is literally a `BornNoSuccessor` / BornExit atom.

This route has no Go cube hypothesis. -/
theorem squareRootLowPrimeNonBornFalloutScheduledReentry_birthAtom_internal_or_exit
    {R K j U p q c s : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hc : 0 < c)
    (hp : p.Prime)
    (hqSet : q ∈ squareRootLowPrimeFreshPrimeSet K U)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hqAlive : s < squareRootLowPrimeCombinedFreshResponse R K j (q * c)) :
    ∃ t,
      t.Prime ∧ q < t ∧ p * c < t ∧
        ((q * c, t) ∈ squareRootLowPrimeBornInternalAtoms R K U ∨
          (q * c, t) ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U) := by
  have hqData := Finset.mem_filter.mp hqSet
  have hqPrime : q.Prime := hqData.2
  have hqIoc := Finset.mem_Ioc.mp hqData.1
  have hKq : K < q := hqIoc.1
  have hqU : q ≤ U := hqIoc.2
  obtain ⟨t, htBirth, hqt, hpct⟩ :=
    squareRootLowPrimeNonBornFalloutReentry_birthWitness
      (by omega) hc hp hqPrime hrough hpq hpU hUR hs hnb hfall hqAlive
  have htBorn : t ∈ squareRootBornPartnerSet R (q * c) :=
    (mem_squareRootBornPartnerBirthBoundary.mp htBirth).1
  have htData := Finset.mem_filter.mp htBorn
  have htPrime : t.Prime := htData.2.1
  have hqcX : q * c ≤ squareRootEndpoint R := by
    have hprod : (q * c) * t ≤ squareRootEndpoint R :=
      htData.2.2.2.2
    calc
      q * c = (q * c) * 1 := by simp
      _ ≤ (q * c) * t := Nat.mul_le_mul_left (q * c) (by omega)
      _ ≤ squareRootEndpoint R := hprod
  have hparent :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
    (mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall).1
  have hseat : (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
  have hcProcessed :
      c ∈ squareRootLowPrimeProcessedSignedCofactors R U :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hseat).1
  have hcMuNe : μ c ≠ 0 :=
    (Finset.mem_filter.mp hcProcessed).2.2
  have hsqC : Squarefree c :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hcMuNe
  have hqRough : canonicalLargestPrimeFactor c < q :=
    hrough.trans hpq
  have hqFresh : ¬ q ∣ c :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hc hqPrime hqRough
  have hcop : Nat.Coprime q c :=
    (hqPrime.coprime_iff_not_dvd).2 hqFresh
  have hsqQC : Squarefree (q * c) :=
    (Nat.squarefree_mul hcop).2 ⟨hqPrime.squarefree, hsqC⟩
  have hmuQC : μ (q * c) ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsqQC
  have hlpfQC : canonicalLargestPrimeFactor (q * c) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hqPrime hqRough
  have hqcProcessed :
      q * c ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
    unfold squareRootLowPrimeProcessedSignedCofactors
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hqPrime.pos hc, hqcX⟩, ?_, hmuQC⟩
    simpa [hlpfQC] using hqU
  have hqcSeat :
      (q * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hqcProcessed, hqAlive⟩
  have hqcCarrier :
      some (q * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
    unfold squareRootLowPrimeProcessedSeatCarrier
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_image.mpr ⟨(q * c, s), hqcSeat, rfl⟩))
  have hdeep : K < canonicalLargestPrimeFactor (q * c) := by
    simpa [hlpfQC] using hKq
  have hownedSeat :
      (q * c, s) ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeat_mem_ownedResponseSeatCarrier_of_deep
      hK hqcCarrier hdeep
  have hownedSigned :
      q * c ∈ squareRootLowPrimeOwnedSignedCofactors R K U :=
    (mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff.mp hownedSeat).1
  have htDeep :
      t ∈ squareRootLowPrimeDeepPartnerSet R (q * c) := by
    unfold squareRootLowPrimeDeepPartnerSet
    exact Finset.mem_union.mpr (Or.inl htBorn)
  have hAtom :
      (q * c, t) ∈ squareRootLowPrimeOwnedResponseAtoms R K U :=
    mem_squareRootLowPrimeOwnedResponseAtoms_iff.mpr
      ⟨hownedSigned, htDeep⟩
  have hBornResponse :
      (q * c, t) ∈ squareRootLowPrimeBornResponseAtoms R K U :=
    mem_squareRootLowPrimeBornResponseAtoms.mpr ⟨hAtom, htBorn⟩
  have hcut : squareRootBornPostTailLowPrimeCutoff R < R := by
    unfold squareRootBornPostTailLowPrimeCutoff
    have hsqrtPos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 (by omega)
    omega
  have hURlt : U < R := lt_of_le_of_lt hUR hcut
  refine ⟨t, htPrime, hqt, hpct, ?_⟩
  by_cases htU : t ≤ U
  · exact Or.inl
      (mem_squareRootLowPrimeBornInternalAtoms.mpr
        ⟨hAtom, htBorn, htU⟩)
  · right
    rw [squareRootLowPrimeBornNoSuccessorAtoms_eq_frontier hURlt]
    exact mem_squareRootLowPrimeBornFrontierAtoms.mpr
      ⟨hAtom, htBorn, Nat.lt_of_not_ge htU⟩


/-- An internal born response atom is not residual: the response-forest
Othello mate sends it to its literal arithmetic child, and the two tagged
weights cancel pointwise. -/
theorem squareRootLowPrimeBornInternalAtom_responseForest_cancel
    {R K U : ℕ} (hUR : U < R) {a : ℕ × ℕ}
    (ha : a ∈ squareRootLowPrimeBornInternalAtoms R K U) :
    squareRootLowPrimeResponseForestOthelloMate R K U (Sum.inl a) =
        Sum.inr (squareRootLowPrimeBadAtomChild a) ∧
      squareRootLowPrimeResponseForestOthelloWeight (Sum.inl a) +
        squareRootLowPrimeResponseForestOthelloWeight
          (squareRootLowPrimeResponseForestOthelloMate R K U (Sum.inl a)) = 0 := by
  have hmate :
      squareRootLowPrimeResponseForestOthelloMate R K U (Sum.inl a) =
        Sum.inr (squareRootLowPrimeBadAtomChild a) := by
    simp [squareRootLowPrimeResponseForestOthelloMate,
      creationResponseOthelloMate, ha]
  have hne :
      squareRootLowPrimeResponseForestOthelloMate R K U (Sum.inl a) ≠
        Sum.inl a := by
    rw [hmate]
    simp
  refine ⟨hmate, ?_⟩
  rw [squareRootLowPrimeResponseForestOthelloMate_weight_neg hUR
    (Sum.inl a) hne]
  abel

/-! ## Exhaustive dynamic split -/

/-- No later same-seat re-entry after the first failed owner.  Every later
processed prime has response fibre too short to recover the inherited seat. -/
def squareRootLowPrimeNoLaterSeatReentry
    (R K j U p c s : ℕ) : Prop :=
  ∀ q ∈ squareRootLowPrimeFreshPrimeSet K U, p < q →
    squareRootLowPrimeCombinedFreshResponse R K j (q * c) ≤ s

/-- Maximum response height attained by any later processed prime.
The empty later-prime set has ceiling zero via `Finset.sup`. -/
def squareRootLowPrimeLaterResponseCeiling
    (R K j U p c : ℕ) : ℕ :=
  (((squareRootLowPrimeFreshPrimeSet K U).filter fun q => p < q).image
      fun q => squareRootLowPrimeCombinedFreshResponse R K j (q * c)).sup id

/-- Every later response is bounded by the finite later-response ceiling. -/
theorem squareRootLowPrimeCombinedFreshResponse_le_laterResponseCeiling
    {R K j U p c q : ℕ}
    (hq : q ∈ squareRootLowPrimeFreshPrimeSet K U)
    (hpq : p < q) :
    squareRootLowPrimeCombinedFreshResponse R K j (q * c) ≤
      squareRootLowPrimeLaterResponseCeiling R K j U p c := by
  unfold squareRootLowPrimeLaterResponseCeiling
  apply Finset.le_sup (f := id)
  exact Finset.mem_image.mpr
    ⟨q, Finset.mem_filter.mpr ⟨hq, hpq⟩, rfl⟩

/-- The negative universal no-re-entry condition is exactly one positive
inequality against the finite response ceiling. -/
theorem squareRootLowPrimeNoLaterSeatReentry_iff_ceiling_le
    {R K j U p c s : ℕ} :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ↔
      squareRootLowPrimeLaterResponseCeiling R K j U p c ≤ s := by
  constructor
  · intro hno
    unfold squareRootLowPrimeLaterResponseCeiling
    apply Finset.sup_le
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
    rcases Finset.mem_filter.mp hq with ⟨hqSet, hpq⟩
    exact hno q hqSet hpq
  · intro hceil q hq hpq
    exact
      (squareRootLowPrimeCombinedFreshResponse_le_laterResponseCeiling
        hq hpq).trans hceil

/-- **Positive interval normal form for the terminal no-reentry branch.**
Once a non-born first-owner fallout has occurred, absence of every later
re-entry is equivalent to membership in one explicit finite seat interval. -/
theorem squareRootLowPrimeNonBornFallout_noLater_iff_mem_terminalResponseTail
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R)
    (hp : p.Prime) (hpU : p ≤ U)
    (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ↔
      s ∈ Finset.Ico
        (max (squareRootBornPartnerCount R c)
          (max
            (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
            (squareRootLowPrimeLaterResponseCeiling R K j U p c)))
        (squareRootLowPrimeCombinedFreshResponse R K j c) := by
  have htail :=
    squareRootLowPrimeNonBornFirstOwnerFalloff_is_responseTail
      hR hp hpU hUR hs hnb hfall
  have hborn : squareRootBornPartnerCount R c ≤ s :=
    Nat.le_of_not_gt hnb
  rw [Finset.mem_Ico]
  rw [squareRootLowPrimeNoLaterSeatReentry_iff_ceiling_le]
  constructor
  · intro hceil
    exact ⟨max_le hborn (max_le htail.1 hceil), htail.2⟩
  · intro h
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h.1)

/-! ## Exact terminal no-reentry fibre -/

/-- Exact lower endpoint of the non-born terminal response tail.  It enforces
all three constraints simultaneously: outside the born prefix, dead at the first
failed owner, and never alive at any later processed owner. -/
def squareRootLowPrimeTerminalNoReentryLower
    (R K j U p c : ℕ) : ℕ :=
  max (squareRootBornPartnerCount R c)
    (max
      (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
      (squareRootLowPrimeLaterResponseCeiling R K j U p c))

/-- Literal terminal seat interval after the born prefix, the first failed owner,
and every later response height have all been accounted for. -/
def squareRootLowPrimeTerminalNoReentrySeatIndices
    (R K j U p c : ℕ) : Finset ℕ :=
  Finset.Ico
    (squareRootLowPrimeTerminalNoReentryLower R K j U p c)
    (squareRootLowPrimeCombinedFreshResponse R K j c)

/-- Exact width of the non-born terminal no-reentry response tail. -/
def squareRootLowPrimeTerminalNoReentryWidth
    (R K j U p c : ℕ) : ℕ :=
  squareRootLowPrimeCombinedFreshResponse R K j c -
    squareRootLowPrimeTerminalNoReentryLower R K j U p c

@[simp] theorem card_squareRootLowPrimeTerminalNoReentrySeatIndices
    (R K j U p c : ℕ) :
    (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).card =
      squareRootLowPrimeTerminalNoReentryWidth R K j U p c := by
  simp [squareRootLowPrimeTerminalNoReentrySeatIndices,
    squareRootLowPrimeTerminalNoReentryWidth,
    squareRootLowPrimeTerminalNoReentryLower]

/-- One cofactor's terminal no-reentry unit-seat fibre. -/
def squareRootLowPrimeTerminalNoReentryFiber
    (R K j U p c : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).image
    fun s => some (c, s)

@[simp] theorem mem_squareRootLowPrimeTerminalNoReentryFiber
    {R K j U p c s : ℕ} :
    some (c, s) ∈ squareRootLowPrimeTerminalNoReentryFiber R K j U p c ↔
      s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c := by
  simp [squareRootLowPrimeTerminalNoReentryFiber]

/-- On an actual non-born first-owner fallout, the negative no-reentry
predicate is *literally* membership in the finite terminal fibre. -/
theorem squareRootLowPrimeNonBornFallout_noLater_iff_mem_terminalFiber
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R)
    (hp : p.Prime) (hpU : p ≤ U)
    (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ↔
      some (c, s) ∈ squareRootLowPrimeTerminalNoReentryFiber R K j U p c := by
  rw [mem_squareRootLowPrimeTerminalNoReentryFiber]
  unfold squareRootLowPrimeTerminalNoReentrySeatIndices
    squareRootLowPrimeTerminalNoReentryLower
  exact squareRootLowPrimeNonBornFallout_noLater_iff_mem_terminalResponseTail
    hR hp hpU hUR hs hnb hfall

/-- The terminal no-reentry fibre has no hidden multiplicity: its signed mass is
one native cofactor sign times the exact terminal response width. -/
theorem squareRootLowPrimeTerminalNoReentryFiber_weight_sum
    (R K j U p c : ℕ) :
    (∑ x ∈ squareRootLowPrimeTerminalNoReentryFiber R K j U p c,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeTerminalNoReentryWidth R K j U p c : ℝ) := by
  unfold squareRootLowPrimeTerminalNoReentryFiber
  calc
    (∑ x ∈
        (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).image
          (fun s => some (c, s)),
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c,
        squareRootLowPrimeProcessedSeatWeightReal (some (c, s)) := by
      apply Finset.sum_image
      intro a _ha b _hb hab
      simpa using hab
    _ = ∑ _s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c,
        ((-μ c : ℤ) : ℝ) := by
      rfl
    _ = ((-μ c : ℤ) : ℝ) *
        ((squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).card : ℝ) := by
      simp
      ring
    _ = ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeTerminalNoReentryWidth R K j U p c : ℝ) := by
      rw [card_squareRootLowPrimeTerminalNoReentrySeatIndices]



/-! ## Exact forest/telescope normal form -/

/-- **Exact global response cancellation before any estimate.**
The whole running-state change across the processed prime interval is the real
part of the response-forest stable boundary. Internal born edges have already
cancelled algebraically; only response roots, complete cofactor mass, BornExit
frontier mass, and post-root ancestry-root mass remain. -/
theorem squareRootLowPrimeRunningImbalanceReal_sub_eq_responseForestBoundary
    {R K j U : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U) (hUR : U < R) :
    squareRootLowPrimeRunningImbalanceReal R K j K -
        squareRootLowPrimeRunningImbalanceReal R K j U =
      (squareRootLowPrimeResponseRootCofactorMass R K U -
        squareRootLowPrimeOwnedResponseCofactorMass R K U -
          squareRootLowPrimeBornFrontierChildMass R K U -
            squareRootLowPrimePostRootChildMass R K U).re := by
  rw [squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
    hK hKU]
  have h := congrArg Complex.re
    (squareRootLowPrimeFreshIncrement_sum_eq_responseForestBoundary
      (R := R) (K := K) (j := j) (U := U) hR hUR)
  simpa [squareRootLowPrimeFreshIncrementReal] using h

/-! ## Global terminal no-reentry ledger -/


/-- If a state falls out at the first scheduled prime strictly above its
canonical largest prime, then the static intrinsic-owner scan returns exactly
that prime.  Earlier listed coordinates cannot be canonical fallout owners
because they lie at or below the largest-prime threshold. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_firstOwnerAbove_of_falloff
    {ps : List ℕ} {S : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState} {p : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove ps
      (canonicalLargestPrimeFactor
        (squareRootLowPrimeProcessedStateCofactor x)) = some p)
    (hfall : x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = some p := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, hpre, _hrough⟩
  have hpreNo :
      ∀ q ∈ pre,
        x ∉ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S q := by
    intro q hq hqFall
    rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hqFall with
      ⟨_hxS, _hxHead, _hqFresh, _hqMissing, hqRough⟩
    exact (Nat.not_lt_of_ge (hpre q hq)) hqRough
  rw [hsplit]
  induction pre with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner, hfall]
  | cons q qs ih =>
      have hqNo :
          x ∉ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S q :=
        hpreNo q (by simp)
      have hrest :
          ∀ r ∈ qs,
            x ∉ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S r := by
        intro r hr
        exact hpreNo r (by simp [hr])
      simp only [List.cons_append,
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwner, if_neg hqNo]
      exact ih hrest

/-- On an actual assigned terminal, the intrinsic owner is therefore the
cofactor-level first eligible owner.  This recovers the cofactor-first picture
after terminal survival has been imposed. -/
theorem squareRootLowPrimeCanonicalAssigned_intrinsicFirstOwner_eq_firstOwnerAbove
    {R K j U c s p : ℕ}
    (hx : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (some (c, s)) = some p := by
  have hxTerminal :
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U :=
    (Finset.mem_sdiff.mp hx).1
  have hfall :=
    squareRootLowPrimeProcessedSeatCanonicalTerminal_firstOwnerAbove_mem_falloff
      hxTerminal (by simp) hfirst
  exact
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_firstOwnerAbove_of_falloff
      hfirst hfall


/-- On an assigned terminal, the intrinsic chronological owner is exactly the
first scheduled prime above the cofactor's canonical largest prime. -/
theorem squareRootLowPrimeCanonicalAssigned_firstOwnerAbove_eq_of_intrinsicOwner
    {R K j U c s p : ℕ}
    (hx : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U)
    (howner :
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (some (c, s)) = some p) :
    squareRootLowPrimeFirstOwnerAbove
        (squareRootLowPrimeFreshPrimeList K U)
        (canonicalLargestPrimeFactor c) = some p := by
  have hxData := Finset.mem_sdiff.mp hx
  have hxTerminal := hxData.1
  have hxNotHead := hxData.2
  cases hfirst :
      squareRootLowPrimeFirstOwnerAbove
        (squareRootLowPrimeFreshPrimeList K U)
        (canonicalLargestPrimeFactor c) with
  | none =>
      exfalso
      apply hxNotHead
      apply Finset.mem_filter.mpr
      exact ⟨hxTerminal, Or.inr hfirst⟩
  | some q =>
      have hqOwner :
          squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
              (squareRootLowPrimeFreshPrimeList K U)
              (squareRootLowPrimeProcessedSeatCarrier R K j U)
              (some (c, s)) = some q :=
        squareRootLowPrimeCanonicalAssigned_intrinsicFirstOwner_eq_firstOwnerAbove
          hx hfirst
      rw [howner] at hqOwner
      have hpq : p = q := Option.some.inj hqOwner
      simpa [hpq] using hfirst

/-- **A shallow genuine NoLater terminal is fixed by the first
creation/response Othello matching.**  Its lower terminal endpoint already
dominates the first-owner response and every later response ceiling, so no
fresh prime can carry the corresponding shallow creation seat into the owned
response carrier. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentry_shallow_not_matchedCreation
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R) (hKU : K ≤ U)
    (hshallow : canonicalLargestPrimeFactor c ≤ K)
    (hs : s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
      R K j U p c) :
    squareRootLowPrimeProcessedShallowSeatToCreation R (c, s) ∉
      squareRootLowPrimeMatchedCreationStates R K j U := by
  classical
  have hsData :=
    squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data hs
  have hsTerminal := hsData.1
  have hxAssigned := hsData.2.1
  have hIntrinsic := hsData.2.2
  have hfirst :=
    squareRootLowPrimeCanonicalAssigned_firstOwnerAbove_eq_of_intrinsicOwner
      hxAssigned hIntrinsic
  have hbounds :
      max (squareRootBornPartnerCount R c)
          (max
            (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
            (squareRootLowPrimeLaterResponseCeiling R K j U p c)) ≤ s ∧
        s < squareRootLowPrimeCombinedFreshResponse R K j c := by
    simpa [squareRootLowPrimeTerminalNoReentrySeatIndices,
      squareRootLowPrimeTerminalNoReentryLower] using hsTerminal
  have hbornLe : squareRootBornPartnerCount R c ≤ s :=
    (le_max_left _ _).trans hbounds.1
  have hinner :
      max
          (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
          (squareRootLowPrimeLaterResponseCeiling R K j U p c) ≤ s :=
    (le_max_right _ _).trans hbounds.1
  have hpChildLe :
      squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s :=
    (le_max_left _ _).trans hinner
  have hceilingLe :
      squareRootLowPrimeLaterResponseCeiling R K j U p c ≤ s :=
    (le_max_right _ _).trans hinner
  have hnotBorn : ¬ s < squareRootBornPartnerCount R c := by omega
  let x := squareRootLowPrimeProcessedShallowSeatToCreation R (c, s)
  have hxCof :
      squareRootLowPrimeCreationStateCofactor x = c := by
    simp [x, squareRootLowPrimeProcessedShallowSeatToCreation, hnotBorn,
      squareRootLowPrimeCreationStateCofactor]
  have hxSeat :
      squareRootLowPrimeCreationStateAbsoluteSeat R x = s := by
    simp [x, squareRootLowPrimeProcessedShallowSeatToCreation, hnotBorn,
      squareRootLowPrimeCreationStateAbsoluteSeat, Nat.add_sub_of_le hbornLe]
  intro hmatched
  have hmData := mem_squareRootLowPrimeMatchedCreationStates.mp hmatched
  obtain ⟨q, hqEligible⟩ := hmData.2.2
  have hqData :=
    mem_squareRootLowPrimeEligibleResponseOwners.mp hqEligible
  have hqSet := hqData.1
  have hqSeat := hqData.2
  have hqAliveRaw :=
    (mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff.mp hqSeat).2
  have hqAlive :
      s < squareRootLowPrimeCombinedFreshResponse R K j (q * c) := by
    simpa [x, hxCof, hxSeat] using hqAliveRaw
  have hqList : q ∈ squareRootLowPrimeFreshPrimeList K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hqSet
  have hKq : K < q := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hqSet).1).1
  have hlpfq : canonicalLargestPrimeFactor c < q := by omega
  have hpqLe :=
    squareRootLowPrimeFirstOwnerAbove_le_of_mem hfirst hqList hlpfq
  by_cases hpqEq : p = q
  · subst q
    omega
  · have hpq : p < q := by omega
    have hqCeiling :=
      squareRootLowPrimeCombinedFreshResponse_le_laterResponseCeiling
        hqSet hpq
    omega

/-- Seat-level no-reentry indices after imposing the actual terminal target and
the unique intrinsic first-owner assignment.  The first owner is a property of
the processed seat, not of the cofactor alone. -/
def squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
    (R K j U p c : ℕ) : Finset ℕ :=
  (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).filter fun s =>
    some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U ∧
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (some (c, s)) = some p

/-- Exact multiplicity of one first-owner/cofactor terminal no-reentry slice. -/
def squareRootLowPrimeFirstOwnerTerminalNoReentryWidth
    (R K j U p c : ℕ) : ℕ :=
  (squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
    R K j U p c).card

/-- Literal processed states in one disjoint first-owner/cofactor no-reentry
slice. -/
def squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
    (R K j U p c : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
      R K j U p c).image fun s => some (c, s)

@[simp] theorem mem_squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
    {R K j U p c s : ℕ} :
    some (c, s) ∈
        squareRootLowPrimeFirstOwnerTerminalNoReentryFiber R K j U p c ↔
      s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
        R K j U p c := by
  simp [squareRootLowPrimeFirstOwnerTerminalNoReentryFiber]

/-- Membership exposes both pieces that make the global ledger canonical:
actual terminal membership and the unique seat-level first owner. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data
    {R K j U p c s : ℕ}
    (hs : s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
      R K j U p c) :
    s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c ∧
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U ∧
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (some (c, s)) = some p := by
  simpa [squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices] using
    Finset.mem_filter.mp hs

/-- Each first-owner/cofactor no-reentry slice has one native Möbius sign, so
its exact signed mass is sign times width. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_weight_sum
    (R K j U p c : ℕ) :
    (∑ x ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
        R K j U p c, squareRootLowPrimeProcessedSeatWeightReal x) =
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeFirstOwnerTerminalNoReentryWidth
          R K j U p c : ℝ) := by
  unfold squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
    squareRootLowPrimeFirstOwnerTerminalNoReentryWidth
  calc
    (∑ x ∈
        (squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
          R K j U p c).image (fun s => some (c, s)),
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
          R K j U p c,
        squareRootLowPrimeProcessedSeatWeightReal (some (c, s)) := by
      apply Finset.sum_image
      intro a _ha b _hb hab
      simpa using hab
    _ = ∑ _s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
          R K j U p c, ((-μ c : ℤ) : ℝ) := by
      rfl
    _ = ((-μ c : ℤ) : ℝ) *
        ((squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
          R K j U p c).card : ℝ) := by
      simp
      ring

/-- Two terminal no-reentry fibres with different first-owner/cofactor labels
are disjoint.  This is the global no-double-counting statement that the
cofactor-only ledger lacks. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_disjoint
    {R K j U p q c d : ℕ} (hpcqd : (p, c) ≠ (q, d)) :
    Disjoint
      (squareRootLowPrimeFirstOwnerTerminalNoReentryFiber R K j U p c)
      (squareRootLowPrimeFirstOwnerTerminalNoReentryFiber R K j U q d) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨t, ht, hEq⟩
  have hpair : (c, s) = (d, t) := Option.some.inj hEq
  have hcd : c = d := congrArg Prod.fst hpair
  have hst : s = t := congrArg Prod.snd hpair
  subst d
  subst t
  have hsData :=
    squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data hs
  have htData :=
    squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data ht
  have hpq : p = q := Option.some.inj (hsData.2.2.symm.trans htData.2.2)
  exact hpcqd (by simp [hpq])

/-- Index set for the global no-reentry ledger. -/
def squareRootLowPrimeFirstOwnerTerminalNoReentryIndex
    (R K j U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeFreshPrimeList K U).toFinset ×ˢ
    squareRootLowPrimeProcessedSignedCofactors R U

/-- The genuine global terminal no-reentry ledger.  It is indexed by the
seat-level first owner and cofactor; summing only over cofactors would merge
distinct chronological fallout layers. -/
def squareRootLowPrimeGlobalTerminalNoReentryLedger
    (R K j U : ℕ) : ℝ :=
  ∑ pc ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryIndex R K j U,
    ((-μ pc.2 : ℤ) : ℝ) *
      (squareRootLowPrimeFirstOwnerTerminalNoReentryWidth
        R K j U pc.1 pc.2 : ℝ)

/-- A genuine labelled no-reentry seat can never be a first-owner square-wall
cell. Product-wall assigned terminals are purely born, whereas this carrier
starts after the born prefix. Hence every NoLater fibre is an inside-square
response-tail fibre. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentry_product_le_endpoint
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hs : s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
      R K j U p c) :
    p * c ≤ squareRootEndpoint R := by
  have hsData :=
    squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data hs
  have hsTerm := hsData.1
  have hxAssigned := hsData.2.1
  have hIntrinsic := hsData.2.2
  have hbornLe : squareRootBornPartnerCount R c ≤ s := by
    have hmem := Finset.mem_Ico.mp hsTerm
    exact le_trans (le_max_left _ _) hmem.1
  have hxTerminal :
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U :=
    (Finset.mem_sdiff.mp hxAssigned).1
  have hcovered :=
    squareRootLowPrimeProcessedSeatCanonicalAssigned_covered hxAssigned
  rcases hcovered with ⟨q, _hqList, hqOwner⟩
  have hpq : p = q := by
    have hpOwner := hIntrinsic
    rw [hqOwner] at hpOwner
    exact Option.some.inj hpOwner
  subst q
  have hfirst :
      squareRootLowPrimeFirstOwnerAbove
          (squareRootLowPrimeFreshPrimeList K U)
          (canonicalLargestPrimeFactor c) = some p := by
    by_contra hne
    cases hopt : squareRootLowPrimeFirstOwnerAbove
        (squareRootLowPrimeFreshPrimeList K U)
        (canonicalLargestPrimeFactor c) with
    | none =>
        have hhead : some (c, s) ∈
            squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U := by
          apply Finset.mem_filter.mpr
          exact ⟨hxTerminal, Or.inr hopt⟩
        exact (Finset.mem_sdiff.mp hxAssigned).2 hhead
    | some r =>
        have hrFall :
            some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
              (squareRootLowPrimeProcessedSeatCarrier R K j U) r :=
          squareRootLowPrimeProcessedSeatCanonicalTerminal_firstOwnerAbove_mem_falloff
            hxTerminal (by simp) hopt
        have hrIntrinsic :
            squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
                (squareRootLowPrimeFreshPrimeList K U)
                (squareRootLowPrimeProcessedSeatCarrier R K j U)
                (some (c, s)) = some r :=
          squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_firstOwnerAbove_of_falloff
            hopt hrFall
        rw [hIntrinsic] at hrIntrinsic
        have : p = r := Option.some.inj hrIntrinsic
        exact hne (by simpa [this] using hopt)
  by_contra hwallNot
  have hwall : squareRootEndpoint R < p * c := Nat.lt_of_not_ge hwallNot
  have hborn : s < squareRootBornPartnerCount R c :=
    (squareRootLowPrimeCanonicalAssigned_wall_bornSeat_oldPartner
      hR hUR hxAssigned hfirst hwall).1
  omega


/-! ## Shallow NoLater pushforward to the first Othello frontier -/

/-- Shallow seat coordinates occurring in the genuine global NoLater carrier. -/
def squareRootLowPrimeGlobalTerminalNoReentryShallowSeatAtoms
    (R K j U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeProcessedSeatAtoms R K j U).filter fun z =>
    some z ∈ squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U ∧
      canonicalLargestPrimeFactor z.1 ≤ K

/-- Global shallow NoLater membership reduces to one labelled first-owner
NoLater fibre, so the corresponding shallow creation state is unmatched. -/
theorem squareRootLowPrimeGlobalTerminalNoReentry_shallow_not_matchedCreation
    {R K j U c s : ℕ}
    (hR : 1 ≤ R) (hKU : K ≤ U)
    (hx : some (c, s) ∈
      squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U)
    (hshallow : canonicalLargestPrimeFactor c ≤ K) :
    squareRootLowPrimeProcessedShallowSeatToCreation R (c, s) ∉
      squareRootLowPrimeMatchedCreationStates R K j U := by
  rcases Finset.mem_biUnion.mp hx with ⟨pc, _hpc, hxpc⟩
  rcases pc with ⟨p, d⟩
  rcases Finset.mem_image.mp hxpc with ⟨t, ht, hEq⟩
  have hPair : (d, t) = (c, s) := Option.some.inj hEq
  have hc : d = c := congrArg Prod.fst hPair
  have hs : t = s := congrArg Prod.snd hPair
  subst d
  subst t
  exact squareRootLowPrimeFirstOwnerTerminalNoReentry_shallow_not_matchedCreation
    hR hKU hshallow ht

/-- **NoLater is literally stable for the first Othello move on the shallow
sector.**  The previous unmatched-creation theorem is therefore not merely a
set-theoretic exclusion: after transporting the absolute processed seat into
the creation/response coordinates, the first Othello involution fixes it
pointwise. -/
theorem squareRootLowPrimeGlobalTerminalNoReentry_shallow_creationResponse_fixed
    {R K j U c s : ℕ}
    (hR : 1 ≤ R) (hK : 1 ≤ K) (hKU : K ≤ U)
    (hx : some (c, s) ∈
      squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U)
    (hshallow : canonicalLargestPrimeFactor c ≤ K) :
    squareRootLowPrimeProcessedSeatCreationResponseMate R K j U
        (some (c, s)) = some (c, s) := by
  have hxAssigned :
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U :=
    squareRootLowPrimeGlobalTerminalNoReentryCarrier_subset_assigned
      R K j U hx
  have hxTerminal :
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U :=
    (Finset.mem_sdiff.mp hxAssigned).1
  have hxCarrier :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier_subset
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U) hxTerminal
  apply (squareRootLowPrimeProcessedSeatCreationResponseMate_shallow_eq_self_iff
    hR hK hKU hxCarrier hshallow).2
  exact squareRootLowPrimeGlobalTerminalNoReentry_shallow_not_matchedCreation
    hR hKU hx hshallow

/-- The shallow NoLater coordinate map is injective because the canonical
shallow creation tag restores the original absolute seat exactly. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryShallow_toCreation_injOn
    {R K j U : ℕ} (hR : 1 ≤ R) (hKU : K ≤ U) :
    Set.InjOn (squareRootLowPrimeProcessedShallowSeatToCreation R)
      (squareRootLowPrimeGlobalTerminalNoReentryShallowSeatAtoms R K j U) := by
  intro z hz w hw hEq
  have hzData := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
  have hwData := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
  have hzShallow :
      z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
      ⟨hzData.1, hzData.2.2⟩
  have hwShallow :
      w ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
      ⟨hwData.1, hwData.2.2⟩
  calc
    z = squareRootLowPrimeCreationToProcessedShallowSeat R
          (squareRootLowPrimeProcessedShallowSeatToCreation R z) :=
      (squareRootLowPrimeCreationToProcessedShallowSeat_toCreation
        hR hKU hzShallow).symm
    _ = squareRootLowPrimeCreationToProcessedShallowSeat R
          (squareRootLowPrimeProcessedShallowSeatToCreation R w) := by
      rw [hEq]
    _ = w :=
      squareRootLowPrimeCreationToProcessedShallowSeat_toCreation
        hR hKU hwShallow

/-- Literal image of the shallow NoLater block in the unmatched creation
frontier. -/
def squareRootLowPrimeGlobalTerminalNoReentryShallowCreationImage
    (R K j U : ℕ) : Finset SquareRootLowPrimeCreationState :=
  (squareRootLowPrimeGlobalTerminalNoReentryShallowSeatAtoms R K j U).image
    (squareRootLowPrimeProcessedShallowSeatToCreation R)

/-- Every image point is an actual creation state and is outside the matched
creation domain. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryShallowCreationImage_subset_unmatched
    {R K j U : ℕ} (hR : 1 ≤ R) (hKU : K ≤ U) :
    squareRootLowPrimeGlobalTerminalNoReentryShallowCreationImage R K j U ⊆
      squareRootLowPrimeCreationCarrierExact R K j \
        squareRootLowPrimeMatchedCreationStates R K j U := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
  have hzData := Finset.mem_filter.mp hz
  have hzShallow :
      z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
      ⟨hzData.1, hzData.2.2⟩
  have hxCreation :=
    squareRootLowPrimeProcessedShallowSeatToCreation_mem hR hKU hzShallow
  have hxCreation' :
      squareRootLowPrimeProcessedShallowSeatToCreation R z ∈
        squareRootLowPrimeCreationCarrierExact R K j :=
    (Finset.mem_erase.mp hxCreation).2
  have hnotMatched :=
    squareRootLowPrimeGlobalTerminalNoReentry_shallow_not_matchedCreation
      hR hKU hzData.2.1 hzData.2.2
  exact Finset.mem_sdiff.mpr ⟨hxCreation', hnotMatched⟩

/-- The shallow NoLater pushforward preserves the native signed mass exactly. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryShallowCreationImage_weight_sum
    {R K j U : ℕ} (hR : 1 ≤ R) (hKU : K ≤ U) :
    (∑ x ∈ squareRootLowPrimeGlobalTerminalNoReentryShallowCreationImage
        R K j U, squareRootLowPrimeCreationWeightReal x) =
      ∑ z ∈ squareRootLowPrimeGlobalTerminalNoReentryShallowSeatAtoms R K j U,
        squareRootLowPrimeProcessedSeatWeightReal (some z) := by
  unfold squareRootLowPrimeGlobalTerminalNoReentryShallowCreationImage
  rw [Finset.sum_image
    (squareRootLowPrimeGlobalTerminalNoReentryShallow_toCreation_injOn hR hKU)]
  apply Finset.sum_congr rfl
  intro z hz
  have hzData := Finset.mem_filter.mp hz
  have hzShallow :
      z ∈ squareRootLowPrimeProcessedShallowSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedShallowSeatAtoms.mpr
      ⟨hzData.1, hzData.2.2⟩
  let zz : ↥(squareRootLowPrimeProcessedShallowSeatAtoms R K j U) :=
    ⟨z, hzShallow⟩
  have hweight :=
    squareRootLowPrimeProcessedShallowSeatCreationEquiv_weight_eq
      hR hKU zz
  simpa [zz, squareRootLowPrimeProcessedShallowSeatCreationEquiv] using hweight

/-- The global ledger is literally the signed mass of its disjoint
first-owner/cofactor fibres. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryLedger_eq_fiberMass
    (R K j U : ℕ) :
    squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U =
      ∑ pc ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryIndex R K j U,
        ∑ x ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
          R K j U pc.1 pc.2,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  unfold squareRootLowPrimeGlobalTerminalNoReentryLedger
  apply Finset.sum_congr rfl
  intro pc _hpc
  rw [squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_weight_sum]


/-- Literal union of all genuine terminal no-reentry first-owner/cofactor
fibres.  Pairwise disjointness of the labelled fibres makes this a true carrier,
not merely a support upper bound. -/
def squareRootLowPrimeGlobalTerminalNoReentryCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeFirstOwnerTerminalNoReentryIndex R K j U).biUnion fun pc =>
    squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
      R K j U pc.1 pc.2

/-- The labelled fibre family used in the global carrier is pairwise disjoint. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_pairwiseDisjoint
    (R K j U : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeFirstOwnerTerminalNoReentryIndex R K j U))
      (fun pc => squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
        R K j U pc.1 pc.2) := by
  intro a _ha b _hb hab
  exact squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_disjoint hab

/-- The literal global no-reentry carrier has exactly the compiled ledger mass. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryCarrier_weight_sum
    (R K j U : ℕ) :
    (∑ x ∈ squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U := by
  unfold squareRootLowPrimeGlobalTerminalNoReentryCarrier
  rw [Finset.sum_biUnion
    (squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_pairwiseDisjoint
      R K j U)]
  exact (squareRootLowPrimeGlobalTerminalNoReentryLedger_eq_fiberMass
    R K j U).symm

/-- Every state in the global no-reentry carrier is an actual assigned
canonical terminal. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryCarrier_subset_assigned
    (R K j U : ℕ) :
    squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U ⊆
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨pc, _hpc, hxpc⟩
  rcases Finset.mem_image.mp hxpc with ⟨s, hs, rfl⟩
  exact
    (squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data hs).2.1

/-- The remaining assigned-terminal carrier after deleting genuine no-reentry
states.  This is the concrete population to which the response-forest/BornExit
classification must now be applied. -/
def squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U \
    squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U

/-- Exact signed partition of the assigned terminal population. -/
theorem squareRootLowPrimeCanonicalAssigned_weight_sum_eq_noReentry_add_complement
    (R K j U : ℕ) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U +
        ∑ x ∈ squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier
            R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  have hsub :=
    squareRootLowPrimeGlobalTerminalNoReentryCarrier_subset_assigned R K j U
  have hsplit := Finset.sum_sdiff hsub
    (f := squareRootLowPrimeProcessedSeatWeightReal)
  rw [squareRootLowPrimeGlobalTerminalNoReentryCarrier_weight_sum] at hsplit
  simpa [squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier,
    add_comm] using hsplit.symm


/-- Born-range part of the literal complement carrier. -/
def squareRootLowPrimeBornComplementCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier R K j U).filter
    fun x => match x with
      | none => False
      | some z => z.2 < squareRootBornPartnerCount R z.1

/-- Non-born part of the literal complement carrier.  The theorem below shows
every such state is necessarily a genuine re-entry state. -/
def squareRootLowPrimeNonBornReentryCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier R K j U).filter
    fun x => ¬ (match x with
      | none => False
      | some z => z.2 < squareRootBornPartnerCount R z.1)

/-- Exact signed split of the complement into born-range and non-born pieces. -/
theorem squareRootLowPrimeComplementCarrier_weight_sum_eq_born_add_nonBorn
    (R K j U : ℕ) :
    (∑ x ∈ squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      (∑ x ∈ squareRootLowPrimeBornComplementCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) +
      ∑ x ∈ squareRootLowPrimeNonBornReentryCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  unfold squareRootLowPrimeBornComplementCarrier
    squareRootLowPrimeNonBornReentryCarrier
  symm
  exact Finset.sum_filter_add_sum_filter_not
    (s := squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier R K j U)
    (p := fun x => match x with
      | none => False
      | some z => z.2 < squareRootBornPartnerCount R z.1)
    (f := squareRootLowPrimeProcessedSeatWeightReal)

/-- **Concrete complement classification.**  Every assigned-terminal state
outside the genuine no-reentry carrier is either still in the born prefix, or
its non-born first-owner fallout necessarily re-enters and is consumed by the
existing response forest (internally or at BornExit).

The NoLater alternative is impossible in the second branch: exact terminal
fibre membership would put the state back into the deleted global no-reentry
carrier. -/
theorem squareRootLowPrimeComplement_born_or_responseForestCancel_or_bornExit
    {R K j U c s : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K)
    (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hx : some (c, s) ∈
      squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier R K j U) :
    s < squareRootBornPartnerCount R c ∨
      ∃ p q t,
        squareRootLowPrimeFirstOwnerAbove
            (squareRootLowPrimeFreshPrimeList K U)
            (canonicalLargestPrimeFactor c) = some p ∧
        q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
        p < q ∧
        t.Prime ∧ q < t ∧ p * c < t ∧
          (((q * c, t) ∈ squareRootLowPrimeBornInternalAtoms R K U ∧
              squareRootLowPrimeResponseForestOthelloWeight
                  (Sum.inl (q * c, t)) +
                squareRootLowPrimeResponseForestOthelloWeight
                  (squareRootLowPrimeResponseForestOthelloMate R K U
                    (Sum.inl (q * c, t))) = 0) ∨
            (q * c, t) ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U) := by
  classical
  rcases Finset.mem_sdiff.mp hx with ⟨hxAssigned, hxNotNoLater⟩
  have hxTerminal :
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U :=
    (Finset.mem_sdiff.mp hxAssigned).1
  have hxNotHead :
      some (c, s) ∉
        squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U :=
    (Finset.mem_sdiff.mp hxAssigned).2
  let owner :=
    squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c)
  have hownerNe : owner ≠ none := by
    intro hnone
    apply hxNotHead
    apply Finset.mem_filter.mpr
    exact ⟨hxTerminal, Or.inr hnone⟩
  obtain ⟨p, hfirst⟩ : ∃ p, owner = some p := by
    cases h : owner with
    | none => exact (hownerNe h).elim
    | some p => exact ⟨p, h⟩
  have hfirst' :
      squareRootLowPrimeFirstOwnerAbove
          (squareRootLowPrimeFreshPrimeList K U)
          (canonicalLargestPrimeFactor c) = some p := by
    simpa [owner] using hfirst
  have hfall :
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
          (squareRootLowPrimeProcessedSeatCarrier R K j U) p :=
    squareRootLowPrimeProcessedSeatCanonicalTerminal_firstOwnerAbove_mem_falloff
      hxTerminal (by simp) hfirst'
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hxCarrier, _hxHead, _hpFresh, _hmissing, hrough⟩
  have hxAtom :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hxCarrier
  have hxAtomData := mem_squareRootLowPrimeProcessedSeatAtoms.mp hxAtom
  have hcSigned : c ∈ squareRootLowPrimeProcessedSignedCofactors R U :=
    hxAtomData.1
  have hs : s < squareRootLowPrimeCombinedFreshResponse R K j c :=
    hxAtomData.2
  have hcRange := (Finset.mem_filter.mp hcSigned).1
  have hcPos : 0 < c := by
    have hcOne := (Finset.mem_Icc.mp hcRange).1
    omega
  have hpList :=
    squareRootLowPrimeFirstOwnerAbove_mem_freshPrimeList hfirst'
  have hpSet : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hpList
  have hpData := Finset.mem_filter.mp hpSet
  have hpPrime : p.Prime := hpData.2
  have hpU : p ≤ U := (Finset.mem_Ioc.mp hpData.1).2
  by_cases hborn : s < squareRootBornPartnerCount R c
  · exact Or.inl hborn
  · right
    rcases squareRootLowPrimeNonBornFallout_noLater_or_responseForestCancel_or_bornExit
        hR hK hcPos hpPrime hrough hpU hUR hs hborn hfall with
      hno | hroute
    · have hxTerminalFiber :
          some (c, s) ∈
            squareRootLowPrimeTerminalNoReentryFiber R K j U p c :=
        (squareRootLowPrimeNonBornFallout_noLater_iff_mem_terminalFiber
          (by omega) hpPrime hpU hUR hs hborn hfall).mp hno
      have hsTerminal :
          s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c := by
        simpa using hxTerminalFiber
      have hIntrinsic :
          squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
              (squareRootLowPrimeFreshPrimeList K U)
              (squareRootLowPrimeProcessedSeatCarrier R K j U)
              (some (c, s)) = some p :=
        squareRootLowPrimeCanonicalAssigned_intrinsicFirstOwner_eq_firstOwnerAbove
          hxAssigned hfirst'
      have hsLabelled :
          s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
            R K j U p c := by
        apply Finset.mem_filter.mpr
        exact ⟨hsTerminal, hxAssigned, hIntrinsic⟩
      have hxLabelled :
          some (c, s) ∈
            squareRootLowPrimeFirstOwnerTerminalNoReentryFiber R K j U p c := by
        simpa using hsLabelled
      have hpc :
          (p, c) ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryIndex
            R K j U := by
        simp [squareRootLowPrimeFirstOwnerTerminalNoReentryIndex,
          hpList, hcSigned]
      apply hxNotNoLater
      apply Finset.mem_biUnion.mpr
      exact ⟨(p, c), hpc, hxLabelled⟩
    · rcases hroute with ⟨q, t, hq, hpq, ht, hqt, hpct, hclass⟩
      exact ⟨p, q, t, hfirst', hq, hpq, ht, hqt, hpct, hclass⟩

/-- Membership in the non-born complement is exactly the branch to which the
compiled complement classifier cannot return BornRange. -/
theorem squareRootLowPrimeNonBornReentryCarrier_routes
    {R K j U c s : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K)
    (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hx : some (c, s) ∈ squareRootLowPrimeNonBornReentryCarrier R K j U) :
    ∃ p q t,
      squareRootLowPrimeFirstOwnerAbove
          (squareRootLowPrimeFreshPrimeList K U)
          (canonicalLargestPrimeFactor c) = some p ∧
      q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
      p < q ∧
      t.Prime ∧ q < t ∧ p * c < t ∧
        (((q * c, t) ∈ squareRootLowPrimeBornInternalAtoms R K U ∧
            squareRootLowPrimeResponseForestOthelloWeight
                (Sum.inl (q * c, t)) +
              squareRootLowPrimeResponseForestOthelloWeight
                (squareRootLowPrimeResponseForestOthelloMate R K U
                  (Sum.inl (q * c, t))) = 0) ∨
          (q * c, t) ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U) := by
  rcases Finset.mem_filter.mp hx with ⟨hxComp, hNonBorn⟩
  rcases squareRootLowPrimeComplement_born_or_responseForestCancel_or_bornExit
      hR hK hUR hxComp with hBorn | hRoute
  · exact (hNonBorn hBorn).elim
  · exact hRoute

/-- The part of the exact intrinsic first-owner mass not belonging to genuine
terminal no-reentry fibres.  The response-forest layer identifies this
complement pointwise with already-existing born/boundary mechanisms; defining
it by subtraction keeps the global accounting exact before that identification
is assembled. -/
def squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger
    (R K j U : ℕ) : ℝ :=
  squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U)
      (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) -
    squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U

/-- **Exact global accounting after the re-entry closure.**  The running
imbalance is the genuine no-reentry ledger, plus the complementary first-owner
mass, plus the explicit no-owner heads.  No transport term is duplicated and no
seat can be counted under two first owners. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_terminalNoReentry_add_complement_add_heads
    {R K j U : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U +
        squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger R K j U +
        ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_firstOwnerMass_add_heads hR]
  unfold squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger
  ring

/-- The scalar complement ledger introduced for bookkeeping is exactly the
signed mass of the literal complement carrier. -/
theorem squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger_eq_carrierMass
    (R K j U : ℕ) :
    squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger R K j U =
      ∑ x ∈ squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x := by
  unfold squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger
  rw [← squareRootLowPrimeProcessedSeatCanonicalAssigned_weight_sum_eq_firstOwnerMass]
  rw [squareRootLowPrimeCanonicalAssigned_weight_sum_eq_noReentry_add_complement]
  ring

/-- **Carrier-level global normal form.**  The running imbalance is the
terminal no-reentry ledger, the born-range complement, the forced non-born
re-entry complement, and the explicit no-owner heads.  The preceding theorem
routes every state in the third summand to an internal response-forest
zero-pair or the existing BornExit frontier. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_noLater_add_born_add_reentry_add_heads
    {R K j U : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U +
        (∑ x ∈ squareRootLowPrimeBornComplementCarrier R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        (∑ x ∈ squareRootLowPrimeNonBornReentryCarrier R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_terminalNoReentry_add_complement_add_heads hR]
  rw [squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger_eq_carrierMass]
  rw [squareRootLowPrimeComplementCarrier_weight_sum_eq_born_add_nonBorn]
  ring


/-- Exact terminal-partition form of the mass-transfer seam.
At any processed cutoff, the old four-home mass-transfer statement is
equivalent to one equality on the new literal partition:
NoLater + BornRange + forced-ReEntry + Heads =
Head + Partial + BornExit + RootEquality.

This is an equality, not an estimate. -/
theorem squareRootLowPrimeMassTransfer_iff_terminalPartitionIdentity
    {R K j U : ℕ} (hR : 2 ≤ R) :
    (squareRootLowPrimeRunningImbalanceReal R K j U =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) ↔
      (squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U +
          (∑ x ∈ squareRootLowPrimeBornComplementCarrier R K j U,
            squareRootLowPrimeProcessedSeatWeightReal x) +
          (∑ x ∈ squareRootLowPrimeNonBornReentryCarrier R K j U,
            squareRootLowPrimeProcessedSeatWeightReal x) +
          (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U,
            squareRootLowPrimeProcessedSeatWeightReal x) =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K U +
          squareRootLowPrimeRootEqualityBoundaryMassReal R) := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_noLater_add_born_add_reentry_add_heads
    hR]

/-- At the canonical cutoff, proving the preceding terminal-partition identity
is exactly enough to discharge the repository's packet-free identity. -/
theorem squareRootLowPrimePacketFree_of_terminalPartitionIdentity
    {R K j : ℕ}
    (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hpart :
      squareRootLowPrimeGlobalTerminalNoReentryLedger R K j
          (squareRootBornPostTailLowPrimeCutoff R) +
        (∑ x ∈ squareRootLowPrimeBornComplementCarrier R K j
            (squareRootBornPostTailLowPrimeCutoff R),
          squareRootLowPrimeProcessedSeatWeightReal x) +
        (∑ x ∈ squareRootLowPrimeNonBornReentryCarrier R K j
            (squareRootBornPostTailLowPrimeCutoff R),
          squareRootLowPrimeProcessedSeatWeightReal x) +
        (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j
            (squareRootBornPostTailLowPrimeCutoff R),
          squareRootLowPrimeProcessedSeatWeightReal x) =
      1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
        squareRootLowPrimeBornExitBoundaryMassReal R K
          (squareRootBornPostTailLowPrimeCutoff R) +
        squareRootLowPrimeRootEqualityBoundaryMassReal R) :
    (squareRootMatchedBornSmoothTransport R).re +
        (squareRootBornPostTailAboveCutoffResponse R K j
          (squareRootBornPostTailLowPrimeCutoff R)).re =
      1 + squareRootLowPrimeBornExitBoundaryMassReal R K
            (squareRootBornPostTailLowPrimeCutoff R) +
        squareRootLowPrimeRootEqualityBoundaryMassReal R := by
  have hmass :
      squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) =
        1 - ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℝ) +
          squareRootLowPrimeBornExitBoundaryMassReal R K
            (squareRootBornPostTailLowPrimeCutoff R) +
          squareRootLowPrimeRootEqualityBoundaryMassReal R :=
    (squareRootLowPrimeMassTransfer_iff_terminalPartitionIdentity
      (R := R) (K := K) (j := j)
      (U := squareRootBornPostTailLowPrimeCutoff R) (by omega)).2 hpart
  exact (squareRootLowPrimeMassTransfer_iff_packetFree R K j
    (squareRootBornPostTailLowPrimeCutoff R) hR hK hKR hj).1 hmass

/-- The proposed sum of the post-root downcross ledger and transport would
double-count the same exact object: the repository already identifies them. -/
theorem lowWheelCanonicalPostRootDowncrossLedger_add_transport_eq_two_transport
    {R : ℕ} (hR : 2 ≤ R) :
    lowWheelCanonicalPostRootDowncrossLedger R +
        squareRootTransportCofactorFirst R =
      2 * squareRootTransportCofactorFirst R := by
  rw [lowWheelCanonicalPostRootDowncrossLedger_eq_transport R hR]
  ring


/-- **Exact dynamic exhaustiveness.**  A non-born first-owner fallout either
never re-enters at any later processed prime, or the first witnessed re-entry
routes pointwise into the already-compiled Go two-boundary shell.

No count, norm, or asymptotic input is used. -/
theorem squareRootLowPrimeNonBornFallout_noLater_or_goShell
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R) (hc : 0 < c)
    (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ∨
      ∃ q t,
        q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
        p < q ∧
        t.Prime ∧ q < t ∧ p * c < t ∧
          (c ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
                t (squareRootEndpoint R / (t * t)) q ∨
            c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
                t (squareRootEndpoint R) q) := by
  classical
  by_cases hno : squareRootLowPrimeNoLaterSeatReentry R K j U p c s
  · exact Or.inl hno
  · right
    have hex :
        ∃ q,
          q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
          p < q ∧
          s < squareRootLowPrimeCombinedFreshResponse R K j (q * c) := by
      by_contra h
      push_neg at h
      apply hno
      intro q hq hpq
      exact Nat.le_of_not_gt (h q hq hpq)
    obtain ⟨q, hqSet, hpq, hqAlive⟩ := hex
    have hqPrime : q.Prime := (Finset.mem_filter.mp hqSet).2
    obtain ⟨t, htPrime, hqt, hpct, hsplit⟩ :=
      squareRootLowPrimeNonBornFalloutReentry_goTerminal_or_secondBoundary
        hR hc hp hqPrime hrough hpq hpU hUR hs hnb hfall hqAlive
    exact ⟨q, t, hqSet, hpq, htPrime, hqt, hpct, hsplit⟩

/-- **Re-entry is completely consumed by the existing response forest.**
After a non-born first-owner fallout, there are only three possibilities:

* the seat never re-enters at a later processed owner;
* a later re-entry produces an internal born atom, paired pointwise with its
  arithmetic child by the response-forest Othello involution;
* a later re-entry produces a born no-successor atom, i.e. the existing
  BornExit frontier.

Thus no re-entry term needs the Go cube hypothesis or a new quantitative
estimate. -/
theorem squareRootLowPrimeNonBornFallout_noLater_or_responseForestCancel_or_bornExit
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hc : 0 < c)
    (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ∨
      ∃ q t,
        q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
        p < q ∧
        t.Prime ∧ q < t ∧ p * c < t ∧
          (((q * c, t) ∈ squareRootLowPrimeBornInternalAtoms R K U ∧
              squareRootLowPrimeResponseForestOthelloWeight
                  (Sum.inl (q * c, t)) +
                squareRootLowPrimeResponseForestOthelloWeight
                  (squareRootLowPrimeResponseForestOthelloMate R K U
                    (Sum.inl (q * c, t))) = 0) ∨
            (q * c, t) ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U) := by
  classical
  have hcut : squareRootBornPostTailLowPrimeCutoff R < R := by
    unfold squareRootBornPostTailLowPrimeCutoff
    have hsqrtPos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 (by omega)
    omega
  have hURlt : U < R := lt_of_le_of_lt hUR hcut
  by_cases hno : squareRootLowPrimeNoLaterSeatReentry R K j U p c s
  · exact Or.inl hno
  · right
    have hex :
        ∃ q,
          q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
          p < q ∧
          s < squareRootLowPrimeCombinedFreshResponse R K j (q * c) := by
      by_contra h
      push_neg at h
      apply hno
      intro q hq hpq
      exact Nat.le_of_not_gt (h q hq hpq)
    obtain ⟨q, hqSet, hpq, hqAlive⟩ := hex
    obtain ⟨t, htPrime, hqt, hpct, hroute⟩ :=
      squareRootLowPrimeNonBornFalloutScheduledReentry_birthAtom_internal_or_exit
        hR hK hc hp hqSet hrough hpq hpU hUR hs hnb hfall hqAlive
    refine ⟨q, t, hqSet, hpq, htPrime, hqt, hpct, ?_⟩
    rcases hroute with hInternal | hExit
    · exact Or.inl
        ⟨hInternal,
          (squareRootLowPrimeBornInternalAtom_responseForest_cancel
            hURlt hInternal).2⟩
    · exact Or.inr hExit

/-- The old root-equality exception is no longer exceptional once the complete
Boolean face is used: every such incidence is already a genuine second-boundary
defect and therefore has an opposite-sign physical full-face mate. -/
theorem squareRootLowPrimeGoRootEquality_fullFace_cancel
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d) +
      lowWheelFullTaggedPhysicalWeight
        (lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d)) = 0 := by
  rcases mem_squareRootLowPrimeGoRootEqualityDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _heq, hcube, hd⟩
  exact squareRootLowPrimeSecondBoundaryDefect_fullFace_cancel
    hR hq hr hrq hcube hd

end RHLean.Proof
