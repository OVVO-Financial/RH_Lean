import Mathlib
import «research.VF_MID_OPTIMAL_BASE_FIRST_CROSSING_TRIGGER»
import «research.VF_MID_ACTUAL_PRIME_FIRST_BAD_MOBIUS_TRIGGER»
import «research.VF_MID_NATIVE_LYAPUNOV_SEAT_GRAM»
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_ARBITRARY_SITE_CELLS»

/-!
# VF subdoubling survivor packet to returned-core owner gate

The post-#885 seam is a carrier identification, not a new cancellation law.

This file starts with the exact quadratic entrance.  The frozen-wheel survivor
Mobius mass already has a zero-target pair dictionary on exactly the same
physical carrier.  Summing that pointwise dictionary first within a pair of
square blocks and then over the complete subdoubling run puts the #885 signed
survivor packet directly into the returned-core zero-target pair currency
before any norm, reciprocal weight, or owner-energy estimate is used.

The next stage will reindex this restricted pair currency through the existing
arbitrary-site first-owner Fubini and then consume the already-compiled signed
incidence gate.  No new descent mechanism is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- **Exact block-pair entrance into zero-target currency.**

The zero-target Gram on two frozen survivor blocks is literally the product of
their signed Mobius masses.  This is just finite Fubini plus the compiled
zero-target pair product identity. -/
theorem vfMidZeroTargetCubeCrossGram_eq_survivorMobiusMass_mul
    (A R S : ℕ) :
    vfMidZeroTargetCubeCrossGram A R S =
      (vfMidSquareBandPrefixSurvivorMobiusMassReal A R : ℂ) *
        (vfMidSquareBandPrefixSurvivorMobiusMassReal A S : ℂ) := by
  unfold vfMidZeroTargetCubeCrossGram
    vfMidSquareBandPrefixSurvivorMobiusMassReal
  simp_rw [RHLean.Proof.postRootZeroTargetPairExcess_eq_weight]
  unfold realMoebiusStep
  push_cast
  rw [← Finset.sum_mul_sum]

/-- Zero-target Gram accumulated over every ordered pair of square blocks in
one frozen-wheel dyadic run. -/
def vfMidDyadicPrefixZeroTargetGram (A B : ℕ) : ℂ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ S ∈ Finset.Ico A B,
      vfMidZeroTargetCubeCrossGram A R S

/-- **Exact dyadic quadratic entrance.**

The square of the #885 frozen survivor Mobius packet is exactly the complete
zero-target Gram on that same run.  No diagonal is discarded and no absolute
value is taken. -/
theorem vfMidDyadicPrefixZeroTargetGram_eq_survivorMobiusMass_sq
    (A B : ℕ) :
    vfMidDyadicPrefixZeroTargetGram A B =
      (vfMidDyadicPrefixSurvivorMobiusMassReal A B : ℂ) ^ 2 := by
  unfold vfMidDyadicPrefixZeroTargetGram
  simp_rw [vfMidZeroTargetCubeCrossGram_eq_survivorMobiusMass_mul]
  rw [← Finset.sum_mul_sum]
  unfold vfMidDyadicPrefixSurvivorMobiusMassReal
  push_cast
  ring



/-! ## Preserve the full #885 affine cancellation before owner energy -/

/-- The exact #885 tracking packet is the literal VF-minus-actual signed-seat
mass over the same run.  This is the correct uncentered object to propagate:
the deterministic affine part and the Mobius part remain coupled. -/
theorem vfMidDyadicVFTrackingDefect_eq_oddRunSeatMass
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMidDyadicVFTrackingDefect A B =
      vfMidOddRunSeatMass A B := by
  have htrack :=
    vfMidOddDyadicCompositeTrackingDefect_eq_vfTrackingDefect
      (A := A) (B := B) hA (hA.trans hAB) hAB
  have hrun := vfMidOddRunSeatMass_eq_dyadicTracking A B hA
  exact htrack.symm.trans hrun.symm

/-- **Minimal first escape in the literal VF signed-seat currency.**

This is #885 with no part of the affine cancellation discarded.  The complete
signed seat run, rather than the raw survivor Mobius mass by itself, carries
the strict first-escape debt. -/
theorem vfMidActualPrimeFirstBadAt_forces_signedSeatRunTrigger
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A) (hABlt : A < B) (hBA : B ≤ 2 * A) :
    (K * vfMidSyntheticRadialScale B -
          K * vfMidSyntheticRadialScale A <
        vfMidOddRunSeatMass A B) ∨
    (vfMidOddRunSeatMass A B <
        K * vfMidSyntheticRadialScale A -
          K * vfMidSyntheticRadialScale B) := by
  have htrigger :=
    vfMidActualPrimeFirstBadAt_forces_subdoublingMobiusTrigger
      hfirst hA hABlt hBA
  have hdict :=
    vfMidDyadicVFTrackingDefect_eq_frozenWheel_add_half_moebius
      hA hABlt.le hBA
  have hrun :=
    vfMidDyadicVFTrackingDefect_eq_oddRunSeatMass
      (A := A) (B := B) (by omega : 2 ≤ A) hABlt.le
  have hpacket :
      vfMidDyadicVFMass A B -
          (1 / 2 : ℝ) * vfMidDyadicPrefixSupply A A B +
          (1 / 2 : ℝ) * vfMidDyadicPrefixSurvivorMobiusMassReal A B =
        vfMidOddRunSeatMass A B :=
    hdict.symm.trans hrun
  rcases htrigger with hlow | hupp
  · exact Or.inl (by simpa only [hpacket] using hlow)
  · exact Or.inr (by simpa only [hpacket] using hupp)

/-! ## Exact affine split on the frozen survivor carrier -/

/-- **The full VF tracking packet is survivor charge plus removed-seat mass.**

The first term keeps the signed prime/composite information on the frozen
survivor carrier.  The second is purely deterministic: the common VF seat
weight times the odd parity seats removed by the stronger frozen wheel. -/
theorem vfMidOddCompositeTrackingDefect_eq_prefixSurvivorCharge_add_removedSeats
    {A R : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A) :
    vfMidOddCompositeTrackingDefect R =
      vfMidSubdoublingPrefixSurvivorChargeSum A R +
        vfMidOddFractionalPrimeSeatWeight R *
          ((R : ℝ) - ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ)) := by
  rw [vfMidOddCompositeTrackingDefect_eq_frozenWheel_add_half_moebius
      hA hAR hRlt,
    vfMidSubdoublingPrefixSurvivorChargeSum_eq_affineMoebius
      hA hAR hRlt]
  have hmass :=
    vfMidOddFractionalPrimeSeatWeight_sum R (by omega : 2 ≤ R)
  rw [Finset.sum_const, nsmul_eq_mul, vfMidOddCandidateSeats_card] at hmass
  have hmass' :
      vfMidBandMass R =
        vfMidOddFractionalPrimeSeatWeight R * (R : ℝ) := by
    simpa [mul_comm] using hmass.symm
  rw [hmass']
  ring

/-- The frozen survivor population is no larger than the parity carrier. -/
theorem vfMidSquarePrefixWheelSurvivors_card_le_root
    {A R : ℕ} (hA : 2 ≤ A) :
    (vfMidSquarePrefixWheelSurvivors A R).card ≤ R := by
  have hsub :
      vfMidSquarePrefixWheelSurvivors A R ⊆
        vfMidSquarePrefixWheelSurvivors 2 R :=
    vfMidSquarePrefixWheelSurvivors_mono hA
  have hcard := Finset.card_le_card hsub
  have hcard' :
      (vfMidSquarePrefixWheelSurvivors A R).card ≤
        (vfMidOddCandidateSeats R).card := by
    simpa [vfMidOddCandidateSeats] using hcard
  rw [vfMidOddCandidateSeats_card] at hcard'
  exact hcard'

/-- The removed-seat affine correction has a fixed favorable sign. -/
theorem vfMidPrefixRemovedSeatMass_nonneg
    {A R : ℕ} (hA : 2 ≤ A) (hR : 2 ≤ R) :
    0 ≤ vfMidOddFractionalPrimeSeatWeight R *
      ((R : ℝ) - ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ)) := by
  have hw : 0 ≤ vfMidOddFractionalPrimeSeatWeight R := by
    unfold vfMidOddFractionalPrimeSeatWeight
    exact div_nonneg (vfMidBandMass_nonneg_of_two_le R hR) (by positivity)
  have hcard := vfMidSquarePrefixWheelSurvivors_card_le_root
    (A := A) (R := R) hA
  have hcardR :
      ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hcard
  have hdiff :
      0 ≤ (R : ℝ) - ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ) := by
    linarith
  exact mul_nonneg hw hdiff

/-! ## Literal restricted carrier and exact first-owner reindex -/

open RHLean.Arithmetic RHLean.Proof

/-- The physical integer carrier underlying the whole #885 subdoubling packet. -/
def vfMidDyadicPrefixSurvivorCarrier (A B : ℕ) : Finset ℕ :=
  (Finset.Ico A B).biUnion (vfMidSquarePrefixWheelSurvivors A)

/-- **Every first fresh owner of two frozen-wheel survivors lies above the frozen wheel.**

This is purely the definition of survival: no prime coordinate at most `A`
divides either endpoint.  Since a first fresh owner divides exactly one endpoint,
it cannot lie at or below `A`.  No subdoubling or endpoint-size hypothesis is
needed. -/
theorem vfMidDyadicPrefixSurvivor_firstOwner_gt_frozen
    {A B p m n : ℕ}
    (hm : m ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (howner : IsSquarefreePairFreshPrimeOwner p m n) :
    A < p := by
  rcases Finset.mem_biUnion.mp hm with ⟨R, _hR, hmSurv⟩
  rcases Finset.mem_biUnion.mp hn with ⟨S, _hS, hnSurv⟩
  have hmAvoid : lowWheelHighSurvivor A m :=
    (Finset.mem_filter.mp hmSurv).2
  have hnAvoid : lowWheelHighSurvivor A n :=
    (Finset.mem_filter.mp hnSurv).2
  rcases Finset.mem_union.mp howner.1 with hleft | hright
  · rcases Finset.mem_sdiff.mp hleft with ⟨hpFace, _hpNot⟩
    have hpData : p.Prime ∧ p ∣ m ∧ m ≠ 0 := by
      simpa [squarefreePrimeFace] using (Nat.mem_primeFactors.mp hpFace)
    by_contra hnot
    have hpLe : p ≤ A := Nat.le_of_not_gt hnot
    have hpMem : p ∈ primesUpTo A :=
      mem_primesUpTo.mpr ⟨hpData.1, hpLe⟩
    exact hmAvoid p hpMem hpData.2.1
  · rcases Finset.mem_sdiff.mp hright with ⟨hpFace, _hpNot⟩
    have hpData : p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
      simpa [squarefreePrimeFace] using (Nat.mem_primeFactors.mp hpFace)
    by_contra hnot
    have hpLe : p ≤ A := Nat.le_of_not_gt hnot
    have hpMem : p ∈ primesUpTo A :=
      mem_primesUpTo.mpr ⟨hpData.1, hpLe⟩
    exact hnAvoid p hpMem hpData.2.1

/-- Distinct square blocks contribute disjoint frozen-wheel survivor sets. -/
theorem vfMidSquarePrefixWheelSurvivors_pairwiseDisjoint
    (A B : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Ico A B))
      (vfMidSquarePrefixWheelSurvivors A) := by
  intro R hR S hS hRS
  change Disjoint (vfMidSquarePrefixWheelSurvivors A R)
    (vfMidSquarePrefixWheelSurvivors A S)
  rw [Finset.disjoint_left]
  intro n hnR hnS
  have hnRI := (Finset.mem_filter.mp hnR).1
  have hnSI := (Finset.mem_filter.mp hnS).1
  unfold vfMidSquareWheelSites at hnRI hnSI
  rcases Finset.mem_Ioo.mp hnRI with ⟨hnRlow, hnRhigh⟩
  rcases Finset.mem_Ioo.mp hnSI with ⟨hnSlow, hnShigh⟩
  rcases lt_or_gt_of_ne hRS with hRltS | hSltR
  · have hsucc : R + 1 ≤ S := by omega
    have hsq : (R + 1) ^ 2 ≤ S ^ 2 :=
      Nat.pow_le_pow_left hsucc 2
    omega
  · have hsucc : S + 1 ≤ R := by omega
    have hsq : (S + 1) ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left hsucc 2
    omega

/-- Flattening the disjoint square blocks does not change their signed mass. -/
theorem sum_vfMidDyadicPrefixSurvivorCarrier_eq_mobiusMass
    (A B : ℕ) :
    (∑ n ∈ vfMidDyadicPrefixSurvivorCarrier A B, realMoebiusStep n) =
      vfMidDyadicPrefixSurvivorMobiusMassReal A B := by
  unfold vfMidDyadicPrefixSurvivorCarrier
    vfMidDyadicPrefixSurvivorMobiusMassReal
  rw [Finset.sum_biUnion
    (vfMidSquarePrefixWheelSurvivors_pairwiseDisjoint A B)]
  apply Finset.sum_congr rfl
  intro R _hR
  unfold vfMidSquareBandPrefixSurvivorMobiusMassReal realMoebiusStep
  rfl

/-- On a genuine subdoubling run every #885 survivor is a nonzero-Mobius site
on the returned-core physical clock at the terminal root B. -/
theorem vfMidDyadicPrefixSurvivorCarrier_subset_lowOwnerNonzero
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorCarrier A B ⊆
      lowOwnerNonzeroMobiusCarrier B := by
  intro n hn
  rcases Finset.mem_biUnion.mp hn with ⟨R, hR, hnSurv⟩
  rcases Finset.mem_Ico.mp hR with ⟨hAR, hRB⟩
  have hR2 : 2 ≤ R := by omega
  have hRlt : R < 2 * A := hRB.trans_le hBA
  have hnSite := (Finset.mem_filter.mp hnSurv).1
  unfold vfMidSquareWheelSites at hnSite
  rcases Finset.mem_Ioo.mp hnSite with ⟨hnLow, hnHigh⟩
  have hR1B : R + 1 ≤ B := by omega
  have hsq : (R + 1) ^ 2 ≤ B ^ 2 :=
    Nat.pow_le_pow_left hR1B 2
  have hnLtBsq : n < B ^ 2 := hnHigh.trans_le hsq
  have hBpos : 0 < B ^ 2 := by
    have hB3 : 3 ≤ B := hA.trans hAB
    nlinarith
  have hnX : n ≤ squareRootEndpoint B := by
    unfold squareRootEndpoint
    omega
  have hnPos : 1 ≤ n := by
    have hRpos : 0 < R ^ 2 := by positivity
    omega
  have hsplit :=
    vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
      (A := A) (R := R) hR2 hAR
  have hmem :
      n ∈ vfMidSquareWheelPrimes R ∪
        vfMidSquareBandPrefixCompositeSurvivors A R := by
    rw [← hsplit]
    exact hnSurv
  have hstep : realMoebiusStep n ≠ 0 := by
    rcases Finset.mem_union.mp hmem with hnPrime | hnComp
    · have hp : n.Prime := (Finset.mem_filter.mp hnPrime).2
      rw [realMoebiusStep, ArithmeticFunction.moebius_apply_prime hp]
      norm_num
    · have hmu :=
        vfMidSquareBandPrefixComposite_moebius_eq_one_of_subdoubling
          hA hAR hRlt hnComp
      rw [realMoebiusStep, hmu]
      norm_num
  unfold lowOwnerNonzeroMobiusCarrier
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hnPos, hnX⟩, hstep⟩

/-- **On the frozen subdoubling carrier the returned-core AMP coefficient is exactly one.**

Every genuine low-q^2 daughter cutoff at terminal root `B` lies below
`A^2`: its owner is an odd prime, hence at least three, while `B <= 2A`.
Every #885 survivor lies strictly above `A^2`.  Thus no reciprocal daughter
indicator is active, while the far-tail indicator is one. -/
theorem lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidSurvivor
    {A B n : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B) :
    lowOwnerZeroFrequencyMobiusWeight B n = 1 := by
  rcases Finset.mem_biUnion.mp hn with ⟨R, hR, hnSurv⟩
  rcases Finset.mem_Ico.mp hR with ⟨hAR, _hRB⟩
  have hnSite := (Finset.mem_filter.mp hnSurv).1
  unfold vfMidSquareWheelSites at hnSite
  have hnLow : R ^ 2 < n := (Finset.mem_Ioo.mp hnSite).1
  have hA2R2 : A ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hAR 2
  have hA2n : A ^ 2 < n := hA2R2.trans_lt hnLow
  have hBn : B ≤ n := by
    have htwoA_le_A2 : 2 * A ≤ A ^ 2 := by nlinarith
    exact hBA.trans (htwoA_le_A2.trans (Nat.le_of_lt hA2n))
  have hrec : lowOwnerReciprocalDaughterWeight B n = 0 := by
    unfold lowOwnerReciprocalDaughterWeight
    apply Finset.sum_eq_zero
    intro q hq
    have hqBase :
        q ∈ (primesUpTo (B - 1)).erase 2 :=
      (Finset.mem_sdiff.mp hq).1
    have hqData := Finset.mem_erase.mp hqBase
    have hqPrime : q.Prime := (mem_primesUpTo.mp hqData.2).1
    have hq3 : 3 ≤ q := by
      have hq2 : 2 ≤ q := hqPrime.two_le
      omega
    have hdenPos : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
    have hXlt :
        squareRootEndpoint B < A ^ 2 * (q * q) := by
      have hB2 : B ^ 2 ≤ (2 * A) ^ 2 :=
        Nat.pow_le_pow_left hBA 2
      have hBsqPos : 0 < B ^ 2 := by
        have hB3 : 3 ≤ B := hA.trans hAB
        nlinarith
      have hsub : B ^ 2 - 1 < B ^ 2 := by omega
      have hfourNine : (2 * A) ^ 2 < A ^ 2 * 9 := by
        nlinarith [hA]
      have hqSq : 9 ≤ q * q := by nlinarith
      have hnine :
          A ^ 2 * 9 ≤ A ^ 2 * (q * q) :=
        Nat.mul_le_mul_left (A ^ 2) hqSq
      unfold squareRootEndpoint
      calc
        B ^ 2 - 1 < B ^ 2 := hsub
        _ ≤ (2 * A) ^ 2 := hB2
        _ < A ^ 2 * 9 := hfourNine
        _ ≤ A ^ 2 * (q * q) := hnine
    have hcut :
        rawQ2ChildCutoff B q < A ^ 2 := by
      unfold rawQ2ChildCutoff
      exact (Nat.div_lt_iff_lt_mul hdenPos).2 hXlt
    have hnNot : ¬ n ≤ rawQ2ChildCutoff B q :=
      Nat.not_le_of_gt (hcut.trans hA2n)
    simp [hnNot]
  unfold lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailWeight
  rw [hrec]
  simp [hBn]

/-- Consequently the centered #885 Mobius site is literally the standard
returned-core AMP site on every frozen survivor. -/
theorem lowOwnerZeroFrequencyMobiusSite_eq_realMoebius_on_vfMidSurvivor
    {A B n : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B) :
    lowOwnerZeroFrequencyMobiusSite B n = realMoebiusStep n := by
  unfold lowOwnerZeroFrequencyMobiusSite
  rw [lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidSurvivor
    hA hAB hBA hn]
  ring

/-- The #885 packet as an arbitrary signed site on the returned-core clock. -/
def vfMidDyadicPrefixSurvivorSignedSite (A B n : ℕ) : ℝ :=
  if n ∈ vfMidDyadicPrefixSurvivorCarrier A B
  then realMoebiusStep n
  else 0

/-- First-owner fibres at or below the frozen wheel carry no #885 restricted
mass. Any nonzero pair contribution has both endpoints on the survivor carrier,
and its least fresh owner is therefore strictly larger than A. -/
theorem lowOwnerGlobalFirstOwnerPairMassWith_vfMidSurvivor_eq_zero_of_le_frozen
    {A B p : ℕ} (hpA : p ≤ A) :
    lowOwnerGlobalFirstOwnerPairMassWith B p
        (vfMidDyadicPrefixSurvivorSignedSite A B) = 0 := by
  unfold lowOwnerGlobalFirstOwnerPairMassWith
  apply Finset.sum_eq_zero
  intro mn hmn
  by_cases hm : mn.1 ∈ vfMidDyadicPrefixSurvivorCarrier A B
  · by_cases hn : mn.2 ∈ vfMidDyadicPrefixSurvivorCarrier A B
    · have howner : IsSquarefreePairFreshPrimeOwner p mn.1 mn.2 :=
        (Finset.mem_filter.mp hmn).2
      have hgt :=
        vfMidDyadicPrefixSurvivor_firstOwner_gt_frozen hm hn howner
      exact False.elim ((Nat.not_lt_of_ge hpA) hgt)
    · simp [vfMidDyadicPrefixSurvivorSignedSite, hm, hn]
  · simp [vfMidDyadicPrefixSurvivorSignedSite, hm]

/-- Restricting the common returned-core clock by the #885 indicator recovers
exactly the #885 signed survivor packet. -/
theorem sum_lowOwnerNonzero_vfMidDyadicPrefixSurvivorSignedSite
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier B,
      vfMidDyadicPrefixSurvivorSignedSite A B n) =
        vfMidDyadicPrefixSurvivorMobiusMassReal A B := by
  have hsub :=
    vfMidDyadicPrefixSurvivorCarrier_subset_lowOwnerNonzero
      hA hAB hBA
  have hfilter :
      (lowOwnerNonzeroMobiusCarrier B).filter
          (fun n => n ∈ vfMidDyadicPrefixSurvivorCarrier A B) =
        vfMidDyadicPrefixSurvivorCarrier A B := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_hnClock, hnCar⟩
      exact hnCar
    · intro hnCar
      exact ⟨hsub hnCar, hnCar⟩
  unfold vfMidDyadicPrefixSurvivorSignedSite
  rw [← Finset.sum_filter, hfilter]
  exact sum_vfMidDyadicPrefixSurvivorCarrier_eq_mobiusMass A B

/-- The returned-core empty-state arbitrary-site Gram is exactly the square of
the #885 survivor mass. -/
theorem lowOwnerRevealedPairMassWith_empty_eq_vfMidSurvivor_sq
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    lowOwnerRevealedPairMassWith B ∅
        (vfMidDyadicPrefixSurvivorSignedSite A B) =
      vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 := by
  rw [lowOwnerRevealedPairMassWith_empty_eq_sum_sq]
  rw [sum_lowOwnerNonzero_vfMidDyadicPrefixSurvivorSignedSite
    hA hAB hBA]

/-- **Exact first-owner carrier weld.**

The quadratic #885 packet is now literally diagonal plus the repository's
existing least-owner/lower-signature cell carrier, with the survivor indicator
kept as an arbitrary signed site.  No owner multiplicity or boundary term is
discarded. -/
theorem vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_firstOwnerCells
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith B
          (vfMidDyadicPrefixSurvivorSignedSite A B) +
        ∑ p ∈ primesUpTo (squareRootEndpoint B),
          2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
            lowOwnerFirstOwnerCellGramWith B p sig
              (vfMidDyadicPrefixSurvivorSignedSite A B) := by
  have hempty :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_firstOwners
      B (vfMidDyadicPrefixSurvivorSignedSite A B)
  have hsquare :=
    lowOwnerRevealedPairMassWith_empty_eq_vfMidSurvivor_sq
      hA hAB hBA
  rw [hsquare] at hempty
  calc
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 =
        lowOwnerGlobalDiagonalPairMassWith B
            (vfMidDyadicPrefixSurvivorSignedSite A B) +
          ∑ p ∈ primesUpTo (squareRootEndpoint B),
            lowOwnerGlobalFirstOwnerPairMassWith B p
              (vfMidDyadicPrefixSurvivorSignedSite A B) := hempty
    _ =
        lowOwnerGlobalDiagonalPairMassWith B
            (vfMidDyadicPrefixSurvivorSignedSite A B) +
          ∑ p ∈ primesUpTo (squareRootEndpoint B),
            2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
              lowOwnerFirstOwnerCellGramWith B p sig
                (vfMidDyadicPrefixSurvivorSignedSite A B) := by
      apply congrArg
        (fun x : ℝ =>
          lowOwnerGlobalDiagonalPairMassWith B
              (vfMidDyadicPrefixSurvivorSignedSite A B) + x)
      apply Finset.sum_congr rfl
      intro p hp
      exact lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
        (mem_primesUpTo.mp hp).1
        (vfMidDyadicPrefixSurvivorSignedSite A B)


/-! ## Remove the frozen first-owner range exactly -/

/-- First-owner primes which can actually carry a nonzero pair from the #885
frozen survivor packet.  The lower frozen wheel has already acted, so only
strictly later coordinates are retained. -/
def vfMidDyadicPrefixSurvivorLiveFirstOwners (A B : ℕ) : Finset ℕ :=
  (primesUpTo (squareRootEndpoint B)).filter fun p => A < p

/-- **No hidden low-owner mass.**

The complete least-owner sum of the #885 restricted site is exactly the sum
over owners strictly above the frozen cutoff.  This is the formal all-scale
version of the x=317 hand ledger: every p <= A fibre is identically zero before
any estimate or square is taken. -/
theorem sum_lowOwnerGlobalFirstOwnerPairMassWith_vfMidSurvivor_eq_liveOwners
    (A B : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint B),
      lowOwnerGlobalFirstOwnerPairMassWith B p
        (vfMidDyadicPrefixSurvivorSignedSite A B)) =
      ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
        lowOwnerGlobalFirstOwnerPairMassWith B p
          (vfMidDyadicPrefixSurvivorSignedSite A B) := by
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint B),
      lowOwnerGlobalFirstOwnerPairMassWith B p
        (vfMidDyadicPrefixSurvivorSignedSite A B)) =
      ∑ p ∈ primesUpTo (squareRootEndpoint B),
        if A < p then
          lowOwnerGlobalFirstOwnerPairMassWith B p
            (vfMidDyadicPrefixSurvivorSignedSite A B)
        else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hAp : A < p
          · simp [hAp]
          · have hpA : p ≤ A := Nat.le_of_not_gt hAp
            rw [
              lowOwnerGlobalFirstOwnerPairMassWith_vfMidSurvivor_eq_zero_of_le_frozen
                (A := A) (B := B) (p := p) hpA]
            simp [hAp]
    _ =
      ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
        lowOwnerGlobalFirstOwnerPairMassWith B p
          (vfMidDyadicPrefixSurvivorSignedSite A B) := by
        unfold vfMidDyadicPrefixSurvivorLiveFirstOwners
        rw [Finset.sum_filter]

/-- **Owner-only form of the quadratic entrance.**

After the diagonal is separated, every off-diagonal #885 survivor pair is
owned by a genuinely later prime p > A.  There is no residual first-owner
sector on the already-frozen wheel. -/
theorem vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_liveFirstOwners
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith B
          (vfMidDyadicPrefixSurvivorSignedSite A B) +
        ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
          lowOwnerGlobalFirstOwnerPairMassWith B p
            (vfMidDyadicPrefixSurvivorSignedSite A B) := by
  have hempty :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_firstOwners
      B (vfMidDyadicPrefixSurvivorSignedSite A B)
  have hsquare :=
    lowOwnerRevealedPairMassWith_empty_eq_vfMidSurvivor_sq
      hA hAB hBA
  rw [hsquare] at hempty
  rw [
    sum_lowOwnerGlobalFirstOwnerPairMassWith_vfMidSurvivor_eq_liveOwners
      A B] at hempty
  exact hempty

end RHLean.Analysis
