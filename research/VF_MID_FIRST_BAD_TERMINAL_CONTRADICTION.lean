import Mathlib
import «research.VF_MID_FULL_AFFINE_PAIR_CLASSIFIER»
import «research.VF_MID_FRACTIONAL_INCIDENCE_CAPACITY»
import «research.VF_MID_FINAL_SIGNED_RANK_CONTRACTION»
import «research.VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET»
import «research.VF_MID_ADJACENT_SQUARE_SELBERG_BOUNDARY»\nimport «research.VF_MID_ACTUAL_PRIME_STAR_DEFECT_CONTRACTION»

/-!
# Terminal first-bad contradiction splice

This file imports the merged #888 affine/owner splice and attempts the terminal
composition directly, without introducing a new cancellation hypothesis.

The intended three inputs are kept in their native currencies:

1. the exact two-sector first-bad wall breach;
2. the first-bad prior-good wall on every genuinely descended child scale;
3. the #888 selection-stable reciprocal quarter contraction.

The child lemmas below make the second input literal for both the processed
low-owner sector and the live post-frozen sector.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A processed-owner child lies at a strict prior square-root scale. -/
theorem vfMidProcessedOwnerChild_sqrt_lt_anchor
    {A B R p m : ℕ}
    (hRB : R < B)
    (hBsq : B ^ 2 ≤ 3 * A ^ 2)
    (hp : p ∈ vfMidFrozenProcessedOwnerPrimes A R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    Nat.sqrt m < A := by
  exact (Nat.sqrt_lt').2
    (vfMidProcessedOwnerChild_lt_anchorSquare hRB hBsq hp hm)

/-- A processed-owner child is not a tiny exceptional scale: it is strictly
above the frozen anchor itself. -/
theorem vfMidProcessedOwnerChild_anchor_lt
    {A R p m : ℕ}
    (hAR : A ≤ R)
    (hp : p ∈ vfMidFrozenProcessedOwnerPrimes A R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    A < m := by
  rcases Finset.mem_filter.mp hp with ⟨_hpLate, hpA⟩
  rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
  rcases vfMidSquareBandCompositeOwner_mem hn with ⟨hnComp, _hmin⟩
  rcases Finset.mem_filter.mp hnComp with ⟨hnBand, _hnNotPrime⟩
  have hnLow : R ^ 2 < n := (Finset.mem_Ioo.mp hnBand).1
  have hmul : p * (n / p) = n :=
    vfMidSquareBandCompositeOwner_mul_div hn
  by_contra hnot
  have hmA : n / p ≤ A := Nat.le_of_not_gt hnot
  have hprod : p * (n / p) ≤ A * A :=
    Nat.mul_le_mul hpA hmA
  have hA2R2 : A ^ 2 ≤ R ^ 2 :=
    Nat.pow_le_pow_left hAR 2
  have hnLe : n ≤ R ^ 2 := by
    calc
      n = p * (n / p) := hmul.symm
      _ ≤ A * A := hprod
      _ = A ^ 2 := by ring
      _ ≤ R ^ 2 := hA2R2
  omega

/-- Therefore every processed-owner child is covered by the first-bad
prior-good wall at its native square-root scale. -/
theorem vfMidProcessedOwnerChild_prior_inside
    {K : ℝ} {A B R p m : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 4 ≤ A)
    (hABlt : A < B)
    (hR : R ∈ Finset.Ico A B)
    (hBsq : B ^ 2 ≤ 3 * A ^ 2)
    (hp : p ∈ vfMidFrozenProcessedOwnerPrimes A R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    |vfMidActualPrimeEndpointDefect (Nat.sqrt m)| ≤
      K * vfMidSyntheticRadialScale (Nat.sqrt m) := by
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hRB : R < B := (Finset.mem_Ico.mp hR).2
  have hAm := vfMidProcessedOwnerChild_anchor_lt (A := A) hAR hp hm
  have hm4 : 4 ≤ m := by omega
  have hs2 : 2 ≤ Nat.sqrt m := by
    exact (Nat.le_sqrt).2 hm4
  have hsA :=
    vfMidProcessedOwnerChild_sqrt_lt_anchor hRB hBsq hp hm
  have hsB : Nat.sqrt m < B := hsA.trans hABlt
  exact vfMidActualPrimeFirstBadAt_prior_inside hfirst hs2 hsB

/-- The post-frozen #887 prime children also lie in the first-bad prior-good
region. -/
theorem vfMidFrozenOwnerPrimeChild_prior_inside
    {K : ℝ} {A B R p q : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 4 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A)
    (hR : R ∈ Finset.Ico A B)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R)
    (hq : q ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    |vfMidActualPrimeEndpointDefect (Nat.sqrt q)| ≤
      K * vfMidSyntheticRadialScale (Nat.sqrt q) := by
  have hdata :=
    vfMidDyadicFrozenCompositeOwnerChild_prime_below_frozenSquare
      hA hABlt.le hBA hR hp hq
  rcases hdata with ⟨_hqPrime, _hqA2, hsA⟩
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hpA : A < p :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).2
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hR3 : 3 ≤ R := by omega
  have hrough : q ∈ vfMidSquareBandOwnerRoughChildren R p := by
    rw [← vfMidSquareBandCompositeOwnerChildren_eq_rough hR3 hpOwner]
    exact hq
  have hpq : p ≤ q :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hrough).1).1
  have hq4 : 4 ≤ q := by omega
  have hs2 : 2 ≤ Nat.sqrt q := by
    exact (Nat.le_sqrt).2 hq4
  have hsB : Nat.sqrt q < B := hsA.trans hABlt
  exact vfMidActualPrimeFirstBadAt_prior_inside hfirst hs2 hsB

/-- Prior-goodness may be squared only after the processed descendant has been
identified with its complete lower square scale.  This is deliberately a bound
on the full endpoint defect, not on the originating owner sub-packet. -/
theorem vfMidProcessedOwnerChild_prior_energy_inside
    {K : ℝ} {A B R p m : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 4 ≤ A)
    (hABlt : A < B)
    (hR : R ∈ Finset.Ico A B)
    (hBsq : B ^ 2 ≤ 3 * A ^ 2)
    (hp : p ∈ vfMidFrozenProcessedOwnerPrimes A R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    vfMidActualPrimeEndpointDefect (Nat.sqrt m) ^ 2 ≤
      (K * vfMidSyntheticRadialScale (Nat.sqrt m)) ^ 2 := by
  have hprior :=
    vfMidProcessedOwnerChild_prior_inside
      hfirst hA hABlt hR hBsq hp hm
  have hwall0 :
      0 ≤ K * vfMidSyntheticRadialScale (Nat.sqrt m) :=
    (abs_nonneg _).trans hprior
  have hsquare :=
    (sq_le_sq₀ (abs_nonneg _) hwall0).2 hprior
  simpa [sq_abs] using hsquare

/-- The same legal square-energy conversion for a live post-frozen #887 child.
Again the bound is applied only to the complete endpoint defect at the child's
native square-root scale. -/
theorem vfMidFrozenOwnerPrimeChild_prior_energy_inside
    {K : ℝ} {A B R p q : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 4 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A)
    (hR : R ∈ Finset.Ico A B)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R)
    (hq : q ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    vfMidActualPrimeEndpointDefect (Nat.sqrt q) ^ 2 ≤
      (K * vfMidSyntheticRadialScale (Nat.sqrt q)) ^ 2 := by
  have hprior :=
    vfMidFrozenOwnerPrimeChild_prior_inside
      hfirst hA hABlt hBA hR hp hq
  have hwall0 :
      0 ≤ K * vfMidSyntheticRadialScale (Nat.sqrt q) :=
    (abs_nonneg _).trans hprior
  have hsquare :=
    (sq_le_sq₀ (abs_nonneg _) hwall0).2 hprior
  simpa [sq_abs] using hsquare

/-- Exact reassembly of the #888 two-sector charge in endpoint-depth
currency.  This is the identity that must remain visible in the terminal
first-bad argument:
`T(A,B) = D_A - D_B`. -/
theorem vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub
    {A B : ℕ}
    (hA : 3 ≤ A)
    (hAB : A ≤ B)
    (hBA : B ≤ 2 * A) :
    vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B =
      vfMidActualPrimeEndpointDefect A -
        vfMidActualPrimeEndpointDefect B := by
  rw [← vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge
    hA hBA]
  rw [← vfMidDyadicVFTrackingDefect_eq_oddRunSeatMass
    (by omega : 2 ≤ A) hAB]
  rw [vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment
    (by omega : 2 ≤ A) (by omega : 2 ≤ B) hAB]
  unfold vfMidActualPrimeEndpointDefect
  ring

/-- Exact accumulated-depth energy identity for the #888 two-sector step.

This is the non-Lipschitz terminal currency:
`D_B^2 - D_A^2 = T(A,B)^2 - 2*D_A*T(A,B)`.
The cross term retains the entire accumulated depth at the anchor. -/
theorem vfMidTwoSectorOwnerCharge_energyStep_eq
    {A B : ℕ}
    (hA : 3 ≤ A)
    (hAB : A ≤ B)
    (hBA : B ≤ 2 * A) :
    vfMidActualPrimeEndpointDefect B ^ 2 -
        vfMidActualPrimeEndpointDefect A ^ 2 =
      (vfMidDyadicFrozenSurvivorSeatCharge A B +
          vfMidDyadicProcessedOwnerSeatCharge A B) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect A *
          (vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B) := by
  have hT :=
    vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub
      hA hAB hBA
  rw [hT]
  ring

/-- A first-bad endpoint forces the exact accumulated-depth quadratic bill
above the squared radial wall at B.  This is the energy form that the #888
quarter-contraction must defeat; no local-gradient bound is used. -/
theorem vfMidActualPrimeFirstBadAt_forces_depthAwareEnergyTrigger
    {K : ℝ} {A B : ℕ}
    (hK : 0 ≤ K)
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A) :
    (K * vfMidSyntheticRadialScale B) ^ 2 -
        vfMidActualPrimeEndpointDefect A ^ 2 <
      (vfMidDyadicFrozenSurvivorSeatCharge A B +
          vfMidDyadicProcessedOwnerSeatCharge A B) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect A *
          (vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B) := by
  have hbad := hfirst.1
  unfold VFMidSyntheticBadAt at hbad
  have hB2 : 2 ≤ B := by omega
  have hscale : 0 < vfMidSyntheticRadialScale B :=
    vfMidSyntheticRadialScale_pos hB2
  have hwall0 : 0 ≤ K * vfMidSyntheticRadialScale B :=
    mul_nonneg hK hscale.le
  have habs0 : 0 ≤ |vfMidActualPrimeEndpointDefect B| := abs_nonneg _
  have habsPos : 0 < |vfMidActualPrimeEndpointDefect B| := by
    linarith
  have hsumPos :
      0 <
        |vfMidActualPrimeEndpointDefect B| +
          K * vfMidSyntheticRadialScale B :=
    add_pos_of_pos_of_nonneg habsPos hwall0
  have hprodPos :
      0 <
        (|vfMidActualPrimeEndpointDefect B| -
          K * vfMidSyntheticRadialScale B) *
        (|vfMidActualPrimeEndpointDefect B| +
          K * vfMidSyntheticRadialScale B) :=
    mul_pos (sub_pos.mpr hbad) hsumPos
  have hsq :
      (K * vfMidSyntheticRadialScale B) ^ 2 <
        vfMidActualPrimeEndpointDefect B ^ 2 := by
    rw [← sq_abs (vfMidActualPrimeEndpointDefect B)]
    nlinarith
  have henergy :=
    vfMidTwoSectorOwnerCharge_energyStep_eq
      hA hABlt.le hBA
  nlinarith

/-- The actual-prime endpoint defect is the repository square-endpoint error. -/
theorem vfMidActualPrimeEndpointDefect_eq_squareEndpointError
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidActualPrimeEndpointDefect R = vfMidSquareEndpointError R := by
  unfold vfMidActualPrimeEndpointDefect
  rw [← vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR]
  rfl

/-- On the literal one-block choice `B = R+1`, the complete #888 two-sector
charge is exactly the negative direct square-band error. -/
theorem vfMidTwoSectorOwnerCharge_succ_eq_neg_bandError
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
        vfMidDyadicProcessedOwnerSeatCharge R (R + 1) =
      -vfMidSquareBandError R := by
  have hT :=
    vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub
      (A := R) (B := R + 1) hR (by omega) (by omega)
  rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError (by omega : 2 ≤ R),
    vfMidActualPrimeEndpointDefect_eq_squareEndpointError
      (by omega : 2 ≤ R + 1)] at hT
  have hstep := vfMidSquareEndpointError_succ R (by omega : 2 ≤ R)
  linarith

/-- **Direct accumulated-depth weld.**

For the one-block anchor `A=R, B=R+1`, the #888 quadratic bill is literally
the already-compiled VF-native Lyapunov seat-Gram bill.  There is no remaining
translation between the first-bad endpoint energy and the physical seat Gram. -/
theorem vfMidTwoSectorOwnerCharge_energyStep_succ_eq_lyapunov
    {R : ℕ} (hR : 3 ≤ R) :
    (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
        vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) ^ 2 -
      2 * vfMidActualPrimeEndpointDefect R *
        (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
          vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) =
      vfMidOddLyapunovSeatGramBill R R := by
  have henergy :=
    vfMidTwoSectorOwnerCharge_energyStep_eq
      (A := R) (B := R + 1) hR (by omega) (by omega)
  rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
        (by omega : 2 ≤ R),
      vfMidActualPrimeEndpointDefect_eq_squareEndpointError
        (by omega : 2 ≤ R + 1)] at henergy
  have hseat :=
    vfMidSquareEndpointError_energy_step_eq_oddLyapunovSeatGramBill
      (A := R) (R := R) (by omega : 2 ≤ R) (by omega)
  rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
    (by omega : 2 ≤ R)]
  exact henergy.symm.trans hseat

/-- The same direct weld in the repository correlation coordinate.  This makes
the only possible remaining positive first-bad energy explicit:
`e_R^2 + 2 D_R e_R`. -/
theorem vfMidTwoSectorOwnerCharge_energyStep_succ_eq_correlation
    {R : ℕ} (hR : 3 ≤ R) :
    (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
        vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) ^ 2 -
      2 * vfMidActualPrimeEndpointDefect R *
        (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
          vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) =
      2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 := by
  have henergy :=
    vfMidTwoSectorOwnerCharge_energyStep_eq
      (A := R) (B := R + 1) hR (by omega) (by omega)
  rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
        (by omega : 2 ≤ R),
      vfMidActualPrimeEndpointDefect_eq_squareEndpointError
        (by omega : 2 ≤ R + 1)] at henergy
  have hcorr :=
    vfMidSquareEndpointError_sq_succ_eq_correlation
      R (by omega : 2 ≤ R)
  rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
    (by omega : 2 ≤ R)]
  exact henergy.symm.trans hcorr

/-- **Unified pre-inequality affine pair transport.**

The complete first-bad quadratic bill is now written on the four-sector #888
pair ledger before any inequality is introduced.  In particular the
survivor/processed cross terms are not discarded or bounded separately. -/
theorem vfMidCorrelationEnergy_eq_completeAffinePairLedger_sub_anchor
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidOneBlockCompleteAffinePairLedger R -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
            vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) := by
  calc
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
          vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
            vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) :=
      (vfMidTwoSectorOwnerCharge_energyStep_succ_eq_correlation hR).symm
    _ = vfMidOneBlockCompleteAffinePairLedger R -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
            vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) := by
      rw [← vfMidOneBlockCompleteAffinePairLedger_eq_twoSector_sq R]

/-- Exact sign-normalized form of the terminal correlation bill.

The two-sector owner charge is `-e_R`, so the anchor polarization contributes
`+ 2 D_R e_R`.  Keeping this sign explicit prevents an invalid terminal
contraction from being obtained by replacing the owner charge with the band
error without negating it. -/
theorem vfMidCorrelationEnergy_eq_completeAffinePairLedger_add_anchorBand
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidOneBlockCompleteAffinePairLedger R +
        2 * vfMidActualPrimeEndpointDefect R *
          vfMidSquareBandError R := by
  calc
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidOneBlockCompleteAffinePairLedger R -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
            vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) :=
      vfMidCorrelationEnergy_eq_completeAffinePairLedger_sub_anchor hR
    _ =
      vfMidOneBlockCompleteAffinePairLedger R +
        2 * vfMidActualPrimeEndpointDefect R *
          vfMidSquareBandError R := by
      rw [vfMidTwoSectorOwnerCharge_succ_eq_neg_bandError hR]
      ring


/-- **Terminal full-carrier zip.**

The entire one-step first-bad correlation energy is now one literal signed field
on the current odd square-block seats.  The current-current affine classifier and
the historical-current polarization have been joined before any reciprocal
energy or inequality gate is introduced. -/
theorem vfMidCorrelationEnergy_eq_unifiedCurrentPhysicalSeatLedger
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidOneBlockUnifiedPhysicalSeatLedger R := by
  calc
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidOneBlockCompleteAffinePairLedger R +
        2 * vfMidActualPrimeEndpointDefect R *
          vfMidSquareBandError R :=
      vfMidCorrelationEnergy_eq_completeAffinePairLedger_add_anchorBand hR
    _ = vfMidOneBlockUnifiedPhysicalSeatLedger R :=
      vfMidOneBlockAffinePair_add_historical_eq_unifiedPhysicalSeatLedger hR

/-- Unified physical carrier for the complete one-step VF Lyapunov bill.

This keeps the current-current affine pair ledger, the literal historical-current
seat rectangle, and the fixed base-anchor polarization in one signed object.
No inequality, absolute value, reciprocal weight, or carrier enlargement occurs
in this definition. -/
def vfMidUnifiedPhysicalSeatGramBill (R : ℕ) : ℝ :=
  vfMidOneBlockCompleteAffinePairLedger R +
    2 * vfMidOddHistoricalCurrentSeatGram 2 R +
    2 * vfMidActualPrimeEndpointDefect 2 *
      vfMidSquareBandError R

/-- **Exact affine-to-physical full-carrier reassembly.**

The sign-normalized affine bill `e_R^2 + 2 D_R e_R` is exactly the complete
current-current pair ledger plus twice the historical-current physical seat
rectangle plus the fixed base anchor.  This is the equality that must precede
every inequality gate. -/
theorem vfMidCorrelationEnergy_eq_unifiedPhysicalSeatGramBill
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidUnifiedPhysicalSeatGramBill R := by
  calc
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidOneBlockCompleteAffinePairLedger R +
        2 * vfMidActualPrimeEndpointDefect R *
          vfMidSquareBandError R :=
      vfMidCorrelationEnergy_eq_completeAffinePairLedger_add_anchorBand hR
    _ = vfMidUnifiedPhysicalSeatGramBill R := by
      unfold vfMidUnifiedPhysicalSeatGramBill
      rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
          (R := R) (by omega : 2 ≤ R),
        vfMidActualPrimeEndpointDefect_eq_squareEndpointError
          (R := 2) (by omega : 2 ≤ 2),
        vfMidOddHistoricalCurrentSeatGram_eq_endpointPolarization
          (A := 2) (R := R) (by omega : 2 ≤ 2) (by omega : 2 ≤ R)]
      ring

/-- Unified physical carrier with the current-current affine ledger fully
decompressed back to literal least-prime-owned sites. -/
def vfMidUnifiedDecompressedPhysicalSeatGramBill (R : ℕ) : ℝ :=
  vfMidOneBlockDecompressedAffinePairLedger R +
    2 * vfMidOddHistoricalCurrentSeatGram 2 R +
    2 * vfMidActualPrimeEndpointDefect 2 *
      vfMidSquareBandError R

/-- **Complete site-level terminal reassembly.**

The first-bad correlation bill is exactly the sum of the literal current-current
physical site ledger, twice the literal historical-current site rectangle, and
the fixed base-anchor polarization.  No processed-owner cardinality atom remains
in the current-current term. -/
theorem vfMidCorrelationEnergy_eq_unifiedDecompressedPhysicalSeatGramBill
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidUnifiedDecompressedPhysicalSeatGramBill R := by
  rw [vfMidCorrelationEnergy_eq_unifiedPhysicalSeatGramBill hR]
  unfold vfMidUnifiedPhysicalSeatGramBill
    vfMidUnifiedDecompressedPhysicalSeatGramBill
  rw [vfMidOneBlockCompleteAffinePairLedger_eq_decompressedPhysical]

/-- The unified #889 physical carrier is literally the pre-existing native
Lyapunov seat-Gram bill anchored at the first square scale. -/
theorem vfMidUnifiedPhysicalSeatGramBill_eq_oddLyapunovSeatGramBill
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidUnifiedPhysicalSeatGramBill R =
      vfMidOddLyapunovSeatGramBill 2 R := by
  unfold vfMidUnifiedPhysicalSeatGramBill vfMidOddLyapunovSeatGramBill
  rw [vfMidOneBlockCompleteAffinePairLedger_eq_bandError_sq hR,
    vfMidOddCurrentSeatSelfGram_eq_bandError_sq R (by omega : 2 ≤ R),
    vfMidActualPrimeEndpointDefect_eq_squareEndpointError
      (R := 2) (by omega : 2 ≤ 2)]

/-- Direct combined form: the terminal correlation bill is exactly the literal
native physical Lyapunov seat Gram before any contraction is applied. -/
theorem vfMidCorrelationEnergy_eq_oddLyapunovSeatGramBill
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      vfMidOddLyapunovSeatGramBill 2 R := by
  rw [vfMidCorrelationEnergy_eq_unifiedPhysicalSeatGramBill hR,
    vfMidUnifiedPhysicalSeatGramBill_eq_oddLyapunovSeatGramBill hR]

/-- **Common-frozen raw terminal normal form.**

For any frozen anchor `A <= R` inside the subdoubling geometry, the complete
one-step correlation bill is the square increment of the literal
survivor+processed physical run, plus only the accumulated anchor polarization.
No inequality or reciprocal currency appears. -/
theorem vfMidCorrelationEnergy_eq_frozenAffineRunStep_add_anchor
    {A R : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      (vfMidFrozenAffineRunPhysicalCharge A (R + 1) ^ 2 -
        vfMidFrozenAffineRunPhysicalCharge A R ^ 2) +
        2 * vfMidActualPrimeEndpointDefect A *
          vfMidSquareBandError R := by
  have hcorr :=
    vfMidSquareEndpointError_sq_succ_eq_correlation
      R (by omega : 2 ≤ R)
  have hnative :=
    vfMidSquareEndpointError_energy_step_eq_oddLyapunovSeatGramBill
      (A := A) (R := R) (by omega : 2 ≤ A) hAR
  have hbill :
      2 * vfMidSquareEndpointAccumulationCorrelation R +
          vfMidSquareBandError R ^ 2 =
        vfMidOddLyapunovSeatGramBill A R := by
    exact hcorr.symm.trans hnative
  rw [hbill]
  unfold vfMidOddLyapunovSeatGramBill
  rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
      (R := A) (by omega : 2 ≤ A)]
  have hstep :=
    vfMidFrozenAffineRunPhysicalCharge_energyStep_eq
      hA hAR hRlt
  rw [hstep]
  rw [vfMidFrozenAffineBlockPhysicalCharge_eq_blockSeatMass
      hA hAR hRlt,
    vfMidOddBlockSeatMass_eq_neg_bandError R (by omega : 2 ≤ R),
    vfMidFrozenAffineHistoricalCurrentPhysicalPairMass_eq
      hA hAR hRlt,
    vfMidOddCurrentSeatSelfGram_eq_bandError_sq
      R (by omega : 2 ≤ R)]
  ring

/-- Exact adjacent-square Fubini transport of the #889 two-sector charge.

The resolved Euler forcing is not the raw two-sector charge itself: logarithmic
position and prime-power endpoint corrections remain explicit. -/
theorem vfMidAdjacentSquareResolvedEulerForcing_eq_twoSectorOwnerCharge
    {R : ℕ} (hR : 7 ≤ R) :
    nativePNTSequentialEulerForcing
        R (R ^ 2) ((R + 1) ^ 2) =
      -Real.log (vfMidBandMidpoint R) *
          (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
            vfMidDyadicProcessedOwnerSeatCharge R (R + 1) +
            vfMidDirectLogPositionError R) +
        (vfMidSquarePrimePowerCorrection (R + 1) -
          vfMidSquarePrimePowerCorrection R) := by
  have heuler :=
    vfMidAdjacentSquareResolvedEulerForcing_eq_vfBandError R hR
  have hcharge :=
    vfMidTwoSectorOwnerCharge_succ_eq_neg_bandError
      (by omega : 3 ≤ R)
  calc
    nativePNTSequentialEulerForcing
        R (R ^ 2) ((R + 1) ^ 2) =
      Real.log (vfMidBandMidpoint R) *
          (vfMidSquareBandError R -
            vfMidDirectLogPositionError R) +
        (vfMidSquarePrimePowerCorrection (R + 1) -
          vfMidSquarePrimePowerCorrection R) := heuler
    _ =
      -Real.log (vfMidBandMidpoint R) *
          (vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
            vfMidDyadicProcessedOwnerSeatCharge R (R + 1) +
            vfMidDirectLogPositionError R) +
        (vfMidSquarePrimePowerCorrection (R + 1) -
          vfMidSquarePrimePowerCorrection R) := by
      have he :
          vfMidSquareBandError R =
            -(vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
              vfMidDyadicProcessedOwnerSeatCharge R (R + 1)) := by
        linarith
      rw [he]
      ring

/-- **Direct first-bad energy trigger on one square block.**

This is the terminal lower bound with every bookkeeping coordinate eliminated:
a first bad endpoint at `R+1` forces the actual VF accumulation correlation
plus the current self-energy above the remaining squared radial budget. -/
theorem vfMidActualPrimeFirstBadAt_succ_forces_correlationEnergyTrigger
    {K : ℝ} {R : ℕ}
    (hK : 0 ≤ K)
    (hR : 3 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt K (R + 1)) :
    (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
        vfMidActualPrimeEndpointDefect R ^ 2 <
      2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 := by
  have h :=
    vfMidActualPrimeFirstBadAt_forces_depthAwareEnergyTrigger
      hK hfirst hR (by omega : R < R + 1) (by omega : R + 1 ≤ 2 * R)
  rw [vfMidTwoSectorOwnerCharge_energyStep_succ_eq_correlation hR] at h
  exact h

/-- A first-bad scale forces the exact two-sector charge to exceed the
**remaining global radial slack**, not merely the local radial gradient.

Equivalently:
`|T(A,B)| > K*rho(B) - |D_A|`.
The right side is
`K*(rho(B)-rho(A)) + (K*rho(A)-|D_A|)`, i.e. local gradient plus the
accumulated slack of the prior-good anchor. -/
theorem vfMidActualPrimeFirstBadAt_forces_depthAwareTwoSectorAbsTrigger
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A) :
    K * vfMidSyntheticRadialScale B -
        |vfMidActualPrimeEndpointDefect A| <
      |vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B| := by
  have hbad := hfirst.1
  unfold VFMidSyntheticBadAt at hbad
  have hT :=
    vfMidTwoSectorOwnerCharge_eq_endpointDefect_sub
      hA hABlt.le hBA
  have hDB :
      vfMidActualPrimeEndpointDefect B =
        vfMidActualPrimeEndpointDefect A -
          (vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B) := by
    linarith
  have htri :
      |vfMidActualPrimeEndpointDefect B| ≤
        |vfMidActualPrimeEndpointDefect A| +
          |vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B| := by
    rw [hDB]
    calc
      |vfMidActualPrimeEndpointDefect A -
          (vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B)| =
        |vfMidActualPrimeEndpointDefect A +
          (-(vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B))| := by ring_nf
      _ ≤ |vfMidActualPrimeEndpointDefect A| +
          |-(vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B)| :=
        abs_add_le _ _
      _ = |vfMidActualPrimeEndpointDefect A| +
          |vfMidDyadicFrozenSurvivorSeatCharge A B +
            vfMidDyadicProcessedOwnerSeatCharge A B| := by
        rw [abs_neg]
  linarith

/-- The anchor part of the depth-aware threshold is genuine nonnegative slack,
because every earlier scale of a first-bad trajectory is prior-good. -/
theorem vfMidActualPrimeFirstBadAt_anchorSlack_nonneg
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A)
    (hABlt : A < B) :
    0 ≤
      K * vfMidSyntheticRadialScale A -
        |vfMidActualPrimeEndpointDefect A| := by
  have hprior :=
    vfMidActualPrimeFirstBadAt_prior_inside
      hfirst (by omega : 2 ≤ A) hABlt
  linarith

/-- Pure algebra: the depth-aware threshold is exactly local radial growth plus
the accumulated slack at the anchor. -/
theorem vfMid_depthAwareThreshold_eq_gradient_add_anchorSlack
    (K : ℝ) (A B : ℕ) :
    K * vfMidSyntheticRadialScale B -
        |vfMidActualPrimeEndpointDefect A| =
      K * (vfMidSyntheticRadialScale B -
        vfMidSyntheticRadialScale A) +
      (K * vfMidSyntheticRadialScale A -
        |vfMidActualPrimeEndpointDefect A|) := by
  ring

/-- Algebraic terminal adapter only.

This theorem is intentionally **not** counted as the missing arithmetic result:
its `hceiling` hypothesis is exactly the depth-aware structural ceiling that
must be derived from the #887/#888 restricted reciprocal ledger and prior-good
children.  Once that ceiling is proved, the first-bad contradiction is
immediate. -/
theorem vfMidActualPrimeFirstBadAt_impossible_of_depthAwareCeiling
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A)
    (hABlt : A < B)
    (hBA : B ≤ 2 * A)
    (hceiling :
      |vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B| ≤
        K * vfMidSyntheticRadialScale B -
          |vfMidActualPrimeEndpointDefect A|) :
    False := by
  have hbreach :=
    vfMidActualPrimeFirstBadAt_forces_depthAwareTwoSectorAbsTrigger
      hfirst hA hABlt hBA
  linarith



/-- **Full #889 Lyapunov source in native descended VF currency.**

For R >= 7 the complete affine/historical first-bad bill is exactly the square
of the native lower-scale aggregate plus its already-proved descent remainder,
with the accumulated endpoint defect retained as the historical scalar.

This is an equality, not an estimate:
  corrBill = (G_native + Rem)^2 - 2 D_R (G_native + Rem).
No packet inheritance or reciprocal-energy promotion is used. -/
theorem vfMidCorrelationEnergy_eq_nativeDescentAffineBill
    {R : ℕ} (hR : 7 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 =
      (vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R) ^ 2 -
        2 * vfMidActualPrimeEndpointDefect R *
          (vfMidRecursiveAggregateNativeCharge R +
            vfMidNativeDescentRemainder R) := by
  have hdesc :=
    vfMidOddCompositeTrackingDefect_eq_nativeCharge_add_descentRemainder
      R hR
  have hseat :=
    vfMidOddBlockSeatMass_eq_trackingDefect R (by omega : 2 ≤ R)
  have hneg :=
    vfMidOddBlockSeatMass_eq_neg_bandError R (by omega : 2 ≤ R)
  have hband :
      vfMidSquareBandError R =
        -(vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R) := by
    rw [hseat] at hneg
    rw [hdesc] at hneg
    linarith
  rw [vfMidCorrelationEnergy_eq_completeAffinePairLedger_add_anchorBand
      (by omega : 3 ≤ R),
    vfMidOneBlockCompleteAffinePairLedger_eq_bandError_sq
      (by omega : 3 ≤ R),
    hband]
  ring

/-- **Terminal first-bad contradiction in the native quadratic currency.**

This is the literal final `linarith` gate.  The lower inequality is already
forced by a first-bad endpoint; the upper inequality is exactly what the signed
rank-exhaustion splice must now deliver from the merged #887--#891 carrier.

No absolute-value wall, packet inheritance, or change of currency occurs here.
-/
theorem vfMidActualPrimeFirstBadAt_succ_finalContraction
    {K : ℝ} {R : ℕ}
    (hK : 0 ≤ K)
    (hR : 3 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt K (R + 1))
    (hrank :
      2 * vfMidSquareEndpointAccumulationCorrelation R +
          vfMidSquareBandError R ^ 2 ≤
        (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
          vfMidActualPrimeEndpointDefect R ^ 2) :
    False := by
  have hbreach :=
    vfMidActualPrimeFirstBadAt_succ_forces_correlationEnergyTrigger
      hK hR hfirst
  linarith


end RHLean.Analysis
