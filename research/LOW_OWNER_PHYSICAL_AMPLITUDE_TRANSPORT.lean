import Mathlib
import «research.LOW_OWNER_PHYSICAL_CENSUS_CORRELATION»
import «research.STABLE_FAR_PERRON_QUARTER_FRAME_BOUND»

/-!
# Exact physical amplitude transport and its full signed correction

This is the literal zero-frequency endpoint test of the proposed AMP route.
The parent is the existing canonical rough correlation; the daughter is the
unmodified Mertens endpoint at `floor((R^2-1)/q^2)`.

The signed physical census already proves that one low-owner atom is

  M(Y_q) + NearHigh_q - IntermediateTower_q - Go_q = -ChildFar_q.

Replacing its unit coefficient on `M(Y_q)` by the critical multiplier `m_q`
therefore leaves the explicit correction

  (1-m_q) M(Y_q) + NearHigh_q - IntermediateTower_q - Go_q.

The complete AMP correction sums these terms, then retains owner two,
stable-far renewal, terminal products and the known root correction. It is
defined from those arithmetic populations, not as `parent - synthesis`.

We prove the exact transport and its energy corollary, with coefficient `1/2`
on the genuine raw daughter energy. The remaining assumption is displayed
explicitly: a root-scale square bound on this *whole* signed correction. No
such bound is proved here, and the clipping identity alone does not supply it.

At nonzero frequency the parent below remains the original physical endpoint;
the correction changes with the inserted multiplier. This does not assert a
new Perron inversion or identify an unspecified frequency-space parent.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The genuine raw endpoint daughter, without an owner-dependent rescaling. -/
def lowOwnerRawMertensAmplitude (R q : ℕ) : ℂ :=
  ((mertensSummatoryInt (rawQ2ChildCutoff R q) : ℤ) : ℂ)

/-- Critical synthesis of the genuine low-owner daughters. -/
def lowOwnerCriticalMertensSynthesis (R : ℕ) (tau : ℝ) : ℂ :=
  stableFarCriticalQ2Synthesis tau (canonicalRoughLowQ2Owners R)
    (lowOwnerRawMertensAmplitude R)

/-- Exact correction within one fully compensated physical owner atom. -/
def lowOwnerAmplitudeTransportCorrection (R q : ℕ) (tau : ℝ) : ℂ :=
  (1 - stableFarCriticalQ2LogMultiplier tau q) * lowOwnerRawMertensAmplitude R q +
    ((q2DaughterNearHighTransport R q : ℤ) : ℂ) -
    ((q2DaughterFarIntermediatePrimeTower R q : ℤ) : ℂ) -
    ((squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R) : ℤ) : ℂ)

/-- The complete signed AMP remainder, retaining every census population. -/
def lowOwnerPhysicalAmplitudeRemainder (R : ℕ) (tau : ℝ) : ℂ :=
  (∑ q ∈ canonicalRoughLowQ2Owners R, lowOwnerAmplitudeTransportCorrection R q tau) +
    farFourQ2OwnerSynthesisAtom R 2 -
    stableFarRenewalColumn R - stableFarTerminalProductColumn R -
    frozenTopFarRoughRootCorrection R

/-- One atom decomposes before any norm is taken. -/
theorem farFourQ2OwnerSynthesisAtom_eq_critical_amplitude_add_correction
    (R q : ℕ) (tau : ℝ) :
    farFourQ2OwnerSynthesisAtom R q =
      stableFarCriticalQ2LogMultiplier tau q * lowOwnerRawMertensAmplitude R q +
        lowOwnerAmplitudeTransportCorrection R q tau := by
  unfold farFourQ2OwnerSynthesisAtom lowOwnerAmplitudeTransportCorrection
    lowOwnerRawMertensAmplitude rawQ2ChildCutoff
  ring

/-- The new correction has a literal physical description: the negative
child-far slice together with the subtracted critical Mertens amplitude. -/
theorem lowOwnerAmplitudeTransportCorrection_eq_neg_childFar_sub_critical
    {R q : ℕ} (hq : q ∈ primesUpTo (R - 1)) (tau : ℝ) :
    lowOwnerAmplitudeTransportCorrection R q tau =
      -(∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) -
        stableFarCriticalQ2LogMultiplier tau q * lowOwnerRawMertensAmplitude R q := by
  have h := farFourQ2OwnerSynthesisAtom_eq_critical_amplitude_add_correction R q tau
  rw [farFourQ2OwnerSynthesisAtom_eq_neg_childFarSlice hq] at h
  linear_combination -h

/-- **AMP with the full physical remainder.** This identifies the actual
parent and actual daughters. It makes no small-remainder assertion. -/
theorem squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder
    (R : ℕ) (hR : 56 ≤ R) (tau : ℝ) :
    squareRootCanonicalRoughCorrelation R =
      lowOwnerCriticalMertensSynthesis R tau + lowOwnerPhysicalAmplitudeRemainder R tau := by
  rw [squareRootCanonicalRoughCorrelation_eq_lowQ2Atoms_add_two_sub_chronology_sub_root R hR]
  have hs :
      (∑ q ∈ canonicalRoughLowQ2Owners R, farFourQ2OwnerSynthesisAtom R q) =
        lowOwnerCriticalMertensSynthesis R tau +
          ∑ q ∈ canonicalRoughLowQ2Owners R, lowOwnerAmplitudeTransportCorrection R q tau := by
    unfold lowOwnerCriticalMertensSynthesis stableFarCriticalQ2Synthesis
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    exact farFourQ2OwnerSynthesisAtom_eq_critical_amplitude_add_correction R q tau
  rw [hs]
  unfold lowOwnerPhysicalAmplitudeRemainder
  ring

/-- At frequency zero, the correction coefficient is literally `1-1/q`.
The critical multiplier does not disappear when the phase becomes one. -/
theorem lowOwnerAmplitudeTransportCorrection_zero
    {R q : ℕ} (hq : 0 < q) :
    lowOwnerAmplitudeTransportCorrection R q 0 =
      (1 - 1 / (q : ℂ)) * lowOwnerRawMertensAmplitude R q +
        ((q2DaughterNearHighTransport R q : ℤ) : ℂ) -
        ((q2DaughterFarIntermediatePrimeTower R q : ℤ) : ℂ) -
        ((squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R) : ℤ) : ℂ) := by
  unfold lowOwnerAmplitudeTransportCorrection
  rw [stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase 0 hq]
  simp

/-- The daughter norm is exactly the recursive energy already in LOW-4. -/
theorem norm_sq_lowOwnerRawMertensAmplitude (R q : ℕ) :
    ‖lowOwnerRawMertensAmplitude R q‖ ^ 2 = rawQ2ChildEnergyReal R q := by
  unfold lowOwnerRawMertensAmplitude rawQ2ChildEnergyReal
  rw [Complex.norm_intCast, sq_abs]

/-- The full odd-prime quarter budget also controls its low-owner subset. -/
theorem lowOwnerCriticalMertensSynthesis_energy_le_quarter (R : ℕ) (tau : ℝ) :
    ‖lowOwnerCriticalMertensSynthesis R tau‖ ^ 2 ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have hsub : canonicalRoughLowQ2Owners R ⊆ (primesUpTo (R - 1)).erase 2 :=
    Finset.sdiff_subset
  have hpos : ∀ q ∈ canonicalRoughLowQ2Owners R, 0 < q := by
    intro q hq
    exact (mem_primesUpTo.mp (Finset.mem_erase.mp (hsub hq)).2).1.pos
  have hbudget :
      (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 / 4 := by
    calc
      _ ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2, (1 : ℝ) / (q : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro q _hq _hnot
        positivity
      _ ≤ 1 / 4 := oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter (R - 1)
  have hframe := stableFarCriticalQ2Synthesis_energy_le_reciprocalSquareBudget
    tau (canonicalRoughLowQ2Owners R) (lowOwnerRawMertensAmplitude R) hpos
  simp only [norm_sq_lowOwnerRawMertensAmplitude] at hframe
  change ‖lowOwnerCriticalMertensSynthesis R tau‖ ^ 2 ≤
    (∑ q ∈ canonicalRoughLowQ2Owners R, (1 : ℝ) / (q : ℝ) ^ 2) *
      canonicalRoughLowQ2DaughterEnergy R at hframe
  exact hframe.trans (mul_le_mul_of_nonneg_right hbudget
    (canonicalRoughLowQ2DaughterEnergy_nonneg R))

/-- Signed physical reassembly precedes the amplitude estimate. -/
theorem norm_correlation_le_half_sqrt_lowEnergy_add_physicalRemainder
    (R : ℕ) (hR : 56 ≤ R) (tau : ℝ) :
    ‖squareRootCanonicalRoughCorrelation R‖ ≤
      (1 / 2 : ℝ) * Real.sqrt (canonicalRoughLowQ2DaughterEnergy R) +
        ‖lowOwnerPhysicalAmplitudeRemainder R tau‖ := by
  have hframe := lowOwnerCriticalMertensSynthesis_energy_le_quarter R tau
  have hsqrt := Real.sq_sqrt (canonicalRoughLowQ2DaughterEnergy_nonneg R)
  have hnorm : ‖lowOwnerCriticalMertensSynthesis R tau‖ ≤
      (1 / 2 : ℝ) * Real.sqrt (canonicalRoughLowQ2DaughterEnergy R) := by
    have hnon := Real.sqrt_nonneg (canonicalRoughLowQ2DaughterEnergy R)
    nlinarith [norm_nonneg (lowOwnerCriticalMertensSynthesis R tau)]
  rw [squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder R hR tau]
  exact (norm_add_le _ _).trans (add_le_add_right hnorm _)

/-- Energy is an immediate corollary only after the exact full remainder is
retained. No ownerwise norm of a physical population enters the proof. -/
theorem correlation_energy_le_half_lowEnergy_add_twice_physicalRemainder
    (R : ℕ) (hR : 56 ≤ R) (tau : ℝ) :
    ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
      (1 / 2 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        2 * ‖lowOwnerPhysicalAmplitudeRemainder R tau‖ ^ 2 := by
  have hframe := lowOwnerCriticalMertensSynthesis_energy_le_quarter R tau
  have htri := norm_add_le (lowOwnerCriticalMertensSynthesis R tau)
    (lowOwnerPhysicalAmplitudeRemainder R tau)
  rw [← squareRootCanonicalRoughCorrelation_eq_criticalSynthesis_add_physicalRemainder R hR tau] at htri
  have hsum : 0 ≤ ‖lowOwnerCriticalMertensSynthesis R tau‖ +
      ‖lowOwnerPhysicalAmplitudeRemainder R tau‖ := by positivity
  have hsq : ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
      (‖lowOwnerCriticalMertensSynthesis R tau‖ +
        ‖lowOwnerPhysicalAmplitudeRemainder R tau‖) ^ 2 := by
    nlinarith [norm_nonneg (squareRootCanonicalRoughCorrelation R)]
  nlinarith [sq_nonneg (‖lowOwnerCriticalMertensSynthesis R tau‖ -
    ‖lowOwnerPhysicalAmplitudeRemainder R tau‖)]

/-- The precise outstanding AMP bound, stated on the defined physical
correction at zero frequency and with the existing lower-envelope convention. -/
def LowOwnerPhysicalAmplitudeRemainderBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ, 56 ≤ R → LowerMertensCriticalEnvelope R K →
    ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤ C * (R : ℝ) ^ 2 * K

/-- A root-scale bound on the full AMP correction gives the claimed
coefficient `1/2` on the actual LOW-4 daughter energy. The assumption is
explicit and is not discharged by a multiplier or coordinate identity. -/
theorem correlationLowQ2Energy_of_physicalAmplitudeRemainderBound
    {C : ℝ} (hE : LowOwnerPhysicalAmplitudeRemainderBound C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith (1 / 2) (2 * C) := by
  intro R K hR hK
  have h := correlation_energy_le_half_lowEnergy_add_twice_physicalRemainder R hR 0
  have he := hE R K hR hK
  nlinarith

/-! ## A physical owner can survive a zero Mertens daughter

This certificate concerns the actual compensated far-slice atom. It does not
refute the global AMP statement with a signed remainder.
-/

private def lowOwnerFarBaseEval (R q : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (R + 7) (rawQ2ChildCutoff R q),
    frozenPredecessorMobiusEval q (rawQ2ChildCutoff R q / p)

private theorem q2DaughterFarBaseColumn_eq_lowOwnerFarBaseEval
    {R q : ℕ} (hq : q.Prime) :
    q2DaughterFarBaseColumn R q = lowOwnerFarBaseEval R q := by
  unfold q2DaughterFarBaseColumn lowOwnerFarBaseEval rawQ2ChildCutoff
  apply Finset.sum_congr rfl
  intro p _hp
  exact frozenPrimeUniverseMass_eq_frozenPredecessorMobiusEval hq

/-- An actual low owner has a zero raw daughter but a nonzero physical atom. -/
theorem lowOwnerPhysicalAmplitude_zero_daughter_witness :
    rawQ2ChildCutoff 64 5 = 163 ∧
      lowOwnerRawMertensAmplitude 64 5 = 0 ∧
      farFourQ2OwnerSynthesisAtom 64 5 = -16 := by
  have hM : mertensSummatoryInt 163 = 0 := by native_decide
  have hF : lowOwnerFarBaseEval 64 5 = 16 := by native_decide
  have hq : 5 ∈ primesUpTo (64 - 1) :=
    mem_primesUpTo.mpr ⟨by norm_num, by norm_num⟩
  refine ⟨by norm_num [rawQ2ChildCutoff, squareRootEndpoint], ?_, ?_⟩
  · change ((mertensSummatoryInt 163 : ℤ) : ℂ) = 0
    rw [hM]
    norm_num
  · rw [farFourQ2OwnerSynthesisAtom_eq_neg_farBase hq,
      q2DaughterFarBaseColumn_eq_lowOwnerFarBaseEval (by norm_num : Nat.Prime 5), hF]
    norm_num

/-- Thus a local linear factorization of the physical owner atom through its
raw Mertens daughter already fails; a signed correction is unavoidable. -/
theorem lowOwnerPhysicalAmplitude_not_scalar_multiple_of_raw_daughter
    (c : ℂ) :
    farFourQ2OwnerSynthesisAtom 64 5 ≠ c * lowOwnerRawMertensAmplitude 64 5 := by
  obtain ⟨_hY, hM, hA⟩ := lowOwnerPhysicalAmplitude_zero_daughter_witness
  rw [hM, hA]
  norm_num

end RHLean.Proof
