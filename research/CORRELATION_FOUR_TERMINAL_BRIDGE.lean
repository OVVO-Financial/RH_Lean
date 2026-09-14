import Mathlib
import RHLean.Proof.StableFarAdaptiveLedgerCollapse
import RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis

/-!
# CORR-4 to the subcritical q^2 terminal recurrence

This file isolates a strictly smaller analytic target than FAR-4.  The hard
input is a factor-four q^2 energy estimate for the canonical rough correlation
itself.  Two root-scale corrections are then absorbed with one percent Young
slack each.  The resulting literal q^2 coefficient is

  4 * (101/100)^2 = 10201/2500 = 4.0804,

which remains below the already compiled terminal threshold

  2592/629 = 4.1208...

No analytic estimate is proved here.  This is only deterministic closure wiring:
CORR-4 is sufficient for the existing RH terminal engine.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Factor-four q^2 energy bound on the canonical rough correlation. -/
def CanonicalRoughCorrelationFourQ2EnergyStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
        4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          rawQ2ChildEnergyReal R q +
        C * (R : ℝ) ^ 2 * K

private theorem one_le_lowerEnvelope_corrFour
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  have hm0 : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  rw [hm0] at h0
  norm_num at h0
  exact h0

private theorem rawQ2_sum_nonneg_corrFour (R : ℕ) :
    0 ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2,
      rawQ2ChildEnergyReal R q := by
  apply Finset.sum_nonneg
  intro q hq
  unfold rawQ2ChildEnergyReal
  positivity

/-- One-percent Young inequality with the first term kept almost intact. -/
private theorem norm_add_sq_le_onePercent
    (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤
      (101 : ℝ) / 100 * ‖u‖ ^ 2 + 101 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - 100 * ‖v‖)]

/-- One-percent Young inequality with the second term kept almost intact. -/
private theorem norm_sub_sq_le_onePercent
    (u v : ℂ) :
    ‖u - v‖ ^ 2 ≤
      101 * ‖u‖ ^ 2 + (101 : ℝ) / 100 * ‖v‖ ^ 2 := by
  have hnorm := norm_sub_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u - v‖ := norm_nonneg _
  nlinarith [sq_nonneg (100 * ‖u‖ - ‖v‖)]

private theorem norm_mertensSummatory_sq_eq_realInt_sq_corrFour (x : ℕ) :
    ‖RHLean.Analysis.mertensSummatory x‖ ^ 2 =
      ((mertensSummatoryInt x : ℤ) : ℝ) ^ 2 := by
  rw [← mertensSummatoryInt_cast x, Complex.norm_intCast]
  exact sq_abs (((mertensSummatoryInt x : ℤ) : ℝ))

private theorem squareEndpointEnergy_eq_squarePrefix_corrFour
    {R : ℕ} (hR : 1 ≤ R) :
    squareEndpointMertensEnergyReal R =
      ‖squarePrefixMertens (R - 1)‖ ^ 2 := by
  unfold squareEndpointMertensEnergyReal squarePrefixMertens
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR]
  symm
  exact norm_mertensSummatory_sq_eq_realInt_sq_corrFour (squareRootEndpoint R)

private theorem squareEndpointEnergy_le_root_fourth_corrFour (R : ℕ) :
    squareEndpointMertensEnergyReal R ≤ (R : ℝ) ^ 4 := by
  let X : ℕ := squareRootEndpoint R
  have hnorm0 := norm_mertensSummatory_sub_le 0 X (Nat.zero_le X)
  have hnorm : ‖RHLean.Analysis.mertensSummatory X‖ ≤ (X : ℝ) := by
    simpa using hnorm0
  have hnorm0' : 0 ≤ ‖RHLean.Analysis.mertensSummatory X‖ := norm_nonneg _
  have hsq :
      ‖RHLean.Analysis.mertensSummatory X‖ ^ 2 ≤ (X : ℝ) ^ 2 := by
    nlinarith
  have hXNat : X ≤ R ^ 2 := by
    dsimp [X, squareRootEndpoint]
    exact Nat.sub_le _ _
  have hX : (X : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hXNat
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  have hXsq : (X : ℝ) ^ 2 ≤ (R : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((R : ℝ) ^ 2 - (X : ℝ))]
  have henergy :
      squareEndpointMertensEnergyReal R =
        ‖RHLean.Analysis.mertensSummatory X‖ ^ 2 := by
    dsimp [X, squareEndpointMertensEnergyReal]
    symm
    exact norm_mertensSummatory_sq_eq_realInt_sq_corrFour (squareRootEndpoint R)
  rw [henergy]
  exact hsq.trans hXsq

private theorem smallRoot_energy_le_corrFour
    {R : ℕ} {K : ℝ}
    (hR : 2 ≤ R) (hsmall : R < 56)
    (hK : LowerMertensCriticalEnvelope R K) :
    squareEndpointMertensEnergyReal R ≤
      3136 * (R : ℝ) ^ 2 * K := by
  have hbase := squareEndpointEnergy_le_root_fourth_corrFour R
  have hK1 : 1 ≤ K := one_le_lowerEnvelope_corrFour (by omega) hK
  have hRle : (R : ℝ) ≤ 56 := by
    exact_mod_cast (show R ≤ 56 by omega)
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hR2 : (R : ℝ) ^ 2 ≤ 3136 := by nlinarith
  have hfour : (R : ℝ) ^ 4 ≤ 3136 * (R : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((R : ℝ) ^ 2)]
  have hscale :
      3136 * (R : ℝ) ^ 2 ≤ 3136 * (R : ℝ) ^ 2 * K := by
    have hnonneg : 0 ≤ 3136 * (R : ℝ) ^ 2 := by positivity
    nlinarith
  exact hbase.trans (hfour.trans hscale)

/-- CORR-4 gives a literal q^2 recurrence at coefficient 10201/2500.  The two
one-percent losses are respectively the rough-root correction and the final
compensated root boundary. -/
theorem correlationFour_implies_rawQ2_10201_over_2500
    (hcorr : CanonicalRoughCorrelationFourQ2EnergyStatement) :
    ∃ C : ℝ, 0 ≤ C ∧
      SquareEndpointRawOddQ2EnergyStepWith ((10201 : ℝ) / 2500) C := by
  rcases hcorr with ⟨C0, hC0, hcorr⟩
  let CF : ℝ := (101 : ℝ) / 100 * C0 + 6464
  let C : ℝ := 10100 + (101 : ℝ) / 100 * CF
  have hCF : 0 ≤ CF := by dsimp [CF]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R K hR hK
  let Q : ℝ := ∑ q ∈ (primesUpTo (R - 1)).erase 2,
    rawQ2ChildEnergyReal R q
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact rawQ2_sum_nonneg_corrFour R
  have hK1 : 1 ≤ K := one_le_lowerEnvelope_corrFour (by omega) hK
  by_cases hlarge : 56 ≤ R
  · have hCorr := hcorr R K hlarge hK
    change ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
      4 * Q + C0 * (R : ℝ) ^ 2 * K at hCorr
    have hRoot := norm_frozenTopFarRoughRootCorrection_le_eight_root R hlarge
    have hRootSq :
        ‖frozenTopFarRoughRootCorrection R‖ ^ 2 ≤ 64 * (R : ℝ) ^ 2 := by
      have hn := norm_nonneg (frozenTopFarRoughRootCorrection R)
      have hR0 : 0 ≤ (R : ℝ) := by positivity
      nlinarith
    have hFsplit := norm_add_sq_le_onePercent
      (squareRootCanonicalRoughCorrelation R)
      (frozenTopFarRoughRootCorrection R)
    rw [← lowWheelFrozenTopFarResidual_eq_roughCorrelation_add_rootCorrection
      R hlarge] at hFsplit
    have hF :
        ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
          (101 : ℝ) / 25 * Q + CF * (R : ℝ) ^ 2 * K := by
      dsimp [CF]
      nlinarith [sq_nonneg (R : ℝ)]
    have hB := norm_finalCompensatedRootBoundary_le_ten_root R hlarge
    have hBSq :
        ‖finalCompensatedRootBoundary R‖ ^ 2 ≤ 100 * (R : ℝ) ^ 2 := by
      have hn := norm_nonneg (finalCompensatedRootBoundary R)
      have hR0 : 0 ≤ (R : ℝ) := by positivity
      nlinarith
    have hsplit := norm_sub_sq_le_onePercent
      (finalCompensatedRootBoundary R) (lowWheelFrozenTopFarResidual R)
    rw [← squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar R hlarge] at hsplit
    have henergy := squareEndpointEnergy_eq_squarePrefix_corrFour
      (R := R) (by omega)
    rw [← henergy] at hsplit
    change squareEndpointMertensEnergyReal R ≤
      C * (R : ℝ) ^ 2 * K + (10201 : ℝ) / 2500 * Q
    dsimp [C]
    nlinarith [sq_nonneg (R : ℝ)]
  · have hsmall : R < 56 := by omega
    have hsmallBound := smallRoot_energy_le_corrFour hR hsmall hK
    change squareEndpointMertensEnergyReal R ≤
      C * (R : ℝ) ^ 2 * K + (10201 : ℝ) / 2500 * Q
    dsimp [C, CF]
    have hscale : 0 ≤ (R : ℝ) ^ 2 * K := by positivity
    nlinarith [mul_nonneg hC0 hscale]

/-- The new literal coefficient remains strictly below the generic terminal
threshold. -/
theorem corrFour_10201_over_2500_is_subcritical :
    ((10201 : ℝ) / 2500) * ((37 : ℝ) / 36) * ((17 : ℝ) / 72) < 1 := by
  norm_num

/-- Therefore CORR-4 alone is sufficient for RH; no separate analytic estimate
on the root correction or final root boundary remains. -/
theorem riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
    (hcorr : CanonicalRoughCorrelationFourQ2EnergyStatement) :
    RiemannHypothesis := by
  rcases correlationFour_implies_rawQ2_10201_over_2500 hcorr with
    ⟨C, hC, hstep⟩
  apply RHLean.Analysis.riemannHypothesis_of_mertensEnergy
  exact mertensEnergyBounded_of_squareRootEndpointAmplification
    (squareEndpointRawOddQ2EnergyStepWith_implies_endpointAmplification
      hC (by norm_num) corrFour_10201_over_2500_is_subcritical hstep)

end RHLean.Proof
