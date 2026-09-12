import Mathlib
import RHLean.Proof.FinalCompensatedParentReduction
import RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis

/-!
# Frozen/top/far energy bridge

After the corrected post-q^2 endpoint recovery, the coupled child-far,
renewal, and terminal populations are exactly the negative of the historical
frozen/top/far residual.  This file records that identity and then shows that
the natural factor-three frozen/top/far energy statement is equivalent to the
repository's square-root endpoint amplification statement.

The equivalence is structural.  It does not prove the remaining RH-scale
energy estimate.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The three far populations exposed after the corrected signed subtraction
are exactly the negative frozen/top/far residual. -/
theorem farPopulations_eq_neg_frozenTopFar
    (R : ℕ) (hR : 56 ≤ R) :
    squareEndpointQ2ChildFarSliceColumn R + stableFarRenewalColumn R +
        stableFarTerminalProductColumn R =
      -lowWheelFrozenTopFarResidual R := by
  have hfar := squarePrefixMertens_eq_farPopulations_add_rootBoundary R hR
  have hfrozen := squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar R hR
  linear_combination hfar - hfrozen

/-- FAR-3 in its exact current form: the frozen/top/far packet is controlled by
three times the genuine odd-owner q^2 daughter energy plus an RH-scale root
boundary. -/
def FrozenTopFarThreeEnergyStatement : Prop :=
  ∃ CF : ℝ, 0 ≤ CF ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
        3 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          rawQ2ChildEnergyReal R q +
        CF * (R : ℝ) ^ 2 * K

private theorem one_le_lowerMertensCriticalEnvelope
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  have hm0 : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  rw [hm0] at h0
  norm_num at h0
  exact h0

private theorem norm_mertensSummatory_sq_eq_realInt_sq_local (x : ℕ) :
    ‖RHLean.Analysis.mertensSummatory x‖ ^ 2 =
      ((mertensSummatoryInt x : ℤ) : ℝ) ^ 2 := by
  rw [← mertensSummatoryInt_cast x, Complex.norm_intCast]

private theorem squareEndpointMertensEnergyReal_eq_squarePrefix_norm_sq
    {R : ℕ} (hR : 1 ≤ R) :
    squareEndpointMertensEnergyReal R =
      ‖squarePrefixMertens (R - 1)‖ ^ 2 := by
  unfold squareEndpointMertensEnergyReal squarePrefixMertens
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR]
  symm
  exact norm_mertensSummatory_sq_eq_realInt_sq_local (squareRootEndpoint R)

private theorem squarePrefix_shifted_norm_sq_eq_realInt_sq
    {R : ℕ} (hR : 1 ≤ R) :
    ‖squarePrefixMertens (R - 1) - 1‖ ^ 2 =
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) := by
  unfold squarePrefixMertens
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR]
  simpa [shiftedMertensEnergy] using
    shiftedMertensEnergy_eq_intSquare (squareRootEndpoint R)

private theorem norm_sub_sq_le_two (u v : ℂ) :
    ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_sub_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u - v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

private theorem norm_sub_sq_le_four_fourThirds (u v : ℂ) :
    ‖u - v‖ ^ 2 ≤ 4 * ‖u‖ ^ 2 + (4 : ℝ) / 3 * ‖v‖ ^ 2 := by
  have hnorm := norm_sub_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u - v‖ := norm_nonneg _
  nlinarith [sq_nonneg (3 * ‖u‖ - ‖v‖)]

private theorem squareEndpointMertensEnergyReal_le_root_fourth (R : ℕ) :
    squareEndpointMertensEnergyReal R ≤ (R : ℝ) ^ 4 := by
  let X : ℕ := squareRootEndpoint R
  have hnorm0 := norm_mertensSummatory_sub_le 0 X (Nat.zero_le X)
  have hnorm : ‖RHLean.Analysis.mertensSummatory X‖ ≤ (X : ℝ) := by
    simpa using hnorm0
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hnorm0' : 0 ≤ ‖RHLean.Analysis.mertensSummatory X‖ := norm_nonneg _
  have hsq :
      ‖RHLean.Analysis.mertensSummatory X‖ ^ 2 ≤ (X : ℝ) ^ 2 := by
    nlinarith
  have hXNat : X ≤ R ^ 2 := by
    dsimp [X, squareRootEndpoint]
    exact Nat.sub_le _ _
  have hX : (X : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hXNat
  have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  have hXsq : (X : ℝ) ^ 2 ≤ (R : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((R : ℝ) ^ 2 - (X : ℝ))]
  have henergy :
      squareEndpointMertensEnergyReal R =
        ‖RHLean.Analysis.mertensSummatory X‖ ^ 2 := by
    dsimp [X, squareEndpointMertensEnergyReal]
    symm
    exact norm_mertensSummatory_sq_eq_realInt_sq_local (squareRootEndpoint R)
  rw [henergy]
  exact hsq.trans hXsq

private theorem smallRoot_squareEndpointMertensEnergyReal_le
    {R : ℕ} {K : ℝ}
    (hR : 2 ≤ R) (hsmall : R < 56)
    (hK : LowerMertensCriticalEnvelope R K) :
    squareEndpointMertensEnergyReal R ≤
      3136 * (R : ℝ) ^ 2 * K := by
  have hbase := squareEndpointMertensEnergyReal_le_root_fourth R
  have hK1 : 1 ≤ K := one_le_lowerMertensCriticalEnvelope (by omega) hK
  have hRleNat : R ≤ 56 := by omega
  have hRle : (R : ℝ) ≤ 56 := by exact_mod_cast hRleNat
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hR2 : (R : ℝ) ^ 2 ≤ 3136 := by nlinarith
  have hfour : (R : ℝ) ^ 4 ≤ 3136 * (R : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((R : ℝ) ^ 2)]
  have hscale :
      3136 * (R : ℝ) ^ 2 ≤ 3136 * (R : ℝ) ^ 2 * K := by
    have hnonneg : 0 ≤ 3136 * (R : ℝ) ^ 2 := by positivity
    nlinarith
  exact hbase.trans (hfour.trans hscale)

private theorem rawQ2ChildEnergy_sum_nonneg (R : ℕ) :
    0 ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2,
      rawQ2ChildEnergyReal R q := by
  apply Finset.sum_nonneg
  intro q hq
  unfold rawQ2ChildEnergyReal
  positivity

/-- The factor-three frozen/top/far estimate is exactly the square-root endpoint
amplification seam.  The forward direction uses the existing literal factor-four
q^2 recurrence equivalence; the reverse direction uses the shifted endpoint
numerator and the `10 R` root boundary. -/
theorem frozenTopFarThreeEnergy_iff_endpointAmplification :
    FrozenTopFarThreeEnergyStatement ↔
      SquareRootMertensEndpointAmplificationStatement := by
  constructor
  · rintro ⟨CF, hCF, hfar⟩
    apply exists_nonneg_squareEndpointRawOddQ2EnergyStep_iff_endpointAmplification.mp
    let C : ℝ := (4 : ℝ) / 3 * CF + 3536
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    refine ⟨C, hC, ?_⟩
    intro R K hR hK
    let Q : ℝ := ∑ q ∈ (primesUpTo (R - 1)).erase 2,
      rawQ2ChildEnergyReal R q
    have hQ : 0 ≤ Q := by
      dsimp [Q]
      exact rawQ2ChildEnergy_sum_nonneg R
    have hK1 : 1 ≤ K := one_le_lowerMertensCriticalEnvelope (by omega) hK
    by_cases hlarge : 56 ≤ R
    · have hF := hfar R K hlarge hK
      change ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
        3 * Q + CF * (R : ℝ) ^ 2 * K at hF
      have hB := norm_finalCompensatedRootBoundary_le_ten_root R hlarge
      have hBsq :
          ‖finalCompensatedRootBoundary R‖ ^ 2 ≤ 100 * (R : ℝ) ^ 2 := by
        have hbn : 0 ≤ ‖finalCompensatedRootBoundary R‖ := norm_nonneg _
        have hR0 : 0 ≤ (R : ℝ) := by positivity
        nlinarith
      have hsplit := norm_sub_sq_le_four_fourThirds
        (finalCompensatedRootBoundary R) (lowWheelFrozenTopFarResidual R)
      rw [← squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar R hlarge] at hsplit
      have henergy := squareEndpointMertensEnergyReal_eq_squarePrefix_norm_sq
        (R := R) (by omega)
      rw [← henergy] at hsplit
      change squareEndpointMertensEnergyReal R ≤
        C * (R : ℝ) ^ 2 * K + 4 * Q
      dsimp [C]
      nlinarith [sq_nonneg (R : ℝ)]
    · have hsmall : R < 56 := by omega
      have hsmallBound :=
        smallRoot_squareEndpointMertensEnergyReal_le hR hsmall hK
      change squareEndpointMertensEnergyReal R ≤
        C * (R : ℝ) ^ 2 * K + 4 * Q
      dsimp [C]
      have hscale : 0 ≤ (R : ℝ) ^ 2 * K := by
        have hK0 : 0 ≤ K := hK.1
        positivity
      nlinarith
  · rintro ⟨A, hA, hamp⟩
    let CF : ℝ := 242 + 2 * A
    have hCF : 0 ≤ CF := by
      dsimp [CF]
      positivity
    refine ⟨CF, hCF, ?_⟩
    intro R K hR hK
    have hK1 : 1 ≤ K := one_le_lowerMertensCriticalEnvelope (by omega) hK
    have hAmp := hamp R K (by omega) hK
    have hMshift :
        ‖squarePrefixMertens (R - 1) - 1‖ ^ 2 ≤
          A * (R : ℝ) ^ 2 * K := by
      rw [squarePrefix_shifted_norm_sq_eq_realInt_sq (R := R) (by omega)]
      exact hAmp
    have hB := norm_finalCompensatedRootBoundary_le_ten_root R hR
    have hBshiftNorm :
        ‖finalCompensatedRootBoundary R - 1‖ ≤ 11 * (R : ℝ) := by
      have hsub := norm_sub_le (finalCompensatedRootBoundary R) (1 : ℂ)
      have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
      norm_num at hsub
      nlinarith
    have hBshiftSq :
        ‖finalCompensatedRootBoundary R - 1‖ ^ 2 ≤
          121 * (R : ℝ) ^ 2 := by
      have hn : 0 ≤ ‖finalCompensatedRootBoundary R - 1‖ := norm_nonneg _
      have hR0 : 0 ≤ (R : ℝ) := by positivity
      nlinarith
    have hendpoint := squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar R hR
    have hrewrite :
        lowWheelFrozenTopFarResidual R =
          (finalCompensatedRootBoundary R - 1) -
            (squarePrefixMertens (R - 1) - 1) := by
      linear_combination hendpoint
    have htwo := norm_sub_sq_le_two
      (finalCompensatedRootBoundary R - 1)
      (squarePrefixMertens (R - 1) - 1)
    rw [← hrewrite] at htwo
    have hcore :
        ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
          CF * (R : ℝ) ^ 2 * K := by
      dsimp [CF]
      nlinarith [sq_nonneg (R : ℝ)]
    have hQ := rawQ2ChildEnergy_sum_nonneg R
    exact hcore.trans (by
      have hthreeQ :
          0 ≤ 3 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
            rawQ2ChildEnergyReal R q := by positivity
      linarith)

end RHLean.Proof
