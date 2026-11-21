import Mathlib
import RHLean.Proof.SquareRootCrossRegionAmplification
import «research.EULER_SELF_DUAL_ENDPOINT_GATE_20261027»
import «research.UNIVERSAL_ENVELOPE_RH_BRIDGES»

/-!
# Subpower finite-C arithmetic consequence of RH

The released Alpoge theorem has undergone independent kernel checks.
This module does NOT import that external RH theorem or claim an independent
proof of RH. It establishes the exact original arithmetic consequence
with an explicit R-dependent epsilon-loss and strict historical K_R.
The stronger fixed-constant finite-C estimate is NOT implied here.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Analysis.MertensExponent
open RHLean.Analysis.UniversalEnvelope

/-- Original signed Euler finite-C source, bounded at the RH subpower scale
with every valid strict-history critical envelope. -/
def EulerSelfDualFiniteCSubpowerStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, ∀ K : ℝ,
        2 ≤ R →
        LowerMertensCriticalEnvelope R K →
        ‖eulerSelfDualBilinear R‖ ≤
          C * Real.rpow (R : ℝ) (1 + ε) * Real.sqrt K

/-- RH proves the actual subpower finite-C inequality, without assuming
character cancellation or an invented constant. It does not prove the
historically stronger epsilon-free finite-C bound. -/
theorem eulerSelfDualFiniteCSubpower_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    EulerSelfDualFiniteCSubpowerStatement := by
  have hhalf : MertensGrowthAtMost ((1 : ℝ) / 2) :=
    mertens_half_iff_riemannHypothesis.mpr hRH
  intro ε hε
  have hδ : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨C, hC, hM⟩ := hhalf (ε / 4) hδ
  refine ⟨3 * C, by positivity, ?_⟩
  intro R K hR hK
  have hRpos : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hRone : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have he : (0 : ℝ) ≤ (1 / 2 : ℝ) + ε / 4 := by linarith
  have he1 : (1 / 2 : ℝ) + ε / 4 ≤ 1 + ε := by linarith
  have he2 : (1 : ℝ) + ε / 2 ≤ 1 + ε := by linarith
  have hpre : (1 : ℕ) ≤ R - 1 := by omega
  have hpreR : ((R - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (Nat.sub_le R 1)
  have hX : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have h4 : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hXR : ((squareRootEndpoint R : ℕ) : ℝ) ≤ (R : ℝ) ^ 2 := by
    have h := Nat.sub_le (R ^ 2) 1
    simp only [squareRootEndpoint]
    exact_mod_cast h
  have hpreBound :
      ‖mertensSummatory (R - 1)‖ ≤
        C * Real.rpow (R : ℝ) (1 + ε) := by
    calc
      _ ≤ C * Real.rpow (((R - 1 : ℕ) : ℝ)) ((1 / 2 : ℝ) + ε / 4) :=
        hM (R - 1) hpre
      _ ≤ C * Real.rpow (R : ℝ) ((1 / 2 : ℝ) + ε / 4) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hpreR he) hC
      _ ≤ C * Real.rpow (R : ℝ) (1 + ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hRone he1) hC
  have hendBound :
      ‖mertensSummatory (squareRootEndpoint R)‖ ≤
        C * Real.rpow (R : ℝ) (1 + ε) := by
    calc
      _ ≤ C * Real.rpow ((squareRootEndpoint R : ℕ) : ℝ)
            ((1 / 2 : ℝ) + ε / 4) := hM _ hX
      _ ≤ C * Real.rpow ((R : ℝ) ^ 2)
            ((1 / 2 : ℝ) + ε / 4) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hXR he) hC
      _ = C * Real.rpow (R : ℝ) (1 + ε / 2) := by
        congr 1
        rw [← Real.rpow_natCast (R : ℝ) 2,
          ← Real.rpow_mul hRpos]
        congr 1
        ring
      _ ≤ C * Real.rpow (R : ℝ) (1 + ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hRone he2) hC
  have hQ :
      ‖eulerSelfDualBilinear R‖ ≤
        3 * C * Real.rpow (R : ℝ) (1 + ε) := by
    have htri : ‖eulerSelfDualBilinear R‖ ≤
        2 * ‖mertensSummatory (R - 1)‖ +
        ‖mertensSummatory (squareRootEndpoint R)‖ := by
      rw [eulerSelfDualBilinear_eq_two_mertens_sub_endpoint R hR]
      calc
        _ ≤ ‖2 * mertensSummatory (R - 1)‖ +
          ‖mertensSummatory (squareRootEndpoint R)‖ :=
          norm_sub_le _ _
        _ = 2 * ‖mertensSummatory (R - 1)‖ +
          ‖mertensSummatory (squareRootEndpoint R)‖ := by simp
    nlinarith [hpreBound, hendBound]
  have hKone : (1 : ℝ) ≤ K :=
    one_le_of_lowerMertensCriticalEnvelope (by omega : 1 ≤ R) hK
  have hKroot : (1 : ℝ) ≤ Real.sqrt K := by
    simpa using Real.sqrt_le_sqrt hKone
  have hQrhs : 0 ≤ 3 * C * Real.rpow (R : ℝ) (1 + ε) := by
    positivity
  calc
    ‖eulerSelfDualBilinear R‖ ≤
        3 * C * Real.rpow (R : ℝ) (1 + ε) := hQ
    _ ≤ 3 * C * Real.rpow (R : ℝ) (1 + ε) * Real.sqrt K := by
      nlinarith [hKroot, hQrhs]

end RHLean.Proof
