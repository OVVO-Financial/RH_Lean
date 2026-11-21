import Mathlib
import RHLean.Analysis.NativePNTAxer
import RHLean.Proof.SquareRootCrossRegionAmplification

/-!
# Native two-wall Q subpower bound from the actual Mertens growth certificate

The Mertens half-growth hypothesis in THIS root-library file is explicit.
It follows from RH by the separately compiled and audited RESEARCH theorem
  research.UNIVERSAL_ENVELOPE_RH_BRIDGES.mertens_half_iff_riemannHypothesis,
but the research library cannot be imported as a root RHLean dependency.

This module does not import Alpoge's terminal theorem or claim an
independent RH proof. It proves a quantitative statement for the actual
real Mobius Q_R = 2*M(R-1)-M(R^2-1) under the separately supplied
Mertens half-growth hypothesis, retaining every strict-history envelope.

The stronger epsilon-free finite-C statement is NOT proved.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

/-- The original Euler self-dual Q in the native real Mertens coordinate.
The existing separate research theorem equates its complex cast with
the literal signed double-floor Euler bilinear. -/
def alpogeNativeTwoWallQ (R : ℕ) : ℝ :=
  2 * nativeMertensSummatory (R - 1) -
    nativeMertensSummatory (squareRootEndpoint R)

/-- Native real version of the standard RH-strength Mertens power envelope;
the bridge from RiemannHypothesis is intentionally a *separate* proof. -/
def AlpogeNativeMertensHalfGrowth : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        ‖nativeMertensSummatory n‖ ≤
          C * Real.rpow (n : ℝ) ((1 : ℝ) / 2 + δ)

/-- The original two-wall Q at subpower size, with the actual strict
history K_R as an *arbitrary* valid critical envelope. -/
def AlpogeNativeTwoWallSubpower : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, ∀ K : ℝ,
        2 ≤ R →
        LowerMertensCriticalEnvelope R K →
        ‖alpogeNativeTwoWallQ R‖ ≤
          C * Real.rpow (R : ℝ) (1 + ε) * Real.sqrt K

/-- An exact, noncircular arithmetic consequence of a half-growth supplier.
This theorem cannot itself be used to establish that supplier or RH. -/
theorem alpogeNativeTwoWallSubpower_of_halfGrowth
    (hhalf : AlpogeNativeMertensHalfGrowth) :
    AlpogeNativeTwoWallSubpower := by
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
      ‖nativeMertensSummatory (R - 1)‖ ≤
        C * Real.rpow (R : ℝ) (1 + ε) := by
    calc
      _ ≤ C * Real.rpow (((R - 1 : ℕ) : ℝ))
          ((1 / 2 : ℝ) + ε / 4) := hM (R - 1) hpre
      _ ≤ C * Real.rpow (R : ℝ)
          ((1 / 2 : ℝ) + ε / 4) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hpreR he) hC
      _ ≤ C * Real.rpow (R : ℝ) (1 + ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hRone he1) hC
  have hendBound :
      ‖nativeMertensSummatory (squareRootEndpoint R)‖ ≤
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
      ‖alpogeNativeTwoWallQ R‖ ≤
        3 * C * Real.rpow (R : ℝ) (1 + ε) := by
    have htri : ‖alpogeNativeTwoWallQ R‖ ≤
        2 * ‖nativeMertensSummatory (R - 1)‖ +
        ‖nativeMertensSummatory (squareRootEndpoint R)‖ := by
      unfold alpogeNativeTwoWallQ
      calc
        _ ≤ ‖2 * nativeMertensSummatory (R - 1)‖ +
          ‖nativeMertensSummatory (squareRootEndpoint R)‖ :=
          norm_sub_le _ _
        _ = 2 * ‖nativeMertensSummatory (R - 1)‖ +
          ‖nativeMertensSummatory (squareRootEndpoint R)‖ := by simp
    nlinarith [hpreBound, hendBound]
  have hKone : (1 : ℝ) ≤ K :=
    one_le_of_lowerMertensCriticalEnvelope (by omega : 1 ≤ R) hK
  have hKroot : (1 : ℝ) ≤ Real.sqrt K := by
    simpa using Real.sqrt_le_sqrt hKone
  have hQrhs : 0 ≤ 3 * C * Real.rpow (R : ℝ) (1 + ε) := by
    positivity
  calc
    ‖alpogeNativeTwoWallQ R‖ ≤
        3 * C * Real.rpow (R : ℝ) (1 + ε) := hQ
    _ ≤ 3 * C * Real.rpow (R : ℝ) (1 + ε) * Real.sqrt K := by
      have hmul := mul_le_mul_of_nonneg_left hKroot hQrhs
      nlinarith [hmul]

end RHLean.Proof
