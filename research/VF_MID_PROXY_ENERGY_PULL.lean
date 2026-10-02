import Mathlib
import «research.VF_MID_SQUARE_THETA_NATIVE_DESCENT»

/-!
# Proxy-renormalized square-theta energy pull

The four fantasy proxy closures show that the deterministic reference side is
already root-close to Li (or better).  For the square-block energy problem the
strongest reference is the exact VF fractional cluster itself.

In theta currency its R-th block mass is

  V_R * log(m_R) = 2R+1,

so the centered VF reference pull is identically zero block-by-block.

Consequently subtracting the solved VF proxy before taking energy removes the
ideal/reference contribution completely.  The hard pull is exactly the actual
theta-minus-VF pull, and PR #856 identifies that pull with the log-weighted
native #855 descent packet.

This file formalizes that renormalization and gives the exact one-step energy
consumer: once the protected theta pull cannot increase the
C^2 R^2 log(R)^4 barrier faster than the barrier itself, the already-compiled
square-theta envelope follows.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Generic solved-reference subtraction -/

/-- If an actual state and a reference state each evolve by subtracting their
respective pulls, then their displacement evolves by subtracting the pull
difference.  The energy increment of the displacement contains no separate
reference-energy term. -/
theorem proxySubtractedEnergyStep
    (E F P Q E' F' : ℝ)
    (hE : E' = E - P)
    (hF : F' = F - Q) :
    (E' - F') ^ 2 - (E - F) ^ 2 =
      (P - Q) ^ 2 - 2 * (E - F) * (P - Q) := by
  rw [hE, hF]
  ring

/-! ## VF is an exact zero-error theta reference -/

/-- Centered theta mass of the deterministic VF midpoint proxy on one square
block. -/
def vfMidThetaVFReferenceBandError (R : ℕ) : ℝ :=
  vfMidBandMass R * Real.log (vfMidBandMidpoint R) -
    (2 * (R : ℝ) + 1)

/-- **The VF proxy has exactly zero centered theta block error.**

This is stronger than a root-scale proxy estimate: after changing to theta
currency, the deterministic midpoint block is exactly the square-block length.
-/
theorem vfMidThetaVFReferenceBandError_eq_zero
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidThetaVFReferenceBandError R = 0 := by
  have hlog := vfMidBandMidpoint_log_pos_of_seven_le hR
  unfold vfMidThetaVFReferenceBandError vfMidBandMass
  field_simp [hlog.ne']

/-- The actual-minus-VF protected pull in theta currency.  Because the VF
reference pull is zero, this is just the negative centered actual theta
increment. -/
def vfMidSquareThetaProtectedPull (R : ℕ) : ℝ :=
  -vfMidDirectThetaBandError R

/-- Exact theta endpoint update after subtracting the solved VF reference. -/
theorem vfMidDirectThetaEndpointError_succ_eq_old_sub_protectedPull
    (R : ℕ) :
    vfMidDirectThetaEndpointError (R + 1) =
      vfMidDirectThetaEndpointError R -
        vfMidSquareThetaProtectedPull R := by
  rw [vfMidSquareThetaProtectedPull,
    vfMidDirectThetaBandError_eq_endpoint_diff]
  ring

/-- Exact proxy-renormalized theta energy increment. -/
theorem vfMidDirectThetaEndpointError_energy_step
    (R : ℕ) :
    vfMidDirectThetaEndpointError (R + 1) ^ 2 -
        vfMidDirectThetaEndpointError R ^ 2 =
      vfMidSquareThetaProtectedPull R ^ 2 -
        2 * vfMidDirectThetaEndpointError R *
          vfMidSquareThetaProtectedPull R := by
  rw [vfMidDirectThetaEndpointError_succ_eq_old_sub_protectedPull]
  ring

/-- **The renormalized theta pull is exactly the #855 native VF packet.**

No ideal Li/VF energy term and no prime-power correction remains:
the hard pull is precisely the logarithmically weighted native descent plus
the already explicit #855 transfer and within-band position terms.
-/
theorem vfMidSquareThetaProtectedPull_eq_nativeVFDescent
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidSquareThetaProtectedPull R =
      Real.log (vfMidBandMidpoint R) *
        (vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R +
          vfMidDirectLogPositionError R) := by
  unfold vfMidSquareThetaProtectedPull
  rw [vfMidDirectThetaBandError_eq_nativeVFDescent R hR]
  ring

/-- The psi protected pull is the proxy-renormalized theta pull minus only the
prime-power correction increment.  Thus moving to the VF theta reference
removes the prime-power nuisance exactly. -/
theorem vfMidSquarePsiProtectedPull_eq_thetaProtectedPull_sub_primePowerDiff
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidSquarePsiProtectedPull R =
      vfMidSquareThetaProtectedPull R -
        (vfMidSquarePrimePowerCorrection (R + 1) -
          vfMidSquarePrimePowerCorrection R) := by
  rw [vfMidSquarePsiProtectedPull_eq_nativeVFDescent R hR,
    vfMidSquareThetaProtectedPull_eq_nativeVFDescent R hR]

/-- At square endpoints, subtracting the prime-power correction from the psi
error is exactly the theta error. -/
theorem nativePNTError_sub_primePowerCorrection_eq_thetaEndpointError
    (R : ℕ) :
    nativePNTError (R ^ 2) - vfMidSquarePrimePowerCorrection R =
      vfMidDirectThetaEndpointError R := by
  unfold nativePNTError vfMidSquarePrimePowerCorrection
    vfMidDirectThetaEndpointError
  ring

/-- Instantiation of the generic solved-reference energy identity: subtracting
the prime-power reference from the psi evolution gives exactly the theta
protected-pull energy step. -/
theorem vfMidSquarePsiEnergy_renormalizes_to_thetaEnergy
    (R : ℕ) (hR : 7 ≤ R) :
    (nativePNTError ((R + 1) ^ 2) -
        vfMidSquarePrimePowerCorrection (R + 1)) ^ 2 -
      (nativePNTError (R ^ 2) -
        vfMidSquarePrimePowerCorrection R) ^ 2 =
      vfMidSquareThetaProtectedPull R ^ 2 -
        2 * (nativePNTError (R ^ 2) -
          vfMidSquarePrimePowerCorrection R) *
          vfMidSquareThetaProtectedPull R := by
  rw [nativePNTError_sub_primePowerCorrection_eq_thetaEndpointError,
    nativePNTError_sub_primePowerCorrection_eq_thetaEndpointError]
  exact vfMidDirectThetaEndpointError_energy_step R

/-! ## Exact barrier consumer -/

/-- Squared RH-scale theta barrier at square index R. -/
def vfMidThetaEnvelopeEnergy (C : ℝ) (R : ℕ) : ℝ :=
  (C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2) ^ 2

/-- **Most specific remaining pull inequality after proxy renormalization.**

The finite block 3..7 is included explicitly.  Above 7, the only analytic
input is that the exact protected-pull energy increment does not exceed the
increment of the desired C^2 R^2 log(R)^4 barrier.
-/
def VFMidThetaProtectedPullBarrierStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ R : ℕ, 3 ≤ R → R ≤ 7 →
      vfMidDirectThetaEndpointError R ^ 2 ≤
        vfMidThetaEnvelopeEnergy C R) ∧
    ∀ R : ℕ, 7 ≤ R →
      vfMidSquareThetaProtectedPull R ^ 2 -
          2 * vfMidDirectThetaEndpointError R *
            vfMidSquareThetaProtectedPull R ≤
        vfMidThetaEnvelopeEnergy C (R + 1) -
          vfMidThetaEnvelopeEnergy C R

/-- The proxy-renormalized one-step barrier is sufficient for the full
square-theta envelope already consumed by PR #856. -/
theorem vfMidSquareThetaEnvelope_of_protectedPullBarrier
    (h : VFMidThetaProtectedPullBarrierStatement) :
    VFMidSquareThetaEnvelopeStatement := by
  rcases h with ⟨C, hC0, hsmall, hstep⟩
  have hsq_large :
      ∀ R : ℕ, 7 ≤ R →
        vfMidDirectThetaEndpointError R ^ 2 ≤
          vfMidThetaEnvelopeEnergy C R := by
    intro R hR
    induction R, hR using Nat.le_induction with
    | base =>
        exact hsmall 7 (by omega) le_rfl
    | succ R hR ih =>
        have hinc := vfMidDirectThetaEndpointError_energy_step R
        have hs := hstep R hR
        linarith
  refine ⟨C, hC0, ?_⟩
  intro R hR
  have hsq :
      vfMidDirectThetaEndpointError R ^ 2 ≤
        vfMidThetaEnvelopeEnergy C R := by
    by_cases hR7 : R ≤ 7
    · exact hsmall R hR hR7
    · exact hsq_large R (by omega)
  have hlog0 : 0 ≤ Real.log (R : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ R by omega)
  have hbar0 :
      0 ≤ C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2 := by
    positivity
  have habsSq :
      |vfMidDirectThetaEndpointError R| ^ 2 ≤
        (C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2) ^ 2 := by
    simpa [sq_abs, vfMidThetaEnvelopeEnergy] using hsq
  exact
    (sq_le_sq₀ (abs_nonneg _) hbar0).1 habsSq

/-! ## Exact invariant formulation (not stronger than the target) -/

/-- Barrier invariance for the renormalized actual-minus-VF theta pull.

Unlike the uniform barrier-increment condition above, this uses the actual
slack at the current endpoint.  It asks only that an endpoint already inside
the desired envelope cannot be pushed outside it by the next exact pull. -/
def VFMidThetaProtectedPullInvariantStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ R : ℕ, 3 ≤ R → R ≤ 7 →
      vfMidDirectThetaEndpointError R ^ 2 ≤
        vfMidThetaEnvelopeEnergy C R) ∧
    ∀ R : ℕ, 7 ≤ R →
      vfMidDirectThetaEndpointError R ^ 2 ≤
        vfMidThetaEnvelopeEnergy C R →
      vfMidSquareThetaProtectedPull R ^ 2 -
          2 * vfMidDirectThetaEndpointError R *
            vfMidSquareThetaProtectedPull R ≤
        vfMidThetaEnvelopeEnergy C (R + 1) -
          vfMidDirectThetaEndpointError R ^ 2

/-- Exact invariance implies the full square-theta envelope. -/
theorem vfMidSquareThetaEnvelope_of_protectedPullInvariant
    (h : VFMidThetaProtectedPullInvariantStatement) :
    VFMidSquareThetaEnvelopeStatement := by
  rcases h with ⟨C, hC0, hsmall, hinv⟩
  have hsq_large :
      ∀ R : ℕ, 7 ≤ R →
        vfMidDirectThetaEndpointError R ^ 2 ≤
          vfMidThetaEnvelopeEnergy C R := by
    intro R hR
    induction R, hR using Nat.le_induction with
    | base =>
        exact hsmall 7 (by omega) le_rfl
    | succ R hR ih =>
        have hinc := vfMidDirectThetaEndpointError_energy_step R
        have hs := hinv R hR ih
        linarith
  refine ⟨C, hC0, ?_⟩
  intro R hR
  have hsq :
      vfMidDirectThetaEndpointError R ^ 2 ≤
        vfMidThetaEnvelopeEnergy C R := by
    by_cases hR7 : R ≤ 7
    · exact hsmall R hR hR7
    · exact hsq_large R (by omega)
  have hlog0 : 0 ≤ Real.log (R : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ R by omega)
  have hbar0 :
      0 ≤ C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2 := by
    positivity
  have habsSq :
      |vfMidDirectThetaEndpointError R| ^ 2 ≤
        (C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2) ^ 2 := by
    simpa [sq_abs, vfMidThetaEnvelopeEnergy] using hsq
  exact (sq_le_sq₀ (abs_nonneg _) hbar0).1 habsSq

/-- Conversely, a proved square-theta envelope automatically satisfies the
renormalized pull invariance condition.  Hence this is an exact reformulation
of the unresolved endpoint target, not a stronger local hypothesis. -/
theorem protectedPullInvariant_of_vfMidSquareThetaEnvelope
    (h : VFMidSquareThetaEnvelopeStatement) :
    VFMidThetaProtectedPullInvariantStatement := by
  rcases h with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_, ?_⟩
  · intro R hR _hR7
    have habs := hC R hR
    have hlog0 : 0 ≤ Real.log (R : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ R by omega)
    have hbar0 :
        0 ≤ C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2 := by
      positivity
    have hsq :=
      (sq_le_sq₀ (abs_nonneg _) hbar0).2 habs
    simpa [sq_abs, vfMidThetaEnvelopeEnergy] using hsq
  · intro R hR _hcurrent
    have habs := hC (R + 1) (by omega)
    have hlog0 : 0 ≤ Real.log ((R + 1 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ R + 1 by omega)
    have hbar0 :
        0 ≤ C * ((R + 1 : ℕ) : ℝ) *
          (Real.log ((R + 1 : ℕ) : ℝ)) ^ 2 := by
      positivity
    have hnextSqRaw :=
      (sq_le_sq₀ (abs_nonneg _) hbar0).2 habs
    have hnextSq :
        vfMidDirectThetaEndpointError (R + 1) ^ 2 ≤
          vfMidThetaEnvelopeEnergy C (R + 1) := by
      simpa [sq_abs, vfMidThetaEnvelopeEnergy] using hnextSqRaw
    have hinc := vfMidDirectThetaEndpointError_energy_step R
    linarith

/-- **Exact proxy-energy reduction.**

The unresolved square-theta envelope is equivalent to invariance of the
renormalized actual-minus-VF pull.  This is the precise form in which the
already-solved proxy closure can be used without assuming the conclusion. -/
theorem vfMidThetaProtectedPullInvariant_iff_squareThetaEnvelope :
    VFMidThetaProtectedPullInvariantStatement ↔
      VFMidSquareThetaEnvelopeStatement :=
  ⟨vfMidSquareThetaEnvelope_of_protectedPullInvariant,
    protectedPullInvariant_of_vfMidSquareThetaEnvelope⟩

/-- Therefore the one-step proxy-renormalized barrier feeds the existing direct
VF endpoint consumer with no additional cancellation hypothesis. -/
theorem abs_vfMidDirectSquareEndpointError_le_of_protectedPullBarrier
    (h : VFMidThetaProtectedPullBarrierStatement)
    (R : ℕ) (hR : 3 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      |vfMidDirectSquareEndpointError R| ≤
        C * (R : ℝ) * Real.log (R : ℝ) +
          (4 * C + 9 / Real.log 4) * (R : ℝ) +
          |vfMidDirectSquareEndpointError 2 -
            vfMidDirectThetaEndpointError 2 *
              vfMidDirectThetaAbelWeight 2| :=
  abs_vfMidDirectSquareEndpointError_le_of_squareThetaEnvelope
    (vfMidSquareThetaEnvelope_of_protectedPullBarrier h) R hR

end RHLean.Analysis
