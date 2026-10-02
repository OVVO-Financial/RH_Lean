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
  ring

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
  push_cast
  ring

/-- Instantiation of the generic solved-reference energy identity: subtracting
the prime-power reference from the psi evolution gives exactly the theta
protected-pull energy step. -/
theorem vfMidSquarePsiEnergy_renormalizes_to_thetaEnergy
    (R : ℕ) :
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


/-! ## Coupled owner packet and signed boundary strip -/

/-- The exact owner packet which drives the proxy-renormalized theta pull.
The native lower-scale charge is deliberately kept coupled to its signed
descent remainder; no absolute value is taken between them. -/
def vfMidCoupledOwnerPacket (R : ℕ) : ℝ :=
  vfMidRecursiveAggregateNativeCharge R +
    vfMidNativeDescentRemainder R +
    vfMidDirectLogPositionError R

/-- **The lower-scale prime correction cancels before any estimate is taken.**

The native recursive charge plus its complete descent remainder is exactly the
parent-level signed supply: positive parent VF weight on actual composites
minus the complementary parent prime channel.  In particular, no child-prime
population survives in this coupled expression. -/
theorem vfMidCoupledNativeDescent_eq_parentSignedSupply
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidRecursiveAggregateNativeCharge R +
        vfMidNativeDescentRemainder R =
      vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℝ) -
        (1 - vfMidOddFractionalPrimeSeatWeight R) *
          (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  rw [←
    vfMidOddCompositeTrackingDefect_eq_nativeCharge_add_descentRemainder
      R hR]
  exact
    vfMidOddCompositeTrackingDefect_eq_compositeCharge_sub_primeCharge
      R (by omega)

/-- The protected pull is the positive midpoint logarithm times the complete
coupled owner packet. -/
theorem vfMidSquareThetaProtectedPull_eq_coupledOwnerPacket
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidSquareThetaProtectedPull R =
      Real.log (vfMidBandMidpoint R) * vfMidCoupledOwnerPacket R := by
  simpa [vfMidCoupledOwnerPacket] using
    vfMidSquareThetaProtectedPull_eq_nativeVFDescent R hR

/-- Unsquared RH-scale theta barrier. -/
def vfMidThetaBarrierRadius (C : ℝ) (R : ℕ) : ℝ :=
  C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2

/-- One-step growth of the unsquared theta barrier. -/
def vfMidThetaBarrierIncrement (C : ℝ) (R : ℕ) : ℝ :=
  vfMidThetaBarrierRadius C (R + 1) - vfMidThetaBarrierRadius C R

/-- **Exact signed invariant for the coupled packet.**

The next theta endpoint lies inside the radius at R+1 if and only if the
log-weighted coupled owner packet lies between the two current-slack
thresholds.  This is the linear, sign-preserving form of the #857 invariant:
there is no separate remainder budget to absorb.

The lower threshold protects the upper endpoint barrier; the upper threshold
protects the lower endpoint barrier. -/
theorem vfMidThetaNextInside_iff_coupledPacketWindow
    (C : ℝ) (R : ℕ) (hR : 7 ≤ R) :
    (-vfMidThetaBarrierRadius C (R + 1) ≤
          vfMidDirectThetaEndpointError (R + 1) ∧
        vfMidDirectThetaEndpointError (R + 1) ≤
          vfMidThetaBarrierRadius C (R + 1)) ↔
      (-(vfMidThetaBarrierRadius C (R + 1) -
            vfMidDirectThetaEndpointError R) ≤
          Real.log (vfMidBandMidpoint R) * vfMidCoupledOwnerPacket R ∧
        Real.log (vfMidBandMidpoint R) * vfMidCoupledOwnerPacket R ≤
          vfMidThetaBarrierRadius C (R + 1) +
            vfMidDirectThetaEndpointError R) := by
  rw [vfMidDirectThetaEndpointError_succ_eq_old_sub_protectedPull,
    vfMidSquareThetaProtectedPull_eq_coupledOwnerPacket R hR]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith

/-- The same exact invariant normalized into native owner-packet currency.
The width is divided by log(m_R), which is positive for R >= 7. -/
theorem vfMidThetaNextInside_iff_coupledPacketWindow_normalized
    (C : ℝ) (R : ℕ) (hR : 7 ≤ R) :
    (-vfMidThetaBarrierRadius C (R + 1) ≤
          vfMidDirectThetaEndpointError (R + 1) ∧
        vfMidDirectThetaEndpointError (R + 1) ≤
          vfMidThetaBarrierRadius C (R + 1)) ↔
      (-(vfMidThetaBarrierRadius C (R + 1) -
            vfMidDirectThetaEndpointError R) /
            Real.log (vfMidBandMidpoint R) ≤
          vfMidCoupledOwnerPacket R ∧
        vfMidCoupledOwnerPacket R ≤
          (vfMidThetaBarrierRadius C (R + 1) +
            vfMidDirectThetaEndpointError R) /
              Real.log (vfMidBandMidpoint R)) := by
  have hlog := vfMidBandMidpoint_log_pos_of_seven_le hR
  rw [vfMidThetaNextInside_iff_coupledPacketWindow C R hR]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_le_iff₀ hlog).2
      simpa [mul_comm] using hlo
    · apply (le_div_iff₀ hlog).2
      simpa [mul_comm] using hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · have h := (div_le_iff₀ hlog).1 hlo
      simpa [mul_comm] using h
    · have h := (le_div_iff₀ hlog).1 hhi
      simpa [mul_comm] using h

/-- At the exact upper barrier, preventing outward escape is equivalent to the
one-sided coupled-packet threshold -delta_R/log(m_R). -/
theorem vfMidThetaUpperBarrier_noEscape_iff_coupledPacket
    (C : ℝ) (R : ℕ) (hR : 7 ≤ R)
    (hbar :
      vfMidDirectThetaEndpointError R = vfMidThetaBarrierRadius C R) :
    vfMidDirectThetaEndpointError (R + 1) ≤
        vfMidThetaBarrierRadius C (R + 1) ↔
      -(vfMidThetaBarrierIncrement C R) /
          Real.log (vfMidBandMidpoint R) ≤
        vfMidCoupledOwnerPacket R := by
  have hlog := vfMidBandMidpoint_log_pos_of_seven_le hR
  rw [vfMidDirectThetaEndpointError_succ_eq_old_sub_protectedPull,
    vfMidSquareThetaProtectedPull_eq_coupledOwnerPacket R hR, hbar]
  constructor
  · intro h
    apply (div_le_iff₀ hlog).2
    unfold vfMidThetaBarrierIncrement
    have :
        -(vfMidThetaBarrierRadius C (R + 1) -
            vfMidThetaBarrierRadius C R) ≤
          Real.log (vfMidBandMidpoint R) * vfMidCoupledOwnerPacket R := by
      linarith
    simpa [mul_comm] using this
  · intro h
    have h' := (div_le_iff₀ hlog).1 h
    unfold vfMidThetaBarrierIncrement at h'
    have :
        -(vfMidThetaBarrierRadius C (R + 1) -
            vfMidThetaBarrierRadius C R) ≤
          Real.log (vfMidBandMidpoint R) * vfMidCoupledOwnerPacket R := by
      simpa [mul_comm] using h'
    linarith

/-- At the exact lower barrier, preventing outward escape is equivalent to the
opposite one-sided coupled-packet threshold +delta_R/log(m_R). -/
theorem vfMidThetaLowerBarrier_noEscape_iff_coupledPacket
    (C : ℝ) (R : ℕ) (hR : 7 ≤ R)
    (hbar :
      vfMidDirectThetaEndpointError R = -vfMidThetaBarrierRadius C R) :
    -vfMidThetaBarrierRadius C (R + 1) ≤
        vfMidDirectThetaEndpointError (R + 1) ↔
      vfMidCoupledOwnerPacket R ≤
        vfMidThetaBarrierIncrement C R /
          Real.log (vfMidBandMidpoint R) := by
  have hlog := vfMidBandMidpoint_log_pos_of_seven_le hR
  rw [vfMidDirectThetaEndpointError_succ_eq_old_sub_protectedPull,
    vfMidSquareThetaProtectedPull_eq_coupledOwnerPacket R hR, hbar]
  constructor
  · intro h
    apply (le_div_iff₀ hlog).2
    unfold vfMidThetaBarrierIncrement
    have :
        Real.log (vfMidBandMidpoint R) * vfMidCoupledOwnerPacket R ≤
          vfMidThetaBarrierRadius C (R + 1) -
            vfMidThetaBarrierRadius C R := by
      linarith
    simpa [mul_comm] using this
  · intro h
    have h' := (le_div_iff₀ hlog).1 h
    unfold vfMidThetaBarrierIncrement at h'
    have :
        Real.log (vfMidBandMidpoint R) * vfMidCoupledOwnerPacket R ≤
          vfMidThetaBarrierRadius C (R + 1) -
            vfMidThetaBarrierRadius C R := by
      simpa [mul_comm] using h'
    linarith


/-! ## Physical theta-supply form of the same boundary condition -/

/-- **Upper barrier row of the boundary table, exactly.**

If the current theta endpoint is on the positive barrier, then the next
endpoint stays below the enlarged barrier if and only if the actual theta
mass in the square block is at most

  (2R+1) + delta_R.

No owner decomposition or estimate appears in this equivalence. -/
theorem vfMidThetaUpperBarrier_noEscape_iff_thetaSupply
    (C : ℝ) (R : ℕ)
    (hbar :
      vfMidDirectThetaEndpointError R = vfMidThetaBarrierRadius C R) :
    vfMidDirectThetaEndpointError (R + 1) ≤
        vfMidThetaBarrierRadius C (R + 1) ↔
      vfMidDirectThetaBandMass R ≤
        (2 * (R : ℝ) + 1) + vfMidThetaBarrierIncrement C R := by
  have hstep := vfMidDirectThetaBandError_eq_endpoint_diff R
  unfold vfMidDirectThetaBandError at hstep
  rw [hbar] at hstep
  unfold vfMidThetaBarrierIncrement
  constructor <;> intro h <;> linarith

/-- **Lower barrier row of the boundary table, exactly.**

If the current theta endpoint is on the negative barrier, then the next
endpoint stays above the enlarged negative barrier if and only if the actual
theta mass in the square block is at least

  (2R+1) - delta_R. -/
theorem vfMidThetaLowerBarrier_noEscape_iff_thetaSupply
    (C : ℝ) (R : ℕ)
    (hbar :
      vfMidDirectThetaEndpointError R = -vfMidThetaBarrierRadius C R) :
    -vfMidThetaBarrierRadius C (R + 1) ≤
        vfMidDirectThetaEndpointError (R + 1) ↔
      (2 * (R : ℝ) + 1) - vfMidThetaBarrierIncrement C R ≤
        vfMidDirectThetaBandMass R := by
  have hstep := vfMidDirectThetaBandError_eq_endpoint_diff R
  unfold vfMidDirectThetaBandError at hstep
  rw [hbar] at hstep
  unfold vfMidThetaBarrierIncrement
  constructor <;> intro h <;> linarith

/-- Every prime in the R-th square block has log-weight at most
2 log(R+1).  Summing gives the deterministic conversion from a prime-population
ceiling to a theta-mass ceiling. -/
theorem vfMidDirectThetaBandMass_le_primeSupply_upperLog
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidDirectThetaBandMass R ≤
      (vfMidIntegerBlockPrimeSupply R : ℝ) *
        (2 * Real.log ((R + 1 : ℕ) : ℝ)) := by
  unfold vfMidDirectThetaBandMass
  calc
    (∑ p ∈ vfMidDirectPrimeBand R, Real.log (p : ℝ))
        ≤ ∑ _p ∈ vfMidDirectPrimeBand R,
            2 * Real.log ((R + 1 : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpIoc, hpPrime⟩
          have hpHighNat : p ≤ (R + 1) ^ 2 :=
            (Finset.mem_Ioc.mp hpIoc).2
          have hpHigh :
              (p : ℝ) ≤ (((R + 1 : ℕ) : ℝ) ^ 2) := by
            exact_mod_cast hpHighNat
          have hpPos : 0 < (p : ℝ) := by
            exact_mod_cast hpPrime.pos
          calc
            Real.log (p : ℝ)
                ≤ Real.log ((((R + 1 : ℕ) : ℝ) ^ 2)) :=
              Real.log_le_log hpPos hpHigh
            _ = 2 * Real.log ((R + 1 : ℕ) : ℝ) := by
              rw [Real.log_pow]
              norm_num
    _ = ((vfMidDirectPrimeBand R).card : ℝ) *
          (2 * Real.log ((R + 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (vfMidIntegerBlockPrimeSupply R : ℝ) *
          (2 * Real.log ((R + 1 : ℕ) : ℝ)) := by
          rfl

/-- Every prime in the R-th square block has log-weight at least 2 log R.
Thus any prime-population floor automatically gives a theta-mass floor. -/
theorem primeSupply_mul_lowerLog_le_vfMidDirectThetaBandMass
    (R : ℕ) (hR : 2 ≤ R) :
    (vfMidIntegerBlockPrimeSupply R : ℝ) *
        (2 * Real.log (R : ℝ)) ≤
      vfMidDirectThetaBandMass R := by
  have hR0 : 0 < (R : ℝ) := by
    exact_mod_cast (show 0 < R by omega)
  unfold vfMidDirectThetaBandMass
  calc
    (vfMidIntegerBlockPrimeSupply R : ℝ) *
          (2 * Real.log (R : ℝ))
        = ∑ _p ∈ vfMidDirectPrimeBand R,
            2 * Real.log (R : ℝ) := by
          unfold vfMidIntegerBlockPrimeSupply
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ vfMidDirectPrimeBand R, Real.log (p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpIoc, _hpPrime⟩
          have hpLowNat : R ^ 2 < p :=
            (Finset.mem_Ioc.mp hpIoc).1
          have hpLow :
              ((R : ℝ) ^ 2) ≤ (p : ℝ) := by
            exact_mod_cast hpLowNat.le
          calc
            2 * Real.log (R : ℝ)
                = Real.log ((R : ℝ) ^ 2) := by
                    rw [Real.log_pow]
                    norm_num
            _ ≤ Real.log (p : ℝ) :=
              Real.log_le_log (sq_pos_of_pos hR0) hpLow

/-- Any deterministic prime-supply ceiling W_R yields the corresponding
theta-supply ceiling used in the upper boundary strip. -/
theorem vfMidDirectThetaBandMass_le_of_primeSupply_le
    (R W : ℕ) (hR : 2 ≤ R)
    (hPW : vfMidIntegerBlockPrimeSupply R ≤ W) :
    vfMidDirectThetaBandMass R ≤
      (W : ℝ) * (2 * Real.log ((R + 1 : ℕ) : ℝ)) := by
  have htheta :=
    vfMidDirectThetaBandMass_le_primeSupply_upperLog R hR
  have hcast :
      (vfMidIntegerBlockPrimeSupply R : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast hPW
  have hlog0 :
      0 ≤ 2 * Real.log ((R + 1 : ℕ) : ℝ) := by
    have hone : (1 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ R + 1 by omega)
    have := Real.log_nonneg hone
    positivity
  exact htheta.trans
    (mul_le_mul_of_nonneg_right hcast hlog0)

/-- Every admissible prefix wheel therefore gives a deterministic theta-mass
ceiling for the upper barrier. -/
theorem vfMidDirectThetaBandMass_le_prefixWheel_upperLog
    (T R : ℕ) (hR : 2 ≤ R) (hTR : T ≤ R) :
    vfMidDirectThetaBandMass R ≤
      (vfMidPrefixWheelEnvelope T R : ℝ) *
        (2 * Real.log ((R + 1 : ℕ) : ℝ)) := by
  exact
    vfMidDirectThetaBandMass_le_of_primeSupply_le
      R (vfMidPrefixWheelEnvelope T R) hR
      (vfMidIntegerBlockPrimeSupply_le_prefixWheelEnvelope T R hR hTR)

/-- **Prefix-wheel sufficient condition for the upper barrier.**

This is the unconditional side of the boundary attack: once a chosen prefix
wheel has a theta ceiling below L_R + delta_R, outward escape through the
positive barrier is impossible. -/
theorem vfMidThetaUpperBarrier_noEscape_of_prefixWheel
    (C : ℝ) (T R : ℕ) (hR : 2 ≤ R) (hTR : T ≤ R)
    (hbar :
      vfMidDirectThetaEndpointError R = vfMidThetaBarrierRadius C R)
    (hbudget :
      (vfMidPrefixWheelEnvelope T R : ℝ) *
          (2 * Real.log ((R + 1 : ℕ) : ℝ)) ≤
        (2 * (R : ℝ) + 1) + vfMidThetaBarrierIncrement C R) :
    vfMidDirectThetaEndpointError (R + 1) ≤
      vfMidThetaBarrierRadius C (R + 1) := by
  apply
    (vfMidThetaUpperBarrier_noEscape_iff_thetaSupply C R hbar).2
  exact
    (vfMidDirectThetaBandMass_le_prefixWheel_upperLog
      T R hR hTR).trans hbudget

/-- **Conditional prime-supply floor sufficient for the lower barrier.**

The lower wall has the opposite character.  Any proved floor K <= P_R is
enough provided its forced theta mass 2 K log R reaches L_R - delta_R.
This exposes exactly the arithmetic input still missing from the descent. -/
theorem vfMidThetaLowerBarrier_noEscape_of_primeSupplyFloor
    (C : ℝ) (K R : ℕ) (hR : 2 ≤ R)
    (hbar :
      vfMidDirectThetaEndpointError R = -vfMidThetaBarrierRadius C R)
    (hKP : K ≤ vfMidIntegerBlockPrimeSupply R)
    (hbudget :
      (2 * (R : ℝ) + 1) - vfMidThetaBarrierIncrement C R ≤
        (K : ℝ) * (2 * Real.log (R : ℝ))) :
    -vfMidThetaBarrierRadius C (R + 1) ≤
      vfMidDirectThetaEndpointError (R + 1) := by
  apply
    (vfMidThetaLowerBarrier_noEscape_iff_thetaSupply C R hbar).2
  have hcast :
      (K : ℝ) ≤ (vfMidIntegerBlockPrimeSupply R : ℝ) := by
    exact_mod_cast hKP
  have hlog0 : 0 ≤ 2 * Real.log (R : ℝ) := by
    have hone : (1 : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast (show 1 ≤ R by omega)
    have := Real.log_nonneg hone
    positivity
  have hfloor :
      (K : ℝ) * (2 * Real.log (R : ℝ)) ≤
        (vfMidIntegerBlockPrimeSupply R : ℝ) *
          (2 * Real.log (R : ℝ)) :=
    mul_le_mul_of_nonneg_right hcast hlog0
  exact hbudget.trans
    (hfloor.trans
      (primeSupply_mul_lowerLog_le_vfMidDirectThetaBandMass R hR))

end RHLean.Analysis
