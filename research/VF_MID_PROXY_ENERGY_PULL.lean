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

open scoped BigOperators ArithmeticFunction.Moebius

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
    (R : ℕ) (_hR : 2 ≤ R) :
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


/-! ## Safe interior and forced boundary strips -/

/-- **Safe-interior theorem with an arbitrary proved prime-supply ceiling.**

Let W bound the actual prime population in the R-th square block.  The crude
log bounds alone give

  0 <= Theta_R <= 2 W log(R+1).

Consequently, if the current endpoint lies in the interval

  -F_{R+1} + (2R+1)
    <= E_R
    <= F_{R+1} + (2R+1) - 2 W log(R+1),

then the next endpoint is guaranteed to lie inside the target envelope.  This
is exactly the unconditional interior region; no cancellation or descent is
used. -/
theorem vfMidThetaNextInside_of_primeSupplyCeiling
    (C : ℝ) (R W : ℕ) (hR : 2 ≤ R)
    (hPW : vfMidIntegerBlockPrimeSupply R ≤ W)
    (hlower :
      -vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) ≤
        vfMidDirectThetaEndpointError R)
    (hupper :
      vfMidDirectThetaEndpointError R ≤
        vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) -
            (W : ℝ) * (2 * Real.log ((R + 1 : ℕ) : ℝ))) :
    -vfMidThetaBarrierRadius C (R + 1) ≤
        vfMidDirectThetaEndpointError (R + 1) ∧
      vfMidDirectThetaEndpointError (R + 1) ≤
        vfMidThetaBarrierRadius C (R + 1) := by
  have hthetaUpper :=
    vfMidDirectThetaBandMass_le_of_primeSupply_le R W hR hPW
  have hlogR0 : 0 ≤ Real.log (R : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ R by omega)
  have hbase0 :
      0 ≤ (vfMidIntegerBlockPrimeSupply R : ℝ) *
        (2 * Real.log (R : ℝ)) := by
    positivity
  have hthetaLower :=
    primeSupply_mul_lowerLog_le_vfMidDirectThetaBandMass R hR
  have htheta0 : 0 ≤ vfMidDirectThetaBandMass R :=
    hbase0.trans hthetaLower
  have hstep := vfMidDirectThetaBandError_eq_endpoint_diff R
  unfold vfMidDirectThetaBandError at hstep
  constructor <;> linarith

/-- Contrapositive form: under a proved supply ceiling, any one-step envelope
escape forces the current endpoint into one of the two boundary strips omitted
by the safe-interior interval. -/
theorem vfMidThetaNextEscape_forces_currentBoundaryStrip
    (C : ℝ) (R W : ℕ) (hR : 2 ≤ R)
    (hPW : vfMidIntegerBlockPrimeSupply R ≤ W)
    (hescape :
      ¬ (-vfMidThetaBarrierRadius C (R + 1) ≤
            vfMidDirectThetaEndpointError (R + 1) ∧
          vfMidDirectThetaEndpointError (R + 1) ≤
            vfMidThetaBarrierRadius C (R + 1))) :
    vfMidDirectThetaEndpointError R <
        -vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) ∨
      vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) -
            (W : ℝ) * (2 * Real.log ((R + 1 : ℕ) : ℝ)) <
        vfMidDirectThetaEndpointError R := by
  by_contra hstrip
  have hnotLower :
      ¬ vfMidDirectThetaEndpointError R <
        -vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) := by
    intro h
    exact hstrip (Or.inl h)
  have hnotUpper :
      ¬ vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) -
            (W : ℝ) * (2 * Real.log ((R + 1 : ℕ) : ℝ)) <
        vfMidDirectThetaEndpointError R := by
    intro h
    exact hstrip (Or.inr h)
  have hlower :
      -vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) ≤
        vfMidDirectThetaEndpointError R :=
    le_of_not_gt hnotLower
  have hupper :
      vfMidDirectThetaEndpointError R ≤
        vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) -
            (W : ℝ) * (2 * Real.log ((R + 1 : ℕ) : ℝ)) :=
    le_of_not_gt hnotUpper
  exact hescape
    (vfMidThetaNextInside_of_primeSupplyCeiling
      C R W hR hPW hlower hupper)

/-- Universal specialization using the already-proved parity ceiling P_R <= R.
Thus every possible one-step escape is confined to the explicit lower
O(R)-scale strip or upper O(R log R)-scale strip obtained from W_R = R. -/
theorem vfMidThetaNextEscape_forces_currentBoundaryStrip_universal
    (C : ℝ) (R : ℕ) (hR : 2 ≤ R)
    (hescape :
      ¬ (-vfMidThetaBarrierRadius C (R + 1) ≤
            vfMidDirectThetaEndpointError (R + 1) ∧
          vfMidDirectThetaEndpointError (R + 1) ≤
            vfMidThetaBarrierRadius C (R + 1))) :
    vfMidDirectThetaEndpointError R <
        -vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) ∨
      vfMidThetaBarrierRadius C (R + 1) +
          (2 * (R : ℝ) + 1) -
            (R : ℝ) * (2 * Real.log ((R + 1 : ℕ) : ℝ)) <
        vfMidDirectThetaEndpointError R := by
  exact
    vfMidThetaNextEscape_forces_currentBoundaryStrip
      C R R hR (vfMidIntegerBlockPrimeSupply_le_R R hR) hescape


/-! ## Exact well-founded forcing seam -/

/-- A genuine one-step boundary escape: the current endpoint is inside the
RH-scale theta envelope at a recursive scale R >= 7, but the next endpoint is
outside the enlarged envelope. -/
def VFMidThetaBoundaryEscapeAt (C : ℝ) (R : ℕ) : Prop :=
  7 ≤ R ∧
    (-vfMidThetaBarrierRadius C R ≤
          vfMidDirectThetaEndpointError R ∧
      vfMidDirectThetaEndpointError R ≤
          vfMidThetaBarrierRadius C R) ∧
    ¬ (-vfMidThetaBarrierRadius C (R + 1) ≤
          vfMidDirectThetaEndpointError (R + 1) ∧
        vfMidDirectThetaEndpointError (R + 1) ≤
          vfMidThetaBarrierRadius C (R + 1))

/-- **The remaining arithmetic forcing statement.**

Every outward escape at a recursive scale must reproduce an outward escape on
some actual recursive child scale.  Since #854 proves every such child scale is
strictly smaller, this statement cannot hold along an infinite lineage.

This definition intentionally contains no estimate: #858 has already reduced
any escape to the explicit signed boundary strips and coupled-packet
inequalities above.  The only missing arithmetic is the implication from a
parent escape to an appropriate child escape. -/
def VFMidThetaBoundaryEscapeForcingStatement (C : ℝ) : Prop :=
  ∀ R : ℕ, VFMidThetaBoundaryEscapeAt C R →
    ∃ S : ℕ,
      VFMidRecursiveScaleStep R S ∧
        VFMidThetaBoundaryEscapeAt C S

/-- Well-founded recursive descent from #854 rules out every boundary escape
as soon as the aggregate parent-to-child forcing implication is proved. -/
theorem not_vfMidThetaBoundaryEscapeAt_of_forcing
    (C : ℝ) (hforce : VFMidThetaBoundaryEscapeForcingStatement C) :
    ∀ R : ℕ, ¬ VFMidThetaBoundaryEscapeAt C R := by
  apply vfMidRecursiveScalePersistent_impossible
  intro R hbad
  exact hforce R hbad

/-- Complete boundary-descent formulation: finite initialization through scale
7 plus the single aggregate forcing statement. -/
def VFMidThetaBoundaryDescentStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ R : ℕ, 3 ≤ R → R ≤ 7 →
      -vfMidThetaBarrierRadius C R ≤
          vfMidDirectThetaEndpointError R ∧
        vfMidDirectThetaEndpointError R ≤
          vfMidThetaBarrierRadius C R) ∧
    VFMidThetaBoundaryEscapeForcingStatement C

/-- **If the signed boundary escape really descends, the theta envelope
closes.**

This is the exact minimal-counterexample engine anticipated in #854.  No
uniform local supply theorem is assumed: the only arithmetic hypothesis is
that an actual outward boundary violation selects a strictly lower recursive
scale carrying the same violation. -/
theorem vfMidSquareThetaEnvelope_of_boundaryDescent
    (h : VFMidThetaBoundaryDescentStatement) :
    VFMidSquareThetaEnvelopeStatement := by
  rcases h with ⟨C, hC0, hsmall, hforce⟩
  have hno :
      ∀ R : ℕ, ¬ VFMidThetaBoundaryEscapeAt C R :=
    not_vfMidThetaBoundaryEscapeAt_of_forcing C hforce
  have hinsideLarge :
      ∀ R : ℕ, 7 ≤ R →
        (-vfMidThetaBarrierRadius C R ≤
              vfMidDirectThetaEndpointError R ∧
          vfMidDirectThetaEndpointError R ≤
              vfMidThetaBarrierRadius C R) := by
    intro R hR
    induction R, hR using Nat.le_induction with
    | base =>
        exact hsmall 7 (by omega) le_rfl
    | succ R hR ih =>
        by_contra hnext
        exact (hno R) ⟨hR, ih, hnext⟩
  refine ⟨C, hC0, ?_⟩
  intro R hR
  have hinside :
      -vfMidThetaBarrierRadius C R ≤
            vfMidDirectThetaEndpointError R ∧
        vfMidDirectThetaEndpointError R ≤
            vfMidThetaBarrierRadius C R := by
    by_cases hR7 : R ≤ 7
    · exact hsmall R hR hR7
    · exact hinsideLarge R (by omega)
  have habs :
      |vfMidDirectThetaEndpointError R| ≤
        vfMidThetaBarrierRadius C R :=
    (abs_le).2 hinside
  simpa [vfMidThetaBarrierRadius] using habs

/-- The same single forcing statement therefore feeds the already-compiled
direct VF endpoint consumer. -/
theorem abs_vfMidDirectSquareEndpointError_le_of_boundaryDescent
    (h : VFMidThetaBoundaryDescentStatement)
    (R : ℕ) (hR : 3 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      |vfMidDirectSquareEndpointError R| ≤
        C * (R : ℝ) * Real.log (R : ℝ) +
          (4 * C + 9 / Real.log 4) * (R : ℝ) +
          |vfMidDirectSquareEndpointError 2 -
            vfMidDirectThetaEndpointError 2 *
              vfMidDirectThetaAbelWeight 2| :=
  abs_vfMidDirectSquareEndpointError_le_of_squareThetaEnvelope
    (vfMidSquareThetaEnvelope_of_boundaryDescent h) R hR


/-! ## Weaker minimal-counterexample forcing socket -/

/-- Every recursive child scale used by #854 is still at least 3.  This is the
lower-range fact needed to feed a child violation back into the finite
initialization / strong-induction envelope argument. -/
theorem vfMidRecursiveScaleStep_three_le
    {R S : ℕ} (hstep : VFMidRecursiveScaleStep R S) :
    3 ≤ S := by
  rcases hstep with ⟨hR, p, m, hp, hm, rfl⟩
  have hmGt :=
    vfMidLateRecursiveOwner_child_gt_two_mul hR hp hm
  apply (Nat.le_sqrt).2
  norm_num
  omega

/-- An endpoint, rather than a block transition, is outside the target theta
envelope. -/
def VFMidThetaEndpointOutsideAt (C : ℝ) (R : ℕ) : Prop :=
  ¬ (-vfMidThetaBarrierRadius C R ≤
        vfMidDirectThetaEndpointError R ∧
      vfMidDirectThetaEndpointError R ≤
        vfMidThetaBarrierRadius C R)

/-- **Logically minimal boundary forcing statement.**

To close the envelope by minimal counterexample, a first one-step escape at
scale R only has to force some already-earlier endpoint T ≤ R outside the
envelope.  The lower endpoint need not itself be the first escape of a new
recursive lineage.  This is strictly weaker than the escape-to-escape forcing
statement above. -/
def VFMidThetaBoundaryEscapeForcesEarlierViolationStatement
    (C : ℝ) : Prop :=
  ∀ R : ℕ, VFMidThetaBoundaryEscapeAt C R →
    ∃ T : ℕ,
      3 ≤ T ∧ T ≤ R ∧ VFMidThetaEndpointOutsideAt C T

/-- Owner-tree shaped version of the same target.  It is enough to force the
lower violation at either endpoint S or S+1 of one genuine recursive child
square block. -/
def VFMidThetaBoundaryEscapeForcesRecursiveViolationStatement
    (C : ℝ) : Prop :=
  ∀ R : ℕ, VFMidThetaBoundaryEscapeAt C R →
    ∃ S T : ℕ,
      VFMidRecursiveScaleStep R S ∧
      (T = S ∨ T = S + 1) ∧
      VFMidThetaEndpointOutsideAt C T

/-- The recursive-child formulation implies the logically minimal earlier
violation formulation, using only #854 strict descent and the child lower
range. -/
theorem vfMidThetaEarlierViolation_of_recursiveViolation
    (C : ℝ)
    (hrec :
      VFMidThetaBoundaryEscapeForcesRecursiveViolationStatement C) :
    VFMidThetaBoundaryEscapeForcesEarlierViolationStatement C := by
  intro R hescape
  obtain ⟨S, T, hstep, hT, houtside⟩ := hrec R hescape
  have hSlt : S < R := vfMidRecursiveScaleStep_lt hstep
  have hS3 : 3 ≤ S := vfMidRecursiveScaleStep_three_le hstep
  refine ⟨T, ?_, ?_, houtside⟩
  · rcases hT with rfl | rfl <;> omega
  · rcases hT with rfl | rfl <;> omega

/-- Finite initialization plus the genuinely minimal earlier-violation forcing
statement. -/
def VFMidThetaBoundaryMinimalDescentStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ R : ℕ, 3 ≤ R → R ≤ 7 →
      -vfMidThetaBarrierRadius C R ≤
          vfMidDirectThetaEndpointError R ∧
        vfMidDirectThetaEndpointError R ≤
          vfMidThetaBarrierRadius C R) ∧
    VFMidThetaBoundaryEscapeForcesEarlierViolationStatement C

/-- **Minimal-counterexample closure.**

If a first outward escape forces any earlier endpoint outside, strong induction
contradicts firstness.  This is weaker than requiring escape-to-escape
persistence and is therefore the sharp logical consumer for the remaining
arithmetic forcing theorem. -/
theorem vfMidSquareThetaEnvelope_of_minimalBoundaryDescent
    (h : VFMidThetaBoundaryMinimalDescentStatement) :
    VFMidSquareThetaEnvelopeStatement := by
  rcases h with ⟨C, hC0, hsmall, hforce⟩
  have hinsideLarge :
      ∀ N : ℕ, 7 ≤ N →
        (-vfMidThetaBarrierRadius C N ≤
              vfMidDirectThetaEndpointError N ∧
          vfMidDirectThetaEndpointError N ≤
              vfMidThetaBarrierRadius C N) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro hN7
        by_cases hN : N = 7
        · subst N
          exact hsmall 7 (by omega) le_rfl
        · have hN8 : 8 ≤ N := by omega
          obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
          have hR7 : 7 ≤ R := by omega
          have hcurrent :
              -vfMidThetaBarrierRadius C R ≤
                    vfMidDirectThetaEndpointError R ∧
                vfMidDirectThetaEndpointError R ≤
                    vfMidThetaBarrierRadius C R :=
            ih R (by omega) hR7
          by_contra hnext
          have hescape :
              VFMidThetaBoundaryEscapeAt C R :=
            ⟨hR7, hcurrent, hnext⟩
          obtain ⟨T, hT3, hTR, hTout⟩ := hforce R hescape
          have hTlt : T < R + 1 := by omega
          have hTin :
              -vfMidThetaBarrierRadius C T ≤
                    vfMidDirectThetaEndpointError T ∧
                vfMidDirectThetaEndpointError T ≤
                    vfMidThetaBarrierRadius C T := by
            by_cases hT7 : T ≤ 7
            · exact hsmall T hT3 hT7
            · exact ih T hTlt (by omega)
          exact hTout hTin
  refine ⟨C, hC0, ?_⟩
  intro R hR3
  have hinside :
      -vfMidThetaBarrierRadius C R ≤
            vfMidDirectThetaEndpointError R ∧
        vfMidDirectThetaEndpointError R ≤
            vfMidThetaBarrierRadius C R := by
    by_cases hR7 : R ≤ 7
    · exact hsmall R hR3 hR7
    · exact hinsideLarge R (by omega)
  have habs :
      |vfMidDirectThetaEndpointError R| ≤
        vfMidThetaBarrierRadius C R :=
    (abs_le).2 hinside
  simpa [vfMidThetaBarrierRadius] using habs

/-- A recursive-child lower violation is therefore already sufficient for the
full theta envelope. -/
theorem vfMidSquareThetaEnvelope_of_recursiveBoundaryViolation
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsmall :
      ∀ R : ℕ, 3 ≤ R → R ≤ 7 →
        -vfMidThetaBarrierRadius C R ≤
            vfMidDirectThetaEndpointError R ∧
          vfMidDirectThetaEndpointError R ≤
            vfMidThetaBarrierRadius C R)
    (hrec :
      VFMidThetaBoundaryEscapeForcesRecursiveViolationStatement C) :
    VFMidSquareThetaEnvelopeStatement := by
  apply vfMidSquareThetaEnvelope_of_minimalBoundaryDescent
  refine ⟨C, hC0, hsmall, ?_⟩
  exact vfMidThetaEarlierViolation_of_recursiveViolation C hrec


/-! ## Direct fresh-prime contraction on the actual square protected pull -/

/-- At a subdoubling endpoint, every divisor in the new physical block has
reciprocal quotient one.  Hence one cofactor response is exactly the negative
sum of its logarithmic multiplier weights. -/
theorem vfMidProtectedBlockCofactorResponse_endpoint_eq_neg_logSum
    (M L m : ℕ) (hsub : L < 2 * M) :
    nativePNTSignedSquareBlockCofactorResponse L M L m =
      -(∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
          Real.log ((d / m : ℕ) : ℝ)) := by
  unfold nativePNTSignedSquareBlockCofactorResponse
  calc
    (∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
        Real.log ((d / m : ℕ) : ℝ) * nativePNTError (L / d)) =
      ∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
        -(Real.log ((d / m : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
          have hlo : 1 * d ≤ L := by simpa using hdI.2
          have hhi : L < (1 + 1) * d := by
            have htwo : 2 * M < 2 * d := by omega
            omega
          have hdiv : L / d = 1 := Nat.div_eq_of_lt_le hlo hhi
          rw [hdiv, nativePNTError_one]
          ring
    _ = -(∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
          Real.log ((d / m : ℕ) : ℝ)) := by
      rw [Finset.sum_neg_distrib]

/-- The logarithmic multiplier mass attached to a positive cofactor is
nonnegative. -/
theorem vfMidProtectedBlockCofactorLogSum_nonneg
    (M L m : ℕ) (hm : 0 < m) :
    0 ≤ ∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
      Real.log ((d / m : ℕ) : ℝ) := by
  apply Finset.sum_nonneg
  intro d hd
  rcases Finset.mem_filter.mp hd with ⟨hdBand, hmd⟩
  have hdI := Finset.mem_Ioc.mp hdBand
  have hdpos : 0 < d := by omega
  have hmle : m ≤ d := Nat.le_of_dvd hdpos hmd
  have hq1 : 1 ≤ d / m := (Nat.one_le_div_iff hm).2 hmle
  exact Real.log_nonneg (by exact_mod_cast hq1)

/-- Adjoining a fresh prime can only decrease the nonnegative endpoint
logarithmic multiplier mass.  This is a literal carrier inclusion plus
monotonicity of the quotient logarithm. -/
theorem vfMidProtectedBlockCofactorLogSum_freshPrime_le
    (M L m p : ℕ) (hm : 0 < m) (hp : p.Prime) :
    (∑ d ∈ (Finset.Ioc M L).filter (fun d => m * p ∣ d),
        Real.log ((d / (m * p) : ℕ) : ℝ)) ≤
      ∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
        Real.log ((d / m : ℕ) : ℝ) := by
  have hmp : 0 < m * p := Nat.mul_pos hm hp.pos
  have hden : m ≤ m * p := by
    simpa using Nat.mul_le_mul_left m hp.one_le
  have hsubset :
      (Finset.Ioc M L).filter (fun d => m * p ∣ d) ⊆
        (Finset.Ioc M L).filter (fun d => m ∣ d) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdBand, hmpd⟩
    refine Finset.mem_filter.mpr ⟨hdBand, ?_⟩
    exact dvd_trans (dvd_mul_right m p) hmpd
  calc
    (∑ d ∈ (Finset.Ioc M L).filter (fun d => m * p ∣ d),
        Real.log ((d / (m * p) : ℕ) : ℝ)) ≤
      ∑ d ∈ (Finset.Ioc M L).filter (fun d => m * p ∣ d),
        Real.log ((d / m : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          rcases Finset.mem_filter.mp hd with ⟨hdBand, hmpd⟩
          have hdI := Finset.mem_Ioc.mp hdBand
          have hdpos : 0 < d := by omega
          have hmple : m * p ≤ d := Nat.le_of_dvd hdpos hmpd
          have hq1 : 1 ≤ d / (m * p) :=
            (Nat.one_le_div_iff hmp).2 hmple
          have hdiv : d / (m * p) ≤ d / m :=
            Nat.div_le_div_left hden hm
          apply Real.log_le_log
          · exact_mod_cast hq1
          · exact_mod_cast hdiv
    _ ≤ ∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
        Real.log ((d / m : ℕ) : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro d hd _hdold
          rcases Finset.mem_filter.mp hd with ⟨hdBand, hmd⟩
          have hdI := Finset.mem_Ioc.mp hdBand
          have hdpos : 0 < d := by omega
          have hmle : m ≤ d := Nat.le_of_dvd hdpos hmd
          have hq1 : 1 ≤ d / m := (Nat.one_le_div_iff hm).2 hmle
          exact Real.log_nonneg (by exact_mod_cast hq1)

/-- On the literal subdoubling endpoint, the child cofactor response lies
between its parent response and zero. -/
theorem vfMidProtectedBlockCofactorResponse_freshPrime_interval
    (M L m p : ℕ) (hsub : L < 2 * M)
    (hm : 0 < m) (hp : p.Prime) :
    nativePNTSignedSquareBlockCofactorResponse L M L m ≤
        nativePNTSignedSquareBlockCofactorResponse L M L (m * p) ∧
      nativePNTSignedSquareBlockCofactorResponse L M L (m * p) ≤ 0 := by
  have hsum :=
    vfMidProtectedBlockCofactorLogSum_freshPrime_le M L m p hm hp
  have hparent :=
    vfMidProtectedBlockCofactorLogSum_nonneg M L m hm
  have hchild :=
    vfMidProtectedBlockCofactorLogSum_nonneg M L (m * p)
      (Nat.mul_pos hm hp.pos)
  rw [vfMidProtectedBlockCofactorResponse_endpoint_eq_neg_logSum M L m hsub,
    vfMidProtectedBlockCofactorResponse_endpoint_eq_neg_logSum M L (m * p) hsub]
  constructor <;> linarith

/-- Therefore the fresh-prime response defect is no larger in absolute value
than the parent response itself. -/
theorem vfMidProtectedBlockCofactorResponse_freshPrime_diff_abs_le
    (M L m p : ℕ) (hsub : L < 2 * M)
    (hm : 0 < m) (hp : p.Prime) :
    |nativePNTSignedSquareBlockCofactorResponse L M L m -
        nativePNTSignedSquareBlockCofactorResponse L M L (m * p)| ≤
      |nativePNTSignedSquareBlockCofactorResponse L M L m| := by
  have h :=
    vfMidProtectedBlockCofactorResponse_freshPrime_interval
      M L m p hsub hm hp
  have hparent : nativePNTSignedSquareBlockCofactorResponse L M L m ≤ 0 :=
    h.1.trans h.2
  have hdiff :
      nativePNTSignedSquareBlockCofactorResponse L M L m -
          nativePNTSignedSquareBlockCofactorResponse L M L (m * p) ≤ 0 :=
    sub_nonpos.mpr h.1
  rw [abs_of_nonpos hdiff, abs_of_nonpos hparent]
  linarith [h.2]

/-- The actual physical defect in the reciprocal protected-pull Euler law costs
at most the lost reciprocal factor 1/p of its parent summand. -/
theorem vfMidProtectedBlockFreshPrimePhysicalDefect_abs_le_inv_mul_parent
    (M L m p : ℕ) (hsub : L < 2 * M)
    (hm : 0 < m) (hp : p.Prime) :
    |nativePNTSignedSquareBlockFreshPrimePhysicalDefect L M L m p| ≤
      (1 / (p : ℝ)) *
        |nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m| := by
  have hresp :=
    vfMidProtectedBlockCofactorResponse_freshPrime_diff_abs_le
      M L m p hsub hm hp
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hmpR : 0 < (m : ℝ) * (p : ℝ) := mul_pos hmR hpR
  have hcalc :
      |((μ m : ℤ) : ℝ)| *
            |nativePNTSignedSquareBlockCofactorResponse L M L m -
              nativePNTSignedSquareBlockCofactorResponse L M L (m * p)| /
          ((m : ℝ) * (p : ℝ)) ≤
        (1 / (p : ℝ)) *
          (|((μ m : ℤ) : ℝ)| *
            |nativePNTSignedSquareBlockCofactorResponse L M L m| /
            (m : ℝ)) := by
    have hmul :
        |((μ m : ℤ) : ℝ)| *
            |nativePNTSignedSquareBlockCofactorResponse L M L m -
              nativePNTSignedSquareBlockCofactorResponse L M L (m * p)| ≤
          |((μ m : ℤ) : ℝ)| *
            |nativePNTSignedSquareBlockCofactorResponse L M L m| :=
      mul_le_mul_of_nonneg_left hresp (abs_nonneg _)
    calc
      |((μ m : ℤ) : ℝ)| *
              |nativePNTSignedSquareBlockCofactorResponse L M L m -
                nativePNTSignedSquareBlockCofactorResponse L M L (m * p)| /
            ((m : ℝ) * (p : ℝ)) ≤
          |((μ m : ℤ) : ℝ)| *
              |nativePNTSignedSquareBlockCofactorResponse L M L m| /
            ((m : ℝ) * (p : ℝ)) := by
              exact (div_le_div_iff_of_pos_right hmpR).2 hmul
      _ = (1 / (p : ℝ)) *
          (|((μ m : ℤ) : ℝ)| *
            |nativePNTSignedSquareBlockCofactorResponse L M L m| /
            (m : ℝ)) := by
              field_simp [hmR.ne', hpR.ne']
              ring
  unfold nativePNTSignedSquareBlockFreshPrimePhysicalDefect
    nativePNTSignedSquareBlockCorrelationReciprocalSummand
  rw [abs_div, abs_mul, abs_div, abs_mul]
  push_cast
  simpa [abs_of_pos hmR, abs_of_pos hpR, abs_of_pos hmpR] using hcalc

/-- Direct protected-pull fresh-prime contraction.
At a subdoubling endpoint, pairing one reciprocal parent with a fresh-prime
child cannot increase absolute protected-block mass.  This is an unconditional
inequality on the actual PNT/VF protected-pull carrier. -/
theorem vfMidProtectedBlockReciprocalPair_abs_le_parent
    (M L m p : ℕ) (hsub : L < 2 * M)
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    |nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m +
        nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L (m * p)| ≤
      |nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m| := by
  rw [nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
    L M L hm hp hcop]
  have hdef :=
    vfMidProtectedBlockFreshPrimePhysicalDefect_abs_le_inv_mul_parent
      M L m p hsub hm hp
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hinv0 : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hinv1 : (1 / (p : ℝ)) ≤ 1 := by
    exact (div_le_iff₀ hpR).2 (by simpa using hp1R)
  have hfactor : 0 ≤ 1 - 1 / (p : ℝ) := sub_nonneg.mpr hinv1
  calc
    |(1 - 1 / (p : ℝ)) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect L M L m p| ≤
      |(1 - 1 / (p : ℝ)) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m| +
        |nativePNTSignedSquareBlockFreshPrimePhysicalDefect L M L m p| :=
          abs_add_le _ _
    _ = (1 - 1 / (p : ℝ)) *
          |nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m| +
        |nativePNTSignedSquareBlockFreshPrimePhysicalDefect L M L m p| := by
          rw [abs_mul, abs_of_nonneg hfactor]
    _ ≤ (1 - 1 / (p : ℝ)) *
          |nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m| +
        (1 / (p : ℝ)) *
          |nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m| :=
            add_le_add_left hdef _
    _ = |nativePNTSignedSquareBlockCorrelationReciprocalSummand L M L m| := by
          ring

/-- Literal consecutive-square specialization of the direct fresh-prime
protected-pull contraction. -/
theorem vfMidSquareProtectedBlockReciprocalPair_abs_le_parent
    (R m p : ℕ) (hR : 3 ≤ R)
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    |nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m +
        nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) (m * p)| ≤
      |nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
  apply vfMidProtectedBlockReciprocalPair_abs_le_parent
  · nlinarith
  · exact hm
  · exact hp
  · exact hcop

end RHLean.Analysis
