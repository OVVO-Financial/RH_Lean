import Mathlib
import «research.VF_MID_RECURSIVE_REMAINDER_BOUND»
import «research.VF_MID_DIRECT_DISCREPANCY_ABEL»
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.VioleSequentialEulerClosure
import RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge

/-!
# Native VF descent written in Chebyshev theta coordinates

The direct signed-dynamics layer already proves, for one square block,

  P_R - V_R
    = (Theta_R - (2R+1)) / log(m_R) + position_R.

PR #855 proves the same VF block defect in the opposite sign as

  V_R - P_R = native_R + remainder_R,

where native_R is carried entirely by strict lower child square scales and
the full transfer remainder is O(R).

This file identifies those two exact descriptions before taking any norm.
Consequently the centered square-block theta increment is exactly the
log-weighted native VF descent packet plus the already-explicit transfer and
within-band position terms.

No new cancellation principle, PNT rate, Li allocation, or RH hypothesis is
introduced here. This is the bridge needed to attack the existing
square-endpoint Chebyshev envelope directly with the #855 native descent.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The direct right-closed prime-band error and the open-interior square-band
error are literally the same scalar. The upper square never contributes a
prime. -/
theorem vfMidDirectBandError_eq_squareBandError
    (R : ℕ) :
    vfMidDirectBandError R = vfMidSquareBandError R := by
  unfold vfMidDirectBandError vfMidDirectPrimeBandCount vfMidSquareBandError
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  simp only [vfMidSquareWheelPrimes, vfMidSquareWheelSites,
    vfMidSquareBandPrimes, vfMidSquareBandSites]

/-- #855 written with the sign convention of the direct prime-band error. -/
theorem vfMidDirectBandError_eq_neg_native_add_remainder
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidDirectBandError R =
      -(vfMidRecursiveAggregateNativeCharge R +
        vfMidNativeDescentRemainder R) := by
  have hdesc :=
    vfMidOddCompositeTrackingDefect_eq_nativeCharge_add_descentRemainder
      R hR
  have hneg :=
    vfMidOddCompositeTrackingDefect_eq_neg_bandError
      R (by omega : 2 ≤ R)
  rw [hneg] at hdesc
  rw [vfMidDirectBandError_eq_squareBandError]
  linarith

/-- The logarithm at the midpoint of every live square band in the #855 range
is strictly positive. -/
theorem vfMidBandMidpoint_log_pos_of_seven_le
    {R : ℕ} (hR : 7 ≤ R) :
    0 < Real.log (vfMidBandMidpoint R) := by
  apply Real.log_pos
  unfold vfMidBandMidpoint
  have hRreal : (7 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  nlinarith

/-- Exact square-block Chebyshev/native-VF identity.

The centered theta increment is not a new cancellation problem. It is exactly
the #855 native lower-scale packet, its explicit transfer remainder, and the
already-bounded within-band logarithmic position correction, all expressed in
the natural logarithmic currency of the block:

  Theta_R - (2R+1)
    = -log(m_R) * (native_R + remainder_R + position_R).
-/
theorem vfMidDirectThetaBandError_eq_nativeVFDescent
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidDirectThetaBandError R =
      -Real.log (vfMidBandMidpoint R) *
        (vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R +
          vfMidDirectLogPositionError R) := by
  have hsplit := vfMidDirectBandError_eq_theta_add_position R
  have hdesc :=
    vfMidDirectBandError_eq_neg_native_add_remainder R hR
  have hlog :=
    vfMidBandMidpoint_log_pos_of_seven_le hR
  have heq :
      vfMidDirectThetaBandError R /
            Real.log (vfMidBandMidpoint R) +
          vfMidDirectLogPositionError R =
        -(vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R) := by
    rw [← hsplit]
    exact hdesc
  have hlogne : Real.log (vfMidBandMidpoint R) ≠ 0 := hlog.ne'
  field_simp [hlogne] at heq
  nlinarith

/-- Native lower-scale part of one centered theta increment. -/
def vfMidThetaNativeDescentMain (R : ℕ) : ℝ :=
  -Real.log (vfMidBandMidpoint R) *
    vfMidRecursiveAggregateNativeCharge R

/-- Everything outside the native lower-scale packet after changing from VF
seat currency to theta/logarithmic currency. The two prime-population terms
inside the #855 remainder remain signed against one another. -/
def vfMidThetaNativeDescentRemainder (R : ℕ) : ℝ :=
  -Real.log (vfMidBandMidpoint R) *
    (vfMidNativeDescentRemainder R +
      vfMidDirectLogPositionError R)

/-- The block theta increment splits exactly into the native descended packet
and the signed non-native transfer packet. -/
theorem vfMidDirectThetaBandError_eq_thetaNativeMain_add_remainder
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidDirectThetaBandError R =
      vfMidThetaNativeDescentMain R +
        vfMidThetaNativeDescentRemainder R := by
  rw [vfMidDirectThetaBandError_eq_nativeVFDescent R hR]
  unfold vfMidThetaNativeDescentMain vfMidThetaNativeDescentRemainder
  ring

/-- Exact theta endpoint ledger over an arbitrary square window.

For 7 <= A <= B, the change of the Chebyshev square-endpoint error is the
signed sum of native lower-scale VF packets plus their explicit transfer
remainders. No absolute values have been inserted. -/
theorem vfMidDirectThetaEndpointError_sub_eq_nativeVFDescent_sum
    (A B : ℕ) (hA : 7 ≤ A) (hAB : A ≤ B) :
    vfMidDirectThetaEndpointError B -
        vfMidDirectThetaEndpointError A =
      ∑ R ∈ Finset.Ico A B,
        (vfMidThetaNativeDescentMain R +
          vfMidThetaNativeDescentRemainder R) := by
  calc
    vfMidDirectThetaEndpointError B -
          vfMidDirectThetaEndpointError A =
        ∑ R ∈ Finset.Ico A B,
          (vfMidDirectThetaEndpointError (R + 1) -
            vfMidDirectThetaEndpointError R) := by
              symm
              exact Finset.sum_Ico_sub vfMidDirectThetaEndpointError hAB
    _ = ∑ R ∈ Finset.Ico A B, vfMidDirectThetaBandError R := by
          apply Finset.sum_congr rfl
          intro R _hR
          rw [vfMidDirectThetaBandError_eq_endpoint_diff]
    _ = ∑ R ∈ Finset.Ico A B,
          (vfMidThetaNativeDescentMain R +
            vfMidThetaNativeDescentRemainder R) := by
          apply Finset.sum_congr rfl
          intro R hRmem
          have hR7 : 7 ≤ R :=
            hA.trans (Finset.mem_Ico.mp hRmem).1
          rw [vfMidDirectThetaBandError_eq_thetaNativeMain_add_remainder R hR7]

/-- The exact square-endpoint Chebyshev target sufficient for the already
compiled Abel consumer. -/
def VFMidSquareThetaEnvelopeStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      |vfMidDirectThetaEndpointError R| ≤
        C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2

/-- A square-theta envelope supplies the direct VF endpoint estimate at every
R >= 3 with the constants already proved by the Abel layer. -/
theorem abs_vfMidDirectSquareEndpointError_le_of_squareThetaEnvelope
    (h : VFMidSquareThetaEnvelopeStatement)
    (R : ℕ) (hR : 3 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      |vfMidDirectSquareEndpointError R| ≤
        C * (R : ℝ) * Real.log (R : ℝ) +
          (4 * C + 9 / Real.log 4) * (R : ℝ) +
          |vfMidDirectSquareEndpointError 2 -
            vfMidDirectThetaEndpointError 2 *
              vfMidDirectThetaAbelWeight 2| := by
  rcases h with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  exact abs_vfMidDirectSquareEndpointError_le_of_thetaEnvelope
    R hR C hC0 (fun r hr _hrR => hC r hr)

/-- The remaining Chebyshev problem after #855, stated directly on the exact
native theta ledger rather than as a new cancellation hypothesis. -/
def VFMidThetaNativeDescentBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 7 ≤ R →
      |vfMidDirectThetaEndpointError R| ≤
        C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2

/-! ## Exact square-psi protected-pull dynamics -/

/-- The protected Selberg/Euler pull on the literal adjacent square step
`R^2 -> (R+1)^2`. -/
def vfMidSquarePsiProtectedPull (R : ℕ) : ℝ :=
  nativePNTSequentialProtectedBlockPull (R ^ 2) ((R + 1) ^ 2)

/-- Prime-power correction separating psi from theta at a square endpoint. -/
def vfMidSquarePrimePowerCorrection (R : ℕ) : ℝ :=
  nativePsi (R ^ 2) - nativeTheta (R ^ 2)

/-- Adjacent squares are subdoubling from R >= 3. -/
theorem vfMidSquare_succ_sq_lt_two_mul_sq
    (R : ℕ) (hR : 3 ≤ R) :
    (R + 1) ^ 2 < 2 * R ^ 2 := by
  nlinarith

/-- **Exact square-psi endpoint update.**

The native Selberg machinery already packages the complete physical response of
one adjacent square block as a single protected pull:

    E_psi((R+1)^2) = E_psi(R^2) - P_R.

No remainder or asymptotic estimate is used. -/
theorem nativePNTError_square_succ_eq_old_sub_vfMidSquarePsiProtectedPull
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTError ((R + 1) ^ 2) =
      nativePNTError (R ^ 2) - vfMidSquarePsiProtectedPull R := by
  unfold vfMidSquarePsiProtectedPull
  exact nativePNTError_eq_old_sub_protectedBlockPull
    (R ^ 2) ((R + 1) ^ 2)
    (by nlinarith : 1 ≤ R ^ 2)
    (by nlinarith : R ^ 2 ≤ (R + 1) ^ 2)
    (vfMidSquare_succ_sq_lt_two_mul_sq R hR)

/-- The complete square-step Chebyshev energy change is therefore the one
quadratic expression P_R^2 - 2 E_R P_R. -/
theorem nativePNTError_square_succ_sq_sub_sq_eq_protectedPull
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTError ((R + 1) ^ 2) ^ 2 -
        nativePNTError (R ^ 2) ^ 2 =
      vfMidSquarePsiProtectedPull R ^ 2 -
        2 * nativePNTError (R ^ 2) *
          vfMidSquarePsiProtectedPull R := by
  unfold vfMidSquarePsiProtectedPull
  exact
    nativePNTError_sq_sub_sq_eq_protectedBlockPull_sq_sub_two_mul_error
      (R ^ 2) ((R + 1) ^ 2)
      (by nlinarith : 1 ≤ R ^ 2)
      (by nlinarith : R ^ 2 ≤ (R + 1) ^ 2)
      (vfMidSquare_succ_sq_lt_two_mul_sq R hR)

/-- The psi square-block discrepancy differs from the theta block discrepancy
only by the discrete derivative of the prime-power correction. -/
theorem nativePNTError_square_diff_eq_thetaBand_add_primePowerDiff
    (R : ℕ) :
    nativePNTError ((R + 1) ^ 2) - nativePNTError (R ^ 2) =
      vfMidDirectThetaBandError R +
        (vfMidSquarePrimePowerCorrection (R + 1) -
          vfMidSquarePrimePowerCorrection R) := by
  unfold nativePNTError vfMidDirectThetaBandError
    vfMidSquarePrimePowerCorrection
  rw [vfMidDirectThetaBandMass_eq_theta_sub]
  push_cast
  ring

/-- **#855 translated all the way into the protected Chebyshev pull.**

The exact protected pull driving the square-psi endpoint update is the
log-weighted native VF descent packet, minus only the discrete prime-power
correction:

    P_R
      = log(m_R) * (native_R + Rem_R + position_R)
        - (Q_{R+1} - Q_R).

Thus the Chebyshev attack and the VF owner descent are now literally the same
one-step arithmetic object in two coordinate systems. -/
theorem vfMidSquarePsiProtectedPull_eq_nativeVFDescent
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidSquarePsiProtectedPull R =
      Real.log (vfMidBandMidpoint R) *
        (vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R +
          vfMidDirectLogPositionError R) -
        (vfMidSquarePrimePowerCorrection (R + 1) -
          vfMidSquarePrimePowerCorrection R) := by
  have hupdate :=
    nativePNTError_square_succ_eq_old_sub_vfMidSquarePsiProtectedPull
      R (by omega : 3 ≤ R)
  have hdiff :=
    nativePNTError_square_diff_eq_thetaBand_add_primePowerDiff R
  have htheta :=
    vfMidDirectThetaBandError_eq_nativeVFDescent R hR
  rw [htheta] at hdiff
  linarith

/-! ## Adjacent-square second-Selberg frontier sign -/

/-- On the exact adjacent-square frontier with cutoff `R` and endpoint
`(R+1)^2`, the positive mixed two-prime face is impossible.  Two distinct
primes both larger than `R` already have product strictly larger than the
endpoint.  Therefore every surviving second-Selberg frontier atom is a
negative prime-square diagonal. -/
theorem vfMidAdjacentSquareSecondSelbergFrontierCharge_nonpos
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTSignedSecondSelbergWheelFrontierCharge
        R ((R + 1) ^ 2) ≤ 0 := by
  unfold nativePNTSignedSecondSelbergWheelFrontierCharge
  apply Finset.sum_nonpos
  intro n hn
  have hscale : (R + 1) ^ 2 < 2 * R ^ 2 :=
    vfMidSquare_succ_sq_lt_two_mul_sq R hR
  rcases
      nativePNTSignedSecondSelbergWheelFrontierSite_classification
        hscale hn with hsq | hmix
  · rcases hsq with ⟨q, _hqPrime, _hRq, _hnq, _herr, hkernel⟩
    rw [hkernel]
    exact neg_nonpos.mpr (sq_nonneg _)
  · rcases hmix with
      ⟨q, r, _hqPrime, _hrPrime, hqr, hRq, hRr, hnqr, _herr, _hkernel⟩
    have hnData :=
      mem_nativePNTSignedSecondSelbergWheelFrontierSites.mp hn
    have hnle : n ≤ (R + 1) ^ 2 :=
      (Finset.mem_Icc.mp hnData.1).2
    rw [hnqr] at hnle
    rcases lt_or_gt_of_ne hqr with hqrLt | hrqLt
    · have hqLower : R + 1 ≤ q := by omega
      have hrLower : R + 2 ≤ r := by omega
      have hprod :
          (R + 1) * (R + 2) ≤ q * r :=
        Nat.mul_le_mul hqLower hrLower
      have hstrict :
          (R + 1) ^ 2 < (R + 1) * (R + 2) := by
        have hpos : 0 < R + 1 := by omega
        rw [pow_two]
        exact Nat.mul_lt_mul_of_pos_left
          (by omega : R + 1 < R + 2) hpos
      omega
    · have hrLower : R + 1 ≤ r := by omega
      have hqLower : R + 2 ≤ q := by omega
      have hprod :
          (R + 2) * (R + 1) ≤ q * r :=
        Nat.mul_le_mul hqLower hrLower
      have hstrict :
          (R + 1) ^ 2 < (R + 2) * (R + 1) := by
        have hpos : 0 < R + 1 := by omega
        rw [pow_two]
        exact Nat.mul_lt_mul_of_pos_right
          (by omega : R + 1 < R + 2) hpos
      omega

/-- Consequently the frontier error mass has the favorable nonnegative sign on
every adjacent square endpoint. -/
theorem vfMidAdjacentSquareSecondSelbergFrontierErrorMass_nonneg
    (R : ℕ) (hR : 3 ≤ R) :
    0 ≤ nativePNTSignedSecondSelbergWheelFrontierErrorMass
      R ((R + 1) ^ 2) := by
  have hscale : (R + 1) ^ 2 < 2 * R ^ 2 :=
    vfMidSquare_succ_sq_lt_two_mul_sq R hR
  rw [nativePNTSignedSecondSelbergWheelFrontierErrorMass_eq_neg_charge hscale]
  exact neg_nonneg.mpr
    (vfMidAdjacentSquareSecondSelbergFrontierCharge_nonpos R hR)

/-! ## Square-psi reduction

The Selberg engine in RHLean is written for the second Chebyshev function
psi.  At square endpoints, repeated prime powers cost only R log(R^2), which
is one logarithm below the R log(R)^2 envelope needed by the existing theta
consumer.  Thus it is enough to tighten the already-native psi error on
squares; no separate theta cancellation theorem is required.
-/

/-- The prime-power correction at a square endpoint is nonnegative and bounded
by R log(R^2). -/
theorem vfMidSquarePsi_sub_theta_le
    (R : ℕ) (hR : 1 ≤ R) :
    0 ≤ nativePsi (R ^ 2) - nativeTheta (R ^ 2) ∧
      nativePsi (R ^ 2) - nativeTheta (R ^ 2) ≤
        (R : ℝ) * Real.log ((R ^ 2 : ℕ) : ℝ) := by
  constructor
  · exact sub_nonneg.mpr (nativeTheta_le_psi (R ^ 2))
  · have h :=
      nativePsi_le_theta_add_sqrt_log (R ^ 2)
        (by nlinarith : 1 ≤ R ^ 2)
    rw [Nat.sqrt_eq'] at h
    linarith

/-- Theta error is the native psi error minus only the square-root-supported
prime-power correction. -/
theorem abs_vfMidDirectThetaEndpointError_le_psi_add_primePower
    (R : ℕ) (hR : 1 ≤ R) :
    |vfMidDirectThetaEndpointError R| ≤
      |nativePNTError (R ^ 2)| +
        (R : ℝ) * Real.log ((R ^ 2 : ℕ) : ℝ) := by
  rcases vfMidSquarePsi_sub_theta_le R hR with ⟨hq0, hq⟩
  have hid :
      vfMidDirectThetaEndpointError R =
        nativePNTError (R ^ 2) -
          (nativePsi (R ^ 2) - nativeTheta (R ^ 2)) := by
    unfold vfMidDirectThetaEndpointError nativePNTError
    push_cast
    ring
  rw [hid]
  calc
    |nativePNTError (R ^ 2) -
        (nativePsi (R ^ 2) - nativeTheta (R ^ 2))|
        ≤ |nativePNTError (R ^ 2)| +
            |nativePsi (R ^ 2) - nativeTheta (R ^ 2)| := abs_sub _ _
    _ = |nativePNTError (R ^ 2)| +
          (nativePsi (R ^ 2) - nativeTheta (R ^ 2)) := by
          rw [abs_of_nonneg hq0]
    _ ≤ |nativePNTError (R ^ 2)| +
          (R : ℝ) * Real.log ((R ^ 2 : ℕ) : ℝ) := by
          exact add_le_add_left hq _

/-- Square-endpoint psi envelope in the exact scale needed for the VF Abel
consumer after the lower-order prime-power correction is removed. -/
def VFMidSquarePsiEnvelopeStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      |nativePNTError (R ^ 2)| ≤
        C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2

private lemma vfMid_log_three_gt_one :
    (1 : ℝ) < Real.log 3 := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
  apply Real.log_lt_log (Real.exp_pos 1)
  exact Real.exp_one_lt_d9.trans (by norm_num)

/-- **Psi on squares is sufficient for theta on squares.**

The conversion loses only the harmless additive constant 2 in the envelope:
the prime-power correction is at most 2 R log R, and log R >= 1 for R >= 3. -/
theorem vfMidSquareThetaEnvelope_of_psiEnvelope
    (hpsi : VFMidSquarePsiEnvelopeStatement) :
    VFMidSquareThetaEnvelopeStatement := by
  rcases hpsi with ⟨C, hC0, hC⟩
  refine ⟨C + 2, by positivity, ?_⟩
  intro R hR
  have hbridge :=
    abs_vfMidDirectThetaEndpointError_le_psi_add_primePower
      R (by omega : 1 ≤ R)
  have hpsiR := hC R hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by positivity
  have hlog1 : (1 : ℝ) ≤ Real.log (R : ℝ) := by
    have hlog3 : (1 : ℝ) < Real.log 3 := vfMid_log_three_gt_one
    have h3R : (3 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hlog3R :
        Real.log 3 ≤ Real.log (R : ℝ) :=
      Real.log_le_log (by norm_num) h3R
    linarith
  have hlog0 : 0 ≤ Real.log (R : ℝ) := by linarith
  have hlogSq :
      Real.log (R : ℝ) ≤ (Real.log (R : ℝ)) ^ 2 := by
    nlinarith
  have hsqlog :
      Real.log ((R ^ 2 : ℕ) : ℝ) =
        2 * Real.log (R : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hprimePower :
      (R : ℝ) * Real.log ((R ^ 2 : ℕ) : ℝ) ≤
        2 * (R : ℝ) * (Real.log (R : ℝ)) ^ 2 := by
    rw [hsqlog]
    nlinarith
  calc
    |vfMidDirectThetaEndpointError R|
        ≤ |nativePNTError (R ^ 2)| +
            (R : ℝ) * Real.log ((R ^ 2 : ℕ) : ℝ) := hbridge
    _ ≤ C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2 +
          2 * (R : ℝ) * (Real.log (R : ℝ)) ^ 2 :=
      add_le_add hpsiR hprimePower
    _ = (C + 2) * (R : ℝ) * (Real.log (R : ℝ)) ^ 2 := by ring

/-- Therefore the existing direct Abel theorem consumes a square-psi envelope
without any additional cancellation hypothesis. -/
theorem abs_vfMidDirectSquareEndpointError_le_of_squarePsiEnvelope
    (h : VFMidSquarePsiEnvelopeStatement)
    (R : ℕ) (hR : 3 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      |vfMidDirectSquareEndpointError R| ≤
        C * (R : ℝ) * Real.log (R : ℝ) +
          (4 * C + 9 / Real.log 4) * (R : ℝ) +
          |vfMidDirectSquareEndpointError 2 -
            vfMidDirectThetaEndpointError 2 *
              vfMidDirectThetaAbelWeight 2| :=
  abs_vfMidDirectSquareEndpointError_le_of_squareThetaEnvelope
    (vfMidSquareThetaEnvelope_of_psiEnvelope h) R hR

end RHLean.Analysis
