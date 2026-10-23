import «research.VF_919_FROZEN_COFACTOR_OAI_NNS_RESPONSE_20261023»

/-!
# Complete source weld: frozen coefficient -> true prime-tail -> restored
# Eisenstein ideal-norm kernel -> SAME physical NNS Gram

The previous source map and the genuine smooth/high-prime Gram are NOW
connected by the exact cofactor Fubini theorem below. No OAI detector
moment estimate, independent seven-eighths bound, or RH statement is assumed.
All excluded rational prime factors 3,4,12 remain in the Hecke kernel.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Proof

/-- No implicit relabeling: the finite physical cofactor sum with
ACTUAL p>R prime-availability weights is precisely the prime-first
Mertens response in the already compiled genuine-root source. -/
theorem vf919FrozenCofactorPhysicalResponse_eq_primeTail
    (R : ℕ) (hR : 2 ≤ R) :
    vf919FrozenCofactorPhysicalResponse R =
      vf919FrozenWheelPrimeTail R := by
  let X := vf919FrozenCofactorEndpoint R
  have hRX : R ≤ X := by
    dsimp [X, vf919FrozenCofactorEndpoint]
    have htwice : R * 2 ≤ R * R :=
      Nat.mul_le_mul_left R (by omega : 2 ≤ R)
    have hpoly : R + 1 ≤ R ^ 2 := by nlinarith
    have hcancel : (R ^ 2 - 1) + 1 = R ^ 2 :=
      Nat.sub_add_cancel (by omega)
    omega
  have hsub : Finset.Ico 1 R ⊆ Finset.Icc 1 X := by
    intro c hc
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hc ⊢
    omega
  change
    (∑ c ∈ Finset.Ico 1 R,
      (ArithmeticFunction.moebius c : ℂ) *
        vf919FrozenCofactorPrimeWeight R c) =
      primeSieveMertensPrimeTail R X
  calc
    (∑ c ∈ Finset.Ico 1 R,
      (ArithmeticFunction.moebius c : ℂ) *
        vf919FrozenCofactorPrimeWeight R c) =
      ∑ c ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius c : ℂ) *
          vf919FrozenCofactorPrimeWeight R c := by
      apply Finset.sum_subset hsub
      intro c hcX hnot
      have hcR : R ≤ c := by
        simp only [Finset.mem_Ico, not_and, not_lt] at hnot
        exact hnot (Finset.mem_Icc.mp hcX).1
      rw [vf919FrozenCofactorPrimeWeight_zero_of_root_le R c hR hcR]
      ring
    _ = primeSieveTransportCofactorMass R X := by
      unfold primeSieveTransportCofactorMass vf919FrozenCofactorPrimeWeight
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      simp only [mul_ite, mul_one, mul_zero, canonicalMoebiusWeight]
    _ = primeSieveMertensPrimeTail R X :=
      primeSieveTransportCofactorMass_eq_mertensPrimeTail R X

/-- The actual sharp square-prefix Mertens amplitude equals
the root-smooth mass MINUS the fully restored Hecke coefficient kernel
with the genuine moving-prime response, no source admission hypothesis. -/
theorem vf919FrozenWheelMertens_eq_smooth_sub_completeHecke
    (R : ℕ) (hR : 4 ≤ R) :
    mertensSummatory (vf919FrozenCofactorEndpoint R) =
      vf919FrozenWheelSmoothMass R -
        vf919FrozenCofactorHeckeResponse R := by
  calc
    mertensSummatory (vf919FrozenCofactorEndpoint R) =
      vf919FrozenWheelSmoothMass R -
        vf919FrozenWheelPrimeTail R :=
      vf919FrozenWheelMertens_eq_smooth_sub_primeTail R (by omega)
    _ = vf919FrozenWheelSmoothMass R -
        vf919FrozenCofactorPhysicalResponse R := by
      rw [vf919FrozenCofactorPhysicalResponse_eq_primeTail R (by omega)]
    _ = vf919FrozenWheelSmoothMass R -
        vf919FrozenCofactorHeckeResponse R := by
      rw [vf919FrozenCofactorPhysicalResponse_eq_completeHecke R hR]

/-- The SAME actual source in both OAI's restored norm coefficients and
zero-target NNS signed mixed Gram. No standalone NNS covariance assumption. -/
theorem vf919FrozenWheel_completeHecke_signedNNS_gram
    (R : ℕ) (hR : 4 ≤ R) :
    ‖mertensSummatory (vf919FrozenCofactorEndpoint R)‖ ^ 2 =
      ‖vf919FrozenWheelSmoothMass R‖ ^ 2 +
      ‖vf919FrozenCofactorHeckeResponse R‖ ^ 2 -
      2 * (vf919FrozenWheelSmoothMass R *
        star (vf919FrozenCofactorHeckeResponse R)).re := by
  rw [vf919FrozenWheelMertens_eq_smooth_sub_completeHecke R hR]
  simpa [Complex.sq_norm] using
    Complex.normSq_sub (vf919FrozenWheelSmoothMass R)
      (vf919FrozenCofactorHeckeResponse R)

/-- This is the exact signed NNS payment one INHERITS FROM an external
Mertens amplitude estimate, including the genuine original Hecke kernel.
The external estimate is explicit and no new 7/8 theorem is asserted. -/
theorem vf919FrozenWheel_completeHecke_antiAlignment_of_externalBound
    (R : ℕ) (hR : 4 ≤ R) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ‖mertensSummatory (vf919FrozenCofactorEndpoint R)‖ ≤ A) :
    ‖vf919FrozenWheelSmoothMass R‖ ^ 2 +
        ‖vf919FrozenCofactorHeckeResponse R‖ ^ 2 - A ^ 2 ≤
      2 * (vf919FrozenWheelSmoothMass R *
        star (vf919FrozenCofactorHeckeResponse R)).re := by
  have hsquared :
      ‖mertensSummatory (vf919FrozenCofactorEndpoint R)‖ ^ 2 ≤ A ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hA).mpr hbound
  rw [vf919FrozenWheel_completeHecke_signedNNS_gram R hR] at hsquared
  linarith

#print axioms vf919FrozenCofactorPhysicalResponse_eq_primeTail
#print axioms vf919FrozenWheelMertens_eq_smooth_sub_completeHecke
#print axioms vf919FrozenWheel_completeHecke_signedNNS_gram
#print axioms vf919FrozenWheel_completeHecke_antiAlignment_of_externalBound

end RHLean.Analysis
