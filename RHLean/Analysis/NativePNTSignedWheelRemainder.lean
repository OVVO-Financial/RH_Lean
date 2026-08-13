import Mathlib
import RHLean.Analysis.NativePNTSquarePrefixMobiusError
import RHLean.Arithmetic.PrimeWheelPartialError

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

def nativePNTWheelResolvedSignedMass (y N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (RHLean.Arithmetic.partialPrimeWheelSite y N m : ℝ) *
      nativePNTMobiusLogReciprocalFiber N m
        (fun d => nativePNTError (N / d))

def nativePNTWheelResidualSignedMass (y N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    ((((μ m : ℤ) : ℝ) -
        (RHLean.Arithmetic.partialPrimeWheelSite y N m : ℝ)) *
      nativePNTMobiusLogReciprocalFiber N m
        (fun d => nativePNTError (N / d)))

theorem nativePNTMobiusReciprocalSignedErrorMass_eq_wheel_add_residual
    (y N : ℕ) :
    nativePNTMobiusReciprocalSignedErrorMass N =
      nativePNTWheelResolvedSignedMass y N +
        nativePNTWheelResidualSignedMass y N := by
  unfold nativePNTMobiusReciprocalSignedErrorMass
    nativePNTMobiusLogReciprocalMass
    nativePNTWheelResolvedSignedMass nativePNTWheelResidualSignedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring_nf
  exact mul_comm _ _

def nativePNTSignedSelbergRemainder (N : ℕ) : ℝ :=
  (nativeSelbergPair N - 2 * (N : ℝ) * Real.log (N : ℝ)) -
    (Real.log ((Nat.factorial N : ℕ) : ℝ) -
      (N : ℝ) * Real.log (N : ℝ))

theorem nativePNTError_mul_log_add_mobiusSigned_eq_remainder (N : ℕ) :
    nativePNTError N * Real.log (N : ℝ) +
      nativePNTMobiusReciprocalSignedErrorMass N =
        nativePNTSignedSelbergRemainder N := by
  have hdecomp := nativePNTError_selberg_decomposition N
  rw [nativeLambdaSignedErrorMass_eq_mobiusReciprocal N] at hdecomp
  unfold nativePNTSignedSelbergRemainder
  linarith

theorem nativePNTError_mul_log_add_wheel_add_residual_eq_remainder
    (y N : ℕ) :
    nativePNTError N * Real.log (N : ℝ) +
        nativePNTWheelResolvedSignedMass y N +
        nativePNTWheelResidualSignedMass y N =
      nativePNTSignedSelbergRemainder N := by
  have h := nativePNTError_mul_log_add_mobiusSigned_eq_remainder N
  rw [nativePNTMobiusReciprocalSignedErrorMass_eq_wheel_add_residual y N] at h
  linarith

theorem nativePNTError_mul_log_add_wheel_eq_remainder_sub_residual
    (y N : ℕ) :
    nativePNTError N * Real.log (N : ℝ) +
        nativePNTWheelResolvedSignedMass y N =
      nativePNTSignedSelbergRemainder N -
        nativePNTWheelResidualSignedMass y N := by
  linarith [nativePNTError_mul_log_add_wheel_add_residual_eq_remainder y N]

theorem nativePNTWheelResidualSignedMass_update
    (y z N : ℕ) :
    nativePNTWheelResidualSignedMass z N =
      nativePNTWheelResidualSignedMass y N -
        (nativePNTWheelResolvedSignedMass z N -
          nativePNTWheelResolvedSignedMass y N) := by
  have hy := nativePNTMobiusReciprocalSignedErrorMass_eq_wheel_add_residual y N
  have hz := nativePNTMobiusReciprocalSignedErrorMass_eq_wheel_add_residual z N
  linarith

theorem partialPrimeWheelSite_eq_moebius_of_endpoint_le_cutoff
    (y N m : ℕ) (hNy : N ≤ y) (hm : m ∈ Finset.Icc 1 N) :
    RHLean.Arithmetic.partialPrimeWheelSite y N m = μ m := by
  have hmI := Finset.mem_Icc.mp hm
  have hmpos : 0 < m := by omega
  have hall : ∀ p ∈ m.primeFactors, p ≤ y := by
    intro p hp
    have hpData := Nat.mem_primeFactors.mp hp
    have hpdvd : p ∣ m := hpData.2.1
    have hpm : p ≤ m := Nat.le_of_dvd (by omega) hpdvd
    exact hpm.trans (hmI.2.trans hNy)
  have hunres : RHLean.Arithmetic.primeWheelUnresolvedPart y m = 1 :=
    (RHLean.Arithmetic.unresolvedPart_eq_one_iff_all_primeFactors_le y).2 hall
  have herr := RHLean.Arithmetic.partialPrimeWheel_error_eq
    y N hmpos hmI.2
  have hzero :
      μ m - RHLean.Arithmetic.partialPrimeWheelSite y N m = 0 := by
    simpa [hunres] using herr
  exact (sub_eq_zero.mp hzero).symm

theorem nativePNTWheelResidualSignedMass_eq_zero_of_endpoint_le_cutoff
    (y N : ℕ) (hNy : N ≤ y) :
    nativePNTWheelResidualSignedMass y N = 0 := by
  unfold nativePNTWheelResidualSignedMass
  apply Finset.sum_eq_zero
  intro m hm
  have hsZ := partialPrimeWheelSite_eq_moebius_of_endpoint_le_cutoff
    y N m hNy hm
  have hsR :
      (RHLean.Arithmetic.partialPrimeWheelSite y N m : ℝ) =
        ((μ m : ℤ) : ℝ) := by
    exact_mod_cast hsZ
  rw [hsR]
  ring

theorem nativePNTError_mul_log_add_completeWheel_eq_remainder
    (y N : ℕ) (hNy : N ≤ y) :
    nativePNTError N * Real.log (N : ℝ) +
        nativePNTWheelResolvedSignedMass y N =
      nativePNTSignedSelbergRemainder N := by
  have h := nativePNTError_mul_log_add_wheel_eq_remainder_sub_residual y N
  rw [nativePNTWheelResidualSignedMass_eq_zero_of_endpoint_le_cutoff y N hNy] at h
  linarith

end RHLean.Analysis
