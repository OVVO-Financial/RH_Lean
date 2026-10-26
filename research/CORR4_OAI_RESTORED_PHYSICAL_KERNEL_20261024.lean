import Mathlib
import «research.CORR4_OAI_RELAXED_REMAINDER_20261024»
import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»

/-!
# Exact original-CORR4 remainder in the restored OAI integer norm coordinate

This is an exact source-specialization, NOT an application of a Hecke moment
bound.  The physical clock has a sharp endpoint mask X=R^2-1.  The four
restoring terms at md, 3md, 4md and 12md cannot be deleted, and equality of
integer norm sums must not be confused with equality of their ideal phases.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Exact original AMP physical site weight, clipped at the SAME endpoint as
    the finite Mobius/norm-coefficient dictionary. -/
def corr4PhysicalFiniteWeight (R n : ℕ) : ℂ :=
  if n ≤ squareRootEndpoint R then
    (lowOwnerZeroFrequencyMobiusWeight R n : ℂ)
  else 0

theorem corr4PhysicalFiniteWeight_zero_above_endpoint
    (R n : ℕ) (h : squareRootEndpoint R < n) :
    corr4PhysicalFiniteWeight R n = 0 := by
  simp [corr4PhysicalFiniteWeight, Nat.not_le.mpr h]

/-- Pointwise identity between a real Möbius site and its actual finite
    complex physical source. This uses no assumption about ideal labels. -/
theorem corr4PhysicalFiniteWeight_site
    (R n : ℕ) (hn : n ≤ squareRootEndpoint R) :
    ((lowOwnerZeroFrequencyMobiusWeight R n * realMoebiusStep n : ℝ) : ℂ) =
      (ArithmeticFunction.moebius n : ℂ) * corr4PhysicalFiniteWeight R n := by
  simp [corr4PhysicalFiniteWeight, hn, realMoebiusStep]
  ring

/-- Exact source preservation across all physical sites, with the original
    sharp admission mask and the complete signed AMP remainder. -/
theorem corr4PhysicalRemainder_eq_restoredNormKernel
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      -(∑ m ∈ Finset.Icc 1 (squareRootEndpoint R),
        vf919ExcludedNormCoefficients m *
          vf919PhysicalHeckeKernel (squareRootEndpoint R)
            (corr4PhysicalFiniteWeight R) m) := by
  let X := squareRootEndpoint R
  have hR2 : 13 ≤ R ^ 2 := by nlinarith
  have hX : 12 ≤ X := by
    dsimp [X, squareRootEndpoint]
    omega
  have hw : ∀ n, X < n → corr4PhysicalFiniteWeight R n = 0 := by
    intro n hn
    exact corr4PhysicalFiniteWeight_zero_above_endpoint R n hn
  have hsource :
      (lowOwnerZeroFrequencyMobiusAmplitude R : ℂ) =
      ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius n : ℂ) * corr4PhysicalFiniteWeight R n := by
    unfold lowOwnerZeroFrequencyMobiusAmplitude
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [Complex.ofReal_mul] using
      corr4PhysicalFiniteWeight_site R n (Finset.mem_Icc.mp hn).2
  have hrestored :=
    vf919WeightedMobius_eq_excludedNormKernel X hX
      (corr4PhysicalFiniteWeight R) hw
  calc
    lowOwnerPhysicalAmplitudeRemainder R 0 =
        -(lowOwnerZeroFrequencyMobiusAmplitude R : ℂ) :=
      lowOwnerPhysicalAmplitudeRemainder_zero_eq_neg_oneAmplitude R hR
    _ = -(∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius n : ℂ) * corr4PhysicalFiniteWeight R n) := by
      rw [hsource]
    _ = -(∑ m ∈ Finset.Icc 1 X,
        vf919ExcludedNormCoefficients m *
          vf919PhysicalHeckeKernel X (corr4PhysicalFiniteWeight R) m) := by
      rw [hrestored]

#print axioms corr4PhysicalFiniteWeight_site
#print axioms corr4PhysicalRemainder_eq_restoredNormKernel

end RHLean.Proof
