import Mathlib
import RHLean.Analysis.PrimeWheelFourierReduction

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Zero-padding into a modulus larger than the arithmetic block is lossless:
the torus pairing is exactly the corrected site sum over `(lower,x]`. -/
theorem torusPrefixPairing_eq_corrected_sum
    (W : PrimeWheelFiniteSystem)
    {x : ℕ} (hupper : x ≤ W.upper) :
    W.torusPrefixPairing x =
      ∑ n ∈ W.prefixInterval x, (((W.correctedSite n : ℤ) : ℂ)) := by
  classical
  have hxmod : x < W.modulus :=
    lt_of_le_of_lt hupper W.upper_lt_modulus
  have hset :
      (Finset.range W.modulus).filter
          (fun n => W.lower < n ∧ n ≤ x) =
        Finset.Ioc W.lower x := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · intro hn
      exact hn.2
    · intro hn
      exact ⟨lt_of_le_of_lt hn.2 hxmod, hn⟩
  unfold torusPrefixPairing RHLean.Analysis.finiteTorusPairing torusJointField
    torusPrefixWindow prefixInterval
  calc
    (∑ z : ZMod W.modulus,
        (if W.lower < z.val ∧ z.val ≤ W.upper then
            ((W.correctedSite z.val : ℤ) : ℂ)
          else 0) *
        (if W.lower < z.val ∧ z.val ≤ x then 1 else 0)) =
      ∑ i : Fin W.modulus,
        (if W.lower < (i : ℕ) ∧ (i : ℕ) ≤ W.upper then
            ((W.correctedSite (i : ℕ) : ℤ) : ℂ)
          else 0) *
        (if W.lower < (i : ℕ) ∧ (i : ℕ) ≤ x then 1 else 0) := by
      symm
      simpa using
        (ZMod.finEquiv W.modulus).sum_comp
          (fun z : ZMod W.modulus =>
            (if W.lower < z.val ∧ z.val ≤ W.upper then
                ((W.correctedSite z.val : ℤ) : ℂ)
              else 0) *
            (if W.lower < z.val ∧ z.val ≤ x then 1 else 0))
    _ = ∑ n ∈ Finset.range W.modulus,
        if W.lower < n ∧ n ≤ x then
          (((W.correctedSite n : ℤ) : ℂ)) else 0 := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hwin : W.lower < (i : ℕ) ∧ (i : ℕ) ≤ x
      · have hfull : W.lower < (i : ℕ) ∧ (i : ℕ) ≤ W.upper :=
          ⟨hwin.1, hwin.2.trans hupper⟩
        simp [hwin, hfull]
      · simp [hwin]
    _ = ∑ n ∈ W.prefixInterval x,
        (((W.correctedSite n : ℤ) : ℂ)) := by
      rw [← hset, Finset.sum_filter]

/-- Every finite system with `upper < modulus` has a canonical lossless torus
realization certificate. -/
def canonicalTorusRealizationCertificate
    (W : PrimeWheelFiniteSystem) : W.TorusRealizationCertificate where
  pairing_eq_residual := by
    intro x hlower hupper
    rw [W.torusPrefixPairing_eq_corrected_sum hupper]
    rw [← W.residual_eq_corrected_sum]
    push_cast
    rfl

end RHLean.Arithmetic.PrimeWheelFiniteSystem

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Canonical family of torus certificates. -/
def canonicalPrimeWheelTorusCertificates
    (W : PrimeWheelFamily) : PrimeWheelTorusCertificates W :=
  fun k => (W k).canonicalTorusRealizationCertificate

end RHLean.Analysis
