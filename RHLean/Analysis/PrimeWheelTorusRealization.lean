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
  let F : ZMod W.modulus → ℂ := fun z =>
    (if W.lower < z.val ∧ z.val ≤ W.upper then
        ((W.correctedSite z.val : ℤ) : ℂ)
      else 0) *
    (if W.lower < z.val ∧ z.val ≤ x then 1 else 0)
  unfold torusPrefixPairing RHLean.Analysis.finiteTorusPairing torusJointField
    torusPrefixWindow
  change (∑ z : ZMod W.modulus, F z) = _
  calc
    (∑ z : ZMod W.modulus, F z) =
        ∑ i : Fin W.modulus, F ((ZMod.finEquiv W.modulus) i) := by
      exact ((ZMod.finEquiv W.modulus).sum_comp F).symm
    _ = ∑ n ∈ Finset.range W.modulus,
        if W.lower < n ∧ n ≤ x then
          (((W.correctedSite n : ℤ) : ℂ)) else 0 := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hval : ((ZMod.finEquiv W.modulus) i).val = i.val := by
        rfl
      by_cases hwin : W.lower < i.val ∧ i.val ≤ x
      · have hfull : W.lower < i.val ∧ i.val ≤ W.upper :=
          ⟨hwin.1, hwin.2.trans hupper⟩
        simp [F, hval, hwin, hfull]
      · simp [F, hval, hwin]
    _ = ∑ n ∈ W.prefixInterval x,
        (((W.correctedSite n : ℤ) : ℂ)) := by
      unfold prefixInterval
      rw [← hset]
      simp only [Finset.sum_filter]

/-- Every finite system with `upper < modulus` has a canonical lossless torus
realization certificate. -/
def canonicalTorusRealizationCertificate
    (W : PrimeWheelFiniteSystem) : W.TorusRealizationCertificate where
  pairing_eq_residual := by
    intro x hlower hupper
    rw [W.torusPrefixPairing_eq_corrected_sum hupper]
    have h := W.residual_eq_corrected_sum x
    exact_mod_cast h.symm

end RHLean.Arithmetic.PrimeWheelFiniteSystem
