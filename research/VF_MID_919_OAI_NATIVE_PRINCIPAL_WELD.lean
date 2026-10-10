import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»
import «research.VF_MID_919_OAI_OWNER_TWO_SIGNED_BOUNDARY»

/-!
# Actual owner-two weights in the constructed principal norm coefficients

Both weights are the original native AMP site weights. The coefficient
conversion is proved for the actual rational Mobius function, so this weld
has no coefficient-identification premise. The interpretation as actual
Eisenstein ideal Mobius and the uniform analytic estimate remain separate.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

private theorem vf919OwnerTwoBaseFiber_subset_clock (R : ℕ) :
    lowOwnerFirstOwnerBaseFiber R 2 ∅ ⊆ Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1

private theorem vf919OwnerTwoReturnedFiber_subset_clock (R : ℕ) :
    lowOwnerFirstOwnerAdmittedBaseFiber R 2 ∅ ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  exact vf919OwnerTwoBaseFiber_subset_clock R (Finset.mem_filter.mp hn).1

def vf919OwnerTwoParentPrincipalNormSum (R : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (squareRootEndpoint R),
    vf919ExcludedNormCoefficients m *
      vf919PhysicalHeckeKernel (squareRootEndpoint R)
        (fun n => (vf919OwnerTwoPhysicalParentSiteWeight R n : ℂ)) m

def vf919OwnerTwoReturnedPrincipalNormSum (R : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (squareRootEndpoint R),
    vf919ExcludedNormCoefficients m *
      vf919PhysicalHeckeKernel (squareRootEndpoint R)
        (fun n => (vf919OwnerTwoPhysicalReturnedSiteWeight R n : ℂ)) m

theorem vf919OwnerTwoParentPrincipalNormSum_eq_native (R : ℕ)
    (hX : 12 ≤ squareRootEndpoint R) :
    vf919OwnerTwoParentPrincipalNormSum R =
      (lowOwnerFirstOwnerBaseAmplitude R 2 ∅ : ℂ) := by
  have hw : ∀ n, squareRootEndpoint R < n →
      (vf919OwnerTwoPhysicalParentSiteWeight R n : ℂ) = 0 := by
    intro n hn
    have hnot : n ∉ lowOwnerFirstOwnerBaseFiber R 2 ∅ := by
      intro h
      have := (Finset.mem_Icc.mp (vf919OwnerTwoBaseFiber_subset_clock R h)).2
      omega
    simp [vf919OwnerTwoPhysicalParentSiteWeight, hnot]
  unfold vf919OwnerTwoParentPrincipalNormSum
  rw [← vf919WeightedMobius_eq_excludedNormKernel _ hX _ hw]
  rw [← Finset.sum_subset (vf919OwnerTwoBaseFiber_subset_clock R)]
  · rw [← vf919OwnerTwoPhysicalParentSite_sum_eq_base R]
    push_cast
    apply Finset.sum_congr rfl
    intro n _hn
    simp [realMoebiusStep]
  · intro n _hn hnot
    simp [vf919OwnerTwoPhysicalParentSiteWeight, hnot]

theorem vf919OwnerTwoReturnedPrincipalNormSum_eq_native (R : ℕ)
    (hX : 12 ≤ squareRootEndpoint R) :
    vf919OwnerTwoReturnedPrincipalNormSum R =
      (lowOwnerFirstOwnerReturnedChildParentAmplitude R 2 ∅ : ℂ) := by
  have hw : ∀ n, squareRootEndpoint R < n →
      (vf919OwnerTwoPhysicalReturnedSiteWeight R n : ℂ) = 0 := by
    intro n hn
    have hnot : n ∉ lowOwnerFirstOwnerAdmittedBaseFiber R 2 ∅ := by
      intro h
      have := (Finset.mem_Icc.mp (vf919OwnerTwoReturnedFiber_subset_clock R h)).2
      omega
    simp [vf919OwnerTwoPhysicalReturnedSiteWeight, hnot]
  unfold vf919OwnerTwoReturnedPrincipalNormSum
  rw [← vf919WeightedMobius_eq_excludedNormKernel _ hX _ hw]
  rw [← Finset.sum_subset (vf919OwnerTwoReturnedFiber_subset_clock R)]
  · rw [← vf919OwnerTwoPhysicalReturnedSite_sum_eq_returned R]
    push_cast
    apply Finset.sum_congr rfl
    intro n _hn
    simp [realMoebiusStep]
  · intro n _hn hnot
    simp [vf919OwnerTwoPhysicalReturnedSiteWeight, hnot]

/-- The COMPLETE actual owner-two signed Gram in the constructed principal
norm currency. Both negative branch squares are absorbed by the existing
native source-product theorem; no analytic bound is used. -/
theorem vf919OwnerTwoSignedGram_eq_constructedPrincipalNormPairing (R : ℕ)
    (hX : 12 ≤ squareRootEndpoint R) :
    2 * lowOwnerFirstOwnerCellGram R 2 ∅ =
      -2 * (vf919OwnerTwoParentPrincipalNormSum R *
        star (vf919OwnerTwoReturnedPrincipalNormSum R)).re := by
  rw [vf919OwnerTwoParentPrincipalNormSum_eq_native R hX,
    vf919OwnerTwoReturnedPrincipalNormSum_eq_native R hX]
  rw [vf919OwnerTwoSignedGram_eq_native_site_products,
    vf919OwnerTwoPhysicalParentSite_sum_eq_base,
    vf919OwnerTwoPhysicalReturnedSite_sum_eq_returned]
  simp

end RHLean.Proof
