import «research.oai_434.VF919WindowErrorClosure»

set_option autoImplicit false

open OAI.SevenEighths
open Parameters RHLeanActualSlotMin RHLeanWindowSaturated
open ProbeFinalAssemblyCertifiedBands RHLean.Analysis.MertensExponent

example : ∀ {Delta : ℝ} (D : HighData Delta) (e : ℝ),
    0 < e → e ≤ D.e → HighData Delta := @withSmallerError

example : ∀ {Delta : ℝ} (D : HighData Delta) (e : ℝ)
    (he : 0 < e) (hle : e ≤ D.e),
    actualSlotMinimum (withSmallerError D e he hle) = actualSlotMinimum D :=
  @withSmallerError_minimum

example : ∀ (D : HighData (1 / 1000000 : ℝ)),
    (∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) →
    HeckeZeroSupremum.beta ≤ 7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D :=
  native_beta_le_window_error_closed_of_fine

example : HeckeZeroSupremum.beta ≤
    (7 / 8 : ℝ) - (7 : ℝ) / (64 * (nearUniformSlotCount : ℝ)) :=
  native_beta_le_near_uniform_window_error_closed

example : ∀ (D : HighData (1 / 1000000 : ℝ)),
    (∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) →
    MertensGrowthAtMost (7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D) :=
  RHLean.Analysis.native_mertens_window_error_closed_of_fine

example : ∀ (D : HighData (1 / 1000000 : ℝ)),
    (∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) →
    MertensPowerBound (7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D + D.e / 2) :=
  RHLean.Analysis.native_mertens_fixed_window_error_closed_of_fine

example : MertensGrowthAtMost
    ((7 / 8 : ℝ) - (7 : ℝ) / (64 * (nearUniformSlotCount : ℝ))) :=
  RHLean.Analysis.native_mertens_near_uniform_window_error_closed

#check withSmallerError_geometry
#check native_beta_le_window_error_closed_of_fine
#check native_beta_le_near_uniform_window_error_closed
#check RHLean.Analysis.native_mertens_window_error_closed_of_fine
#check RHLean.Analysis.native_mertens_fixed_window_error_closed_of_fine
#check RHLean.Analysis.native_mertens_near_uniform_window_error_closed

#print axioms withSmallerError
#print axioms withSmallerError_minimum
#print axioms native_beta_le_window_error_closed_of_fine
#print axioms native_beta_le_near_uniform_window_error_closed
#print axioms RHLean.Analysis.native_mertens_window_error_closed_of_fine
#print axioms RHLean.Analysis.native_mertens_fixed_window_error_closed_of_fine
#print axioms RHLean.Analysis.native_mertens_near_uniform_window_error_closed
