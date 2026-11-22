import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

namespace RHLean.Geometry.AlpogeAllPlace.Formalism.F

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem discreteTopology_of_le {L N : Submodule ℤ E} (h : N ≤ L) [hL : DiscreteTopology L] :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (f := Submodule.inclusion h)
    (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective h)

end RHLean.Geometry.AlpogeAllPlace.Formalism.F
