import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.CovolAntiSameRank
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open Module

namespace RHLean.Geometry.AlpogeAllPlace.Formalism.F

universe u

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem att_rk_pos {N : Submodule ℤ E} [DiscreteTopology N] (hN : N ≠ ⊥) : 0 < rk N := by
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  exact Module.finrank_pos

theorem att_rk_le {L N : Submodule ℤ E} [DiscreteTopology L] (h : N ≤ L) : rk N ≤ rk L :=
  LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion h) (Submodule.inclusion_injective h)

end

end RHLean.Geometry.AlpogeAllPlace.Formalism.F
