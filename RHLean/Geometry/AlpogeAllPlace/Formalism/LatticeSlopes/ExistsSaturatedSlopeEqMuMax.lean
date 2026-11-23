import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin
import RHLean.Geometry.AlpogeAllPlace.Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

namespace RHLean.Geometry.AlpogeAllPlace.Formalism.F

theorem covolEqGram : CovolEqGram := covol_eq_gram
theorem covolPos : CovolPos := covol_pos'
theorem covolBasic : CovolBasic := covol_basic_properties
theorem covolEqCovolume : CovolEqCovolume := covol_eq_covolume'
theorem gramDetLe : GramDetLe := gram_det_le
theorem slopesBdd : SlopesBdd := slopesBdd_of gramDetLe
theorem slopeLeMuMax : SlopeLeMuMax := slopeLeMuMax_of slopesBdd
theorem muMaxMono : MuMaxMono := muMaxMono_of slopesBdd
theorem degQuot : DegQuot := degree_quotient
theorem covolAntiSameRank : CovolAntiSameRank := covol_anti_same_rank
theorem saturProps : SaturProps := saturation_properties
theorem shortVector : ShortVector := shortVector_of covolEqCovolume
theorem finiteSaturated : FiniteSaturated := finiteSaturated_of shortVector
theorem muMaxLeMin : MuMaxLeMin := muMaxLeMin_of covolPos shortVector
theorem orthSum : OrthSum := orthogonal_sum_slope

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem muMax_mono {L N : Submodule ℤ E} [DiscreteTopology L] (hN : N ≤ L) (hN0 : N ≠ ⊥) :
    muMax N ≤ muMax L :=
  muMaxMono E L N ‹_› hN hN0

theorem covol_pos (L : Submodule ℤ E) [DiscreteTopology L] : 0 < covol L :=
  covolPos E L ‹_›

theorem deg_eq_deg_add_deg_quot {L N : Submodule ℤ E} [DiscreteTopology L] (hN : IsSaturated L N) :
    deg L = deg N + deg (quot L N) :=
  (degQuot E L N ‹_› hN).2.2

end

end RHLean.Geometry.AlpogeAllPlace.Formalism.F
