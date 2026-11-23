import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNExtreme
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.PiSumForallInsertOnly
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.RescaleCovol
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeIneq
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameHermSharpB
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

namespace RHLean.Geometry.AlpogeAllPlace.Formalism.HN

theorem satR : SatR := real_saturation_property
theorem finSup : FinSup := finite_supremum_slopes
theorem satBasic : SatBasic := saturation_basic_properties
theorem ratioMax : RatioMax := maximal_slope_ratio
theorem degSupermod : DegSupermod := degree_supermodular
theorem muChar : MuChar := slope_characterization
theorem hnStep_spec : HNStep := hnStep_of degSupermod muChar ratioMax finSup satR satBasic
theorem slopeIneq : SlopeIneq := slope_inequality_general
theorem hnSum : HNSum := polygon_slope_sum
theorem hnSlopes : HNSlopes := polygon_slopes_characterization
theorem shiftInvariance : ShiftInvariance := shiftInvariance_of muChar muChar hnSlopes
theorem duality : Duality := slope_duality_formula
theorem piSum : PiSum := product_slope_sum
theorem plLat : PlLat := place_lattice_structure
theorem sizeMu : SizeMu := size_maximal_slope
theorem gramBlock : GramBlock := gram_block_determinant
theorem rescaleCovol : RescaleCovol := rescale_covolume_formula
theorem twist : Twist := twist_of rescaleCovol plLat shiftInvariance
theorem slopeIneqMean : SlopeIneqMean := slope_inequality_mean
theorem htGram : HtGram := height_gram_determinant
theorem htImage : HtImage := height_image_formula
theorem sizeIneq : SizeIneq := sizeIneq_of size_maximal_slope height_image_formula place_lattice_structure
theorem rerealize : Rerealize := lattice_rerealization
theorem quotRealize : QuotRealize := quotient_lattice_realization
theorem theoremFSharp : TheoremFSharp := frame_theorem_sharp
theorem theoremF : TheoremF := frame_theorem_log_ideal
theorem dualPl : DualPl := dual_polygon_identity

end RHLean.Geometry.AlpogeAllPlace.Formalism.HN
