import RHLean.Geometry.NativeCMWeierstrassAppellHumbert
import RHLean.Geometry.NativeCMWeierstrassMorphismTangent
import RHLean.Geometry.NativeCMWeierstrassOriginBaseChange

/-!
# The actual polarized analytic seed at every infinite place

The same integral equation is base changed at the actual representative of
each infinite place. Its constructed holomorphic uniformization has the
actual origin line bundle, sigma Appell--Humbert law, and the actual scalar
extension of the original integral epsilon vector. The resulting Lie length
is the previously computed place profile, whose logarithm is the exact
lattice period. Neither a target norm nor a class-group mean is assumed.

This is native glue between the attributed equation, regular-section,
origin-bundle base-change and canonical-sigma constructions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory PeriodPair

namespace RHLean.Geometry.NativeCM.AllPlaceTangentPeriod

open SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie
open SchemeTheory.WeierstrassMorphismTangent WeierstrassTheta

variable {F : Type} [Field F] (W : _root_.WeierstrassCurve (𝓞 F))
    [W.IsElliptic] (hΔ : W.Δ = 1)

local instance (v : InfinitePlace F) : (complexEquation W v).IsElliptic :=
  inferInstanceAs (W.map (placeMap v)).IsElliptic

def holomorphicComparison (v : InfinitePlace F) :
    coordinateChange W hΔ v • (complexEquation W v).baseChange ℂ =
      Weierstrass.latticeCurve (lattice W hΔ v) := by
  change coordinateChange W hΔ v •
    ((complexEquation W v).map (RingHom.id ℂ)) = _
  rw [_root_.WeierstrassCurve.map_id]
  exact comparison W hΔ v

/-- The uniformization is constructed on the literal complex base change
of the same integral equation and its actual origin line bundle. -/
def placeHolUnif (v : InfinitePlace F) :
    EllipticHolUnif (complexEquation W v) (lattice W hΔ v) :=
  canonicalHolUnif (lattice W hΔ v) (complexEquation W v)
    (coordinateChange W hΔ v) (holomorphicComparison W hΔ v)

theorem placeHolUnif_isAH (v : InfinitePlace F) :
    (placeHolUnif W hΔ v).IsAH (Weierstrass.latticeForm (lattice W hΔ v))
      (Weierstrass.sigmaSign (lattice W hΔ v)) :=
  canonicalHolUnif_isAH _ _ _ _

omit [W.IsElliptic] in
/-- This is the scalar extension of the original integral vector, not a
new generator chosen after complex uniformization. -/
theorem integralVector_place_baseChange (v : InfinitePlace F) :
    (integralVector (complexEquation W v)).left ≫
        mapHom W (placeMap v) rfl =
      spMap (WeierstrassTangent.dualMap (placeMap v)) ≫ (integralVector W).left := by
  simpa only [map_one] using! vec_mapHom W (placeMap v) 1

theorem placeHolUnif_integral_tangent (v : InfinitePlace F) :
    (placeHolUnif W hΔ v).HasTangentDirection
      ((coordinateChange W hΔ v).u : ℂ) (integralVector (complexEquation W v)) :=
  canonicalHolUnif_integral_tangent _ _ _ _

/-- The actual atlas, the actual base-changed integral vector, and the
exact logarithmic period comparison hold together at every place. -/
theorem actual_polarized_tangent_period (v : InfinitePlace F) :
    (placeHolUnif W hΔ v).IsAH (Weierstrass.latticeForm (lattice W hΔ v))
      (Weierstrass.sigmaSign (lattice W hΔ v)) ∧
    (placeHolUnif W hΔ v).HasTangentDirection
      ((coordinateChange W hΔ v).u : ℂ) (integralVector (complexEquation W v)) ∧
    (integralVector (complexEquation W v)).left ≫ mapHom W (placeMap v) rfl =
      spMap (WeierstrassTangent.dualMap (placeMap v)) ≫ (integralVector W).left ∧
    0 < Real.pi * (Weierstrass.latticeForm (lattice W hΔ v)
      ((coordinateChange W hΔ v).u : ℂ) ((coordinateChange W hΔ v).u : ℂ)).re ∧
    Real.pi * (Weierstrass.latticeForm (lattice W hΔ v)
      ((coordinateChange W hΔ v).u : ℂ) ((coordinateChange W hΔ v).u : ℂ)).re =
        placeProfile W hΔ v ∧
    -Real.log (Real.pi * (Weierstrass.latticeForm (lattice W hΔ v)
      ((coordinateChange W hΔ v).u : ℂ) ((coordinateChange W hΔ v).u : ℂ)).re) =
        PeriodArithmetic.latticeLogPeriod (lattice W hΔ v) :=
  ⟨placeHolUnif_isAH W hΔ v, placeHolUnif_integral_tangent W hΔ v,
    integralVector_place_baseChange W v, integral_direction_length_pos _ _,
    automorphy_tangent_eq_placeProfile W hΔ v, neg_log_automorphy_tangent W hΔ v⟩

end RHLean.Geometry.NativeCM.AllPlaceTangentPeriod
