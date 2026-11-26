import RHLean.Geometry.NativeCMWeierstrassGraphGroup

/-!
# Actual multiplication and torsion schemes on the constructed graph

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/SplitTori/SplitTorusAff.lean`,
only the final three definitions. The source archive states no license;
attribution is retained without assigning one.

The torsion scheme is the literal pullback of multiplication and the
identity section. The first projection is its actual scheme morphism.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

variable {S : Scheme.{0}}

def mulN (G : Over S) [GrpObj G] : ℕ → (G ⟶ G)
  | 0 => toUnit G ≫ η
  | n + 1 => lift (mulN G n) (𝟙 G) ≫ μ

def torsion (G : Over S) [GrpObj G] (n : ℕ) : Over S :=
  pullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)

def torsion.ι (G : Over S) [GrpObj G] (n : ℕ) : torsion G n ⟶ G :=
  pullback.fst _ _

end RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

end
