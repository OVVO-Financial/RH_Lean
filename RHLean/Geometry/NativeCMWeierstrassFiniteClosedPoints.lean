import RHLean.Geometry.NativeCMWeierstrassFiniteModel
import RHLean.Geometry.NativeCMWeierstrassReducedGroup

/-!
# Proper closed subsets of the actual elliptic scheme have finitely many points

This is a native elliptic specialization of the geometric-kernel input
in the good-reduction extension argument. A nonzero element of the
actual affine coordinate ring has nonzero polynomial norm. Every affine
point at which that element vanishes is a root of that norm polynomial.
The proved dense affine chart supplies such an element for every proper
closed subset of the actual projective scheme.

The norm and rank-two coordinate-ring basis are Mathlib's actual
`WeierstrassCurve.Affine.CoordinateRing` constructions. The finite-root
argument is the reconstructed `finite_points_of_root` in
`NativeCMWeierstrassFiniteModel`. No dimension or subgroup-finiteness
hypothesis is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial MonoidalCategory MonObj
open scoped Classical Polynomial.Bivariate CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

variable {k : Type} [Field k] (W : _root_.WeierstrassCurve k)

/-- Evaluation of the original rank-two coordinate-ring coordinates. -/
theorem affineEval_smul_basis (p q : k[X]) (x y : k)
    (h : (W.map (RingHom.id k)).toAffine.Equation x y) :
    affineEval W (RingHom.id k) x y h
      (p • (1 : W.toAffine.CoordinateRing) +
        q • _root_.WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Y) =
      p.eval x + q.eval x * y := by
  simp [_root_.WeierstrassCurve.Affine.CoordinateRing.smul, affineEval]

/-- Vanishing of the actual coordinate-ring element forces vanishing of
its actual polynomial norm. -/
theorem affineEval_norm_eq_zero (f : W.toAffine.CoordinateRing) (x y : k)
    (h : (W.map (RingHom.id k)).toAffine.Equation x y)
    (hf : affineEval W (RingHom.id k) x y h f = 0) :
    (Algebra.norm k[X] f).eval x = 0 := by
  obtain ⟨p, q, rfl⟩ :=
    _root_.WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq f
  rw [affineEval_smul_basis] at hf
  rw [_root_.WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
  simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X]
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y =
      x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    simpa only [_root_.WeierstrassCurve.map_id] using!
      (_root_.WeierstrassCurve.Affine.equation_iff ..).mp h
  linear_combination (p.eval x - q.eval x * y - q.eval x * (W.a₁ * x + W.a₃)) * hf +
    (q.eval x) ^ 2 * hE

/-- A nonzero actual regular function has only finitely many affine
zeros, including the possible projective origin in the chosen point set. -/
theorem finite_points_of_affine_vanishing {f : W.toAffine.CoordinateRing} (hf : f ≠ 0)
    {s : Set (W.baseChange k).toAffine.Point}
    (hs : ∀ x y h, _root_.WeierstrassCurve.Affine.Point.some x y h ∈ s →
      affineEval W (RingHom.id k) x y h.left f = 0) : s.Finite := by
  have hn : Algebra.norm k[X] f ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis
      (_root_.WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)).mpr hf
  exact Weierstrass.finite_points_of_root hn fun x y h hp =>
    affineEval_norm_eq_zero W f x y h.left (hs x y h hp)

/-- The actual dense affine chart detects that a closed subset is proper. -/
theorem exists_nonzero_vanishing_of_proper_closed (Z : Set (scheme W))
    (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    ∃ f : W.toAffine.CoordinateRing, f ≠ 0 ∧
      ∀ x y (h : (W.baseChange k).toAffine.Nonsingular x y),
        Set.range (ofAffinePoint W k (.some x y h)).left ⊆ Z →
          affineEval W (RingHom.id k) x y h.left f = 0 := by
  let S : Set (PrimeSpectrum W.toAffine.CoordinateRing) := (chartZ W) ⁻¹' Z
  have hS : IsClosed S := hZ.preimage (chartZ W).continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal S).mp hS
  have hI0 : I ≠ ⊥ := by
    intro hi
    have hr : Set.range (chartZ W) ⊆ Z := by
      rintro _ ⟨p, rfl⟩
      change p ∈ S
      rw [hI, hi, PrimeSpectrum.zeroLocus_bot]
      exact Set.mem_univ p
    have hc : closure (Set.range (chartZ W)) ⊆ Z := hZ.closure_subset_iff.mpr hr
    exact hne (Set.eq_univ_of_forall fun z => hc (denseRange_chartZ W z))
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  refine ⟨f, hf0, fun x y h hp => ?_⟩
  let q : Spec (.of k) := IsLocalRing.closedPoint k
  have hm : PrimeSpectrum.comap (affineEval W (RingHom.id k) x y h.left) q ∈ S := by
    change (Spec.map (CommRingCat.ofHom (affineEval W (RingHom.id k) x y h.left)) ≫
      chartZ W) q ∈ Z
    have hmap : Spec.map (CommRingCat.ofHom (affineEval W (RingHom.id k) x y h.left)) ≫
        chartZ W = (ofAffinePoint W k (.some x y h)).left :=
      SpecMap_affineEval_chartZ W (RingHom.id k) x y h.left
    have hpoint : (ofAffinePoint W k (.some x y h)).left q ∈ Z := hp ⟨q, rfl⟩
    exact (congrArg (fun φ : Spec (.of k) ⟶ scheme W => φ q ∈ Z) hmap).mpr hpoint
  rw [hI] at hm
  have he : affineEval W (RingHom.id k) x y h.left f ∈ q.asIdeal := hm hf
  rw [Ideal.eq_bot_of_prime q.asIdeal] at he
  exact Ideal.mem_bot.mp he

/-- The proper closed subset has finitely many actual elliptic-curve
points over the given field. -/
theorem finite_affinePoints_of_proper_closed (Z : Set (scheme W))
    (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    {P : (W.baseChange k).toAffine.Point |
      Set.range (ofAffinePoint W k P).left ⊆ Z}.Finite := by
  obtain ⟨f, hf, hvan⟩ := exists_nonzero_vanishing_of_proper_closed W Z hZ hne
  exact finite_points_of_affine_vanishing W hf hvan

/-- The same statement uses the represented scheme points, via the
already proved equivalence with the actual affine point group. -/
theorem finite_schemePoints_of_proper_closed [W.IsElliptic] (Z : Set (scheme W))
    (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    {P : specOver k k ⟶ schemeOver W | Set.range P.left ⊆ Z}.Finite := by
  refine ((finite_affinePoints_of_proper_closed W Z hZ hne).image (ofAffinePoint W k)).subset ?_
  intro p hp
  obtain ⟨P, rfl⟩ := (ofAffinePoint_bijective W k).surjective p
  exact ⟨P, hp, rfl⟩

private theorem selfSpec_hom : (specOver k k).hom = 𝟙 (Spec (.of k)) := Spec.map_id _

private def unitToSelfSpec : 𝟙_ (Over (Spec (.of k))) ⟶ specOver k k :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans selfSpec_hom)

private def pointOnUnit {G : Over (Spec (.of k))} (P : specOver k k ⟶ G) :
    𝟙_ (Over (Spec (.of k))) ⟶ G :=
  Over.homMk P.left ((Over.w P).trans selfSpec_hom)

private theorem pointOnUnit_eq_comp {G : Over (Spec (.of k))} (P : specOver k k ⟶ G) :
    pointOnUnit P = unitToSelfSpec ≫ P :=
  Over.OverMorphism.ext (Category.id_comp P.left).symm

private def selfSpecMulEquiv (G : Over (Spec (.of k))) [MonObj G] :
    (specOver k k ⟶ G) ≃* (𝟙_ (Over (Spec (.of k))) ⟶ G) where
  toFun := pointOnUnit
  invFun P := Over.homMk P.left ((Over.w P).trans selfSpec_hom.symm)
  left_inv P := Over.OverMorphism.ext rfl
  right_inv P := Over.OverMorphism.ext rfl
  map_mul' P Q := by simp only [pointOnUnit_eq_comp, MonObj.comp_mul]

/-- Changing the self-spectrum presentation to the actual tensor unit
keeps the underlying scheme point unchanged. -/
def selfSpecPointMulEquiv [W.IsElliptic] :
    (specOver k k ⟶ schemeOver W) ≃* (𝟙_ (Over (Spec (.of k))) ⟶ schemeOver W) :=
  selfSpecMulEquiv (schemeOver W)

/-- Finiteness for the unit-valued points used by the geometric kernel
of a group-scheme morphism. -/
theorem finite_unitPoints_of_proper_closed [W.IsElliptic] (Z : Set (scheme W))
    (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    {P : 𝟙_ (Over (Spec (.of k))) ⟶ schemeOver W | Set.range P.left ⊆ Z}.Finite := by
  refine ((finite_schemePoints_of_proper_closed W Z hZ hne).image
    (selfSpecPointMulEquiv W)).subset ?_
  intro p hp
  refine ⟨(selfSpecPointMulEquiv W).symm p, hp, ?_⟩
  exact (selfSpecPointMulEquiv W).apply_symm_apply p

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

end
