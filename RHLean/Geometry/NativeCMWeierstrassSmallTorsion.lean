import RHLean.Geometry.NativeCMWeierstrassFiniteClosedPoints

/-!
# Explicit small torsion and the elliptic geometric-kernel supplier

The actual Weierstrass equation supplies a nonzero point of order dividing
2 when 2 is nonzero, and one of order dividing 3 when 3 is nonzero. The
points are constructed from roots of the actual division polynomials.
Consequently a closed subgroup without the corresponding small torsion
is a proper closed subset, whose points are finite by the preceding
coordinate-norm argument.

This is a native elliptic replacement for the general abelian-subgroup
input of the source declaration
`src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueHomExtensionSemiAbelianDvr.lean`,
Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.
The source archive states no license; attribution is retained without
assigning one. The finite-subgroup conclusion is proved here, rather
than supplied as an extension hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial MonoidalCategory
open scoped Classical CategoryTheory.MonObj

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

variable {k : Type} [Field k] [IsAlgClosed k]
  (W : _root_.WeierstrassCurve k) [W.IsElliptic]

/-- The cubic two-torsion polynomial supplies an actual nonzero point. -/
theorem exists_nonzero_two_torsion (h2 : (2 : k) ≠ 0) :
    ∃ P : W.toAffine.Point, P ≠ 0 ∧ 2 • P = 0 := by
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by ring]
    exact mul_ne_zero h2 h2
  obtain ⟨x, hx⟩ := Weierstrass.exists_root_cubic h4 W.b₂ (2 * W.b₄) W.b₆
  have hx' : W.twoTorsionPolynomial.toPoly.IsRoot x := by
    rw [IsRoot.def, _root_.WeierstrassCurve.eval_toPoly_twoTorsionPolynomial]
    exact hx
  obtain ⟨y, hy, hP⟩ :=
    (_root_.WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_iff
      (W := W.toAffine) ⟨h2⟩ W.isUnit_Δ.ne_zero x).mp hx'
  exact ⟨.some x y hy, _root_.WeierstrassCurve.Affine.Point.some_ne_zero hy,
    by rw [two_nsmul]; exact hP⟩

/-- The quartic three-division polynomial supplies an actual nonzero point. -/
theorem exists_nonzero_three_torsion (h3 : (3 : k) ≠ 0) :
    ∃ P : W.toAffine.Point, P ≠ 0 ∧ 3 • P = 0 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root W.Ψ₃
    (degree_ne_of_natDegree_ne (W.natDegree_Ψ₃_pos h3).ne')
  obtain ⟨y, hy⟩ := Weierstrass.exists_equation W x
  have hn : W.toAffine.Nonsingular x y :=
    _root_.WeierstrassCurve.Affine.equation_iff_nonsingular.mp hy
  exact ⟨.some x y hn, _root_.WeierstrassCurve.Affine.Point.some_ne_zero hn,
    (Weierstrass.three_nsmul_eq_zero_iff hn).mpr hx⟩

/-- The construction chooses only 2 or 3; no general torsion-existence
or cardinality theorem is assumed. -/
theorem exists_nonzero_small_torsion (n : ℕ) (hn : n = 2 ∨ n = 3)
    (hnk : (n : k) ≠ 0) : ∃ P : W.toAffine.Point, P ≠ 0 ∧ n • P = 0 := by
  rcases hn with rfl | rfl
  · exact exists_nonzero_two_torsion W hnk
  · exact exists_nonzero_three_torsion W hnk

/-- The same explicit point belongs to the actual represented group. -/
theorem exists_nontrivial_small_torsion_schemePoint (n : ℕ) (hn : n = 2 ∨ n = 3)
    (hnk : (n : k) ≠ 0) :
    ∃ P : 𝟙_ (Over (Spec (.of k))) ⟶ schemeOver W, P ≠ 1 ∧ P ^ n = 1 := by
  obtain ⟨P, hP, hnP⟩ := exists_nonzero_small_torsion (W.baseChange k) n hn hnk
  let e := (affinePointMulEquiv W k).trans (selfSpecPointMulEquiv W)
  refine ⟨e (Multiplicative.ofAdd P), ?_, ?_⟩
  · intro h
    apply hP
    have he := e.injective (h.trans e.map_one.symm)
    exact congrArg Multiplicative.toAdd he
  · rw [← map_pow]
    change e (Multiplicative.ofAdd (n • P)) = 1
    rw [hnP]
    exact e.map_one

/-- A closed subgroup without the selected invertible small torsion is
finite on the actual elliptic scheme, in every characteristic. -/
theorem finite_closed_subgroup_of_no_small_torsion
    (n : ℕ) (hn : n = 2 ∨ n = 3) (hnk : (n : k) ≠ 0)
    (C : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ schemeOver W)) (Z : Set (scheme W))
    (hZ : IsClosed Z) (hC : ∀ x, x ∈ C ↔ Set.range x.left ⊆ Z)
    (htor : ∀ x ∈ C, x ^ n = 1 → x = 1) : Finite C := by
  have hne : Z ≠ Set.univ := by
    intro he
    obtain ⟨P, hP, hnP⟩ := exists_nontrivial_small_torsion_schemePoint W n hn hnk
    exact hP (htor P ((hC P).mpr (by rw [he]; exact Set.subset_univ _)) hnP)
  have hf : (C : Set (𝟙_ (Over (Spec (.of k))) ⟶ schemeOver W)).Finite :=
    (finite_unitPoints_of_proper_closed W Z hZ hne).subset fun x hx => (hC x).mp hx
  exact hf.to_subtype

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

end
