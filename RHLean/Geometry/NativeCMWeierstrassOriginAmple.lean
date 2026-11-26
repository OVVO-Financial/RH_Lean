import RHLean.Geometry.NativeCMWeierstrassOriginCube

/-!
# Relative ampleness of the actual origin line bundle

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/NonzeroLocus.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsUniqueEqConstMulOriginSec.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean`

The original source definition asks for a positive tensor power whose sections
cover every affine base restriction, have affine nonzero loci, and whose ratios
generate the actual section algebras. All those conditions are constructed from
the three projective coordinate sections of the cubed origin bundle.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

section Ampleness

variable {S : Scheme.{0}} (A : Over S)

def powOver (L : LB A.left) (U : S.Opens) (N : ℕ) : LB (A.hom ⁻¹ᵁ U).toScheme :=
  LB.LinComb L (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)

def RelAmple (L : LB A.left) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (powOver A L U N),
      (⨆ i, nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
        ∃ r : Fin (M + 1) → Γ((A.hom ⁻¹ᵁ U).toScheme, nonzeroLocus (s i)),
          (∀ j k, ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_right :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ (powOver A L U N).U k)).op).hom
                ((s j).f k) =
            ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_left :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ nonzeroLocus (s i))).op).hom (r j) *
            ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_right :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ (powOver A L U N).U k)).op).hom
                ((s i).f k)) ∧
          Function.Surjective (MvPolynomial.eval₂Hom
            ((A.hom ∣_ U).appLE ⊤ (nonzeroLocus (s i)) le_top).hom r)

end Ampleness

open LBGerm

namespace WeierstrassCurve

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem eval₂Hom_ratio_surjective (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (constOn W (coordOpen W i)) (ratio W i)) := by
  intro a
  obtain ⟨a, rfl⟩ := (awayFnEquiv W i).surjective a
  obtain ⟨n, b, hb, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading W) (coord_mem W i) a
  rw [← evalHom_awayCoord]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨p, ?_⟩
  rw [evalHom_mk]
  have := MvPolynomial.eval₂_comp_left (awayFnEquiv W i).toRingHom (awayConst W i)
    (awayCoord W i) p
  refine Eq.trans ?_ this.symm
  rw [MvPolynomial.coe_eval₂Hom]
  congr 1
  · exact RingHom.ext fun r => (awayFnEquiv_awayConst W i r).symm
  · exact funext fun j => (awayFnEquiv_awayCoord W i j).symm

theorem relAmple_originLB : RelAmple (schemeOver W) (originLB W) := by
  intro U hU
  let ι := (toSpec W ⁻¹ᵁ U).ι
  have H : IsPullback ι (toSpec W ∣_ U) (toSpec W) U.ι := (isPullback_morphismRestrict _ U).flip
  have : IsAffine U := hU
  have : IsAffineHom ι := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  let s : Fin 3 → (powOver (schemeOver W) (originLB W) U 3).Sec := fun j =>
    finPowSec (originLB_isLB W) (n := 2) (coordSec W j) ι
  have loc : ∀ j, nonzeroLocus (s j) = ι ⁻¹ᵁ coordOpen W j := fun j =>
    (nonzeroLocus_finPowSec _ _ _).trans (by rw [nonzeroLocus_coordSec])
  refine ⟨3, by norm_num, 2, s, top_le_iff.1 fun y _ => ?_, fun i => ⟨?_,
    fun j => (ι.appLE _ _ (loc i).le).hom (ratio W i j), fun j k => fn_ext fun y hy => ?_, ?_⟩⟩
  · rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ (ι y)) with h | h
    · exact Opens.mem_iSup.2 ⟨1, (loc 1).ge h⟩
    · exact Opens.mem_iSup.2 ⟨2, (loc 2).ge h⟩
  · rw [loc]
    exact (isAffineOpen_coordOpen W i).preimage ι
  · obtain ⟨v, hv⟩ := exists_gs_finPowSec (originLB_isLB W) (n := 2) ι y k hy.2
    have e := gs_coordFn ι y j (k := k 0) ((loc i).le hy.1) (Set.mem_iInter.1 hy.2 0)
    have e₁ := hv (coordSec W j)
    have e₂ := hv (coordSec W i)
    rw [powSecFn_coordSec] at e₁ e₂
    refine (gs_res _ y _ hy _).trans (e₁.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      ((congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans ((gs_appLE ι _ _ _ (𝟙 _) y hy.1 _).trans
        (by rw [Category.id_comp]))) ((gs_res _ y _ hy _).trans e₂)).trans ?_))))
    rw [e, mul_left_comm]
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := coordOpen W i) le_top le_top
      (UY := nonzeroLocus (s i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _)
        (isAffineOpen_coordOpen W i))
    exact eval₂Hom_surjective_of_isPushout po (Scheme.ΓSpecIso (.of R)).inv.hom (ratio W i)
      (eval₂Hom_ratio_surjective W i)

end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory
