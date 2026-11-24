import RHLean.Geometry.NativeCMWeierstrassMultiplicationEtale

/-!
# The actual generic graph kernel has no invertible torsion

The equalizer inside the actual etale torsion scheme is open and flat.
Its generic fibre is trivial because the graph projection is generically
an isomorphism. The proved generic-fibre faithfulness therefore makes it
trivial over the valuation ring itself.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean`.
Only the open-equalizer declaration is reconstructed from
`src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean`.
The source archive states no license; attribution is retained without
assigning one. The final theorem supplies etaleness from the actual flat
group schemes, rather than assuming a torsion or extension property.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

universe u

set_option backward.isDefEq.respectTransparency false in

theorem isOpenImmersion_equalizer_ι_left_of_unramified {S : Scheme.{u}} {T X : Over S}
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] (a b : T ⟶ X) :
    IsOpenImmersion (equalizer.ι a b).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod a b).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback X X).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal X.hom))
  ext1 <;> simp [← Over.comp_left]

namespace KernelNoTorsion

theorem comp_mulN {S : Scheme.{0}} {Y G : Over S} [GrpObj G] (x : Y ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, mulN, Hom.one_def, comp_toUnit_assoc]
  | succ n ih => rw [pow_succ, mulN, Hom.mul_def, comp_lift_assoc, ih, Category.comp_id]

noncomputable def torsionLift {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : Y ⟶ torsion G n :=
  pullback.lift x (toUnit Y) (by rw [comp_mulN, hx, Hom.one_def])

theorem torsionLift_ι {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : torsionLift x hx ≫ torsion.ι G n = x :=
  pullback.lift_fst _ _ _

theorem torsion_hom_ext {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ}
    {a b : Y ⟶ torsion G n} (h : a ≫ torsion.ι G n = b ≫ torsion.ι G n) : a = b :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem torsionι_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 := by
  rw [← comp_mulN, Hom.one_def]
  refine (pullback.condition).trans ?_
  congr 1
  exact toUnit_unique _ _

theorem eq_one_of_pow_eq_one_of_comp_eq_one :
    ∀ (T K : Type) [CommRing T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] [IsCommMonObj Ga] [IsCommMonObj G] (p : Ga ⟶ G) (n : ℕ), IsMonHom p → IsSeparated Ga.hom → Etale (torsion Ga n).hom → Etale (torsion G n).hom → IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → ∀ (Y : Over (Sp T)) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ p = 1 → x = 1 := by
  intro T K _ _ _ _ _ Ga G _ _ _ _ p n hp hsep hA hB hiso Y x hx hxp
  have hq : (torsion.ι Ga n ≫ p) ^ n = 1 := by
    rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp]
  let q : torsion Ga n ⟶ torsion G n := torsionLift _ hq
  let e : torsion Ga n ⟶ torsion G n := torsionLift 1 (one_pow n)
  have hopen := isOpenImmersion_equalizer_ι_left_of_unramified q e
  have hflat : Flat (equalizer q e).hom := by
    rw [← Over.w (equalizer.ι q e)]
    infer_instance
  have h1 : (equalizer.ι q e ≫ torsion.ι Ga n) ≫ p = (1 : equalizer q e ⟶ Ga) ≫ p := by
    have := equalizer.condition q e =≫ torsion.ι G n
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one] at this
    rw [Category.assoc, this, MonObj.one_comp]
  have h2 : equalizer.ι q e ≫ torsion.ι Ga n = 1 := by
    apply fractionField_map_injective T K
    rw [← cancel_mono ((Over.pullback (spMap (algebraMap T K))).map p), ← Functor.map_comp,
      ← Functor.map_comp, h1]
  have h3 : torsionLift x hx ≫ q = torsionLift x hx ≫ e := by
    apply torsion_hom_ext
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one,
      ← Category.assoc, torsionLift_ι, hxp]
  rw [← torsionLift_ι x hx, ← equalizer.lift_ι (torsionLift x hx) h3, Category.assoc, h2,
    MonObj.comp_one]


end KernelNoTorsion

/-- The etale-torsion hypotheses are supplied by actual flatness and
finite type over the discrete valuation ring. -/
theorem graph_kernel_no_torsion (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (Ga G : Over (Sp R)) [GrpObj Ga] [GrpObj G] [IsCommMonObj Ga] [IsCommMonObj G]
    [Flat Ga.hom] [Flat G.hom] [LocallyOfFiniteType Ga.hom] [LocallyOfFiniteType G.hom]
    [IsSeparated Ga.hom] (p : Ga ⟶ G) [IsMonHom p]
    [IsIso ((Over.pullback (spMap (algebraMap R K))).map p)]
    (n : ℕ) (hn : IsUnit (n : R)) (Y : Over (Sp R)) (x : Y ⟶ Ga)
    (hx : x ^ n = 1) (hxp : x ≫ p = 1) : x = 1 :=
  KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one R K Ga G p n inferInstance
    inferInstance (etale_mulN_torsion_dvr R Ga n hn inferInstance inferInstance).2
    (etale_mulN_torsion_dvr R G n hn inferInstance inferInstance).2 inferInstance Y x hx hxp

/-- One of the two explicit elliptic torsion orders is a unit at every
local base. The order remains part of the witness. -/
theorem exists_small_isUnit_of_isLocalRing (R : Type) [CommRing R] [IsLocalRing R] :
    ∃ n : ℕ, (n = 2 ∨ n = 3) ∧ IsUnit (n : R) := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : R) with h | h
  · exact ⟨3, Or.inr rfl, h⟩
  · refine ⟨2, Or.inl rfl, ?_⟩
    rw [show (1 - 3 : R) = -2 by ring] at h
    exact (IsUnit.neg_iff _).mp h

end RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

end
