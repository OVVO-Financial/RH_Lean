import RHLean.Geometry.NativeCMLineBundleTransport
import RHLean.Geometry.NativeCMWeierstrassOriginSymmetry

/-!
# Trivial translation kernel from the actual origin-section criterion

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/NonzeroLocus.lean`
- `src/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsGenTranslDiffComp.lean`
- `src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/KernelPolarisationTrivialOfSectionsVanishZero.lean`

The kernel condition is tested over arbitrary rings and locally trivial
translation differences. All transport and cancellation use genuine scheme
sections. The universal zero-subscheme and base-change section conditions
remain explicit here and are discharged for the origin bundle separately.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

open MonoidalCategory CartesianMonoidalCategory MonObj LBGerm

attribute [local instance] Over.cartesianMonoidalCategory

section Definitions

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def translDiff (L : LB A.left) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] ![1, -1]

def KTriv (L : LB A.left) : Prop :=
  ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (x : Over.mk t ⟶ A),
    (∀ p : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, p ∈ V ∧
      ∃ c : LB.Gen ((translDiff A L x).pull ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι), c.IsGen) →
    x = toUnit _ ≫ η[A]

end Definitions

theorem exists_isGen_linComb_of_pull {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (f : Z ⟶ Y) (c : LB.Gen ((LB.LinComb L φ ε).pull f))
    (hc : c.IsGen) : ∃ d : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), d.IsGen := by
  have hle : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => f) (fun _ => j) :=
    fun j _ hy => Set.mem_iInter.2 fun _ => LB.wchart_comp_le L f φ j hy
  refine ⟨⟨fun j => res (hle j) (LB.ts c (fun _ => j))⟩, ?_⟩
  refine (LB.isGen_iff L _).2 fun i j => ?_
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff (LB.LinComb L φ ε) c).1 hc (fun _ => i) (fun _ => j))
  have e := LB.lcg_pull (LB.LinComb L φ ε) f (fun _ => i) (fun _ => j)
  rw [LB.lcg_comp]
  refine (LB.res_res _ _ _).trans (((LB.res_res _ _ _).symm.trans key).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · exact (congrArg _ e).trans (LB.res_res _ _ _)
  · exact (LB.res_res _ _ _).trans (LB.res_res _ _ _).symm

theorem exists_isGen_translDiff_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T T' : Over S} (x : T ⟶ A) (g : T' ⟶ T) (V : T.left.Opens)
    (hg : ∀ q, g.left q ∈ V)
    (c : LB.Gen ((translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) :
    ∃ d : LB.Gen (translDiff A L (g ≫ x)), d.IsGen := by
  obtain ⟨d, hd⟩ := exists_isGen_linComb_of_pull L _ _ _ c hc
  have hr : Set.range (g ▷ A).left ⊆ Set.range ((fst T A).left ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((g ▷ A).left ≫ (fst T A).left) y ∈ V
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    exact hg _
  have hl := IsOpenImmersion.lift_fac ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr
  have h4 : ∃ w : LB.Gen (LB.LinComb L _ _), w.IsGen :=
    ⟨_, LB.isGen_pullGen L _ _ d hd (IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr)⟩
  have h3 : (fun k : Fin 2 => IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr ≫
      ((fst T A).left ⁻¹ᵁ V).ι ≫
        ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k) =
      ![(lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext k
    rw [← Category.assoc, hl]
    fin_cases k
    · change (g ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (g ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

theorem appLE_top_eq_zero_iff_gs {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(X, U)) :
    (r.appLE U ⊤ h).hom a = 0 ↔ ∀ z, gs r z U a = 0 := by
  have e : ∀ z, gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom a) = gs r z U a := fun z =>
    (gs_appLE r U ⊤ h (𝟙 Z) z trivial a).trans (by rw [Category.id_comp])
  have e0 : ∀ z : Z, gs (𝟙 Z) z ⊤ 0 = 0 := fun z => by
    rw [gs_eq (𝟙 Z) z ⊤ trivial, map_zero, map_zero]
  exact ⟨fun H z => by rw [← e z, H, e0], fun H => fn_ext fun z _ => by rw [e z, H z, e0]⟩

theorem exists_pull_sec_sval {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (F : Y ⟶ X) :
    ∃ s : (L.pull F).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s r z J = gs (r ≫ F) z (L.U (J (r ≫ F))) (θ.f (J (r ≫ F))) := by
  have le : ∀ J, (L.pull F).U J ≤ F ⁻¹ᵁ L.U (J PUnit.unit) := fun J => LB.wchart_le L _ J PUnit.unit
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) z J, r z ∈ (L.pull F).U J →
      gs r z _ ((F.appLE _ _ (le J)).hom (θ.f _)) = gs (r ≫ F) z _ (θ.f (J PUnit.unit)) :=
    fun Z r z J h => gs_appLE F _ _ (le J) r z h _
  refine ⟨⟨fun J => (F.appLE _ _ (le J)).hom (θ.f _), fun J J' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ev Z r z _ (hJ.mem _ r)⟩
  have hm : (𝟙 Y ≫ F) y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gs (𝟙 Y ≫ F) y _) (θ.compat (J PUnit.unit) (J' PUnit.unit))
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
  refine ((gs_res (𝟙 Y) y _ hy _).trans ((ev _ _ y J hy.1).trans e)).trans
    (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y J J' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (ev _ _ y J' hy.2)))).symm)
  simp

theorem exists_sec_of_gen_diff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (θ : L.Sec) (ψ φ : Y ⟶ X)
    (d : LB.Gen (LB.LinComb L (K := Fin 2) ![ψ, φ] ![1, -1])) (hd : d.IsGen) :
    ∃ s : (L.pull φ).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s r z J = 0 → gs (r ≫ ψ) z (L.U (J (r ≫ ψ))) (θ.f (J (r ≫ ψ))) = 0 := by
  obtain ⟨s₀, hs₀⟩ := exists_pull_sec_sval θ ψ
  have hF : FormEq (Sum.elim (fun _ : PUnit => 𝟙 Y ≫ ψ) ![ψ, φ])
      (Sum.elim (fun _ => 1) (fun k => -(![1, -1] : Fin 2 → ℤ) k)) (fun _ : PUnit => φ) (fun _ => 1) := by
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two]
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec s₀ (𝟙 Y) (LB.invGen L _ _ d) (LB.isGen_invGen L _ _ d hd))
  refine ⟨s, fun Z r z J hJ H => ?_⟩
  rw [hs Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, Category.comp_id, hs₀ Z r z J hJ] at H
  exact (Units.mul_left_eq_zero _).1 H

theorem kTriv_of_sections_vanish_on_zero : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ identitySection A) → (∀ (R' : Type) [CommRing R'] (f : Sp R' ⟶ S) (Y : Scheme.{0}) (φ : Y ⟶ A.left) (q : Y ⟶ Sp R'), IsPullback φ q A.hom f → ∀ (s : (L.pull φ).Sec) (T : Scheme.{0}) (t : T ⟶ Y) (j : (L.pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ (L.pull φ).U j), t ≫ φ = t ≫ φ ≫ A.hom ≫ identitySection A → (t.appLE ((L.pull φ).U j) ⊤ h).hom (s.f j) = 0) → KTriv A L := by
  intro S A _ L θ hL hθ hs R _ t x hx
  have one : ∀ (T : Over S) (y : T ⟶ A), y.left ≫ A.hom ≫ identitySection A = (1 : T ⟶ A).left := fun T y => by
    rw [← Category.assoc, Over.w y]; rfl
  have H' : ∀ (R' : CommRingCat.{0}) (t' : Spec R' ⟶ S) (y : Over.mk t' ⟶ A) (i i₀ : L.ι),
      ⊤ ≤ y.left ⁻¹ᵁ L.U i → ⊤ ≤ (1 : Over.mk t' ⟶ A).left ⁻¹ᵁ L.U i₀ →
      (∃ c : LB.Gen (translDiff A L y), c.IsGen) → y = 1 := by
    rintro R' t' y i i₀ hi hi₀ ⟨c, hc⟩
    by_contra hne
    have hne' : y.left ≠ (1 : Over.mk t' ⟶ A).left := fun e => hne (Over.OverMorphism.ext e)
    obtain ⟨s, hs'⟩ := exists_sec_of_gen_diff hL θ _ _ c hc
    let r : Over.mk t' ⟶ Over.mk t' ⊗ A := lift (𝟙 _) 1
    have r₁ : r.left ≫ (lift (fst _ A ≫ y) (snd _ A) ≫ μ[A]).left = y.left := by
      rw [← Over.comp_left, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]
      exact congrArg (fun q : Over.mk t' ⟶ A => q.left) (_root_.mul_one y)
    have r₂ : r.left ≫ (snd _ A).left = (1 : Over.mk t' ⟶ A).left := by
      rw [← Over.comp_left, lift_snd]
    have hj : ⊤ ≤ r.left ⁻¹ᵁ (L.pull (snd (Over.mk t') A).left).U (fun _ => i₀) := fun z _ =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q z ∈ L.U i₀) r₂).mpr (hi₀ trivial)
    have hz := hs R' t' _ (snd (Over.mk t') A).left (fst (Over.mk t') A).left
      (IsPullback.of_hasPullback t' A.hom).flip s _ r.left (fun _ => i₀) hj
      (by rw [← Category.assoc, r₂, one])
    refine hne' (((hθ _ y.left i hi).1 ((appLE_top_eq_zero_iff_gs _ _ hi _).2 fun z => ?_)).trans (one _ y))
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Bool)
      (fun b => cond b y.left (1 : Over.mk t' ⟶ A).left) (fun b => cond b i i₀) (by
        rintro (_ | _) (_ | _) e
        exacts [rfl, absurd e.symm hne', absurd e hne', rfl]) (by
        rintro (_ | _)
        exacts [hi₀ trivial, hi trivial])
    have := hs' _ r.left z J hJ ((sval_of s r.left z J (fun _ => i₀) (fun _ => by rw [r₂]; exact e false)).trans
      ((appLE_top_eq_zero_iff_gs _ _ hj _).1 hz z))
    rw [r₁] at this
    obtain rfl : J y.left = i := e true
    exact this
  change x = 1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hp, c, hc⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((1 : Over.mk t ⟶ A).left p)
  obtain ⟨U, hU, hpU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (U := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ A).left ⁻¹ᵁ L.U i₀) (x := p) ⟨⟨hp, hi⟩, hi₀⟩
  refine ⟨U, hpU, ?_⟩
  let g : Over.mk (hU.fromSpec ≫ t) ⟶ Over.mk t := Over.homMk hU.fromSpec rfl
  have hq := fun q => hUV (hU.range_fromSpec.le ⟨q, rfl⟩)
  have h1 : g ≫ x = g ≫ 1 := by
    rw [MonObj.comp_one]
    refine H' _ _ _ i i₀ (fun q _ => (hq q).1.2) ?_ (exists_isGen_translDiff_comp A L x g V
      (fun q => (hq q).1.1) c hc)
    rw [← MonObj.comp_one g]
    exact fun q _ => (hq q).2
  have h2 : hU.fromSpec ≫ x.left = hU.fromSpec ≫ (1 : Over.mk t ⟶ A).left :=
    congrArg (·.left) h1
  rw [IsAffineOpen.fromSpec, Category.assoc, Category.assoc, cancel_epi] at h2
  exact h2

end RHLean.Geometry.NativeCM.SchemeTheory
