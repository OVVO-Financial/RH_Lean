import RHLean.Geometry.NativeCMLineBundleRegularSection

/-!
# Actual line-bundle isomorphism from the same regular zero subscheme

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUnitMul.lean`
- `src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsoLineBundleOfRegularPullbacksSameZeroScheme.lean`

Universal scheme-valued vanishing, including nonreduced test schemes, forces
local sections to differ by an actual unit. These units glue and satisfy the
transition law of the genuine bundle isomorphism. No reduced-point shortcut
or isomorphism premise is used. The source archive states no license;
attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open RHLean.Geometry.NativeCM.SchemeTheory

namespace RHLean.Geometry.NativeCM.SchemeTheory.SectionIso

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom a = _
  rw [← X.presheaf.map_comp]
  rfl

theorem top_le_preimage {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ V := by
  intro x _
  apply h
  have : hU.fromSpec (Spec.map φ x) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
  rw [hU.range_fromSpec] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
theorem appLE_spec {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) :
    (Spec.map φ ≫ hU.fromSpec).appLE V ⊤ (top_le_preimage hU h φ) =
      Y.presheaf.map (homOfLE h).op ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ V := by
    rw [← hU.fromSpec_preimage_self]
    exact fun x hx => h hx
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) hU.fromSpec V ⊤ ⊤ h1 le_top,
    Scheme.ΓSpecIso_inv_naturality]
  have e1 : hU.fromSpec.appLE V ⊤ h1 =
      Y.presheaf.map (homOfLE h).op ≫ (Scheme.ΓSpecIso Γ(Y, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_of_le V h, Category.assoc, Category.assoc,
      ← Functor.map_comp]
    congr 1
  have e2 : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  rw [e1, e2, Category.assoc]

theorem dvd_on_affine {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    (a b : Γ(Y, V))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 → (t.appLE V ⊤ h).hom b = 0) :
    resG Y h a ∣ resG Y h b := by
  let I : Ideal Γ(Y, U) := Ideal.span {resG Y h a}
  let φ : Γ(Y, U) ⟶ CommRingCat.of (Γ(Y, U) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have key := H _ _ (top_le_preimage hU h φ)
  rw [appLE_spec hU h φ] at key
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).commRingCatIsoToRingEquiv.symm.injective
  have ha : Ideal.Quotient.mk I (resG Y h a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hb := key (by
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom
      (Ideal.Quotient.mk I (resG Y h a)) = 0
    rw [ha]; exact map_zero _)
  have hb' : Ideal.Quotient.mk I (resG Y h b) = 0 :=
    hinj (hb.trans (map_zero _).symm)
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb')

theorem exists_unit_mul (Y : Scheme.{0}) (V : Y.Opens) (a b : Γ(Y, V))
    (ha : ∀ (V' : Y.Opens) (h : V' ≤ V), resG Y h a ∈ nonZeroDivisors Γ(Y, V'))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 ↔ (t.appLE V ⊤ h).hom b = 0) :
    ∃ c : Γ(Y, V)ˣ, b = (c : Γ(Y, V)) * a := by
  let J := {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}
  let W : J → Y.Opens := fun i => i.1
  have hW : ∀ i, W i ≤ V := fun i => i.2.2
  have hcov : ∀ y ∈ V, ∃ i, y ∈ W i := fun y hy => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    exact ⟨⟨U, hU, hUV⟩, hyU⟩
  have hc : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 (hcov y hy)
  have hloc : ∀ i, ∃ c : Γ(Y, W i), IsUnit c ∧ resG Y (hW i) b = c * resG Y (hW i) a := fun i => by
    obtain ⟨c, hc⟩ := dvd_on_affine i.2.1 (hW i) a b fun T t h => (H T t h).1
    obtain ⟨d, hd⟩ := dvd_on_affine i.2.1 (hW i) b a fun T t h => (H T t h).2
    refine ⟨c, ?_, hc.trans (mul_comm _ _)⟩
    have e : (c * d) * resG Y (hW i) a = 1 * resG Y (hW i) a := by
      rw [_root_.one_mul]
      conv_rhs => rw [hd, hc]
      ring
    exact IsUnit.of_mul_eq_one d ((mul_cancel_right_mem_nonZeroDivisors (ha _ (hW i))).1 e)
  choose u hu hub using hloc
  have hh : ∀ i j, resG Y (inf_le_left : W i ⊓ W j ≤ W i) (u i) = resG Y inf_le_right (u j) := by
    intro i j
    have e₁ := congrArg (resG Y (inf_le_left : W i ⊓ W j ≤ W i)) (hub i)
    have e₂ := congrArg (resG Y (inf_le_right : W i ⊓ W j ≤ W j)) (hub j)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact (mul_cancel_right_mem_nonZeroDivisors (ha _ (inf_le_left.trans (hW i)))).1
      (e₁.symm.trans e₂)
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc u hh
  have hs' : ∀ i, resG Y (hW i) (show Γ(Y, V) from s) = u i := hs
  have hunit : IsUnit (show Γ(Y, V) from s) :=
    Y.toRingedSpace.isUnit_of_isUnit_germ V _ fun y hy => by
      obtain ⟨i, hi⟩ := hcov y hy
      have h1 := (hu i).map (Y.presheaf.germ (W i) y hi).hom
      rw [← hs' i] at h1
      have h2 := Y.presheaf.germ_res_apply (homOfLE (hW i)) y hi (show Γ(Y, V) from s)
      exact h2 ▸ h1
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  apply Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
  intro i
  change resG Y (hW i) b = resG Y (hW i) ((show Γ(Y, V) from s) * a)
  rw [map_mul, hs', hub]

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((f.appLE U V h).hom a) = (f.appLE U W (h'.trans h)).hom a := by
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom a = _
  rw [Scheme.Hom.appLE_map]

theorem appLE_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : U ≤ U') (h'' : V ≤ f ⁻¹ᵁ U') (a : Γ(X, U')) :
    (f.appLE U V h).hom (resG X h' a) = (f.appLE U' V h'').hom a := by
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U V h).hom a = _
  rw [Scheme.Hom.map_appLE]

theorem appLE_appLE {X Y T : Scheme.{0}} (t : T ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ t ⁻¹ᵁ V) (h'' : ⊤ ≤ (t ≫ f) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (t.appLE V ⊤ h').hom ((f.appLE U V h).hom a) = ((t ≫ f).appLE U ⊤ h'').hom a := by
  change (f.appLE U V h ≫ t.appLE V ⊤ h').hom a = _
  rw [Scheme.Hom.appLE_comp_appLE]

theorem appLE_compat {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (f : Y ⟶ X) (i j : L.ι) {W : Y.Opens}
    (hi : W ≤ f ⁻¹ᵁ L.U i) (hj : W ≤ f ⁻¹ᵁ L.U j) (hij : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j)) :
    (f.appLE (L.U i) W hi).hom (θ.f i) =
      (res hij (pullU f (L.U i ⊓ L.U j) (L.g i j)) : Γ(Y, W)ˣ) * (f.appLE (L.U j) W hj).hom (θ.f j) := by
  have e := congrArg (f.appLE (L.U i ⊓ L.U j) W hij).hom (θ.compat i j)
  rw [map_mul] at e
  exact (appLE_resG f hij inf_le_left hi _).symm.trans
    (e.trans (congrArg₂ (· * ·) rfl (appLE_resG f hij inf_le_right hj _)))

theorem unit_eq_of_mul {R : Type*} [CommRing R] {a a' b b' : R} {c c' g₀ g₁ : Rˣ}
    (ha : a ∈ nonZeroDivisors R) (h : b = c * a) (h' : b' = c' * a') (hb : b = g₀ * b')
    (haa : a = g₁ * a') : c = g₀ ^ (1 : ℤ) * g₁ ^ (-1 : ℤ) * c' := by
  apply Units.ext
  apply (mul_cancel_right_mem_nonZeroDivisors ha).1
  rw [← h, hb, h', zpow_one, zpow_neg_one, haa]
  have := g₁.inv_mul
  push_cast
  linear_combination (-(g₀ * c' * a' : R)) * this

theorem exists_isGen_linComb : ∀ (X Y : Scheme.{0}) (L : LB X) (θ : L.Sec) (φ ψ : Y ⟶ X), L.IsLB → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ L.U i), (φ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ ψ ⁻¹ᵁ L.U i), (ψ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ Y) (i j : L.ι) (h : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U j), ((t ≫ φ).appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ ((t ≫ ψ).appLE (L.U j) ⊤ h').hom (θ.f j) = 0) → ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![φ, ψ] ![1, -1]), t.IsGen := by
  intro X Y L θ φ ψ _ _ hψ H
  have h0 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L ![φ, ψ] j 0
  have h1 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ ψ ⁻¹ᵁ L.U (j 1) :=
    fun j => LB.wchart_le L ![φ, ψ] j 1
  have hc : ∀ j : Fin 2 → L.ι, ∃ c : Γ(Y, L.wchart ![φ, ψ] j)ˣ,
      (φ.appLE _ _ (h0 j)).hom (θ.f (j 0)) = c * (ψ.appLE _ _ (h1 j)).hom (θ.f (j 1)) := by
    intro j
    apply exists_unit_mul
    · intro V' h
      rw [resG_appLE]
      exact hψ _ _ _
    · intro T t h
      have k0 : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U (j 0) := fun x hx => h0 j (h hx)
      have k1 : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U (j 1) := fun x hx => h1 j (h hx)
      rw [appLE_appLE t φ _ h k0, appLE_appLE t ψ _ h k1]
      exact (H T t _ _ k0 k1).symm
  choose c hc using hc
  refine ⟨⟨c⟩, fun i j => ?_⟩
  let W : Y.Opens := L.wchart ![φ, ψ] i ⊓ L.wchart ![φ, ψ] j
  have wi : W ≤ L.wchart ![φ, ψ] i := inf_le_left
  have wj : W ≤ L.wchart ![φ, ψ] j := inf_le_right
  have ei := congrArg (resG Y wi) (hc i)
  have ej := congrArg (resG Y wj) (hc j)
  rw [map_mul, resG_appLE, resG_appLE] at ei ej
  have p0 : W ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)) := le_inf (wi.trans (h0 i)) (wj.trans (h0 j))
  have p1 : W ≤ ψ ⁻¹ᵁ (L.U (i 1) ⊓ L.U (j 1)) := le_inf (wi.trans (h1 i)) (wj.trans (h1 j))
  have key := unit_eq_of_mul (c := res wi (c i)) (c' := res wj (c j)) (hψ _ _ _) ei ej
    (appLE_compat θ φ (i 0) (j 0) _ _ p0) (appLE_compat θ ψ (i 1) (j 1) _ _ p1)
  refine key.trans ?_
  congr 1
  exact (Fin.prod_univ_two (fun k : Fin 2 => (res (le_inf (wi.trans (LB.wchart_le L ![φ, ψ] i k))
    (wj.trans (LB.wchart_le L ![φ, ψ] j k)) : W ≤ (![φ, ψ] k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
    (pullU (![φ, ψ] k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ((![1, -1] : Fin 2 → ℤ) k))).symm

end RHLean.Geometry.NativeCM.SchemeTheory.SectionIso
