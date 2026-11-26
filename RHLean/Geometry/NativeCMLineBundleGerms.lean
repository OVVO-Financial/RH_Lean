import RHLean.Geometry.NativeCMLineBundleRegularSection

/-!
# Stalk calculations for the actual line-bundle atlas

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabPull.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DivCalc.lean`
- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSecNonzeroLocusEqOfLbIso.lean`

These are restriction, pullback and stalk maps on the original scheme rings.
The tensor-atlas cocycle and its sections are proved from actual unit transitions;
no ampleness or line-bundle existence is assumed.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

variable {X Y Z : Scheme.{0}}

namespace LB

lemma res_factor {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) {h : W ≤ U} (x : Γ(X, U)ˣ) :
    res h x = res h₂ (res h₁ x) := by
  rw [res_res]

lemma pullU_res (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (f.preimage_mono h) (pullU f U x) := by
  ext
  change ((X.presheaf.map (homOfLE h).op ≫ f.app V).hom) (x : Γ(X, U)) = _
  rw [Scheme.Hom.naturality]
  rfl

lemma res_pullU_eq (f : Y ⟶ X) {U U' : X.Opens} (hU' : U' ≤ U) {W : Y.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) (hW' : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) :
    res hW (pullU f U x) = res hW' (pullU f U' (res hU' x)) := by
  rw [pullU_res, res_res]

lemma res_g_self {L : LB X} (hL : L.IsLB) (i : L.ι) {W : X.Opens} (h : W ≤ L.U i ⊓ L.U i) :
    res h (L.g i i) = 1 := by
  rw [res_factor (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (h.trans inf_le_left),
    hL.g_self, map_one]

lemma res_cocycle {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  rw [res_factor (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) hW,
    res_factor (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) hW,
    res_factor (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) hW,
    ← map_mul, hL.cocycle]

lemma pull_g_self {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι) {W : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U i)) : res h (pullU f _ (L.g i i)) = 1 := by
  rw [res_pullU_eq f (le_refl (L.U i ⊓ L.U i)) h h, res_g_self hL i le_rfl, map_one, map_one]

lemma pull_cocycle {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i j k : L.ι) {W : Y.Opens}
    (h₁ : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j)) (h₂ : W ≤ f ⁻¹ᵁ (L.U j ⊓ L.U k))
    (h₃ : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    res h₁ (pullU f _ (L.g i j)) * res h₂ (pullU f _ (L.g j k)) =
      res h₃ (pullU f _ (L.g i k)) := by
  have hW : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := fun _ hy => ⟨h₁ hy, (h₂ hy).2⟩
  rw [res_pullU_eq f (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) h₁ hW,
    res_pullU_eq f (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) h₂ hW,
    res_pullU_eq f (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) h₃ hW,
    ← map_mul, ← map_mul, hL.cocycle]

lemma mem_of_cover {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hx

variable (L : LB X) {K : Type} [Fintype K]

lemma wchart_inter_le (φ : K → (Y ⟶ X)) (j j' : K → L.ι) (k : K) :
    wchart L φ j ⊓ wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) :=
  le_inf (inf_le_left.trans (wchart_le L φ j k)) (inf_le_right.trans (wchart_le L φ j' k))

def lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) :
    Γ(Y, wchart L φ j ⊓ wchart L φ j')ˣ :=
  ∏ k, (res (wchart_inter_le L φ j j' k) (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)

def ts {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : Gen (LinComb L φ ε)) (j : K → L.ι) :
    Γ(Y, wchart L φ j)ˣ :=
  t.s j

lemma res_lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) {W : Y.Opens}
    (hW : W ≤ wchart L φ j ⊓ wchart L φ j') :
    res hW (lcg L φ ε j j') =
      ∏ k, (res (hW.trans (wchart_inter_le L φ j j' k)) (pullU (φ k) _ (L.g (j k) (j' k)))) ^
        (ε k) := by
  rw [lcg, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) (res_res _ _ _)

lemma lcg_self {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j : K → L.ι) :
    res (le_inf le_rfl le_rfl : wchart L φ j ≤ wchart L φ j ⊓ wchart L φ j) (lcg L φ ε j j) = 1 := by
  rw [res_lcg]
  exact Finset.prod_eq_one fun k _ => by rw [pull_g_self hL (φ k), one_zpow]

lemma lcg_cocycle {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a b c : K → L.ι) :
    res (inf_le_left : wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ a ⊓ wchart L φ b)
        (lcg L φ ε a b) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ b ⊓ wchart L φ c)
        (lcg L φ ε b c) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ a ⊓ wchart L φ c)
        (lcg L φ ε a c) := by
  rw [res_lcg, res_lcg, res_lcg, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow]
  exact congrArg (· ^ ε k) (pull_cocycle hL (φ k) _ _ _ _ _ _)

theorem isLB_linComb {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (LinComb L φ ε).IsLB where
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    choose j hj using fun k => mem_of_cover hL ((φ k).base y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩
  g_self := lcg_self hL φ ε
  cocycle := lcg_cocycle hL φ ε

theorem isLB_pull {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) : (L.pull f).IsLB :=
  isLB_linComb hL _ _

end LB

namespace LBGerm

open Classical in

def gm (f : Y ⟶ X) (y : Y) (U : X.Opens) : Γ(X, U)ˣ →* (Y.presheaf.stalk y)ˣ :=
  if h : f y ∈ U then (Units.map (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.toMonoidHom).comp (pullU f U) else 1

theorem gm_val (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a.val) := by
  simp [gm, h, pullU]

theorem gm_res (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)ˣ) :
    gm f y V (res hle a) = gm f y U a := by
  apply Units.ext
  rw [gm_val f y V h, gm_val f y U (hle h)]
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have e1 := Scheme.Hom.naturality f (homOfLE hle).op
  rw [← Y.presheaf.germ_res (homOfLE (Scheme.Hom.preimage_mono f hle)) y h]
  rw [CommRingCat.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e1]
  rfl

theorem gm_pull (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    gm f z (g ⁻¹ᵁ U) (pullU g U a) = gm (f ≫ g) z U a := by
  apply Units.ext
  rw [gm_val f z _ h, gm_val (f ≫ g) z U h]
  simp only [pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl

theorem unit_ext {V : X.Opens} {a b : Γ(X, V)ˣ} (h : ∀ x ∈ V, gm (𝟙 X) x V a = gm (𝟙 X) x V b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext X.sheaf V
  intro x hx
  have e := congrArg Units.val (h x hx)
  rw [gm_val _ _ _ hx, gm_val _ _ _ hx] at e
  exact e

theorem exists_chart {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have := hL.cover
  have hx : x ∈ (⨆ i, L.U i : X.Opens) := by rw [this]; trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using hx

theorem gm_cocycle {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i j k : L.ι} (hi : f y ∈ L.U i) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gm f y _ (L.g i j) * gm f y _ (L.g j k) = gm f y _ (L.g i k) := by
  have hijk : f y ∈ L.U i ⊓ L.U j ⊓ L.U k := ⟨⟨hi, hj⟩, hk⟩
  rw [← gm_res f y (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) hijk,
    ← gm_res f y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) hijk,
    ← gm_res f y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) hijk,
    ← map_mul, hL.cocycle]

theorem gm_self {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i : L.ι} (hi : f y ∈ L.U i) :
    gm f y (L.U i ⊓ L.U i) (L.g i i) = 1 := by
  rw [← gm_res f y (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) hi, hL.g_self i, map_one]

theorem gm_linComb {Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (j j' : K → L.ι) (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') =
      ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ (show r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' from ⟨hj, hj'⟩) _).trans
    (gm_pull r (φ k) z (L.U (j k) ⊓ L.U (j' k)) ⟨Set.mem_iInter.1 hj k, Set.mem_iInter.1 hj' k⟩ _)

open Classical in

def gs (f : Y ⟶ X) (y : Y) (U : X.Opens) (a : Γ(X, U)) : Y.presheaf.stalk y :=
  if h : f y ∈ U then (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a) else 0

theorem gs_eq (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a) := by
  unfold gs
  exact dite_eq_left h

theorem gs_unit (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) : gs f y U a.val = (gm f y U a).val := by
  rw [gs_eq f y U h]
  unfold gm
  rw [dite_eq_left h]
  rfl

theorem gs_mul (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a * b) = gs f y U a * gs f y U b := by
  simp only [gs_eq f y U h, map_mul]

theorem gs_add (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a + b) = gs f y U a + gs f y U b := by
  simp only [gs_eq f y U h, map_add]

theorem gs_res (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)) :
    gs f y V ((X.presheaf.map (homOfLE hle).op).hom a) = gs f y U a := by
  rw [gs_eq f y V h, gs_eq f y U (hle h)]
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    Scheme.Hom.naturality_assoc]
  erw [TopCat.Presheaf.germ_res]

theorem gs_resG (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U)
    (h : f y ∈ V) (a : Γ(X, U)) : gs f y V (resG X hle a) = gs f y U a :=
  gs_res f y hle h a

theorem gs_pull (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)) :
    gs f z (g ⁻¹ᵁ U) ((g.app U).hom a) = gs (f ≫ g) z U a := by
  have h' : (f ≫ g) z ∈ U := h
  rw [gs_eq f z (g ⁻¹ᵁ U) h, gs_eq (f ≫ g) z U h']
  rfl

theorem fn_ext {V : X.Opens} {a b : Γ(X, V)} (h : ∀ x ∈ V, gs (𝟙 X) x V a = gs (𝟙 X) x V b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf V a b
  intro x hx
  have e := h x hx
  rw [gs_eq (𝟙 X) x V hx, gs_eq (𝟙 X) x V hx] at e
  exact e

private lemma germ_app_presheaf_map_eq_germ_app {A B : Scheme.{0}} (f : A ⟶ B) (y : A) {U V : B.Opens} (hVU : V ≤ U)
    (hy : f y ∈ V) (a : Γ(B, U)) :
    (A.presheaf.germ (f ⁻¹ᵁ V) y hy).hom ((f.app V).hom ((B.presheaf.map (homOfLE hVU).op).hom a)) =
      (A.presheaf.germ (f ⁻¹ᵁ U) y (hVU hy)).hom ((f.app U).hom a) := by
  have nat := congrArg (fun g => g.hom a) (Scheme.Hom.naturality f (homOfLE hVU).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at nat
  rw [nat]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private lemma germ_app_app_eq_germ_app_comp {A B C : Scheme.{0}} (r : A ⟶ B) (h : B ⟶ C) (y : A) (W : C.Opens)
    (hy : h (r y) ∈ W) (a : Γ(C, W)) :
    (A.presheaf.germ (r ⁻¹ᵁ h ⁻¹ᵁ W) y hy).hom ((r.app (h ⁻¹ᵁ W)).hom ((h.app W).hom a)) =
      (A.presheaf.germ ((r ≫ h) ⁻¹ᵁ W) y hy).hom (((r ≫ h).app W).hom a) := by
  rfl

theorem gs_appLE {Y : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ W) (f : Γ(X, U)) : gs r z W ((q.appLE U W e).hom f) = gs (r ≫ q) z U f := by
  unfold gs
  rw [dite_eq_left hz, dite_eq_left (show (r ≫ q) z ∈ U from e hz)]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (germ_app_presheaf_map_eq_germ_app r z e hz _).trans (germ_app_app_eq_germ_app_comp r q z U (e hz) f)

theorem gs_stalkMap (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    gs r z U f = (r.stalkMap z).hom (gs (𝟙 X) (r z) U f) := by
  unfold gs
  rw [dite_eq_left h, dite_eq_left (show (𝟙 X : X ⟶ X) (r z) ∈ U from h)]
  rw [← Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem gs_compat {L : LB X} (s : L.Sec) (r : Z ⟶ X) (z : Z)
    {i j : L.ι} (hi : r z ∈ L.U i) (hj : r z ∈ L.U j) :
    gs r z _ (s.f i) = (gm r z (L.U i ⊓ L.U j) (L.g i j)).val * gs r z _ (s.f j) := by
  have h : r z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have e := congrArg (gs r z (L.U i ⊓ L.U j)) (s.compat i j)
  rw [gs_res _ z _ h, gs_mul _ z _ h, gs_unit _ z _ h, gs_res _ z _ h] at e
  exact e

theorem gs_pow (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem isUnit_gs_iff (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_stalkMap r z U h, isUnit_map_iff (r.stalkMap z).hom, gs_eq (𝟙 X) (r z) U h]
  exact (X.mem_basicOpen a _ h).symm

def secOfGerm {M : LB X} (f : ∀ i, Γ(X, M.U i))
    (h : ∀ (y : X) i j, y ∈ M.U i → y ∈ M.U j →
      gs (𝟙 X) y _ (f i) = (gm (𝟙 X) y (M.U i ⊓ M.U j) (M.g i j)).val * gs (𝟙 X) y _ (f j)) : M.Sec where
  f := f
  compat i j := fn_ext fun y hy => by
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy]
    exact h y i j hy.1 hy.2

end LBGerm

open LBGerm

variable {M : LB Y}

theorem exists_chart_of_mem_nonzeroLocus {s : M.Sec} {y : Y} (h : y ∈ nonzeroLocus s) : ∃ k, y ∈ M.U k := by
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
  exact ⟨k, Y.basicOpen_le _ hk⟩

theorem mem_nonzeroLocus_iff_pull (s : M.Sec) (r : Z ⟶ Y) (z : Z) {k : M.ι} (hk : r z ∈ M.U k) :
    r z ∈ nonzeroLocus s ↔ IsUnit (gs r z _ (s.f k)) := by
  refine ⟨fun h => ?_, fun h => basicOpen_le_nonzeroLocus s k ((isUnit_gs_iff r z _ hk _).1 h)⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
  have hjU : r z ∈ M.U j := Y.basicOpen_le _ hj
  have u := (isUnit_gs_iff r z _ hjU _).2 hj
  rw [gs_compat s r z hjU hk] at u
  exact isUnit_of_mul_isUnit_right u

theorem mem_nonzeroLocus_iff_isUnit (s : M.Sec) {y : Y} {k : M.ι} (hk : y ∈ M.U k) :
    y ∈ nonzeroLocus s ↔ IsUnit (gs (𝟙 Y) y _ (s.f k)) :=
  mem_nonzeroLocus_iff_pull s (𝟙 Y) y hk

theorem nonzeroLocus_inf_chart (s : M.Sec) (k : M.ι) : nonzeroLocus s ⊓ M.U k = Y.basicOpen (s.f k) :=
  le_antisymm (fun y hy => (isUnit_gs_iff (𝟙 Y) y _ hy.2 _).1 ((mem_nonzeroLocus_iff_isUnit s hy.2).1 hy.1))
    (le_inf (basicOpen_le_nonzeroLocus s k) (Y.basicOpen_le _))

theorem mem_nonzeroLocus_iff_basicOpen (s : M.Sec) {y : Y} {k : M.ι} (hk : y ∈ M.U k) :
    y ∈ nonzeroLocus s ↔ y ∈ Y.basicOpen (s.f k) :=
  (mem_nonzeroLocus_iff_isUnit s hk).trans (isUnit_gs_iff (𝟙 Y) y _ hk _)

theorem nonzeroLocus_eq_of (s : M.Sec) (W : Y.Opens) (hW : ∀ y ∈ W, ∃ k, y ∈ M.U k)
    (h : ∀ (y : Y) k, y ∈ M.U k → (IsUnit (gs (𝟙 Y) y _ (s.f k)) ↔ y ∈ W)) : nonzeroLocus s = W := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact (h y k hk).1 ((mem_nonzeroLocus_iff_isUnit s hk).1 hy)
  · obtain ⟨k, hk⟩ := hW y hy
    exact (mem_nonzeroLocus_iff_isUnit s hk).2 ((h y k hk).2 hy)

end RHLean.Geometry.NativeCM.SchemeTheory
