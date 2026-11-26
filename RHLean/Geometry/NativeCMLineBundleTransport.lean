import RHLean.Geometry.NativeCMLineBundleGerms

/-!
# Transport actual sections through tensor-atlas identities

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/CubicalStructures/CubeSymmetricSwapFirst.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean`

The section transport is proved by gluing in actual sheaves of rings. Equality
of tensor exponents is used only after a concrete product identity is proved;
no line-bundle isomorphism, global section or polarization is postulated.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

variable {X Y Y' Z : Scheme.{0}}

namespace LB

variable (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

def pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : Gen (LinComb L φ ε)) (h : Z ⟶ Y) :
    Gen (LinComb L (fun k => h ≫ φ k) ε) where
  s := fun j => res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ wchart L φ j)
    (pullU h _ (c.s j))

def invGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : Gen (LinComb L φ ε)) :
    Gen (LinComb L φ (fun k => - ε k)) where
  s := fun j => (t.s j)⁻¹

lemma isGen_iff {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : Gen (LinComb L φ ε)) :
    t.IsGen ↔ ∀ i j : K → L.ι,
      res (inf_le_left : wchart L φ i ⊓ wchart L φ j ≤ wchart L φ i) (ts t i) =
        lcg L φ ε i j * res (inf_le_right : wchart L φ i ⊓ wchart L φ j ≤ wchart L φ j) (ts t j) :=
  Iff.rfl

lemma wchart_comp_le (h : Z ⟶ Y) (φ : K → (Y ⟶ X)) (j : K → L.ι) :
    wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ wchart L φ j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

lemma wchart_comp_le₂ (h : Z ⟶ Y) (φ : K → (Y ⟶ X)) (i j : K → L.ι) :
    wchart L (fun k => h ≫ φ k) i ⊓ wchart L (fun k => h ≫ φ k) j ≤
      h ⁻¹ᵁ (wchart L φ i ⊓ wchart L φ j) :=
  fun _ hy => ⟨wchart_comp_le L h φ i hy.1, wchart_comp_le L h φ j hy.2⟩

lemma ts_pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : Gen (LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) :
    ts (pullGen L φ ε c h) j = res (wchart_comp_le L h φ j) (pullU h _ (ts c j)) := rfl

lemma pullU_comp (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (h ≫ f) U x = pullU h (f ⁻¹ᵁ U) (pullU f U x) := by
  ext; rfl

lemma pull_res_comp (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (hV : V ≤ f ⁻¹ᵁ U)
    {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ V) (hW' : W ≤ (h ≫ f) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res hW (pullU h V (res hV (pullU f U x))) = res hW' (pullU (h ≫ f) U x) := by
  rw [pullU_res, res_res, pullU_comp]
  rfl

lemma lcg_comp (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (i j : K → L.ι) :
    lcg L (fun k => h ≫ φ k) ε i j =
      res (wchart_comp_le₂ L h φ i j) (pullU h _ (lcg L φ ε i j)) := by
  rw [lcg, lcg, map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  exact congrArg (· ^ ε k) (pull_res_comp h (φ k) _ _ _ _ _).symm

theorem isGen_pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : Gen (LinComb L φ ε)) (hc : c.IsGen)
    (h : Z ⟶ Y) : (pullGen L φ ε c h).IsGen := by
  refine (isGen_iff L _).2 fun i j => ?_
  have key := congrArg (fun x => res (wchart_comp_le₂ L h φ i j) (pullU h _ x))
    ((isGen_iff L c).1 hc i j)
  simp only [map_mul, pullU_res, res_res] at key
  rw [ts_pullGen, ts_pullGen, lcg_comp]
  simp only [res_res]
  exact key

lemma ts_invGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : Gen (LinComb L φ ε)) (j : K → L.ι) :
    ts (invGen L φ ε t) j = (ts t j)⁻¹ := rfl

lemma lcg_neg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j : K → L.ι) :
    lcg L φ (fun k => - ε k) i j = (lcg L φ ε i j)⁻¹ := by
  simp only [lcg, zpow_neg, Finset.prod_inv_distrib]

theorem isGen_invGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : Gen (LinComb L φ ε)) (ht : t.IsGen) :
    (invGen L φ ε t).IsGen := by
  refine (isGen_iff L _).2 fun i j => ?_
  rw [ts_invGen, ts_invGen, lcg_neg, map_inv, map_inv, (isGen_iff L t).1 ht i j, mul_inv]

lemma wchart_pu_le (M : LB X) (f : Y ⟶ X) (i j : PUnit → M.ι) :
    wchart M (K := PUnit) (fun _ => f) i ⊓ wchart M (K := PUnit) (fun _ => f) j ≤
      f ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
  wchart_inter_le M (K := PUnit) (fun _ => f) i j PUnit.unit

lemma lcg_pull (M : LB X) (f : Y ⟶ X) (i j : PUnit → M.ι) :
    lcg M (K := PUnit) (fun _ => f) (fun _ => 1) i j =
      res (wchart_pu_le M f i j) (pullU f _ (M.g (i PUnit.unit) (j PUnit.unit))) := by
  rw [lcg, Fintype.prod_unique, zpow_one]

end LB

namespace LBGerm

variable (L : LB X)

def Good (z : Z) (J : (Z ⟶ X) → L.ι) : Prop := ∀ ψ : Z ⟶ X, ψ z ∈ L.U (J ψ)

theorem exists_good (hL : L.IsLB) (z : Z) {K : Type} (ψ : K → (Z ⟶ X)) (j : K → L.ι)
    (hc : ∀ a b, ψ a = ψ b → j a = j b) (hj : ∀ k, ψ k z ∈ L.U (j k)) :
    ∃ J, Good L z J ∧ ∀ k, J (ψ k) = j k := by
  classical
  have hcov : ∀ x : X, ∃ i, x ∈ L.U i := fun x => by
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; simp
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨fun ψ' => if hk : ∃ k, ψ k = ψ' then j hk.choose else (hcov (ψ' z)).choose, ?_, ?_⟩
  · intro ψ'
    dsimp only
    split_ifs with hk
    · have hm := hj hk.choose
      rw [hk.choose_spec] at hm
      exact hm
    · exact (hcov _).choose_spec
  · intro k
    dsimp only
    rw [dite_eq_left ⟨k, rfl⟩]
    exact hc _ _ (Exists.choose_spec (⟨k, rfl⟩ : ∃ k', ψ k' = ψ k))

variable {L} {K K' : Type} [Fintype K] [Fintype K']

theorem Good.mem {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (φ : K → (Y ⟶ X)) (r : Z ⟶ Y) :
    r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ φ k)

def val {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    (Z.presheaf.stalk z)ˣ := gm r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (t.s (fun k => J (r ≫ φ k)))

def sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    Z.presheaf.stalk z := gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (s.f (fun k => J (r ≫ φ k)))

theorem val_of {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    val t r z J = gm r z (LB.wchart L φ j) (t.s j) := by
  obtain rfl : (fun k => J (r ≫ φ k)) = j := funext h
  rfl

theorem sval_of {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    sval s r z J = gs r z (LB.wchart L φ j) (s.f j) := by
  obtain rfl : (fun k => J (r ≫ φ k)) = j := funext h
  rfl

def trF (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (j j' : K → L.ι) : (Z.presheaf.stalk z)ˣ :=
  ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k

theorem trF_trans (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {i j k : K → L.ι}
    (hi : r z ∈ LB.wchart L φ i) (hj : r z ∈ LB.wchart L φ j) (hk : r z ∈ LB.wchart L φ k) :
    trF φ ε r z i j * trF φ ε r z j k = trF φ ε r z i k := by
  unfold trF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← mul_zpow]
  congr 1
  have hm : (r ≫ φ c) z ∈ L.U (i c) ⊓ L.U (j c) ⊓ L.U (k c) :=
    ⟨⟨Set.mem_iInter.1 hi c, Set.mem_iInter.1 hj c⟩, Set.mem_iInter.1 hk c⟩
  have c1 := congrArg (gm (r ≫ φ c) z (L.U (i c) ⊓ L.U (j c) ⊓ L.U (k c))) (hL.cocycle (i c) (j c) (k c))
  rw [map_mul] at c1
  exact (congrArg₂ (· * ·) (gm_res (r ≫ φ c) z _ hm _) (gm_res (r ≫ φ c) z _ hm _)).symm.trans
    (c1.trans (gm_res (r ≫ φ c) z _ hm _))

theorem gen_trans {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j) (t.s j) = trF φ ε r z j j' * gm r z (LB.wchart L φ j') (t.s j') := by
  have hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := ⟨hj, hj'⟩
  have e := congrArg (gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j')) (ht j j')
  have e1 : gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') = trF φ ε r z j j' :=
    gm_linComb L φ ε r z j j' hj hj'
  exact (gm_res r z inf_le_left hm _).symm.trans
    (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) e1 (gm_res r z inf_le_right hm _))))

theorem sec_trans {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gs r z (LB.wchart L φ j) (s.f j) = (trF φ ε r z j j').val * gs r z (LB.wchart L φ j') (s.f j') := by
  have hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := ⟨hj, hj'⟩
  have e := congrArg (gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j')) (s.compat j j')
  have e1 := (gs_unit r z _ hm ((LB.LinComb L φ ε).g j j')).trans
    (congrArg Units.val (gm_linComb L φ ε r z j j' hj hj'))
  exact (gs_res r z inf_le_left hm _).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) e1 (gs_res r z inf_le_right hm _))))

def FormEq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) : Prop :=
  ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = ∏ k, h (φ' k) ^ ε' k

theorem FormEq.trF {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') (r : Z ⟶ Y)
    (z : Z) (I I' : (Y ⟶ X) → L.ι) :
    trF φ ε r z (fun k => I (φ k)) (fun k => I' (φ k)) = trF φ' ε' r z (fun k => I (φ' k)) (fun k => I' (φ' k)) := h _ fun ψ => gm (r ≫ ψ) z (L.U (I ψ) ⊓ L.U (I' ψ)) (L.g (I ψ) (I' ψ))

theorem exists_sec (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L φ' ε'),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s' r z J = sval s r z J := by
  have glue : ∀ j : K' → L.ι, ∃ a : Γ(Y, LB.wchart L φ' j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Y ⟶ X) → L.ι),
      r z ∈ LB.wchart L φ' j → r z ∈ LB.wchart L φ' (fun k => I (φ' k)) → r z ∈ LB.wchart L φ (fun k => I (φ k)) →
      gs r z _ a = (trF φ' ε' r z j (fun k => I (φ' k))).val * gs r z (LB.wchart L φ (fun k => I (φ k))) (s.f (fun k => I (φ k))) := by
    intro j
    let W : ((Y ⟶ X) → L.ι) → Y.Opens := fun I =>
      LB.wchart L φ' j ⊓ LB.wchart L φ' (fun k => I (φ' k)) ⊓ LB.wchart L φ (fun k => I (φ k))
    obtain ⟨u, hu⟩ : ∃ u : ∀ I, Γ(Y, W I), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) I, r z ∈ W I →
        gs r z (W I) (u I) = (trF φ' ε' r z j (fun k => I (φ' k))).val * gs r z (LB.wchart L φ (fun k => I (φ k))) (s.f (fun k => I (φ k))) :=
      ⟨fun I => (Y.presheaf.map (homOfLE (inf_le_left : W I ≤ LB.wchart L φ' j ⊓ LB.wchart L φ' (fun k => I (φ' k)))).op).hom
          ((LB.LinComb L φ' ε').g j (fun k => I (φ' k))).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W I ≤ LB.wchart L φ (fun k => I (φ k)))).op).hom (s.f (fun k => I (φ k))), fun Z r z I hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ hz.1 _).trans
          (congrArg Units.val (gm_linComb L φ' ε' r z _ _ hz.1.1 hz.1.2)))) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L φ' j)
      (fun I => homOfLE (inf_le_left.trans inf_le_left)) (fun y hy => by
        choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
        exact Opens.mem_iSup.2 ⟨I, ⟨hy, Set.mem_iInter.2 fun k => hI _⟩, Set.mem_iInter.2 fun k => hI _⟩) u
      (fun I I' => fn_ext (V := W I ⊓ W I') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y I hy.1, hu _ _ y I' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2, h.trF, ← mul_assoc, ← Units.val_mul,
          trF_trans hL φ' ε' (𝟙 Y) y hy.1.1.1 hy.1.1.2 hy.2.1.2])
    refine ⟨a, fun Z r z I h₁ h₂ h₃ => ?_⟩
    have hz : r z ∈ W I := ⟨⟨h₁, h₂⟩, h₃⟩
    exact (gs_res r z (inf_le_left.trans inf_le_left) hz a).symm.trans ((congrArg (gs r z (W I)) (ha I)).trans
      (hu Z r z I hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (fun k => I (φ' k)) := Set.mem_iInter.2 fun k => hI _
    have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ (fun k => I (φ k)) := Set.mem_iInter.2 fun k => hI _
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ' ε' (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y I hy.1 m₁ m₂).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y I hy.2 m₁ m₂)).symm)
    rw [← trF_trans hL φ' ε' (𝟙 Y) y hy.1 hy.2 m₁, Units.val_mul, mul_assoc]; rfl
  · have m := hJ.mem φ' r
    refine (ha _ Z r z (fun χ => J (r ≫ χ)) m m (hJ.mem φ r)).trans ?_
    rw [mul_eq_left.1 (trF_trans hL φ' ε' r z m m m), Units.val_one, one_mul]; rfl

def pullMulSec {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) :
    LB.Sec (LB.LinComb L (Sum.elim (fun k => h ≫ φ k) φ₃) (Sum.elim ε ε₃)) :=
  have l₁ : ∀ j : K ⊕ K₃ → L.ι, LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j ≤ h ⁻¹ᵁ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have l₂ : ∀ j : K ⊕ K₃ → L.ι, LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j ≤ LB.wchart L φ₃ (j ∘ Sum.inr) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  { f := fun j => (Y'.presheaf.map (homOfLE (l₁ j)).op).hom ((h.app _).hom (s.f (j ∘ Sum.inl))) *
      (Y'.presheaf.map (homOfLE (l₂ j)).op).hom (u.s (j ∘ Sum.inr)).val
    compat := fun (j j' : K ⊕ K₃ → L.ι) => fn_ext fun y hy => by
      have v : ∀ j : K ⊕ K₃ → L.ι, y ∈ LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j →
          gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (l₁ j)).op).hom ((h.app _).hom (s.f (j ∘ Sum.inl))) *
            (Y'.presheaf.map (homOfLE (l₂ j)).op).hom (u.s (j ∘ Sum.inr)).val) =
          gs (𝟙 Y' ≫ h) y (LB.wchart L φ (j ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) *
            (gm (𝟙 Y') y (LB.wchart L φ₃ (j ∘ Sum.inr)) (u.s (j ∘ Sum.inr))).val := fun j hj =>
        (gs_mul _ y _ hj _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hj _).trans (gs_pull _ h y _ (l₁ j hj) _))
          ((gs_res _ y _ hj _).trans (gs_unit _ y _ (l₂ j hj) _)))
      refine ((gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y' ≫ h) y (l₁ j hy.1) (l₁ j' hy.2), gen_trans hu (𝟙 Y') y (l₂ j hy.1) (l₂ j' hy.2),
        Fintype.prod_sum_type, Units.val_mul, Units.val_mul, mul_mul_mul_comm]
      simp only [trF, Category.assoc, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] }

theorem sval_pullMulSec {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (r : Z ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (pullMulSec s h u hu) r z J = sval s (r ≫ h) z J * (val u r z J).val := by
  have hm := hJ.mem (Sum.elim (fun k => h ≫ φ k) φ₃) r
  have hm1 : h (r z) ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  have hm3 : r z ∈ LB.wchart L φ₃ (fun k => J (r ≫ φ₃ k)) := hJ.mem φ₃ r
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z _ hm _).trans (gs_pull r h z _ hm1 _))
    ((gs_res r z _ hm _).trans (gs_unit r z _ hm3 _)))

end LBGerm

end RHLean.Geometry.NativeCM.SchemeTheory
