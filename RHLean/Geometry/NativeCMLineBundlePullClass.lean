import RHLean.Geometry.NativeCMLineBundleGenerators
import RHLean.Geometry.NativeCMWeierstrassOriginBaseChange

/-!
# Pullback classes defined by genuine trivializations

The relations in `PullClass` are precisely signed pullbacks for which an
actual chart generator has been constructed. The converse is proved by
unit gluing. Equality in this group therefore yields an actual line-bundle
isomorphism, including after flattening the original nested pullbacks.

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`:

- `src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPrimitiveNormalisation.lean`, the `Classes` section;
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabPull.lean`, `gm_div` and isomorphism transport;
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/AmplePt.lean`, `gen_chartPull`.

Only the actual-generator quotient required by the Serre pairing proof is
used; no abstract Picard representability is assumed. The source archive
states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

open LBGerm

variable {X Y Y' Z : Scheme.{0}}

def LBIso (A B : LB Y) : Prop := ∃ w : LB.Iso A B, w.IsGen

theorem gm_div (A B : LB Y) (r : Z ⟶ Y) (z : Z) (p q : B.ι × A.ι)
    (hm : r z ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) :
    gm r z (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) ((LB.div B A).g p q) =
      gm r z _ (B.g p.1 q.1) * (gm r z _ (A.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hm _))))

def chartPullId (A : LB Y) : ChartPull A A (𝟙 Y) where
  idx := id
  le _ := le_rfl
  g _ _ _ _ _ := rfl

def chartPullSame (L : LB X) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (hc : ∀ k, φ' k = h ≫ φ k) :
    ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h :=
  have le : ∀ j : K → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have hk := Set.mem_iInter.1 hy k
      change (h ≫ φ k) y ∈ L.U (j k)
      rw [← hc k]
      exact hk
  { idx := id
    le := le
    g := fun y j j' hj hj' =>
      (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans
        ((Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, hc k]).trans
          (gm_linComb L φ ε h y j j' (le j hj) (le j' hj')).symm) }

theorem gen_chartPull {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y}
    (a : ChartPull A' A h) (t : LB.Gen A) (ht : t.IsGen) :
    ∃ t' : LB.Gen A', t'.IsGen := by
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (t.s (a.idx i)))⟩,
    fun i j => unit_ext fun y hy => ?_⟩
  have v : ∀ i, y ∈ A'.U i →
      gm (𝟙 Y') y (A'.U i) (res (a.le i) (pullU h _ (t.s (a.idx i)))) =
        gm h y (A.U (a.idx i)) (t.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans
      ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := (gm_res h y _ hm _).symm.trans
    ((congrArg (gm h y _) (ht (a.idx i) (a.idx j))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res h y _ hm _))))
  exact ((gm_res _ y _ hy _).trans (v i hy.1)).trans
    (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (a.g y i j hy.1 hy.2) ((gm_res _ y _ hy _).trans (v j hy.2)))).symm)

theorem LBIso.chartPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y}
    (a : ChartPull A' A h) (b : ChartPull B' B h) (H : LBIso A B) :
    LBIso A' B' := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ p : B'.ι × A'.ι,
      B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) :=
    fun p _ hy => ⟨b.le p.1 hy.1, a.le p.2 hy.2⟩
  refine ⟨⟨fun p => res (le p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩,
    fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ (res (le p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))) =
        gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) :=
    fun p hp => (gm_res (𝟙 Y') y (le p) hp _).trans
      ((gm_pull (𝟙 Y') h y _ (le p hp) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓
      (B.U (b.idx q.1) ⊓ A.U (a.idx q.2)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓
      (B.U (b.idx q.1) ⊓ A.U (a.idx q.2))))
    (hw (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2))
  have e' := (gm_res h y _ hm _).symm.trans
    (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div A B h y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hm)
      (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (v p hy.1)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div A' B' (𝟙 Y') y p q hy).trans ?_)
    ((gm_res (𝟙 Y') y _ hy _).trans (v q hy.2)))
  rw [a.g y _ _ hy.1.2 hy.2.2, b.g y _ _ hy.1.1 hy.2.1]

namespace PullClasses

def trivialSums (L : LB X) (Y : Scheme.{0}) :
    Subgroup (Abelianization (FreeGroup (Y ⟶ X))) where
  carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ),
    HasGen L φ ε ∧ ∏ k, Abelianization.of (FreeGroup.of (φ k)) ^ ε k = s}
  one_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim,
    ⟨LB.oneGen L, LB.isGen_oneGen L⟩, Fintype.prod_empty _⟩
  mul_mem' := by
    rintro _ _ ⟨K, _, φ, ε, h, rfl⟩ ⟨K', _, φ', ε', h', rfl⟩
    exact ⟨K ⊕ K', inferInstance, _, _, h.mul h', Fintype.prod_sum_type _⟩
  inv_mem' := by
    rintro _ ⟨K, _, φ, ε, h, rfl⟩
    exact ⟨K, inferInstance, _, _, h.inv, by simp only [zpow_neg, Finset.prod_inv_distrib]⟩

abbrev PullClass (L : LB X) (Y : Scheme.{0}) : Type :=
  Abelianization (FreeGroup (Y ⟶ X)) ⧸ trivialSums L Y

def cls (L : LB X) (ψ : Y ⟶ X) : PullClass L Y :=
  QuotientGroup.mk' _ (Abelianization.of (FreeGroup.of ψ))

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem hasGen_iff (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    HasGen L φ ε ↔ ∏ k, cls L (φ k) ^ ε k = 1 := by
  have e : ∏ k, cls L (φ k) ^ ε k =
      QuotientGroup.mk' (trivialSums L Y)
        (∏ k, Abelianization.of (FreeGroup.of (φ k)) ^ ε k) := by
    simp only [map_prod, map_zpow, cls]
  rw [e, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨fun h => ⟨K, inferInstance, φ, ε, h, rfl⟩, ?_⟩
  rintro ⟨K', _, φ', ε', h, e⟩
  refine h.of_formEq hL fun U _ f => ?_
  simpa only [map_prod, map_zpow, Abelianization.lift_apply_of, FreeGroup.lift_apply_of] using
    congrArg (Abelianization.lift (FreeGroup.lift f)) e

def chartDivOut (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    ChartPull (LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε))
      (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) (𝟙 Y) :=
  have le : ∀ p : (K' → L.ι) × (K → L.ι),
      LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤
        LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := fun p _ hy =>
    Set.mem_iInter.2 fun k => by
      rcases k with k | k
      exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  { idx := fun p => Sum.elim p.1 p.2
    le := le
    g := fun y p q hp hq => by
      refine (gm_div _ _ (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans ?_
        (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm)
      refine (congrArg₂ (fun a b => a * b⁻¹)
        (gm_linComb L φ' ε' (𝟙 Y) y p.1 q.1 hp.1 hq.1)
        (gm_linComb L φ ε (𝟙 Y) y p.2 q.2 hp.2 hq.2)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
        zpow_neg, Finset.prod_inv_distrib]
      rfl }

def chartDivIn (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    ChartPull (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k))
      (LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) (𝟙 Y) :=
  have le : ∀ j : K' ⊕ K → L.ι,
      LB.wchart L (Sum.elim φ' φ) j ≤
        LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inr k)⟩
  { idx := fun j => (j ∘ Sum.inl, j ∘ Sum.inr)
    le := le
    g := fun y p q hp hq => by
      refine (gm_linComb L _ _ (𝟙 Y) y p q hp hq).trans (Eq.trans ?_
        (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y
          (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr)
          ⟨le p hp, le q hq⟩).symm)
      refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹)
        (gm_linComb L φ' ε' (𝟙 Y) y _ _ (le p hp).1 (le q hq).1)
        (gm_linComb L φ ε (𝟙 Y) y _ _ (le p hp).2 (le q hq).2)).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
        zpow_neg, Finset.prod_inv_distrib]
      rfl }

theorem lbIso_iff (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔
      ∏ k, cls L (φ k) ^ ε k = ∏ k, cls L (φ' k) ^ ε' k := by
  have e : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔
      HasGen L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k) :=
    ⟨fun ⟨w, hw⟩ => gen_chartPull (chartDivIn L φ ε φ' ε') w hw,
      fun ⟨w, hw⟩ => gen_chartPull (chartDivOut L φ ε φ' ε') w hw⟩
  rw [e, hasGen_iff hL]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    zpow_neg, Finset.prod_inv_distrib, mul_inv_eq_one]
  exact eq_comm

def chartFlat (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
    ChartPull (LB.LinComb (LB.LinComb L φ ε) ψ δ)
      (LB.LinComb L (fun p : K' × K => ψ p.1 ≫ φ p.2)
        (fun p => ε p.2 * δ p.1)) (𝟙 Z) :=
  have le : ∀ j : K' → K → L.ι,
      LB.wchart (LB.LinComb L φ ε) ψ j ≤
        LB.wchart L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => j p.1 p.2) :=
    fun j _ hy => Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  { idx := fun j p => j p.1 p.2
    le := le
    g := fun y p q hp hq => by
      refine (gm_linComb (LB.LinComb L φ ε) ψ δ (𝟙 Z) y p q hp hq).trans
        (Eq.trans ?_ (gm_linComb L _ _ (𝟙 Z) y _ _ (le p hp) (le q hq)).symm)
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun k _ => ?_
      refine (congrArg (· ^ δ k) (gm_linComb L φ ε (𝟙 Z ≫ ψ k) y (p k) (q k)
        (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hq k))).trans ?_
      simp only [← Finset.prod_zpow, zpow_mul, Category.assoc] }

theorem prod_flat (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
    ∏ p : K' × K, cls L (ψ p.1 ≫ φ p.2) ^ (ε p.2 * δ p.1) =
      ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k := by
  simp only [Fintype.prod_prod_type, ← Finset.prod_zpow, zpow_mul]

theorem hasGen_nested (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ)
    (h : ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k = 1) :
    HasGen (LB.LinComb L φ ε) ψ δ := by
  obtain ⟨t, ht⟩ := (hasGen_iff hL _ _).2 ((prod_flat φ ε ψ δ).trans h)
  exact gen_chartPull (chartFlat L φ ε ψ δ) t ht

theorem lbIso_nested (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ)
    {K₃ : Type} [Fintype K₃] (χ : K₃ → (Z ⟶ X)) (κ : K₃ → ℤ)
    (h : ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k =
      ∏ k, cls L (χ k) ^ κ k) :
    LBIso (LB.LinComb (LB.LinComb L φ ε) ψ δ) (LB.LinComb L χ κ) :=
  ((lbIso_iff hL _ _ χ κ).2 ((prod_flat φ ε ψ δ).trans h)).chartPull
    (chartFlat L φ ε ψ δ) (chartPullId _)

end PullClasses

end RHLean.Geometry.NativeCM.SchemeTheory

end
