import RHLean.Geometry.NativeCMLineBundleGerms

/-!
# Actual powers and finite tensor sections of the line-bundle atlas

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ThetaUnifAV.lean`
- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemNonzeroLocusIffPowFn.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsUniqueEqConstMulOriginSec.lean`

Only the literal lbPow definition is taken from ThetaUnifAV; no uniformization
statement or premise is imported. Finite tensor sections are constructed from
the same transition cocycles and retain their exact nonzero loci.
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

open LBGerm

abbrev lbPow {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))

variable {L : LB X} {n : ℕ}

abbrev powChart (L : LB X) (J : PUnit → L.ι) : X.Opens := LB.wchart L (fun _ : PUnit => 𝟙 X) J

theorem mem_powChart {J : PUnit → L.ι} {x : X} : x ∈ powChart L J ↔ x ∈ L.U (J PUnit.unit) := ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem powChart_eq (J : PUnit → L.ι) : powChart L J = L.U (J PUnit.unit) := SetLike.ext fun _ => mem_powChart

theorem isLB_lbPow (hL : L.IsLB) (n : ℕ) : (lbPow L n).IsLB := LB.isLB_linComb hL _ _

theorem gm_lbPow_g (n : ℕ) (r : Z ⟶ X) (z : Z) (J J' : PUnit → L.ι) (hJ : r z ∈ powChart L J)
    (hJ' : r z ∈ powChart L J') :
    gm r z ((lbPow L n).U J ⊓ (lbPow L n).U J') ((lbPow L n).g J J') =
      gm r z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit)) ^ n := by
  refine (gm_linComb L _ _ r z J J' hJ hJ').trans ?_
  simp only [Fintype.prod_unique, Category.comp_id, zpow_natCast]

def powFn (s : (lbPow L n).Sec) (J : PUnit → L.ι) : Γ(X, powChart L J) := s.f J

theorem gs_powFn_compat (s : (lbPow L n).Sec) (r : Z ⟶ X) (z : Z) (J J' : PUnit → L.ι) (hJ : r z ∈ powChart L J)
    (hJ' : r z ∈ powChart L J') :
    gs r z _ (powFn s J) =
      (gm r z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit))).val ^ n *
        gs r z _ (powFn s J') := by
  have e := gs_compat s r z hJ hJ'
  rw [gm_lbPow_g n r z J J' hJ hJ', Units.val_pow_eq_pow_val] at e
  exact e

def powSecOfGerm (n : ℕ) (f : ∀ J : PUnit → L.ι, Γ(X, powChart L J))
    (h : ∀ (y : X) (J J' : PUnit → L.ι), y ∈ powChart L J → y ∈ powChart L J' → gs (𝟙 X) y _ (f J) =
      (gm (𝟙 X) y (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit))).val ^ n *
        gs (𝟙 X) y _ (f J')) : (lbPow L n).Sec :=
  secOfGerm (M := lbPow L n) f fun y J J' hJ hJ' => by
    rw [gm_lbPow_g n (𝟙 X) y J J' hJ hJ', Units.val_pow_eq_pow_val]
    exact h y J J' hJ hJ'

theorem mem_nonzeroLocus_iff_powFn (s : (lbPow L n).Sec) {y : X} {J : PUnit → L.ι} (hJ : y ∈ powChart L J) :
    y ∈ nonzeroLocus s ↔ IsUnit (gs (𝟙 X) y _ (powFn s J)) := mem_nonzeroLocus_iff_isUnit s hJ

theorem nonzeroLocus_pow_eq_of (s : (lbPow L n).Sec) (W : X.Opens) (hW : ∀ y ∈ W, ∃ J, y ∈ powChart L J)
    (h : ∀ (y : X) J, y ∈ powChart L J → (IsUnit (gs (𝟙 X) y _ (powFn s J)) ↔ y ∈ W)) : nonzeroLocus s = W := nonzeroLocus_eq_of s W hW h

def powSecMk (n : ℕ) (f : ∀ i, Γ(X, L.U i))
    (h : ∀ i j, resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (f i) =
      (L.g i j).val ^ n * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (f j)) : (lbPow L n).Sec :=
  powSecOfGerm n (fun J => resG X (powChart_eq J).le (f (J PUnit.unit))) fun y J J' hJ hJ' => by
    have hy : y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨mem_powChart.1 hJ, mem_powChart.1 hJ'⟩
    have e := congrArg (gs (𝟙 X) y _) (h (J PUnit.unit) (J' PUnit.unit))
    rw [gs_resG _ y _ hy, gs_mul _ y _ hy, gs_resG _ y _ hy, gs_pow _ y _ hy, gs_unit _ y _ hy] at e
    rw [gs_resG _ y _ hJ, gs_resG _ y _ hJ', e]

@[simp] theorem powFn_powSecMk (n : ℕ) (f : ∀ i, Γ(X, L.U i)) (h) (J : PUnit → L.ι) :
    powFn (powSecMk n f h) J = resG X (powChart_eq J).le (f (J PUnit.unit)) := rfl

theorem nonzeroLocus_powSecMk (n : ℕ) (f : ∀ i, Γ(X, L.U i)) (h) :
    nonzeroLocus (powSecMk n f h) = ⨆ i, X.basicOpen (f i) := by
  refine nonzeroLocus_pow_eq_of _ _ (fun y hy => ?_) fun y J hJ => ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    exact ⟨fun _ => i, mem_powChart.2 (X.basicOpen_le _ hi)⟩
  · rw [powFn_powSecMk, gs_resG _ y _ hJ, isUnit_gs_iff (𝟙 X) y _ (mem_powChart.1 hJ), Opens.mem_iSup]
    constructor
    · exact fun hy => ⟨_, hy⟩
    · rintro ⟨i, hi⟩
      have hy : y ∈ L.U i ⊓ L.U (J PUnit.unit) := ⟨X.basicOpen_le _ hi, mem_powChart.1 hJ⟩
      have e := congrArg (gs (𝟙 X) y _) (h i (J PUnit.unit))
      rw [gs_resG _ y _ hy, gs_mul _ y _ hy, gs_resG _ y _ hy, gs_pow _ y _ hy, gs_unit _ y _ hy] at e
      have hu := (isUnit_gs_iff (𝟙 X) y _ hy.1 (f i)).2 hi
      rw [e] at hu
      exact (isUnit_gs_iff (𝟙 X) y _ hy.2 _).1 (IsUnit.mul_iff.1 hu).2

def powSecFn (s : (lbPow L n).Sec) (i : L.ι) : Γ(X, L.U i) :=
  resG X (powChart_eq (fun _ => i)).ge (powFn s fun _ => i)

theorem powSecFn_compat (s : (lbPow L n).Sec) (i j : L.ι) :
    resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (powSecFn s i) =
      (L.g i j).val ^ n * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (powSecFn s j) := fn_ext fun y hy => by
  have hi : y ∈ powChart L (fun _ => i) := mem_powChart.2 hy.1
  have hj : y ∈ powChart L (fun _ => j) := mem_powChart.2 hy.2
  rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_unit _ y _ hy, gs_resG _ y _ hy, gs_resG _ y _ hy]
  unfold powSecFn
  rw [gs_resG _ y _ hy.1, gs_resG _ y _ hy.2]
  exact gs_powFn_compat s (𝟙 X) y _ _ hi hj

theorem nonzeroLocus_inf_powSecFn (s : (lbPow L n).Sec) (i : L.ι) :
    nonzeroLocus s ⊓ L.U i = X.basicOpen (powSecFn s i) := by
  refine SetLike.ext fun y => ?_
  rw [Opens.mem_inf]
  constructor
  · rintro ⟨hs, hy⟩
    refine (isUnit_gs_iff (𝟙 X) y _ hy (powSecFn s i)).1 ?_
    unfold powSecFn
    rw [gs_resG _ y _ hy]
    exact (mem_nonzeroLocus_iff_powFn s (mem_powChart.2 hy)).1 hs
  · intro hy
    have hU : y ∈ L.U i := X.basicOpen_le _ hy
    refine ⟨?_, hU⟩
    rw [mem_nonzeroLocus_iff_powFn s (J := fun _ => i) (mem_powChart.2 hU)]
    have hu := (isUnit_gs_iff (𝟙 X) y _ hU (powSecFn s i)).2 hy
    unfold powSecFn at hu
    rwa [gs_resG _ y _ hU] at hu

theorem wchart_le_const (L : LB X) (φ : Y ⟶ X) (n : ℕ) (k : Fin (n + 1) → L.ι) :
    LB.wchart L (fun _ : Fin (n + 1) => φ) k ≤
      LB.wchart L (fun _ : Fin (n + 1) => φ) k ⊓ LB.wchart L (fun _ : Fin (n + 1) => φ) fun _ => k 0 :=
  le_inf le_rfl fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0

def finPowSec {L : LB X} (hL : L.IsLB) {n : ℕ} (s : (lbPow L (n + 1)).Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)).Sec :=
  secOfGerm (fun k => (res (wchart_le_const L φ n k)
      ((LB.LinComb L (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)).g k fun _ => k 0)).val *
      (φ.appLE _ _ (LB.wchart_le L (fun _ : Fin (n + 1) => φ) k 0)).hom (powSecFn s (k 0)))
    fun y k k' hk hk' => by
      have hM := LB.isLB_linComb hL (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)
      have h₀ := (wchart_le_const L φ n k hk).2
      have h₀' := (wchart_le_const L φ n k' hk').2
      have hy : φ y ∈ L.U (k 0) ⊓ L.U (k' 0) := ⟨Set.mem_iInter.1 hk 0, Set.mem_iInter.1 hk' 0⟩
      have e := congrArg (gs φ y _) (powSecFn_compat s (k 0) (k' 0))
      rw [gs_resG _ y _ hy, gs_mul _ y _ hy, gs_resG _ y _ hy, gs_pow _ y _ hy, gs_unit _ y _ hy] at e
      have e₀ := gm_linComb L (fun _ : Fin (n + 1) => φ) (fun _ => 1) (𝟙 Y) y _ _ h₀ h₀'
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_one, Category.id_comp] at e₀
      have c₁ := gm_cocycle hM (𝟙 Y) y hk h₀ h₀'
      have c₂ := gm_cocycle hM (𝟙 Y) y hk hk' h₀'
      have v : ∀ (k : Fin (n + 1) → L.ι) (hk : y ∈ LB.wchart L (fun _ : Fin (n + 1) => φ) k),
          gs (𝟙 Y) y _ ((res (wchart_le_const L φ n k)
            ((LB.LinComb L (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)).g k fun _ => k 0)).val *
            (φ.appLE _ _ (LB.wchart_le L (fun _ : Fin (n + 1) => φ) k 0)).hom (powSecFn s (k 0))) =
          (gm (𝟙 Y) y _
            ((LB.LinComb L (K := Fin (n + 1)) (fun _ => φ) (fun _ => 1)).g k fun _ => k 0)).val *
            gs φ y _ (powSecFn s (k 0)) := fun k hk =>
        (gs_mul _ y _ hk _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hk _).trans
          (congrArg Units.val (gm_res _ y _ hk _)))
          ((gs_appLE φ _ _ _ (𝟙 Y) y hk _).trans (by rw [Category.id_comp])))
      refine (v k hk).trans (Eq.trans ?_ (congrArg (_ * ·) (v k' hk')).symm)
      rw [e, ← Units.val_pow_eq_pow_val, ← e₀, ← mul_assoc, ← mul_assoc]
      exact congrArg (· * _) (congrArg Units.val (c₁.trans c₂.symm))

theorem exists_gs_finPowSec {L : LB X} (hL : L.IsLB) {n : ℕ} (φ : Y ⟶ X) (y : Y)
    (k : Fin (n + 1) → L.ι) (hk : y ∈ LB.wchart L (fun _ : Fin (n + 1) => φ) k) :
    ∃ v : (Y.presheaf.stalk y)ˣ, ∀ s : (lbPow L (n + 1)).Sec,
      gs (𝟙 Y) y _ ((finPowSec hL s φ).f k) = v.val * gs φ y _ (powSecFn s (k 0)) :=
  ⟨_, fun _ => (gs_mul _ y _ hk _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hk _)
    ((gs_appLE φ _ _ _ (𝟙 Y) y hk _).trans (by rw [Category.id_comp])))⟩

theorem nonzeroLocus_finPowSec {L : LB X} (hL : L.IsLB) {n : ℕ} (s : (lbPow L (n + 1)).Sec)
    (φ : Y ⟶ X) : nonzeroLocus (finPowSec hL s φ) = φ ⁻¹ᵁ nonzeroLocus s := by
  refine nonzeroLocus_eq_of _ _ (fun y _ => exists_chart (LB.isLB_linComb hL _ _) y) fun y k hk => ?_
  obtain ⟨v, hv⟩ := exists_gs_finPowSec hL φ y k hk
  have hy : φ y ∈ L.U (k 0) := Set.mem_iInter.1 hk 0
  rw [hv, Units.isUnit_units_mul, isUnit_gs_iff φ y _ hy, ← nonzeroLocus_inf_powSecFn]
  exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩

theorem eval₂Hom_surjective_of_isPushout {A B C D : CommRingCat.{0}} {a : A ⟶ B} {b : A ⟶ C}
    {inl : B ⟶ D} {inr : C ⟶ D} (po : IsPushout a b inl inr) {R σ : Type} [CommRing R]
    (c : R →+* A) (r : σ → B) (h : Function.Surjective (MvPolynomial.eval₂Hom (a.hom.comp c) r)) :
    Function.Surjective (MvPolynomial.eval₂Hom inr.hom fun j => inl.hom (r j)) := by
  rw [← RingHom.range_eq_top, ← top_le_iff,
    ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
  · obtain ⟨p, rfl⟩ := h d
    refine ⟨MvPolynomial.map (b.hom.comp c) p, ?_⟩
    have e : inr.hom.comp b.hom = inl.hom.comp a.hom := congrArg CommRingCat.Hom.hom po.w.symm
    rw [MvPolynomial.eval₂Hom_map_hom, ← RingHom.comp_assoc, e, RingHom.comp_assoc]
    exact (MvPolynomial.map_eval₂Hom _ _ _ p).symm
  · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end RHLean.Geometry.NativeCM.SchemeTheory
