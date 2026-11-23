import Mathlib

/-!
# Actual line-bundle atlases and their two-chart sections

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/CubicalStructures/CubeSymmetricSwapFirst.lean`
- `src/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/BijectiveSmulChartSec.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsUniqueEqConstMulOriginSec.lean`
- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean`
- `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/NonzeroLocus.lean`

These are open-cover unit transition data with the full cocycle law and compatible
sections. They are used to construct the origin bundle on the actual integral cubic;
no ampleness, symmetry, or polarization-kernel property is assumed.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace RHLean.Geometry.NativeCM.SchemeTheory

def resG (X : Scheme.{u}) {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

def res {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U)ˣ →* Γ(X, V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom

def pullU {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) : Γ(X, U)ˣ →* Γ(Y, f ⁻¹ᵁ U)ˣ :=
  Units.map (f.app U).hom

structure LB (X : Scheme.{u}) where
  ι : Type u
  U : ι → X.Opens
  g : ∀ i j, Γ(X, U i ⊓ U j)ˣ

structure LB.IsLB {X : Scheme.{u}} (L : LB X) : Prop where
  cover : ⨆ i, L.U i = ⊤
  g_self : ∀ i, res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (L.g i i) = 1
  cocycle : ∀ i j k,
    res (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) (L.g i j) *
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) (L.g j k) =
    res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) (L.g i k)

namespace LB

variable {X Y Z : Scheme.{u}}

structure Gen (L : LB X) where
  s : ∀ i, Γ(X, L.U i)ˣ

def Gen.IsGen {L : LB X} (t : Gen L) : Prop :=
  ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i) =
    L.g i j * res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j)

structure Sec (L : LB X) where
  f : ∀ i, Γ(X, L.U i)
  compat : ∀ i j, (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom (f i) =
    (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
      (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom (f j)

def div (M L : LB X) : LB X where
  ι := M.ι × L.ι
  U := fun p => M.U p.1 ⊓ L.U p.2
  g := fun p q =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
    (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹

abbrev Iso (L M : LB X) := Gen (div M L)

def wchart (L : LB X) {K : Type u} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι) : Y.Opens :=
  ⟨⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X),
    isOpen_iInter_of_finite fun k => (L.U (j k)).isOpen.preimage (φ k).base.hom.continuous⟩

lemma wchart_le (L : LB X) {K : Type u} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι) (k : K) :
    wchart L φ j ≤ φ k ⁻¹ᵁ L.U (j k) :=
  fun _ hy => Set.mem_iInter.1 hy k

def LinComb (L : LB X) {K : Type u} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : LB Y where
  ι := K → L.ι
  U := wchart L φ
  g := fun j j' => ∏ k, (res (le_inf (inf_le_left.trans (wchart_le L φ j k))
      (inf_le_right.trans (wchart_le L φ j' k)) :
        wchart L φ j ⊓ wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
      (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)

abbrev pull (L : LB X) (f : Y ⟶ X) : LB Y := LinComb L (K := PUnit) (fun _ => f) (fun _ => 1)

end LB

section Restriction

variable {X : Scheme.{u}}

theorem resG_resG {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _
  rw [← Functor.map_comp]
  rfl

theorem resG_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  change (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show homOfLE h = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem val_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res h u : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (u : Γ(X, U)) := rfl


end Restriction

section Base

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

def baseRingHom (p : X ⟶ Spec R) (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ U le_top

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_res (p : X ⟶ Spec R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseRingHom p U r) = baseRingHom p V r := by
  rw [← ConcreteCategory.comp_apply, baseRingHom, Category.assoc, Scheme.Hom.appLE_map]
  rfl

theorem baseRingHom_top (p : X ⟶ Spec R) :
    baseRingHom p ⊤ = (Scheme.ΓSpecIso R).inv ≫ p.appTop := by
  rw [baseRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_app (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) :
    baseRingHom p U ≫ g.app U = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) := by
  rw [baseRingHom, baseRingHom, Category.assoc, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]

theorem app_baseRingHom (g : Y ⟶ X) (p : X ⟶ Spec R) (U : X.Opens) (r : R) :
    g.app U (baseRingHom p U r) = baseRingHom (g ≫ p) (g ⁻¹ᵁ U) r := by
  rw [← baseRingHom_comp_app]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem baseRingHom_comp_SpecMap {L : CommRingCat.{u}} (q : Y ⟶ Spec L) (ι : R ⟶ L)
    (V : Y.Opens) : baseRingHom (q ≫ Spec.map ι) V = ι ≫ baseRingHom q V := by
  rw [baseRingHom, baseRingHom, Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  exact congrArg _ (Scheme.Hom.appLE_comp_appLE q (Spec.map ι) ⊤ ⊤ V le_top le_top).symm

end Base

namespace LB

variable {X : Scheme.{u}}

lemma res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl


end LB

namespace LB

variable {X : Scheme.{0}}

def twoChart (U₀ U₁ : X.Opens) (u : Γ(X, U₀ ⊓ U₁)ˣ) : LB X where
  ι := Bool
  U i := cond i U₀ U₁
  g i j := match i, j with
    | true, true => 1
    | true, false => u
    | false, true => (res (le_inf inf_le_right inf_le_left) u)⁻¹
    | false, false => 1

theorem twoChart_isLB {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (u : Γ(X, U₀ ⊓ U₁)ˣ) :
    (twoChart U₀ U₁ u).IsLB where
  cover := (iSup_bool_eq (f := fun i => cond i U₀ U₁)).trans h
  g_self := by rintro (_ | _) <;> exact map_one _
  cocycle := by
    have aux {W : X.Opens} (h₁ : W ≤ U₁ ⊓ U₀) (h₂ : W ≤ U₀ ⊓ U₁) :
        res h₁ (res (le_inf inf_le_right inf_le_left) u)⁻¹ * res h₂ u = 1 := by
      rw [map_inv, res_res, inv_mul_cancel]
    rintro (_ | _) (_ | _) (_ | _)
    · exact (congrArg (· * _) (map_one _)).trans (one_mul _)
    · exact (congrArg (· * _) (map_one _)).trans (one_mul _)
    · exact (aux _ _).trans (map_one _).symm
    · exact (congrArg (_ * ·) (map_one _)).trans (mul_one _)
    · exact (congrArg (_ * ·) (map_one _)).trans (mul_one _)
    · exact ((mul_comm _ _).trans (aux _ _)).trans (map_one _).symm
    · exact (congrArg (· * _) (map_one _)).trans (one_mul _)
    · exact (congrArg (· * _) (map_one _)).trans (one_mul _)

variable {Y : Scheme.{0}} {U₀ U₁ : X.Opens} (u : Γ(X, U₀ ⊓ U₁)ˣ)

def twoChartFn (a : Γ(X, U₀)) (b : Γ(X, U₁)) : ∀ i, Γ(X, (twoChart U₀ U₁ u).U i)
  | true => a
  | false => b

theorem twoChartFn_compat (n : ℕ) {a : Γ(X, U₀)} {b : Γ(X, U₁)}
    (h : resG X inf_le_left a = (u : Γ(X, U₀ ⊓ U₁)) ^ n * resG X inf_le_right b) (i j : Bool) :
    resG X (inf_le_left : (twoChart U₀ U₁ u).U i ⊓ (twoChart U₀ U₁ u).U j ≤ _) (twoChartFn u a b i) =
      ((twoChart U₀ U₁ u).g i j).val ^ n * resG X inf_le_right (twoChartFn u a b j) := by
  rcases i with _ | _ <;> rcases j with _ | _
  · exact ((congrArg (· * _) (one_pow n)).trans (one_mul _)).symm
  · have l : U₁ ⊓ U₀ ≤ U₀ ⊓ U₁ := le_inf inf_le_right inf_le_left
    have e := congrArg (resG X l) h
    simp only [map_mul, map_pow, resG_resG] at e
    change resG X (inf_le_left : U₁ ⊓ U₀ ≤ U₁) b = ((res l u)⁻¹).val ^ n *
      resG X (inf_le_right : U₁ ⊓ U₀ ≤ U₀) a
    rw [e, ← val_res, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  · exact h
  · exact ((congrArg (· * _) (one_pow n)).trans (one_mul _)).symm

def twoChartSec (a : Γ(X, U₀)) (b : Γ(X, U₁))
    (h : resG X inf_le_left a = (u : Γ(X, U₀ ⊓ U₁)) * resG X inf_le_right b) :
    (twoChart U₀ U₁ u).Sec where
  f := twoChartFn u a b
  compat i j := (twoChartFn_compat u 1 (by rwa [pow_one]) i j).trans (by rw [pow_one])

end LB

def nonzeroLocus {Y : Scheme.{0}} {L : LB Y} (s : LB.Sec L) : Y.Opens :=
  ⨆ k, Y.basicOpen (s.f k)

theorem basicOpen_le_nonzeroLocus {Y : Scheme.{0}} {L : LB Y} (s : LB.Sec L) (k : L.ι) :
    Y.basicOpen (s.f k) ≤ nonzeroLocus s := le_iSup (fun i => Y.basicOpen (s.f i)) k

end RHLean.Geometry.NativeCM.SchemeTheory
