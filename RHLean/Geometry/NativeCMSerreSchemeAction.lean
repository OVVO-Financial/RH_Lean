import Mathlib

/-!
# Actual scalar actions on group schemes and their natural point modules

An action consists of actual scheme morphisms and proved group/ring laws.
Its point modules are bundled with that action, and precomposition and
postcomposition are proved linear. Natural linear point maps yield actual
scheme morphisms by the elementary Yoneda construction.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/
ToroidalCompactification/IsGrpPullback.lean (`OAct`), and
src/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/
PowObjGeometricallyConnected.lean (point-module and Yoneda declarations).
The source archive states no license; attribution is retained without
assigning one. No polarized-variety or tensor representability premise is
introduced by this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SerreScheme

variable {S : Scheme.{0}}

structure OAct (O : Type) [CommRing O] (G : Over S) [GrpObj G] where
  act : O → (G ⟶ G)
  hom : ∀ a, IsMonHom (act a)
  one : act 1 = 𝟙 G
  mul : ∀ a b, act (a * b) = act a ≫ act b
  add : ∀ a b, act (a + b) = act a * act b

section Hom

variable {G H : Over S} [GrpObj G] [GrpObj H]

theorem isMonHom_of_mul_comp (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G => x ≫ f) (h _))
  mul_hom := by
    rw [MonObj.mul_eq_mul, h, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp

theorem isMonHom_mul [IsCommMonObj H] (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] :
    IsMonHom (f * g) :=
  isMonHom_of_mul_comp _ fun _ _ _ => by
    simp only [MonObj.comp_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

theorem isMonHom_one : IsMonHom (1 : G ⟶ H) :=
  isMonHom_of_mul_comp _ fun _ _ _ => by simp

end Hom

section Points

variable {O : Type} [CommRing O] {G H K : Over S} [GrpObj G] [GrpObj H] [GrpObj K]

theorem act_zero (a : OAct O G) : a.act 0 = 1 := by
  have h := a.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem act_comm (a : OAct O G) (c d : O) : a.act c ≫ a.act d = a.act d ≫ a.act c := by
  rw [← a.mul, ← a.mul, mul_comm]

structure IsLinearHom (a : OAct O G) (b : OAct O H) (f : G ⟶ H) : Prop where
  isMonHom : IsMonHom f
  comm : ∀ c : O, a.act c ≫ f = f ≫ b.act c

theorem IsLinearHom.id (a : OAct O G) : IsLinearHom a a (𝟙 G) :=
  ⟨inferInstance, fun _ => by simp⟩

theorem IsLinearHom.comp {a : OAct O G} {b : OAct O H} {c : OAct O K}
    {f : G ⟶ H} {g : H ⟶ K} (hf : IsLinearHom a b f) (hg : IsLinearHom b c g) :
    IsLinearHom a c (f ≫ g) :=
  ⟨by have := hf.1; have := hg.1; infer_instance, fun _ => by
    rw [← Category.assoc, hf.comm, Category.assoc, hg.comm, Category.assoc]⟩

theorem IsLinearHom.act (a : OAct O G) (c : O) : IsLinearHom a a (a.act c) :=
  ⟨a.hom c, fun d => act_comm a d c⟩

variable [IsCommMonObj G] [IsCommMonObj H] [IsCommMonObj K]

/-- The action on points is composition with the actual scheme morphism. -/
def pointsModule (a : OAct O G) (T : Over S) : Module O (Additive (T ⟶ G)) where
  smul c x := Additive.ofMul (x.toMul ≫ a.act c)
  one_smul x := by
    change Additive.ofMul (x.toMul ≫ a.act 1) = x
    rw [a.one, Category.comp_id]
    rfl
  mul_smul c d x := by
    change Additive.ofMul (x.toMul ≫ a.act (c * d)) =
      Additive.ofMul ((x.toMul ≫ a.act d) ≫ a.act c)
    rw [mul_comm, a.mul, Category.assoc]
  smul_zero c := by
    have := a.hom c
    exact congrArg Additive.ofMul (MonObj.one_comp (a.act c))
  smul_add c x y := by
    have := a.hom c
    exact congrArg Additive.ofMul (MonObj.mul_comp x.toMul y.toMul (a.act c))
  add_smul c d x := by
    change Additive.ofMul (x.toMul ≫ a.act (c + d)) =
      Additive.ofMul ((x.toMul ≫ a.act c) * (x.toMul ≫ a.act d))
    rw [a.add, MonObj.comp_mul]
  zero_smul x := by
    change Additive.ofMul (x.toMul ≫ a.act 0) = Additive.ofMul 1
    rw [act_zero, MonObj.comp_one]

/-- Bundling retains the actual action in the module data. -/
def Pts (a : OAct O G) (T : Over S) : ModuleCat O :=
  let _ : Module O (Additive (T ⟶ G)) := pointsModule a T
  ModuleCat.of O (Additive (T ⟶ G))

namespace Pts

variable {a : OAct O G} {b : OAct O H} {c : OAct O K} {T T' T'' : Over S}

def mk (a : OAct O G) : (T ⟶ G) ≃ Pts a T := Additive.ofMul

def hom (x : Pts a T) : T ⟶ G := Additive.toMul x

@[simp] theorem hom_mk (x : T ⟶ G) : (mk a x).hom = x := rfl

@[simp] theorem mk_hom (x : Pts a T) : mk a x.hom = x := rfl

@[ext] theorem ext {x y : Pts a T} (h : x.hom = y.hom) : x = y := h

@[simp] theorem hom_zero : (0 : Pts a T).hom = 1 := rfl

@[simp] theorem hom_add (x y : Pts a T) : (x + y).hom = x.hom * y.hom := rfl

@[simp] theorem hom_neg (x : Pts a T) : (-x).hom = x.hom⁻¹ := rfl

@[simp] theorem hom_sub (x y : Pts a T) : (x - y).hom = x.hom / y.hom := rfl

@[simp] theorem hom_smul (r : O) (x : Pts a T) : (r • x).hom = x.hom ≫ a.act r := rfl

theorem mk_one : mk a (1 : T ⟶ G) = 0 := rfl

theorem mk_mul (x y : T ⟶ G) : mk a (x * y) = mk a x + mk a y := rfl

theorem mk_comp_act (x : T ⟶ G) (r : O) : mk a (x ≫ a.act r) = r • mk a x := rfl

def pre (a : OAct O G) (u : T' ⟶ T) : Pts a T →ₗ[O] Pts a T' where
  toFun x := mk a (u ≫ x.hom)
  map_add' x y := ext (MonObj.comp_mul u x.hom y.hom)
  map_smul' r x := ext (Category.assoc u x.hom (a.act r)).symm

@[simp] theorem hom_pre (u : T' ⟶ T) (x : Pts a T) : (pre a u x).hom = u ≫ x.hom := rfl

@[simp] theorem pre_id : pre a (𝟙 T) = LinearMap.id := by
  ext x
  simp

theorem pre_comp (v : T'' ⟶ T') (u : T' ⟶ T) : pre a (v ≫ u) = pre a v ∘ₗ pre a u := by
  ext x
  simp

def post {f : G ⟶ H} (hf : IsLinearHom a b f) (T : Over S) : Pts a T →ₗ[O] Pts b T where
  toFun x := mk b (x.hom ≫ f)
  map_add' x y := ext (by have := hf.1; exact MonObj.mul_comp x.hom y.hom f)
  map_smul' _ _ := ext (by simp [hf.comm])

@[simp] theorem hom_post {f : G ⟶ H} (hf : IsLinearHom a b f) (x : Pts a T) :
    (post hf T x).hom = x.hom ≫ f := rfl

theorem pre_post {f : G ⟶ H} (hf : IsLinearHom a b f) (u : T' ⟶ T) (x : Pts a T) :
    pre b u (post hf T x) = post hf T' (pre a u x) := by
  ext
  simp

section Yoneda

variable (φ : ∀ T : Over S, Pts a T →ₗ[O] Pts b T)

/-- The actual scheme morphism extracted from a natural linear point map. -/
def homOfNat : G ⟶ H := (φ G (mk a (𝟙 G))).hom

variable (hφ : ∀ {T T' : Over S} (u : T' ⟶ T) (x : Pts a T),
  φ T' (pre a u x) = pre b u (φ T x))
include hφ

theorem comp_homOfNat (x : T ⟶ G) : x ≫ homOfNat φ = (φ T (mk a x)).hom := by
  have h := congrArg hom (hφ x (mk a (𝟙 G)))
  rw [hom_pre] at h
  rw [homOfNat, ← h]
  congr 2

theorem isLinearHom_homOfNat : IsLinearHom a b (homOfNat φ) where
  isMonHom := isMonHom_of_mul_comp _ fun _ _ _ => by
    simp only [comp_homOfNat φ hφ, mk_mul, map_add, hom_add]
  comm r := by
    rw [comp_homOfNat φ hφ, ← Category.id_comp (a.act r), mk_comp_act, map_smul]
    rfl

end Yoneda
end Pts
end Points

end RHLean.Geometry.NativeCM.SerreScheme

end
