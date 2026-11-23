import RHLean.Geometry.NativeCMSerreSchemeAction
import RHLean.Geometry.NativeCMSerreTensor

/-!
# The represented Serre tensor from the original trace-Hermitian frame

The finite product of the given group scheme is constructed, its matrix
endomorphism is induced by the actual trace frame, and the Serre scheme is
the equalizer of that idempotent with the identity. The proved retraction
gives its commutative group structure and natural tensor equivalences on
points over every test scheme. Coefficient endomorphisms induce actual
scheme morphisms by naturality. No representing object is assumed.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/
DegProd.lean (finite powers), and
src/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/
PowObjGeometricallyConnected.lean (tensor functor, equalizer and retraction).
Only these categorical constructions are used. The original native trace
frame supplies the summand; no free replacement for B^-1 is made. The
source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical TensorProduct Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SerreScheme

open Pts

variable {S : Scheme.{0}}

/-- Naturality expresses a represented tensor functor on actual schemes. -/
structure IsTensor {O : Type} [CommRing O]
    (H : Over S) [GrpObj H] [IsCommMonObj H] (b : OAct O H)
    (G : Over S) [GrpObj G] [IsCommMonObj G] (a : OAct O G)
    (M : Type) [AddCommGroup M] [Module O M] where
  equiv : ∀ T : Over S, M ⊗[O] Pts a T ≃ₗ[O] Pts b T
  natural : ∀ {T T' : Over S} (u : T' ⟶ T) (z : M ⊗[O] Pts a T),
    equiv T' ((Pts.pre a u).lTensor M z) = Pts.pre b u (equiv T z)

namespace IsTensor

variable {O : Type} [CommRing O]
    {G H H' H'' : Over S} [GrpObj G] [GrpObj H] [GrpObj H'] [GrpObj H'']
    [IsCommMonObj G] [IsCommMonObj H] [IsCommMonObj H'] [IsCommMonObj H'']
    {a : OAct O G} {b : OAct O H} {b' : OAct O H'} {b'' : OAct O H''}
    {M M' M'' : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']
    {T T' : Over S}
    (h : IsTensor H b G a M)

theorem natural_symm (u : T' ⟶ T) (y : Pts b T) :
    (h.equiv T').symm (Pts.pre b u y) = (Pts.pre a u).lTensor M ((h.equiv T).symm y) := by
  rw [LinearEquiv.symm_apply_eq, h.natural, LinearEquiv.apply_symm_apply]

def tmul (m : M) : G ⟶ H := (h.equiv G (m ⊗ₜ[O] Pts.mk a (𝟙 G))).hom

@[simp] theorem hom_equiv_tmul (m : M) (x : Pts a T) :
    (h.equiv T (m ⊗ₜ[O] x)).hom = x.hom ≫ h.tmul m := by
  have e := congrArg Pts.hom (h.natural x.hom (m ⊗ₜ[O] Pts.mk a (𝟙 G)))
  rw [Pts.hom_pre, LinearMap.lTensor_tmul] at e
  rw [tmul, ← e]
  congr 3

theorem isLinearHom_tmul (m : M) : IsLinearHom a b (h.tmul m) :=
  Pts.isLinearHom_homOfNat
    (fun T => (h.equiv T).toLinearMap ∘ₗ TensorProduct.mk O M _ m)
    (fun _ _ => by ext; simp)

instance isMonHom_tmul (m : M) : IsMonHom (h.tmul m) := (h.isLinearHom_tmul m).isMonHom

@[simp] theorem tmul_zero : h.tmul 0 = 1 := by simp [tmul]

theorem tmul_add (m n : M) : h.tmul (m + n) = h.tmul m * h.tmul n := by
  simp only [tmul, TensorProduct.add_tmul, map_add, Pts.hom_add]

theorem tmul_smul (c : O) (m : M) : h.tmul (c • m) = h.tmul m ≫ b.act c := by
  simp only [tmul, ← TensorProduct.smul_tmul', map_smul, Pts.hom_smul]

theorem hom_ext {K : Over S} [GrpObj K] {f g : H ⟶ K} [IsMonHom f] [IsMonHom g]
    (e : ∀ m : M, h.tmul m ≫ f = h.tmul m ≫ g) : f = g := by
  obtain ⟨z, hz⟩ := (h.equiv H).surjective (Pts.mk b (𝟙 H))
  have heq : ∀ z : M ⊗[O] Pts a H,
      (h.equiv H z).hom ≫ f = (h.equiv H z).hom ≫ g := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m x => simp only [hom_equiv_tmul, Category.assoc, e]
    | add z w hz hw =>
      simp only [map_add, Pts.hom_add, MonObj.mul_comp, hz, hw]
  simpa only [hz, Pts.hom_mk, Category.id_comp] using heq z

variable (h' : IsTensor H' b' G a M') (h'' : IsTensor H'' b'' G a M'')

def mapLeftPoints (φ : M →ₗ[O] M') (T : Over S) : Pts b T →ₗ[O] Pts b' T :=
  (h'.equiv T).toLinearMap ∘ₗ φ.rTensor (Pts a T) ∘ₗ (h.equiv T).symm.toLinearMap

theorem mapLeftPoints_natural (φ : M →ₗ[O] M') (u : T' ⟶ T) (y : Pts b T) :
    h.mapLeftPoints h' φ T' (Pts.pre b u y) = Pts.pre b' u (h.mapLeftPoints h' φ T y) := by
  simp only [mapLeftPoints, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h.natural_symm, ← h'.natural]
  congr 1
  induction (h.equiv T).symm y using TensorProduct.inductionOn with
  | tmul m x => rfl
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Coefficient maps are actual scheme morphisms induced on the represented
point functor. -/
def mapLeft (φ : M →ₗ[O] M') : H ⟶ H' :=
  Pts.homOfNat (h.mapLeftPoints h' φ)

theorem isLinearHom_mapLeft (φ : M →ₗ[O] M') : IsLinearHom b b' (h.mapLeft h' φ) :=
  Pts.isLinearHom_homOfNat _ (h.mapLeftPoints_natural h' φ)

instance isMonHom_mapLeft (φ : M →ₗ[O] M') : IsMonHom (h.mapLeft h' φ) :=
  (h.isLinearHom_mapLeft h' φ).isMonHom

theorem hom_equiv_comp_mapLeft (φ : M →ₗ[O] M') (z : M ⊗[O] Pts a T) :
    (h.equiv T z).hom ≫ h.mapLeft h' φ = (h'.equiv T (φ.rTensor (Pts a T) z)).hom := by
  rw [mapLeft, Pts.comp_homOfNat _ (h.mapLeftPoints_natural h' φ)]
  change (h'.equiv T (φ.rTensor (Pts a T)
    ((h.equiv T).symm (Pts.mk b (h.equiv T z).hom)))).hom = _
  rw [Pts.mk_hom, LinearEquiv.symm_apply_apply]

@[reassoc (attr := simp)]
theorem tmul_mapLeft (φ : M →ₗ[O] M') (m : M) :
    h.tmul m ≫ h.mapLeft h' φ = h'.tmul (φ m) := by
  simpa only [tmul, LinearMap.rTensor_tmul] using
    h.hom_equiv_comp_mapLeft h' φ (m ⊗ₜ[O] Pts.mk a (𝟙 G))

@[simp] theorem mapLeft_id : h.mapLeft h LinearMap.id = 𝟙 H :=
  h.hom_ext fun _ => by simp

theorem mapLeft_comp (φ : M →ₗ[O] M') (ψ : M' →ₗ[O] M'') :
    h.mapLeft h'' (ψ ∘ₗ φ) = h.mapLeft h' φ ≫ h'.mapLeft h'' ψ :=
  h.hom_ext fun _ => by simp

theorem mapLeft_add (φ ψ : M →ₗ[O] M') :
    h.mapLeft h' (φ + ψ) = h.mapLeft h' φ * h.mapLeft h' ψ := by
  have := isMonHom_mul (h.mapLeft h' φ) (h.mapLeft h' ψ)
  exact h.hom_ext fun _ => by simp [MonObj.comp_mul, tmul_add]

theorem mapLeft_smul (c : O) (φ : M →ₗ[O] M') :
    h.mapLeft h' (c • φ) = h.mapLeft h' φ ≫ b'.act c := by
  have := b'.hom c
  exact h.hom_ext fun _ => by simp [tmul_smul]

end IsTensor

section Powers

def powObj (G : Over S) : ℕ → Over S
  | 0 => 𝟙_ (Over S)
  | n + 1 => G ⊗ powObj G n

instance powObj.grp (G : Over S) [GrpObj G] : ∀ n, GrpObj (powObj G n)
  | 0 => inferInstanceAs (GrpObj (𝟙_ (Over S)))
  | n + 1 => by
    have := powObj.grp G n
    exact inferInstanceAs (GrpObj (G ⊗ powObj G n))

instance powObj.comm (G : Over S) [GrpObj G] [IsCommMonObj G] : ∀ n, IsCommMonObj (powObj G n)
  | 0 => inferInstanceAs (IsCommMonObj (𝟙_ (Over S)))
  | n + 1 => by
    have := powObj.comm G n
    exact inferInstanceAs (IsCommMonObj (G ⊗ powObj G n))

def powPr (G : Over S) : ∀ {n : ℕ}, Fin n → (powObj G n ⟶ G)
  | _ + 1, ⟨0, _⟩ => fst _ _
  | n + 1, ⟨i + 1, hi⟩ => snd _ _ ≫ powPr G (n := n) ⟨i, Nat.lt_of_succ_lt_succ hi⟩

instance powPr.isMonHom (G : Over S) [GrpObj G] : ∀ {n : ℕ} (i : Fin n), IsMonHom (powPr G i)
  | _ + 1, ⟨0, _⟩ => inferInstanceAs (IsMonHom (fst _ _))
  | n + 1, ⟨i + 1, hi⟩ => by
    have := powPr.isMonHom G (n := n) ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    exact inferInstanceAs (IsMonHom (snd _ _ ≫ powPr G (n := n) ⟨i, Nat.lt_of_succ_lt_succ hi⟩))

def powIsLimit (G : Over S) : ∀ n : ℕ, IsLimit (Fan.mk (powObj G n) (powPr G (n := n)))
  | 0 => mkFanLimit _ (fun s => toUnit s.pt) (fun _ i => i.elim0) (fun _ _ _ => toUnit_unique _ _)
  | n + 1 =>
    mkFanLimit _
      (fun s => lift (s.proj 0) ((powIsLimit G n).lift (Fan.mk s.pt (fun i => s.proj i.succ))))
      (fun s i => by
        refine Fin.cases ?_ (fun i => ?_) i
        · exact lift_fst _ _
        · exact (lift_snd_assoc _ _ _).trans
            ((powIsLimit G n).fac (Fan.mk s.pt fun i => s.proj i.succ) ⟨i⟩))
      (fun s m hm => by
        apply CartesianMonoidalCategory.hom_ext
        · have h0 : m ≫ powPr G 0 = s.proj 0 := hm 0
          exact h0.trans (lift_fst _ _).symm
        · refine Eq.trans ?_ (lift_snd _ _).symm
          apply (powIsLimit G n).hom_ext
          rintro ⟨i⟩
          have hi : m ≫ snd _ _ ≫ powPr G i = s.proj i.succ := hm i.succ
          exact ((Category.assoc _ _ _).trans hi).trans
            ((powIsLimit G n).fac (Fan.mk s.pt fun i => s.proj i.succ) ⟨i⟩).symm)

structure IsPowGrp (G' G : Over S) [GrpObj G'] [GrpObj G] (n : ℕ) where
  pr : Fin n → (G' ⟶ G)
  hom : ∀ i, IsMonHom (pr i)
  lim : IsLimit (Fan.mk G' pr)

def powIsPowGrp (G : Over S) [GrpObj G] (n : ℕ) : IsPowGrp (powObj G n) G n :=
  ⟨powPr G, fun _ => inferInstance, powIsLimit G n⟩

variable {O : Type} [CommRing O] {G G' : Over S} [GrpObj G] [GrpObj G']

theorem pow_hom_ext {n : ℕ} (p : IsPowGrp G' G n) {T : Over S} {x y : T ⟶ G'}
    (e : ∀ i, x ≫ p.pr i = y ≫ p.pr i) : x = y := p.lim.hom_ext fun i => e i.as

def powLift {n : ℕ} (p : IsPowGrp G' G n) {T : Over S} (x : Fin n → (T ⟶ G)) : T ⟶ G' :=
  p.lim.lift (Fan.mk T x)

@[reassoc (attr := simp)]
theorem powLift_pr {n : ℕ} (p : IsPowGrp G' G n) {T : Over S}
    (x : Fin n → (T ⟶ G)) (i : Fin n) : powLift p x ≫ p.pr i = x i :=
  p.lim.fac (Fan.mk T x) ⟨i⟩

def powAct {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) : OAct O G' where
  act c := powLift p fun i => p.pr i ≫ a.act c
  hom c := isMonHom_of_mul_comp _ fun _ _ _ => pow_hom_ext p fun i => by
    have := p.hom i
    have := a.hom c
    simp [MonObj.mul_comp, MonObj.mul_comp_assoc]
  one := pow_hom_ext p fun _ => by simp [a.one]
  mul _ _ := pow_hom_ext p fun _ => by simp [a.mul]
  add _ _ := pow_hom_ext p fun i => by
    have := p.hom i
    simp [a.add, MonObj.mul_comp, MonObj.comp_mul]

@[reassoc (attr := simp)]
theorem powAct_act_pr {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) (c : O) (i : Fin n) :
    (powAct p a).act c ≫ p.pr i = p.pr i ≫ a.act c := powLift_pr p _ i

theorem isLinearHom_pr {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) (i : Fin n) :
    IsLinearHom (powAct p a) a (p.pr i) :=
  ⟨p.hom i, fun c => powAct_act_pr p a c i⟩

variable [IsCommMonObj G] [IsCommMonObj G']

def Pts.powEquiv {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) (T : Over S) :
    Pts (powAct p a) T ≃ₗ[O] (Fin n → Pts a T) where
  __ := LinearMap.pi fun i => Pts.post (isLinearHom_pr p a i) T
  invFun y := Pts.mk _ (powLift p fun i => (y i).hom)
  left_inv _ := Pts.ext (pow_hom_ext p fun _ => by simp)
  right_inv _ := by ext; simp

def IsTensor.pow {n : ℕ} (p : IsPowGrp G' G n) (a : OAct O G) :
    IsTensor G' (powAct p a) G a (Fin n → O) where
  equiv T := TensorProduct.comm O _ _ ≪≫ₗ
    TensorProduct.piScalarRight O O (Pts a T) (Fin n) ≪≫ₗ (Pts.powEquiv p a T).symm
  natural _ z := by
    induction z using TensorProduct.inductionOn with
    | tmul m x => exact Pts.ext (pow_hom_ext p fun _ => by simp)
    | add z w hz hw => simp only [map_add, hz, hw]

end Powers

section Idempotent

variable {K : Over S} [GrpObj K]

/-- The group laws are transported along an actual scheme retraction. -/
@[reducible] def grpObjOfRetract {H : Over S} (i : H ⟶ K) (r : K ⟶ H)
    (hir : i ≫ r = 𝟙 H) [IsMonHom (r ≫ i)] : GrpObj H := by
  have : Mono i := (SplitMono.mk r hir).mono
  have hi : i ≫ r ≫ i = i := by rw [reassoc_of% hir]
  have h₁ : (1 ≫ r : 𝟙_ (Over S) ⟶ H) ≫ i = 1 := by rw [Category.assoc, MonObj.one_comp]
  have h₂ : ((fst H H ≫ i * snd H H ≫ i) ≫ r) ≫ i = fst H H ≫ i * snd H H ≫ i := by
    rw [Category.assoc, MonObj.mul_comp, Category.assoc, Category.assoc, hi]
  have h₃ : (i⁻¹ ≫ r) ≫ i = i⁻¹ := by rw [Category.assoc, GrpObj.inv_comp, hi]
  exact
    { one := 1 ≫ r
      mul := (fst H H ≫ i * snd H H ≫ i) ≫ r
      inv := i⁻¹ ≫ r
      one_mul := by
        rw [← cancel_mono i, Category.assoc, h₂, MonObj.comp_mul, whiskerRight_fst_assoc,
          whiskerRight_snd_assoc, h₁, MonObj.comp_one, _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, h₂, MonObj.comp_mul, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, h₁, MonObj.comp_one, _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono i, Category.assoc, h₂, Category.assoc, Category.assoc, h₂]
        simp only [MonObj.comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc,
          whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, h₂]
        simp [_root_.mul_assoc]
      left_inv := by
        rw [← cancel_mono i, Category.assoc, h₂, MonObj.comp_mul, lift_fst_assoc,
          lift_snd_assoc, h₃, Category.id_comp, inv_mul_cancel, Category.assoc, h₁,
          MonObj.comp_one]
      right_inv := by
        rw [← cancel_mono i, Category.assoc, h₂, MonObj.comp_mul, lift_fst_assoc,
          lift_snd_assoc, h₃, Category.id_comp, mul_inv_cancel, Category.assoc, h₁,
          MonObj.comp_one] }

def fixObj {K : Over S} (p : K ⟶ K) : Over S := equalizer p (𝟙 K)

def fixIncl {K : Over S} (p : K ⟶ K) : fixObj p ⟶ K := equalizer.ι p (𝟙 K)

instance mono_fixIncl {K : Over S} (p : K ⟶ K) : Mono (fixIncl p) :=
  inferInstanceAs (Mono (equalizer.ι p (𝟙 K)))

@[reassoc (attr := simp)]
theorem fixIncl_comp {K : Over S} (p : K ⟶ K) : fixIncl p ≫ p = fixIncl p :=
  (equalizer.condition p (𝟙 K)).trans (Category.comp_id _)

def fixProj {K : Over S} {p : K ⟶ K} (hp : p ≫ p = p) : K ⟶ fixObj p :=
  equalizer.lift p (hp.trans (Category.comp_id p).symm)

@[reassoc (attr := simp)]
theorem fixProj_incl {K : Over S} {p : K ⟶ K} (hp : p ≫ p = p) :
    fixProj hp ≫ fixIncl p = p := equalizer.lift_ι _ _

@[reassoc (attr := simp)]
theorem fixIncl_proj {K : Over S} {p : K ⟶ K} (hp : p ≫ p = p) :
    fixIncl p ≫ fixProj hp = 𝟙 _ := by
  rw [← cancel_mono (fixIncl p)]
  simp

@[reducible] def fixGrp {p : K ⟶ K} [IsMonHom p] (hp : p ≫ p = p) : GrpObj (fixObj p) :=
  have : IsMonHom (fixProj hp ≫ fixIncl p) := by rw [fixProj_incl]; infer_instance
  grpObjOfRetract (fixIncl p) (fixProj hp) (fixIncl_proj hp)

theorem isMonHom_fixIncl {p : K ⟶ K} [IsMonHom p] (hp : p ≫ p = p) :
    let _ := fixGrp hp
    IsMonHom (fixIncl p) := by
  let _ := fixGrp hp
  refine isMonHom_of_mul_comp _ fun _ x y => ?_
  change (lift x y ≫ (fst _ _ ≫ fixIncl p * snd _ _ ≫ fixIncl p) ≫ fixProj hp) ≫ fixIncl p = _
  simp [MonObj.mul_comp, MonObj.comp_mul]

theorem isMonHom_fixProj {p : K ⟶ K} [IsMonHom p] (hp : p ≫ p = p) :
    let _ := fixGrp hp
    IsMonHom (fixProj hp) := by
  let _ := fixGrp hp
  have := isMonHom_fixIncl hp
  refine isMonHom_of_mul_comp _ fun _ _ _ => ?_
  rw [← cancel_mono (fixIncl p)]
  simp [MonObj.mul_comp]

theorem isCommMonObj_fix [IsCommMonObj K] {p : K ⟶ K} [IsMonHom p] (hp : p ≫ p = p) :
    let _ := fixGrp hp
    IsCommMonObj (fixObj p) := by
  let _ := fixGrp hp
  have := isMonHom_fixIncl hp
  rw [isCommMonObj_iff_isMulCommutative]
  refine fun _ => ⟨⟨fun _ _ => ?_⟩⟩
  rw [← cancel_mono (fixIncl p), MonObj.mul_comp, MonObj.mul_comp, mul_comm]

variable {O : Type} [CommRing O] {H : Over S} [GrpObj H]

def retractAct (c : OAct O K) (i : H ⟶ K) (r : K ⟶ H) [IsMonHom i] [IsMonHom r]
    (hir : i ≫ r = 𝟙 H) (hc : ∀ x, c.act x ≫ r ≫ i = r ≫ i ≫ c.act x) : OAct O H where
  act x := i ≫ c.act x ≫ r
  hom x := by have := c.hom x; infer_instance
  one := by rw [c.one, Category.id_comp, hir]
  mul _ y := by
    simp only [c.mul, Category.assoc]
    rw [← reassoc_of% hc y, hir, Category.comp_id]
  add _ _ := by rw [c.add, MonObj.mul_comp, MonObj.comp_mul]

theorem isLinearHom_retract_incl (c : OAct O K) (i : H ⟶ K) (r : K ⟶ H)
    [IsMonHom i] [IsMonHom r] (hir : i ≫ r = 𝟙 H)
    (hc : ∀ x, c.act x ≫ r ≫ i = r ≫ i ≫ c.act x) :
    IsLinearHom (retractAct c i r hir hc) c i :=
  ⟨inferInstance, fun x => by
    change (i ≫ c.act x ≫ r) ≫ i = _
    simp only [Category.assoc]
    rw [hc, reassoc_of% hir]⟩

theorem isLinearHom_retract_proj (c : OAct O K) (i : H ⟶ K) (r : K ⟶ H)
    [IsMonHom i] [IsMonHom r] (hir : i ≫ r = 𝟙 H)
    (hc : ∀ x, c.act x ≫ r ≫ i = r ≫ i ≫ c.act x) :
    IsLinearHom c (retractAct c i r hir hc) r :=
  ⟨inferInstance, fun x => by
    change _ = r ≫ i ≫ c.act x ≫ r
    rw [← reassoc_of% hc x, hir, Category.comp_id]⟩

/-- The tensor equivalence is proved from the constructed split scheme
retraction and the original split module maps. -/
def IsTensor.ofRetract {G : Over S} [GrpObj G] [IsCommMonObj G]
    [IsCommMonObj K] [IsCommMonObj H]
    {a : OAct O G} {b : OAct O H} {c : OAct O K}
    {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (k : IsTensor K c G a N) (s : M →ₗ[O] N) (t : N →ₗ[O] M)
    (hst : t ∘ₗ s = LinearMap.id) {i : H ⟶ K} {r : K ⟶ H}
    (hi : IsLinearHom b c i) (hr : IsLinearHom c b r)
    (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = k.mapLeft k (s ∘ₗ t)) :
    IsTensor H b G a M where
  equiv T := LinearEquiv.ofLinear
    (Pts.post hr T ∘ₗ (k.equiv T).toLinearMap ∘ₗ s.rTensor _)
    (t.rTensor _ ∘ₗ (k.equiv T).symm.toLinearMap ∘ₗ Pts.post hi T)
    (by
      refine LinearMap.ext fun y => Pts.ext ?_
      have e := k.hom_equiv_comp_mapLeft k (s ∘ₗ t) ((k.equiv T).symm (Pts.post hi T y))
      rw [LinearMap.rTensor_comp, LinearMap.comp_apply] at e
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pts.hom_post, ← e, ← hri]
      simp [hir, reassoc_of% hir])
    (by
      refine TensorProduct.ext' fun m x => ?_
      have hm : t (s m) = m := LinearMap.congr_fun hst m
      have e : Pts.post hi T (Pts.post hr T (k.equiv T (s m ⊗ₜ[O] x))) =
          k.equiv T (s m ⊗ₜ[O] x) :=
        Pts.ext (by simp [hri, hm])
      simp [e, hm])
  natural u z := by
    change Pts.post hr _ (k.equiv _ (s.rTensor _ _)) =
      Pts.pre b u (Pts.post hr _ (k.equiv _ (s.rTensor _ z)))
    rw [Pts.pre_post, ← k.natural, ← LinearMap.comp_apply (s.rTensor _),
      ← LinearMap.comp_apply (LinearMap.lTensor _ _), LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]

end Idempotent

end RHLean.Geometry.NativeCM.SerreScheme

namespace RHLean.Geometry.NativeCM.TraceFrame

open NumberField SerreScheme

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} {D : TraceLattice H} {ε : ℤˣ}
    (F : TraceFrame D ε) {S : Scheme.{0}} {G : Over S}
    [GrpObj G] [IsCommMonObj G] (a : OAct (OK H) G)

/-- The actual trace-pairing coordinates define an endomorphism of the
finite product of the input scheme. -/
def schemeIdempotent : powObj G F.n ⟶ powObj G F.n :=
  (IsTensor.pow (powIsPowGrp G F.n) a).mapLeft
    (IsTensor.pow (powIsPowGrp G F.n) a) (F.incl ∘ₗ F.proj)

instance isMonHom_schemeIdempotent : IsMonHom (F.schemeIdempotent a) :=
  IsTensor.isMonHom_mapLeft _ _ _

theorem schemeIdempotent_comp_self :
    F.schemeIdempotent a ≫ F.schemeIdempotent a = F.schemeIdempotent a := by
  rw [schemeIdempotent, ← IsTensor.mapLeft_comp, LinearMap.comp_assoc,
    ← LinearMap.comp_assoc _ _ F.proj, F.proj_incl, LinearMap.id_comp]

/-- The represented tensor scheme is this equalizer, constructed using
the original Hermitian frame on the original module. -/
def schemeObj : Over S := fixObj (F.schemeIdempotent a)

instance schemeGrp : GrpObj (F.schemeObj a) := fixGrp (F.schemeIdempotent_comp_self a)

instance schemeComm : IsCommMonObj (F.schemeObj a) :=
  isCommMonObj_fix (F.schemeIdempotent_comp_self a)

def schemeIncl : F.schemeObj a ⟶ powObj G F.n := fixIncl (F.schemeIdempotent a)

def schemeProj : powObj G F.n ⟶ F.schemeObj a := fixProj (F.schemeIdempotent_comp_self a)

instance isMonHom_schemeIncl : IsMonHom (F.schemeIncl a) :=
  isMonHom_fixIncl (F.schemeIdempotent_comp_self a)

instance isMonHom_schemeProj : IsMonHom (F.schemeProj a) :=
  isMonHom_fixProj (F.schemeIdempotent_comp_self a)

theorem schemeIncl_proj : F.schemeIncl a ≫ F.schemeProj a = 𝟙 _ :=
  fixIncl_proj (F.schemeIdempotent_comp_self a)

theorem schemeProj_incl : F.schemeProj a ≫ F.schemeIncl a = F.schemeIdempotent a :=
  fixProj_incl (F.schemeIdempotent_comp_self a)

theorem scheme_act_idempotent (c : OK H) :
    (powAct (powIsPowGrp G F.n) a).act c ≫ F.schemeProj a ≫ F.schemeIncl a =
      F.schemeProj a ≫ F.schemeIncl a ≫ (powAct (powIsPowGrp G F.n) a).act c := by
  rw [← Category.assoc (F.schemeProj a), schemeProj_incl]
  exact (IsTensor.isLinearHom_mapLeft _ _ _).comm c

def schemeAct : OAct (OK H) (F.schemeObj a) :=
  retractAct (powAct (powIsPowGrp G F.n) a) (F.schemeIncl a) (F.schemeProj a)
    (F.schemeIncl_proj a) (F.scheme_act_idempotent a)

/-- For every test scheme, the points of the constructed scheme are
naturally the tensor with the literal original module. -/
def schemeIsTensor : IsTensor (F.schemeObj a) (F.schemeAct a) G a D.La :=
  (IsTensor.pow (powIsPowGrp G F.n) a).ofRetract F.incl F.proj F.proj_incl
    (isLinearHom_retract_incl _ _ _ _ _) (isLinearHom_retract_proj _ _ _ _ _)
    (F.schemeIncl_proj a) (F.schemeProj_incl a)

variable (D) in
/-- Multiplication by the full CM order acts on the original module. -/
def moduleScalar (c : 𝓞 E) : D.La →ₗ[OK H] D.La where
  toFun x := c • x
  map_add' := smul_add c
  map_smul' _ _ := smul_comm _ _ _

/-- The full CM-order action is induced on the represented scheme from
the coefficient factor. It is not reduced to the quadratic seed action. -/
def schemeCoefficientAct : OAct (𝓞 E) (F.schemeObj a) where
  act c := (F.schemeIsTensor a).mapLeft (F.schemeIsTensor a) (moduleScalar D c)
  hom _ := inferInstance
  one := by
    have h : moduleScalar D 1 = LinearMap.id := by ext; simp [moduleScalar]
    rw [h, IsTensor.mapLeft_id]
  mul c d := by
    have h : moduleScalar D (c * d) = moduleScalar D d ∘ₗ moduleScalar D c := by
      ext x
      change (c * d) • x = d • (c • x)
      rw [smul_smul, mul_comm]
    rw [h, IsTensor.mapLeft_comp]
  add c d := by
    have h : moduleScalar D (c + d) = moduleScalar D c + moduleScalar D d := by
      ext x
      exact add_smul c d x
    rw [h, IsTensor.mapLeft_add]

@[reassoc]
theorem schemeCoefficientAct_tmul (c : 𝓞 E) (m : D.La) :
    (F.schemeIsTensor a).tmul m ≫ (F.schemeCoefficientAct a).act c =
      (F.schemeIsTensor a).tmul (c • m) :=
  (F.schemeIsTensor a).tmul_mapLeft (F.schemeIsTensor a) (moduleScalar D c) m

end RHLean.Geometry.NativeCM.TraceFrame

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open NumberField Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM SerreScheme

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (ε : ℤˣ)
    {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (a : OAct (OK G) A)

/-- The original coefficient ideal B^-1 is represented by the actual
equalizer constructed from its own perfect trace-Hermitian frame. -/
def coefficientSerreScheme : Over S :=
  (coefficientSerreFrame H G hbar B hB ε).schemeObj a

instance coefficientSerreScheme_grp : GrpObj (coefficientSerreScheme H G hbar B hB ε a) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeGrp a

instance coefficientSerreScheme_comm :
    IsCommMonObj (coefficientSerreScheme H G hbar B hB ε a) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeComm a

def coefficientSerreSchemeAct : OAct (OK G) (coefficientSerreScheme H G hbar B hB ε a) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeAct a

def coefficientSerreSchemeTensor :
    IsTensor (coefficientSerreScheme H G hbar B hB ε a)
      (coefficientSerreSchemeAct H G hbar B hB ε a) A a
        (coefficientIdeal H B : Submodule (𝓞 H.E) H.E) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeIsTensor a

def coefficientSerreSchemeFullAction :
    OAct (𝓞 H.E) (coefficientSerreScheme H G hbar B hB ε a) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeCoefficientAct a

/-- The retained CM coefficient action is an equality of actual scheme
morphisms on every original tensor generator. -/
@[reassoc]
theorem coefficientSerreSchemeFullAction_tmul (c : 𝓞 H.E)
    (m : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) :
    (coefficientSerreSchemeTensor H G hbar B hB ε a).tmul m ≫
        (coefficientSerreSchemeFullAction H G hbar B hB ε a).act c =
      (coefficientSerreSchemeTensor H G hbar B hB ε a).tmul (c • m) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeCoefficientAct_tmul a c m

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
