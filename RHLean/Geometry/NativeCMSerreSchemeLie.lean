import RHLean.Geometry.NativeCMSerreSchemeTensor
import RHLean.Geometry.NativeCMSerreSchemeTangent

/-!
# The integral Lie module of the represented native Serre tensor

The tensor scheme is the trace-frame equalizer constructed in
`NativeCMSerreSchemeTensor`. Its intrinsic dual-number Lie module is proved
isomorphic to R tensor_OK M, with the literal integral elliptic tangent
generator and every coefficient endomorphism retained. For the coefficient
module M=B^-1 the resulting full O_E action acts on the second tensor factor.

The elliptic input is an actual scheme action, together with its actual
action on the specified integral tangent generator. These are genuine
compatibility inputs; neither an abelian scheme nor tensor representability,
a tangent equivalence, a metric, or a degree formula is assumed.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
TensorLieBasisExists.lean. The unnecessary finite/projective hypotheses in
its generic Lie argument are omitted: the constructed native trace-frame
tensor already supplies the needed natural point equivalence. The source
archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical TensorProduct Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SerreScheme

open SchemeTheory Pts

namespace LieTensor

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff (c : R) (v x : epsR R ⟶ G) :
    IsLieComb ![c] ![v] x ↔ x = epsScale c ≫ v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u 0 = epsScale c ≫ v := Over.OverMorphism.ext (hu 0)
    simp [h]
  · rintro rfl
    refine ⟨![epsScale c ≫ v], fun i => ?_, by simp⟩
    fin_cases i
    rfl

variable [IsCommMonObj G] {O : Type} [CommRing O] [Algebra O R]

def multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = epsScale (algebraMap O R c) ≫ v) :
    R →ₗ[O] Pts a (epsR R) where
  toFun r := Pts.mk a (epsScale r ≫ v)
  map_add' r s := Pts.ext (epsScale_add_comp r s hv)
  map_smul' _ _ := Pts.ext (by
    simp only [Pts.hom_mk, RingHom.id_apply, Pts.hom_smul, Category.assoc, ha]
    rw [epsScale_mul_assoc, Algebra.smul_def, mul_comm])

theorem hom_multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = epsScale (algebraMap O R c) ≫ v) (r : R) :
    Pts.hom (multiples a hv ha r) = epsScale r ≫ v := rfl

omit [Algebra O R] in
theorem pre_eq_zero_iff (a : OAct O G) (x : Pts a (epsR R)) :
    Pts.pre a (toUnit (epsR R) ≫ epsZero R) x = 0 ↔ IsTangent (Pts.hom x) := by
  rw [isTangent_iff]
  constructor
  · intro h
    have h1 : (toUnit (epsR R) ≫ epsZero R) ≫ Pts.hom x = 1 := congrArg Pts.hom h
    have h2 := congrArg (epsZero R ≫ ·) h1
    simp only [← Category.assoc, MonObj.comp_one] at h2
    rwa [toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.id_comp] at h2
  · intro h
    exact Pts.ext (by rw [Pts.hom_pre, Category.assoc, h, MonObj.comp_one]; rfl)

omit [Algebra O R] in
theorem isTangent_sub_pre (a : OAct O G) (x : Pts a (epsR R)) :
    IsTangent (Pts.hom (x - Pts.pre a (toUnit (epsR R) ≫ epsZero R) x)) := by
  rw [← pre_eq_zero_iff, map_sub, sub_eq_zero]
  apply Pts.ext
  simp only [Pts.hom_pre, ← Category.assoc]
  rw [Category.assoc (toUnit _) (epsZero R) (toUnit _),
    toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.comp_id]

theorem exists_retraction (a : OAct O G) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (ha : ∀ c, v ≫ a.act c = epsScale (algebraMap O R c) ≫ v) :
    ∃ ρ : Pts a (epsR R) →ₗ[O] R, ρ ∘ₗ multiples a (hv.1 0) ha = LinearMap.id ∧
      multiples a (hv.1 0) ha ∘ₗ ρ =
        LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) := by
  have hinj : Function.Injective (multiples a (hv.1 0) ha) := fun r s h => by
    have h' : epsScale r ≫ v = epsScale s ≫ v := congrArg Pts.hom h
    have := (hv.2 _ (isTangent_epsScale r (hv.1 0))).unique
      ((isLieComb_one_iff r v _).2 rfl) ((isLieComb_one_iff s v _).2 h')
    exact congrFun this 0
  have hsur : ∀ x : Pts a (epsR R), ∃ r, multiples a (hv.1 0) ha r =
      (LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) : _ →ₗ[O] _) x := fun x => by
    obtain ⟨c, hc, -⟩ := hv.2 _ (isTangent_sub_pre a x)
    have e : c = ![c 0] := by ext i; fin_cases i; rfl
    rw [e, isLieComb_one_iff] at hc
    exact ⟨c 0, Pts.ext hc.symm⟩
  choose ρ hρ using hsur
  refine ⟨⟨⟨ρ, fun _ _ => hinj ?_⟩, fun _ _ => hinj ?_⟩,
    LinearMap.ext fun r => hinj ?_, LinearMap.ext hρ⟩
  · rw [map_add, hρ, hρ, hρ, map_add]
  · simp only [RingHom.id_apply, map_smul, hρ]
  · change multiples a (hv.1 0) ha (ρ _) = _
    rw [hρ, LinearMap.sub_apply, (pre_eq_zero_iff a (multiples a (hv.1 0) ha r)).2
      (isTangent_epsScale r (hv.1 0)), sub_zero]
    rfl

/-- The natural tensor point equivalence identifies every actual tangent,
and intertwines all module endomorphisms. -/
theorem exists_lie_tensor
    (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (O : Type) [CommRing O] [Algebra O R]
    (M : Type) [AddCommGroup M] [Module O M]
    (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (v : epsR R ⟶ G)
    (hv : IsLieBasis ![v])
    (ha' : ∀ c, IsLieComb ![algebraMap O R c] ![v] (v ≫ a.act c)) :
    ∃ Φ : R ⊗[O] M → (epsR R ⟶ A), Function.Injective Φ ∧
      (∀ x, IsTangent x ↔ x ∈ Set.range Φ) ∧
      (∀ y z, Φ (y + z) = Φ y * Φ z) ∧
      (∀ (c : R) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) ∧
      (∀ m, Φ (1 ⊗ₜ[O] m) = v ≫ t.tmul m) ∧
      ∀ (φ : M →ₗ[O] M) y, Φ (φ.baseChange R y) = Φ y ≫ t.mapLeft t φ := by
  have ha : ∀ c, v ≫ a.act c = epsScale (algebraMap O R c) ≫ v :=
    fun c => (isLieComb_one_iff _ _ _).1 (ha' c)
  obtain ⟨ρ, h₁, h₂⟩ := exists_retraction a hv ha
  set j := multiples a (hv.1 0) ha with hj
  let Ψ : R ⊗[O] M →ₗ[O] Pts b (epsR R) :=
    (t.equiv _).toLinearMap ∘ₗ j.lTensor M ∘ₗ (TensorProduct.comm O R M).toLinearMap
  have hΨ : ∀ (r : R) (m : M), Pts.hom (Ψ (r ⊗ₜ[O] m)) = epsScale r ≫ v ≫ t.tmul m :=
    fun _ _ => by simp [Ψ, hj, hom_multiples]
  refine ⟨fun y => Pts.hom (Ψ y), fun y z h => ?_, fun x => ⟨fun hx => ?_, ?_⟩,
    fun _ _ => ?_, fun c y => ?_, fun _ => ?_, fun φ y => ?_⟩
  · have h' : j.lTensor M (TensorProduct.comm O R M y) =
        j.lTensor M (TensorProduct.comm O R M z) := (t.equiv _).injective (Pts.ext h)
    have h'' := congrArg (ρ.lTensor M) h'
    simp only [← LinearMap.lTensor_comp_apply, h₁, LinearMap.lTensor_id, LinearMap.id_apply] at h''
    exact (TensorProduct.comm O R M).injective h''
  · obtain ⟨z, hz⟩ := (t.equiv (epsR R)).surjective (Pts.mk b x)
    have h0 : (Pts.pre a (toUnit (epsR R) ≫ epsZero R)).lTensor M z = 0 := by
      apply (t.equiv _).injective
      rw [t.natural, hz, map_zero]
      exact (pre_eq_zero_iff b _).2 hx
    refine ⟨(TensorProduct.comm O R M).symm (ρ.lTensor M z), ?_⟩
    simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← LinearMap.lTensor_comp_apply, h₂, LinearMap.lTensor_sub, LinearMap.sub_apply, h0,
      sub_zero, LinearMap.lTensor_id, LinearMap.id_apply, hz, Pts.hom_mk]
  · rintro ⟨y, rfl⟩
    rw [← pre_eq_zero_iff]
    induction y using TensorProduct.inductionOn with
    | tmul r m =>
      rw [pre_eq_zero_iff, hΨ]
      exact isTangent_epsScale r (isTangent_comp (hv.1 0) _)
    | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
  · simp only [map_add, Pts.hom_add]
  · rw [isLieComb_one_iff]
    induction y using TensorProduct.inductionOn with
    | tmul r m =>
      simp only [TensorProduct.smul_tmul', hΨ, smul_eq_mul]
      rw [epsScale_mul_assoc]
    | add y z hy hz =>
      simp only [smul_add, map_add, Pts.hom_add, MonObj.comp_mul] at hy hz ⊢
      rw [hy, hz]
  · simp only [hΨ, epsScale_one, Category.id_comp]
  · induction y using TensorProduct.inductionOn with
    | tmul r m =>
      simp only [LinearMap.baseChange_tmul, hΨ, Category.assoc, IsTensor.tmul_mapLeft]
    | add y z hy hz =>
      simp only [map_add, Pts.hom_add, MonObj.mul_comp] at hy hz ⊢
      rw [hy, hz]

/-- The target module has the intrinsic dual-number scalar operations
proved in `SchemeTheory.Lie.module`; they are not assigned by transport. -/
theorem exists_lie_equiv
    (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (O : Type) [CommRing O] [Algebra O R]
    (M : Type) [AddCommGroup M] [Module O M]
    (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (v : epsR R ⟶ G)
    (hv : IsLieBasis ![v])
    (ha : ∀ c, IsLieComb ![algebraMap O R c] ![v] (v ≫ a.act c)) :
    ∃ e : R ⊗[O] M ≃ₗ[R] Lie A,
      (∀ m, Lie.hom (e (1 ⊗ₜ[O] m)) = v ≫ t.tmul m) ∧
      ∀ (φ : M →ₗ[O] M) y,
        Lie.hom (e (φ.baseChange R y)) = Lie.hom (e y) ≫ t.mapLeft t φ := by
  obtain ⟨Φ, hΦ, ht, hadd, hsmul, hone, hnat⟩ :=
    exists_lie_tensor R G O M A a b t v hv ha
  let f : R ⊗[O] M →ₗ[R] Lie A :=
    { toFun := fun y => ⟨Additive.ofMul (Φ y), (ht _).mpr ⟨y, rfl⟩⟩
      map_add' := fun y z => Lie.ext (hadd y z)
      map_smul' := fun c y => Lie.ext ((isLieComb_one_iff _ _ _).mp (hsmul c y)) }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact hΦ (congrArg Lie.hom h)
    · intro x
      obtain ⟨y, hy⟩ := (ht _).mp x.property
      exact ⟨y, Lie.ext hy⟩
  exact ⟨LinearEquiv.ofBijective f hf, hone, hnat⟩

end LieTensor
end RHLean.Geometry.NativeCM.SerreScheme

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open NumberField Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM SerreScheme SchemeTheory
open SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie

/-- One literal B^-1, its actual trace-frame equalizer scheme, and the
specified integral vector of the original Weierstrass equation are retained
through the integral Lie equivalence, including the full CM-order action. -/
theorem coefficientSerreScheme_exists_integralLie
    {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (R : Type) [CommRing R] [_root_.IsReduced R] [Algebra (OK G) R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (a : OAct (OK G) (schemeOver W))
    (ha : ∀ c, IsLieComb ![algebraMap (OK G) R c] ![integralVector W]
      (integralVector W ≫ a.act c)) :
    ∃ e : R ⊗[OK G] (coefficientIdeal H B : Submodule (𝓞 H.E) H.E) ≃ₗ[R]
        Lie (coefficientSerreScheme H G hbar B hB 1 a),
      (∀ m, Lie.hom (e (1 ⊗ₜ[OK G] m)) =
        integralVector W ≫ (coefficientSerreSchemeTensor H G hbar B hB 1 a).tmul m) ∧
      ∀ (c : 𝓞 H.E) y,
        Lie.hom (e ((TraceFrame.moduleScalar (coefficientTraceLattice H G hbar B hB) c).baseChange R y)) =
        Lie.hom (e y) ≫ (coefficientSerreSchemeFullAction H G hbar B hB 1 a).act c := by
  obtain ⟨e, hone, hnat⟩ := LieTensor.exists_lie_equiv R (schemeOver W) (OK G)
    (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)
    (coefficientSerreScheme H G hbar B hB 1 a) a
    (coefficientSerreSchemeAct H G hbar B hB 1 a)
    (coefficientSerreSchemeTensor H G hbar B hB 1 a)
    (integralVector W) (integralVector_isLieBasis W) ha
  exact ⟨e, hone, fun c y => hnat
    (TraceFrame.moduleScalar (coefficientTraceLattice H G hbar B hB) c) y⟩

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
