import Mathlib
import RHLean.Geometry.NativeThetaAppellHumbert

/-!
# The actual quadratic CM order and projective restriction

For the native geometric host this constructs the literal order `Z[w0]`,
its unique integral coordinates, involution, Dedekind property, and the exact
rank of an actual finite projective `O_E` module after restriction of scalars.
No free `O_E` basis or principal coefficient ideal is substituted.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`IntegersOfCmFieldConjStructure.lean`, `CmGeneratorSqQuadraticEq.lean`;
`Proofs/UnitaryExistence/HostGeneratorPowFourTraceNormModEight.lean`;
`Proofs/ThetaShiftProofs/NonemptyFiniteRootsOfBimul.lean`.
The original scheme and CM-degree conclusions are not imported. The source
mirror states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace RHLean.Geometry.NativeCM

theorem finrank_int_eq_mul_of_finite {O M : Type*} [CommRing O] [IsDomain O] [CharZero O]
    [Module.Free ℤ O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by
  classical
  let K := FractionRing O
  let N := LocalizedModule O⁰ M
  let f : M →ₗ[O] N := LocalizedModule.mkLinearMap O⁰ M
  let T := Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)
  have hdvd : ∀ s ∈ O⁰, ∃ n : ℤ, n ≠ 0 ∧ s ∣ (n : O) := fun s hs => by
    obtain ⟨r, hr, hd⟩ := IsAlgebraic.exists_nonzero_dvd (R := ℤ)
      (Algebra.IsIntegral.isIntegral (R := ℤ) s).isAlgebraic hs
    exact ⟨r, hr, by simpa using hd⟩
  have hT : ∀ t ∈ T, t ≠ 0 := by
    rintro _ ⟨n, hn, rfl⟩
    simpa using nonZeroDivisors.ne_zero hn
  have hTK : IsLocalization T K :=
    { map_units := fun t => IsLocalization.map_units K (M := O⁰)
        ⟨t, mem_nonZeroDivisors_of_ne_zero (hT t t.2)⟩
      surj := fun z => by
        obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj O⁰ z
        obtain ⟨n, hn, t, ht⟩ := hdvd s s.2
        refine ⟨⟨a * t, ⟨(n : O), n, mem_nonZeroDivisors_of_ne_zero hn, by simp⟩⟩, ?_⟩
        simp only [ht, map_mul] at hz ⊢
        rw [← hz]; ring
      exists_of_eq := fun {x y} h => ⟨1, by simpa using IsFractionRing.injective O K h⟩ }
  have : IsLocalizedModule T f := by
    rw [isLocalizedModule_iff_isBaseChange T K, ← isLocalizedModule_iff_isBaseChange O⁰ K]
    infer_instance
  have : IsLocalizedModule (nonZeroDivisors ℤ) (f.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars _ f
  have h1 : Module.finrank ℤ N = Module.finrank ℤ M :=
    IsLocalizedModule.finrank_eq _ (f.restrictScalars ℤ) le_rfl
  have h2 : Module.finrank O N = Module.finrank O M := IsLocalizedModule.finrank_eq O⁰ f le_rfl
  have h3 : Module.finrank K N = Module.finrank O N := IsLocalization.finrank_eq K O⁰ le_rfl
  let : Module ℚ N := Module.compHom N (algebraMap ℚ K)
  have : IsScalarTower ℚ K N := ⟨fun q k n => by
    change (q • k) • n = (algebraMap ℚ K q) • (k • n)
    rw [Algebra.smul_def, mul_smul]⟩
  have h4 : Module.finrank ℚ N = Module.finrank ℤ N :=
    IsLocalization.finrank_eq ℚ (nonZeroDivisors ℤ) le_rfl
  have h5 : Module.finrank ℚ K * Module.finrank K N = Module.finrank ℚ N :=
    Module.finrank_mul_finrank ℚ K N
  have h6 : Module.finrank ℚ K = Module.finrank ℤ K :=
    IsLocalization.finrank_eq ℚ (nonZeroDivisors ℤ) le_rfl
  have h7 : Module.finrank ℤ O * Module.finrank O K = Module.finrank ℤ K := by
    convert Module.finrank_mul_finrank' (R := ℤ) (S := O) K using 2
    all_goals first | rfl | exact Subsingleton.elim _ _
  have h8 : Module.finrank K K = Module.finrank O K := IsLocalization.finrank_eq K O⁰ le_rfl
  rw [Module.finrank_self] at h8
  rw [← h1, ← h4, ← h5, h6, ← h7, ← h8, h3, h2, mul_one]

section Projective

variable (O : Type*) [CommRing O] (X : Type*) [AddCommGroup X] [Module O X]

theorem torsion_eq_bot_of_int [IsDomain O] [Module.Finite ℤ O]
    [Module.IsTorsionFree ℤ X] : Submodule.torsion O X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨a, ha⟩, hx⟩ := (Submodule.mem_torsion_iff x).mp hx
  obtain ⟨n, hn, c, hc⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd ha
  have h : n • x = 0 := by
    have hx' : a • x = 0 := hx
    rw [← Int.cast_smul_eq_zsmul O, ← eq_intCast (algebraMap ℤ O), hc, mul_comm, mul_smul, hx',
      smul_zero]
  exact (smul_eq_zero.1 h).resolve_left hn

theorem projective_of_int [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Finite ℤ X]
    [Module.IsTorsionFree ℤ X] : Module.Projective O X := by
  have : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  have : Module.Flat O X :=
    IsDedekindDomain.flat_iff_torsion_eq_bot.2 (torsion_eq_bot_of_int O X)
  have : Module.FinitePresentation O X := Module.finitePresentation_of_finite O X
  exact Module.Flat.projective_of_finitePresentation

end Projective

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- The quadratic order used by the genuine Serre construction. -/
abbrev OK (H : NativeGeometricHost E) : Subalgebra ℤ (𝓞 E) :=
  Algebra.adjoin ℤ {H.w0}

def wK (H : NativeGeometricHost E) : OK H :=
  ⟨H.w0, Algebra.subset_adjoin rfl⟩

theorem bar_w0 (H : NativeGeometricHost E) : H.bar H.w0 = 1 - H.w0 := by
  have h := NativeTheta.AppellHumbert.weight_add_bar H
  linear_combination h

theorem bar_bar (H : NativeGeometricHost E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem rt_eq (H : NativeGeometricHost E) : H.rt = 2 * H.w0 - 1 := by
  rw [H.two_weight_eq_one_add_root]
  ring

theorem rt_ne_zero (H : NativeGeometricHost E) : H.rt ≠ 0 := by
  intro h
  have h2 := H.rt_sq
  rw [h] at h2
  have : (H.d : 𝓞 E) = 0 := by simpa using h2.symm
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem bar_mem_adjoin (H : NativeGeometricHost E) {a : 𝓞 E} (ha : a ∈ OK H) :
    H.bar a ∈ OK H := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, bar_w0]
    exact sub_mem (one_mem _) (Algebra.self_mem_adjoin_singleton ℤ _)
  | algebraMap r =>
    rw [eq_intCast, map_intCast]
    exact intCast_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

omit [IsCMField E] in

theorem int_dvd_of_mul_eq_ringOfIntegers {N m : ℤ} {z : 𝓞 E} (h : (N : 𝓞 E) * z = m) : N ∣ m := by
  have h1 : algebraMap ℤ (𝓞 E) N ∣ algebraMap ℤ (𝓞 E) m := ⟨z, by simpa using h.symm⟩
  have h2 := map_dvd (Algebra.norm ℤ) h1
  rw [Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').1 h2

theorem int_dvd_of_sq_dvd_squarefree_mul_sq {d N v : ℤ} (hd : Squarefree d) (hN : N ≠ 0)
    (h : N ^ 2 ∣ d * v ^ 2) : N ∣ v := by
  obtain ⟨N', v', h1, h2, h3⟩ := extract_gcd N v
  generalize gcd N v = g at h1 h2
  subst h1 h2
  have hg : g ≠ 0 := left_ne_zero_of_mul hN
  have h4 : N' ^ 2 ∣ d * v' ^ 2 := by
    rw [mul_pow, mul_pow, mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hg)).1 h
  have hc : IsCoprime N' v' := (gcd_isUnit_iff _ _).1 h3
  have h5 : N' * N' ∣ d := by
    rw [← sq]
    exact (hc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right h4
  exact mul_dvd_mul_left g (hd _ h5).dvd

theorem cm_generator_sq_quadratic_eq (H : NativeGeometricHost E) : H.w0 ^ 2 + (((1 + H.d) / 4 : ℕ) : 𝓞 E) = H.w0 := by
  have h4 : 4 * ((1 + H.d) / 4) = 1 + H.d := by have := H.d_mod; omega
  have h5 : (4 : 𝓞 E) * (((1 + H.d) / 4 : ℕ) : 𝓞 E) = 1 + H.d := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) h4
  have h := H.rt_sq
  rw [rt_eq] at h
  apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
  linear_combination h + h5

theorem exists_coord (H : NativeGeometricHost E) {a : 𝓞 E} (ha : a ∈ OK H) :
    ∃ u v : ℤ, a = u + v * H.w0 := by
  have hsq : H.w0 * H.w0 = H.w0 - (((1 + H.d) / 4 : ℕ) : 𝓞 E) := by
    have h := cm_generator_sq_quadratic_eq H
    linear_combination h
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - v * v' * ((1 + H.d) / 4 : ℕ),
      u * v' + v * u' + v * v', ?_⟩
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linear_combination (v * v' : 𝓞 E) * hsq

theorem coord_eq_zero (H : NativeGeometricHost E) {u v : ℤ} (h : (u : 𝓞 E) + v * H.w0 = 0) : u = 0 ∧ v = 0 := by
  have h1 := congrArg H.bar h
  rw [map_add, map_mul, map_intCast, map_intCast, bar_w0, map_zero] at h1
  have h2 : (v : 𝓞 E) * H.rt = 0 := by rw [rt_eq]; linear_combination h - h1
  have h3 : v = 0 := by exact_mod_cast (mul_eq_zero.1 h2).resolve_right (rt_ne_zero H)
  subst h3
  exact ⟨by simpa using h, rfl⟩

theorem coord_mem (H : NativeGeometricHost E) (u v : ℤ) : (u : 𝓞 E) + v * H.w0 ∈ OK H :=
  add_mem (intCast_mem _ u) (mul_mem (intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))

theorem coord_mul_bar (H : NativeGeometricHost E) (u v : ℤ) : ((u : 𝓞 E) + v * H.w0) * H.bar (u + v * H.w0) =
    ((u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 : ℤ) : 𝓞 E) := by
  have h := cm_generator_sq_quadratic_eq H
  generalize (1 + H.d) / 4 = k at h
  rw [map_add, map_mul, map_intCast, map_intCast, bar_w0]
  push_cast
  linear_combination (-v ^ 2 : 𝓞 E) * h

theorem mem_OK_of_int_mul_mem (H : NativeGeometricHost E) {N : ℤ} (hN : N ≠ 0) {y : 𝓞 E} (hy : (N : 𝓞 E) * y ∈ OK H) :
    y ∈ OK H := by
  obtain ⟨u, v, h⟩ := exists_coord H hy
  have hb := congrArg H.bar h
  have hn := coord_mul_bar H u v
  rw [← h, map_mul, map_intCast] at hn
  rw [map_mul, map_add, map_mul, map_intCast, map_intCast, map_intCast, bar_w0] at hb
  have h1 : N ∣ 2 * u + v :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y + H.bar y) (by push_cast; linear_combination h + hb)
  have h2 : N ^ 2 ∣ u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y * H.bar y) (by rw [← hn]; push_cast; ring)
  have h4 : (4 : ℤ) * ((1 + H.d) / 4 : ℕ) = 1 + H.d := by have := H.d_mod; omega
  have h3 : N ^ 2 ∣ H.d * v ^ 2 := by
    have := dvd_sub (h2.mul_left 4) (pow_dvd_pow_of_dvd h1 2)
    rwa [show 4 * (u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2) - (2 * u + v) ^ 2 = H.d * v ^ 2 by
      linear_combination v ^ 2 * h4] at this
  obtain ⟨v', rfl⟩ := int_dvd_of_sq_dvd_squarefree_mul_sq
    (Int.squarefree_natCast.2 H.d_prime.squarefree) hN h3
  obtain ⟨u', rfl⟩ : N ∣ u :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y - (v' : 𝓞 E) * H.w0) (by push_cast at h; linear_combination h)
  have : y = u' + v' * H.w0 :=
    mul_left_cancel₀ (show (N : 𝓞 E) ≠ 0 by exact_mod_cast hN) (by push_cast at h; linear_combination h)
  rw [this]
  exact coord_mem H u' v'

theorem finite_int_OK (H : NativeGeometricHost E) : Module.Finite ℤ (OK H) :=
  Module.Finite.of_injective (OK H).val.toLinearMap Subtype.val_injective

theorem isIntegrallyClosed_OK (H : NativeGeometricHost E) : IsIntegrallyClosed (OK H) := by
  have := finite_int_OK H
  rw [isIntegrallyClosed_iff (FractionRing (OK H))]
  intro x hx
  have hinj : Function.Injective (algebraMap (OK H) E) :=
    RingOfIntegers.coe_injective.comp Subtype.val_injective
  let φ : FractionRing (OK H) →ₐ[OK H] E :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId (OK H) E) hinj
  have hy : IsIntegral ℤ (φ x) := isIntegral_trans _ (hx.map φ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OK H) x
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) b).exists_nonzero_dvd hb
  have hb' : algebraMap (OK H) E b ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)
  have hm : (⟨_, hy⟩ : 𝓞 E) ∈ OK H := by
    refine mem_OK_of_int_mul_mem H hn ?_
    convert (a * c).2 using 1
    apply RingOfIntegers.coe_injective
    have h1 : (n : E) = algebraMap (OK H) E b * algebraMap (OK H) E c := by
      rw [← map_mul, ← hc]; simp
    change (n : E) * φ _ = algebraMap (OK H) E (a * c)
    rw [map_div₀, φ.commutes, φ.commutes, h1, map_mul]
    field_simp
  refine ⟨⟨_, hm⟩, φ.injective ?_⟩
  exact φ.commutes _

theorem isDedekindDomain_OK (H : NativeGeometricHost E) : IsDedekindDomain (OK H) :=
  have := finite_int_OK H
  { isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ (OK H)),
    Ring.DimensionLEOne.of_isIntegral ℤ (OK H), isIntegrallyClosed_OK H with }

theorem existsUnique_coord (H : NativeGeometricHost E) (a : OK H) :
    ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H := by
  obtain ⟨u, v, h⟩ := exists_coord H a.2
  refine ⟨(u, v), Subtype.ext h, ?_⟩
  rintro ⟨u', v'⟩ h'
  have h2 : (a : 𝓞 E) = u' + v' * H.w0 := congrArg Subtype.val h'
  obtain ⟨h3, h4⟩ := coord_eq_zero H (u := u' - u) (v := v' - v) (by push_cast; linear_combination h - h2)
  exact Prod.ext (sub_eq_zero.1 h3) (sub_eq_zero.1 h4)

theorem finrank_int_OK (H : NativeGeometricHost E) : Module.finrank ℤ (OK H) = 2 := by
  let f : (ℤ × ℤ) →ₗ[ℤ] OK H := LinearMap.coprod (LinearMap.toSpanSingleton ℤ _ 1)
    (LinearMap.toSpanSingleton ℤ _ (wK H))
  have hf : Function.Bijective f := by
    rw [Function.bijective_iff_existsUnique]
    intro a
    simpa [f, eq_comm (a := a)] using existsUnique_coord H a
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  simp

def barOK (H : NativeGeometricHost E) : OK H ≃+* OK H where
  toFun a := ⟨H.bar a, bar_mem_adjoin H a.2⟩
  invFun a := ⟨H.bar a, bar_mem_adjoin H a.2⟩
  left_inv a := Subtype.ext (bar_bar H a)
  right_inv a := Subtype.ext (bar_bar H a)
  map_mul' a b := Subtype.ext (map_mul H.bar (a : 𝓞 E) (b : 𝓞 E))
  map_add' a b := Subtype.ext (map_add H.bar (a : 𝓞 E) (b : 𝓞 E))

theorem two_mul_finrank_OK (H : NativeGeometricHost E) (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] :
    2 * Module.finrank (OK H) M = Module.finrank ℚ E * Module.finrank (𝓞 E) M := by
  have := finite_int_OK H
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  have : Module.Finite (OK H) M := Module.Finite.of_restrictScalars_finite ℤ _ _
  rw [← finrank_int_OK H, ← finrank_int_eq_mul_of_finite, ← RingOfIntegers.rank,
    ← finrank_int_eq_mul_of_finite]

theorem OK_isDedekindDomain_and_projective :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : NativeGeometricHost E), IsDedekindDomain (OK H) ∧ (∀ a : OK H, ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H) ∧ (∃ br : OK H ≃+* OK H, (∀ a, ((br a : OK H) : 𝓞 E) = H.bar a) ∧ wK H + br (wK H) = 1 ∧ ∀ a, br (br a) = a) ∧ wK H ^ 2 + (((1 + H.d) / 4 : ℕ) : OK H) = wK H ∧ 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E ∧
  ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → Module.Finite (OK H) M ∧ Module.Projective (OK H) M ∧ Module.finrank (OK H) M = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) M := by
  intro E _ _ _ H
  have h2 : 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E := by
    simpa using two_mul_finrank_OK H (𝓞 E)
  refine ⟨isDedekindDomain_OK H, existsUnique_coord H,
    ⟨barOK H, fun _ => rfl, Subtype.ext ?_, fun a => Subtype.ext (bar_bar H a)⟩, Subtype.ext (cm_generator_sq_quadratic_eq H), h2, ?_⟩
  · change H.w0 + H.bar H.w0 = 1
    rw [bar_w0, add_sub_cancel]
  · intro M _ _ _ _
    have := finite_int_OK H
    have := isDedekindDomain_OK H
    have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
    have : Module.IsTorsionFree ℤ M := Module.IsTorsionFree.trans (𝓞 E)
    refine ⟨Module.Finite.of_restrictScalars_finite ℤ _ _, projective_of_int _ _, ?_⟩
    have h3 := two_mul_finrank_OK H M
    rw [← h2, mul_assoc] at h3
    rw [← h2, Nat.mul_div_cancel_left _ two_pos]
    omega

/-- An actual integral basis of the quadratic order, not a selected basis of
its larger CM field. -/
def coordEquiv (H : NativeGeometricHost E) : (ℤ × ℤ) ≃ₗ[ℤ] OK H :=
  LinearEquiv.ofBijective
    (LinearMap.coprod (LinearMap.toSpanSingleton ℤ _ 1)
      (LinearMap.toSpanSingleton ℤ _ (wK H))) (by
        rw [Function.bijective_iff_existsUnique]
        intro a
        simpa [eq_comm (a := a)] using existsUnique_coord H a)

theorem coordEquiv_apply (H : NativeGeometricHost E) (m : ℤ × ℤ) :
    coordEquiv H m = (m.1 : OK H) + (m.2 : OK H) * wK H := by
  simp [coordEquiv, LinearMap.coprod_apply]

/-- The actual complex embedding of the quadratic order. -/
def embed (H : NativeGeometricHost E) (τ : E →+* ℂ) : OK H →+* ℂ :=
  τ.comp ((algebraMap (𝓞 E) E).comp (OK H).val.toRingHom)

theorem embed_wK (H : NativeGeometricHost E) (τ : E →+* ℂ) :
    embed H τ (wK H) = τ (H.w0 : E) := rfl

end RHLean.Geometry.NativeCM
end
