import RHLean.Geometry.NativeThetaCuspShiftedPhase

/-!
# The actual auxiliary Hermitian lattice family

The standard Hermitian form uses the native host's actual conjugation.
Finite projective dual frames are constructed from finite generation and
integral self-duality, using projective lifting and extension of integral
linear forms. The auxiliary family retains its original congruence-away-
from-level condition; the standard integral lattice is proved to belong.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/
FirstCoordinateAdmissible.lean (`stdL`, `Agree`, `Vset`),
Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean
(`exists_dual_family`), and Proofs/SiegelThetaTransformation/
AdmissibleIndicatorFunctions.lean (`mem_stdL`, `stdL_mem_Vset`).
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix
open scoped nonZeroDivisors BigOperators Pointwise Classical

namespace RHLean.Geometry.NativeTheta.Cusp.AuxiliaryLattices

section Extension

variable {E : Type} [Field E] [NumberField E]

private lemma exists_linearForm_extend_of_span_eq_univ {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (g : Λ →ₗ[𝓞 E] 𝓞 E) :
    ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y : Λ, φ y = g y := by
  obtain ⟨t, htΛ, hts, hli⟩ := exists_linearIndependent E (Λ : Set (Fin n → E))
  let b : Module.Basis t E (Fin n → E) :=
    Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hts, hspan]))
  have hb : ∀ i, b i ∈ Λ := fun i => by rw [Module.Basis.mk_apply]; exact htΛ i.2
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  refine ⟨b.constr E fun i => ((g ⟨b i, hb i⟩ : 𝓞 E) : E), fun y => ?_⟩
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ (b.repr y)
  have hd' : ∀ i, ∃ x : 𝓞 E, algebraMap (𝓞 E) E x = (d : 𝓞 E) • b.repr y i :=
    fun i => hd i (Finset.mem_univ _)
  choose a ha using hd'
  have hdy : (d : 𝓞 E) • y = ∑ i, a i • (⟨b i, hb i⟩ : Λ) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_sum]
    conv_lhs => rw [← b.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul E (a i), ha i, smul_assoc]
  have hg := congrArg (fun z => ((g z : 𝓞 E) : E)) hdy
  simp only [map_smul, map_sum, smul_eq_mul, map_mul] at hg
  simp only [RingOfIntegers.coe_eq_algebraMap]
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  apply mul_left_cancel₀ hd0
  rw [hg]
  conv_lhs => rw [← b.sum_repr (y : Fin n → E)]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, ha i, smul_eq_mul, Algebra.smul_def]
  ring


end Extension

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization

variable {φ : Frame} (H : HostRaw φ)

/-- The standard Hermitian form with the actual native conjugation. -/
def herm {n : ℕ} (x y : Fin n → H.E) : H.E := ∑ a, x a * H.conj (y a)

theorem herm_symm {n : ℕ} (x y : Fin n → H.E) :
    herm H x y = H.conj (herm H y x) := by
  rw [herm, herm, map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [map_mul, conj_conj, mul_comm]

theorem isIntegral_conj {a : H.E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (H.conj a) :=
  ha.map H.conj.toRingHom.toIntAlgHom

theorem exists_herm_eq {n : ℕ} (f : (Fin n → H.E) →ₗ[H.E] H.E) :
    ∃ w : Fin n → H.E, ∀ u, f u = herm H u w := by
  refine ⟨fun a => H.conj (f fun b => if a = b then 1 else 0), fun u => ?_⟩
  rw [f.pi_apply_eq_sum_univ u, herm]
  exact Finset.sum_congr rfl fun a _ => by rw [conj_conj, smul_eq_mul]

theorem eq_zero_of_line {n : ℕ} (Λ : Submodule (𝓞 H.E) (Fin n → H.E))
    (hfg : Λ.FG) (w : Fin n → H.E) (hw : ∀ c : H.E, c • w ∈ Λ) : w = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  have htop : Λ.map (LinearMap.proj (R := 𝓞 H.E) (φ := fun _ : Fin n => H.E) j) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ⟨(x / w j) • w, hw _, ?_⟩
    simp [div_mul_cancel₀ _ hj]
  have : Module.Finite (𝓞 H.E) H.E := ⟨by rw [← htop]; exact hfg.map _⟩
  have := Algebra.IsIntegral.of_finite (𝓞 H.E) H.E
  exact RingOfIntegers.not_isField H.E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 H.E) H.E)
      (Field.toIsField H.E))

theorem span_eq_top {n : ℕ} (Λ : Submodule (𝓞 H.E) (Fin n → H.E)) (hfg : Λ.FG)
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm H x y)) → x ∈ Λ) :
    Submodule.span H.E (Λ : Set (Fin n → H.E)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨w, hw⟩ := exists_herm_eq H f
  have hline : ∀ c : H.E, c • w ∈ Λ := fun c => hdual _ fun y hy => by
    have hfy : f y = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hy))
    have hsmul : herm H (c • w) y = c * herm H w y := by
      simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [hsmul, herm_symm H w y, ← hw, hfy, map_zero, mul_zero]
    exact isIntegral_zero
  have hw0 := eq_zero_of_line H Λ hfg w hline
  exact hf0 (LinearMap.ext fun u => by simp [hw u, hw0, herm])

/-- A finite dual projective frame, constructed inside the actual lattice. -/
theorem exists_dual_family {n : ℕ} (Λ : Submodule (𝓞 H.E) (Fin n → H.E))
    (hfg : Λ.FG)
    (_hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm H x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm H x y)) → x ∈ Λ) :
    Submodule.span H.E (Λ : Set (Fin n → H.E)) = ⊤ ∧ ∃ (m : ℕ) (v w : Fin m → Fin n → H.E),
      (∀ i, v i ∈ Λ) ∧ (∀ i, w i ∈ Λ) ∧ ∀ u : Fin n → H.E, u = ∑ i, herm H u (w i) • v i := by
  have hspan := span_eq_top H Λ hfg hdual
  refine ⟨hspan, ?_⟩
  have : Module.Finite (𝓞 H.E) Λ := Module.Finite.iff_fg.mpr hfg
  have := Module.finitePresentation_of_finite (𝓞 H.E) Λ
  have : Module.Projective (𝓞 H.E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 H.E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hext : ∀ j : Fin m, ∃ φ : (Fin n → H.E) →ₗ[H.E] H.E, ∀ y (hy : y ∈ Λ), φ y = σ ⟨y, hy⟩ j :=
    fun j => (exists_linearForm_extend_of_span_eq_univ Λ hspan ((LinearMap.proj j).comp σ)).imp
      fun φ h y hy => h ⟨y, hy⟩
  choose φ hφ using hext
  choose w hw using fun j => exists_herm_eq H (φ j)
  let v : Fin m → Fin n → H.E := fun j => (π fun k => if j = k then 1 else 0 : Λ)
  refine ⟨m, v, w, fun j => (π _).2, fun j => hdual _ fun y hy => ?_, fun u => ?_⟩
  · rw [herm_symm, ← hw, hφ j y hy]
    exact isIntegral_conj H (RingOfIntegers.isIntegral_coe _)
  · have hL : (∑ j, (φ j).smulRight (v j)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun y hy => ?_
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have hy' : y = ((π (σ ⟨y, hy⟩) : Λ) : Fin n → H.E) := by
        rw [← LinearMap.comp_apply, hσ]
        rfl
      conv_rhs => rw [hy', π.pi_apply_eq_sum_univ]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hφ j y hy, RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    have hu := congrArg (fun L : (Fin n → H.E) →ₗ[H.E] (Fin n → H.E) => L u) hL
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply, hw] at hu
    exact hu.symm


/-- The standard integral lattice as the literal span of coordinate vectors. -/
def stdL (n : ℕ) : Submodule (𝓞 H.E) (Fin n → H.E) :=
  Submodule.span (𝓞 H.E) (Set.range fun a : Fin n => (Pi.single a 1 : Fin n → H.E))

/-- Exact agreement away from the unchanged level modulus. -/
def Agree {n : ℕ} (M : ℕ) (Λ Λ' : Submodule (𝓞 H.E) (Fin n → H.E)) : Prop :=
  ∃ s : ℕ, 0 < s ∧ s.Coprime M ∧
    (∀ v ∈ Λ, (s : H.E) • v ∈ Λ') ∧ ∀ v ∈ Λ', (s : H.E) • v ∈ Λ

/-- All finite self-dual auxiliary lattices at the original level. -/
def Vset (n M : ℕ) : Set (Submodule (𝓞 H.E) (Fin n → H.E)) :=
  {Λ | Λ.FG ∧ (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm H x y)) ∧
    Agree H M Λ (stdL H n)}

theorem mem_stdL {n : ℕ} {x : Fin n → H.E} :
    x ∈ stdL H n ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      intro a
      by_cases hab : a = b
      · subst hab
        simpa using isIntegral_one
      · simp [hab, isIntegral_zero]
    | zero => intro a; exact isIntegral_zero
    | add y z _ _ hy hz => intro a; exact (hy a).add (hz a)
    | smul r y _ hy =>
      intro a
      rw [Pi.smul_apply, Algebra.smul_def]
      exact (RingOfIntegers.isIntegral_coe r).mul (hy a)
  · intro hx
    have hsum : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 H.E) • (Pi.single a 1 : Fin n → H.E) := by
      ext b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- The family has an actual integral member for every original modulus. -/
theorem stdL_mem_Vset (n M : ℕ) : stdL H n ∈ Vset H n M := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ?_,
    ⟨1, one_pos, Nat.coprime_one_left M,
      fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩⟩
  constructor
  · intro hx y hy
    rw [herm]
    rw [mem_stdL] at hx hy
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_conj H (hy a))
  · intro h
    rw [mem_stdL]
    intro a
    have ha := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [herm, Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)] at ha
    simpa using ha

end RHLean.Geometry.NativeTheta.Cusp.AuxiliaryLattices
