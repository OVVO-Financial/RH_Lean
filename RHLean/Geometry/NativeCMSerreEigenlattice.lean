import RHLean.Geometry.NativeCMSerreEigenlatticeAlgebra
import RHLean.Geometry.NativeCMFiniteDegreeCorrection

/-!
# The exact integral eigenline of the native projective Serre module

The integral tensor is O_F tensor_OK B^-1. Its coefficient action acts on
the B^-1 factor; it is deliberately distinguished from scalar multiplication
through O_F. The evaluation map is proved injective using the actual perfect
trace-Hermitian frame. Its image is the integral O_F span of the embedding
coordinates. The identity-character eigenspace is then identified with the
literal extended ideal B^-1 D(E/K) = conjugate(B), including its finite index.

This is an algebraic lattice identification, independent of an assigned
metric. It supplies the actual fractional ideal to the finite degree and
all-place norm computations. Identifying this tensor with the integral Lie
module of a represented Serre abelian scheme is a separate obligation.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
TwoMulDegreeEigenLatticeTensorRankOne.lean, `exists_eigenline`, and
TwoMulDegDualLineCmIdeal.lean, `two_mul_deg_dual_line`. Only their algebraic
coordinate/ideal argument is needed here; the actual native trace form has
beta=1. The archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open NumberField
open scoped Classical BigOperators Pointwise nonZeroDivisors TensorProduct

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM RHLean.Geometry.NativeCM.SerreEigenlattice

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) (F : Type) [Field F] [Algebra H.E F]

/-- The complete pure-character embeddings into the actual extension F. -/
def coefficientEmbedding (σ : RootAut G) : H.E →+* F :=
  (algebraMap H.E F).comp σ.1.toRingHom

theorem coefficientEmbedding_injective : Function.Injective (coefficientEmbedding H G F) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  exact (algebraMap H.E F).injective (RingHom.congr_fun h x)

/-- Original coefficient evaluations, with the actual order action. -/
def coefficientEvaluation (B : Ideal (𝓞 H.E)) :
    coefficientIdeal H B →ₗ[OK G] (RootAut G → F) where
  toFun x σ := algebraMap H.E F (σ.1 (x : H.E))
  map_add' _ _ := by
    ext σ
    exact map_add (coefficientEmbedding H G F σ) _ _
  map_smul' a x := by
    ext σ
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, Pi.smul_apply]
    have hs : a • (x : H.E) = ((a : 𝓞 H.E) : H.E) * (x : H.E) :=
      Algebra.smul_def (a : 𝓞 H.E) (x : H.E)
    rw [hs, Algebra.smul_def]
    change algebraMap H.E F (σ.1 (((a : 𝓞 H.E) : H.E) * (x : H.E))) =
      algebraMap H.E F ((a : 𝓞 H.E) : H.E) *
        algebraMap H.E F (σ.1 (x : H.E))
    rw [map_mul, map_mul, rootAut_fix_order]

def coefficientDualEvaluation (B : Ideal (𝓞 H.E)) (y : coefficientIdeal H B) :
    RootAut G → F := fun σ => algebraMap H.E F (σ.1 (H.conj (y : H.E)))

theorem coefficientEvaluation_span (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    Submodule.span F (Set.range (coefficientEvaluation H G F B)) = ⊤ := by
  let a₀ : coefficientIdeal H B := ⟨1, FractionalIdeal.one_mem_inv_coe_ideal
    (FractionalIdeal.coeIdeal_ne_zero.mp (halfDifferent_ne_zero H B hB).1)⟩
  exact span_embeddings_eq_top (coefficientEmbedding H G F)
    (coefficientEmbedding_injective H G F)
    (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).subtype a₀ (by simp [a₀])

theorem coefficientEvaluation_pairing
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (x y : coefficientIdeal H B) :
    algebraMap (𝓞 F) F (algebraMap (OK G) (𝓞 F)
      (kLin (coefficientTraceLattice H G hbar B hB) 1 x y)) =
      ∑ σ, coefficientEvaluation H G F B x σ * coefficientDualEvaluation H G F B y σ := by
  have h := congrArg (algebraMap H.E F)
    (coefficient_kLin_sum H G hroot hbar B hB x y)
  simpa only [map_sum, map_mul] using! h

/-- The actual integral base change of the projective coefficient module. -/
abbrev IntegralTensor (B : Ideal (𝓞 H.E)) :=
  𝓞 F ⊗[OK G] coefficientIdeal H B

def integralEvaluation (B : Ideal (𝓞 H.E)) :
    IntegralTensor H G F B →ₗ[𝓞 F] (RootAut G → F) :=
  LinearMap.liftBaseChange (𝓞 F) (coefficientEvaluation H G F B)

theorem integralEvaluation_tmul (B : Ideal (𝓞 H.E))
    (a : 𝓞 F) (x : coefficientIdeal H B) :
    integralEvaluation H G F B (a ⊗ₜ[OK G] x) =
      a • coefficientEvaluation H G F B x := rfl

/-- The integral tensor image is the integral span, including every index. -/
theorem integralEvaluation_range (B : Ideal (𝓞 H.E)) :
    LinearMap.range (integralEvaluation H G F B) =
      Submodule.span (𝓞 F) (Set.range (coefficientEvaluation H G F B)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [integralEvaluation_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    | add t u ht hu =>
      rw [map_add]
      exact Submodule.add_mem _ ht hu
  · rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ[OK G] x, by rw [integralEvaluation_tmul, one_smul]⟩

def integralPairing
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (i : Fin (coefficientSerreFrame H G hbar B hB 1).n) :
    IntegralTensor H G F B →ₗ[𝓞 F] 𝓞 F :=
  LinearMap.liftBaseChange (𝓞 F)
    ((Algebra.linearMap (OK G) (𝓞 F)).comp
      ((LinearMap.proj i).comp (coefficientSerreFrame H G hbar B hB 1).incl))

theorem integralPairing_tmul
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (i : Fin (coefficientSerreFrame H G hbar B hB 1).n)
    (a : 𝓞 F) (x : coefficientIdeal H B) :
    integralPairing H G F hbar B hB i (a ⊗ₜ[OK G] x) =
      a * algebraMap (OK G) (𝓞 F)
        (kLin (coefficientTraceLattice H G hbar B hB) 1 x
          ((coefficientSerreFrame H G hbar B hB 1).y i)) := rfl

theorem integralPairing_sum
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (i : Fin (coefficientSerreFrame H G hbar B hB 1).n)
    (t : IntegralTensor H G F B) :
    algebraMap (𝓞 F) F (integralPairing H G F hbar B hB i t) =
      ∑ σ, integralEvaluation H G F B t σ *
        coefficientDualEvaluation H G F B
          ((coefficientSerreFrame H G hbar B hB 1).y i) σ := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [integralPairing_tmul, map_mul, coefficientEvaluation_pairing H G F hroot hbar B hB x
      ((coefficientSerreFrame H G hbar B hB 1).y i)]
    simp only [integralEvaluation_tmul, Pi.smul_apply, Algebra.smul_def,
      Finset.mul_sum, mul_assoc]
  | add t u ht hu =>
    simp only [map_add, ht, hu, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The original Hermitian frame still resolves the integral tensor. -/
theorem integralTensor_resolve
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (t : IntegralTensor H G F B) :
    t = ∑ i, integralPairing H G F hbar B hB i t •
      (1 ⊗ₜ[OK G] (coefficientSerreFrame H G hbar B hB 1).x i) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    conv_lhs => rw [(coefficientSerreFrame H G hbar B hB 1).resolve x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integralPairing_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  | add t u ht hu =>
    simp only [map_add, add_smul, Finset.sum_add_distrib, ← ht, ← hu]

theorem integralEvaluation_injective
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    Function.Injective (integralEvaluation H G F B) := by
  apply (injective_iff_map_eq_zero (integralEvaluation H G F B)).2
  intro t ht
  have hp : ∀ i, integralPairing H G F hbar B hB i t = 0 := by
    intro i
    apply RingOfIntegers.coe_injective
    rw [map_zero, integralPairing_sum H G F hroot hbar, ht]
    simp
  rw [integralTensor_resolve H G F hbar B hB t]
  simp [hp]

/-- Multiplication on M itself, before base change. -/
def coefficientMultiplication (B : Ideal (𝓞 H.E)) (a : 𝓞 H.E) :
    Module.End (OK G) (coefficientIdeal H B) where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' b x := smul_comm a b x

/-- The full O_E action is on the projective factor, not the scalar factor. -/
def integralCoefficientAction (B : Ideal (𝓞 H.E)) (a : 𝓞 H.E) :
    Module.End (𝓞 F) (IntegralTensor H G F B) :=
  LinearMap.baseChange (𝓞 F) (coefficientMultiplication H G B a)

theorem integralEvaluation_action (B : Ideal (𝓞 H.E)) (a : 𝓞 H.E)
    (t : IntegralTensor H G F B) (σ : RootAut G) :
    integralEvaluation H G F B (integralCoefficientAction H G F B a t) σ =
      algebraMap H.E F (σ.1 (a : H.E)) * integralEvaluation H G F B t σ := by
  induction t using TensorProduct.inductionOn with
  | tmul r x =>
    change (r : F) * algebraMap H.E F (σ.1 ((a : H.E) * (x : H.E))) =
      algebraMap H.E F (σ.1 (a : H.E)) *
        ((r : F) * algebraMap H.E F (σ.1 (x : H.E)))
    rw [map_mul, map_mul]
    ring
  | add t u ht hu =>
    simp only [map_add, Pi.add_apply, ht, hu, mul_add]

/-- The integral eigenspace for the actual field inclusion E -> F. -/
def integralEigenmodule (B : Ideal (𝓞 H.E)) :
    Submodule (𝓞 F) (IntegralTensor H G F B) where
  carrier := {t | ∀ a : 𝓞 H.E, integralCoefficientAction H G F B a t =
    algebraMap (𝓞 H.E) (𝓞 F) a • t}
  zero_mem' := by simp
  add_mem' := by
    intro t u ht hu a
    rw [map_add, ht a, hu a, smul_add]
  smul_mem' := by
    intro r t ht a
    rw [map_smul, ht a]
    exact smul_comm r (algebraMap (𝓞 H.E) (𝓞 F) a) t

theorem integralEigenmodule_iff_coordinates
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (t : IntegralTensor H G F B) :
    t ∈ integralEigenmodule H G F B ↔
      integralEvaluation H G F B t = Pi.single (identityAut G)
        (integralEvaluation H G F B t (identityAut G)) := by
  constructor
  · intro ht
    change ∀ a, integralCoefficientAction H G F B a t =
      algebraMap (𝓞 H.E) (𝓞 F) a • t at ht
    ext σ
    by_cases hσ : σ = identityAut G
    · simp [hσ]
    · rw [Pi.single_eq_of_ne hσ]
      by_contra hn
      have hs : (σ.1 : H.E →+* H.E) = RingHom.id H.E := by
        apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 H.E))
        apply RingHom.ext
        intro a
        apply (algebraMap H.E F).injective
        have ha := congrArg (fun u => integralEvaluation H G F B u σ) (ht a)
        rw [integralEvaluation_action, map_smul, Pi.smul_apply] at ha
        change algebraMap H.E F (σ.1 (a : H.E)) *
            integralEvaluation H G F B t σ =
          algebraMap H.E F (a : H.E) * integralEvaluation H G F B t σ at ha
        exact mul_right_cancel₀ hn ha
      exact hσ (Subtype.ext (AlgEquiv.ext fun a => DFunLike.congr_fun hs a))
  · intro ht a
    apply integralEvaluation_injective H G F hroot hbar B hB
    ext σ
    rw [integralEvaluation_action, map_smul, Pi.smul_apply, ht]
    by_cases hσ : σ = identityAut G
    · subst hσ
      rw [Pi.single_eq_same, Algebra.smul_def]
      rfl
    · simp [Pi.single_eq_of_ne hσ]

variable [NumberField F]

omit [IsCMField H.E] in
theorem inverse_extended_mem_iff (I : FractionalIdeal (𝓞 H.E)⁰ H.E) (hI : I ≠ 0)
    (t : F) :
    t ∈ (FractionalIdeal.extendedHom F (𝓞 F) I)⁻¹ ↔
      ∀ y ∈ I, t * algebraMap H.E F y ∈ (algebraMap (𝓞 F) F).range := by
  rw [FractionalIdeal.mem_inv_iff
    ((FractionalIdeal.extendedHom_eq_zero_iff F (𝓞 F)).not.mpr hI)]
  constructor
  · intro ht y hy
    apply (FractionalIdeal.mem_one_iff _).mp
    apply ht
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_extendedHom_eq_span]
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  · intro ht y hy
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_extendedHom_eq_span] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact (FractionalIdeal.mem_one_iff _).mpr (ht x hx)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add, ← FractionalIdeal.mem_coe]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [mul_smul_comm, ← FractionalIdeal.mem_coe]
      exact Submodule.smul_mem _ a hx

omit [IsCMField H.E] in
/-- Integral multiplication against conjugate(M) gives exactly the
extended different twist M D(E/K), with no principal replacement. -/
theorem coefficient_dual_axis_iff (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (t : F) :
    (∀ y : coefficientIdeal H B,
      t * algebraMap H.E F (H.conj (y : H.E)) ∈ (algebraMap (𝓞 F) F).range) ↔
      t ∈ FractionalIdeal.extendedHom F (𝓞 F)
        (coefficientIdeal H B *
          (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E)) := by
  let J : FractionalIdeal (𝓞 H.E)⁰ H.E :=
    ((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)
  have hJ : J ≠ 0 := (halfDifferent_ne_zero H B hB).2
  have hB0 : B ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp (halfDifferent_ne_zero H B hB).1
  have hrange : Set.range (fun y : coefficientIdeal H B => H.conj (y : H.E)) =
      ((J⁻¹ : FractionalIdeal (𝓞 H.E)⁰ H.E) : Set H.E) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (NativeRawHostDifferent.kc_mem_inv_smul H H.conj B hB0 _).mpr y.2
    · intro hz
      have hy : H.conj z ∈ coefficientIdeal H B := by
        apply (NativeRawHostDifferent.kc_mem_inv_smul H H.conj B hB0 _).mp
        simpa only [conj_conj] using! hz
      exact ⟨⟨H.conj z, hy⟩, conj_conj H z⟩
  rw [coefficientDifferent_eq_conjHalf H B hB]
  change _ ↔ t ∈ FractionalIdeal.extendedHom F (𝓞 F) J
  rw [← inv_inv J, map_inv₀, inverse_extended_mem_iff H F J⁻¹ (inv_ne_zero hJ)]
  constructor
  · intro ht y hy
    rw [← SetLike.mem_coe, ← hrange] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ht z
  · intro ht y
    apply ht
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨y, rfl⟩

theorem coefficient_single_mem_iff
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (t : F) :
    Pi.single (identityAut G) t ∈
        Submodule.span (𝓞 F) (Set.range (coefficientEvaluation H G F B)) ↔
      t ∈ FractionalIdeal.extendedHom F (𝓞 F)
        (coefficientIdeal H B *
          (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E)) := by
  let D := coefficientTraceLattice H G hbar B hB
  let fr := coefficientSerreFrame H G hbar B hB 1
  have hexp (a : coefficientIdeal H B) :
      coefficientEvaluation H G F B a =
        ∑ m, algebraMap (𝓞 F) F (algebraMap (OK G) (𝓞 F)
          (kLin D 1 a (fr.y m))) • coefficientEvaluation H G F B (fr.x m) := by
    conv_lhs => rw [fr.resolve a, map_sum]
    simp only [map_smul, algebraMap_smul, D]
  have h := single_mem_span_iff_of_pairing (OK G) (𝓞 F) F (coefficientIdeal H B)
    (RootAut G) (algebraMap (OK G) (𝓞 F)) (fun a b => kLin D 1 a b)
    (coefficientEvaluation H G F B) (coefficientDualEvaluation H G F B)
    fr.n fr.x fr.y (coefficientEvaluation_pairing H G F hroot hbar B hB)
    hexp (coefficientEvaluation_span H G F B hB) (identityAut G) t
  exact h.trans (coefficient_dual_axis_iff H F B hB t)

def eigenCoordinate (B : Ideal (𝓞 H.E)) :
    integralEigenmodule H G F B →ₗ[𝓞 F] F :=
  (LinearMap.proj (identityAut G)).comp
    ((integralEvaluation H G F B).comp (integralEigenmodule H G F B).subtype)

/-- The coordinate image of the actual integral eigenspace is the actual
extended fractional ideal used by the native CM degree computation. -/
theorem eigenCoordinate_range
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    LinearMap.range (eigenCoordinate H G F B) =
      (FractionalIdeal.extendedHom F (𝓞 F)
        (coefficientIdeal H B *
          (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
          Submodule (𝓞 F) F) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    apply (coefficient_single_mem_iff H G F hroot hbar B hB _).mp
    change (Pi.single (identityAut G) (integralEvaluation H G F B t (identityAut G)) :
      RootAut G → F) ∈ _
    rw [← (integralEigenmodule_iff_coordinates H G F hroot hbar B hB t).mp t.property,
      ← integralEvaluation_range]
    exact ⟨t, rfl⟩
  · intro hz
    have hm := (coefficient_single_mem_iff H G F hroot hbar B hB z).mpr hz
    rw [← integralEvaluation_range] at hm
    obtain ⟨t, ht⟩ := hm
    have ht0 : integralEvaluation H G F B t (identityAut G) = z := by
      simpa using! congrFun ht (identityAut G)
    have heig : t ∈ integralEigenmodule H G F B := by
      apply (integralEigenmodule_iff_coordinates H G F hroot hbar B hB t).mpr
      rw [ht0]
      exact ht
    exact ⟨⟨t, heig⟩, ht0⟩

omit [NumberField F] in
theorem eigenCoordinate_injective
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    Function.Injective (eigenCoordinate H G F B) := by
  intro x y hxy
  apply Subtype.ext
  apply integralEvaluation_injective H G F hroot hbar B hB
  rw [(integralEigenmodule_iff_coordinates H G F hroot hbar B hB x).mp x.property,
    (integralEigenmodule_iff_coordinates H G F hroot hbar B hB y).mp y.property]
  exact congrArg (Pi.single (identityAut G)) hxy

/-- The genuine integral eigenmodule is linearly equivalent to the literal
different-twisted coefficient ideal. Both modules are constructed. -/
def eigenCoordinateEquiv
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    integralEigenmodule H G F B ≃ₗ[𝓞 F]
      (FractionalIdeal.extendedHom F (𝓞 F)
        (coefficientIdeal H B *
          (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E))) := by
  let f := (eigenCoordinate H G F B).codRestrict
    (FractionalIdeal.extendedHom F (𝓞 F)
      (coefficientIdeal H B *
        (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
          Submodule (𝓞 F) F)
    (fun x => (eigenCoordinate_range H G F hroot hbar B hB).le ⟨x, rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    exact eigenCoordinate_injective H G F hroot hbar B hB
      (congrArg Subtype.val hxy)
  · intro t
    obtain ⟨x, hx⟩ := (eigenCoordinate_range H G F hroot hbar B hB).symm.le t.property
    exact ⟨x, Subtype.ext hx⟩

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM NativeRawHostPolarization

/-- A single native half-different supplies the integral tensor eigenline
and the exact finite ideal for every field extension. -/
theorem nativeDyadicHost_exists_integralSerreEigenlattice
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (_hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ (F : Type) [Field F] [NumberField F] [Algebra H.E F],
        Nonempty (integralEigenmodule H.toHostRaw G F B ≃ₗ[𝓞 F]
          FractionalIdeal.extendedHom F (𝓞 F)
            (coefficientIdeal H.toHostRaw B *
              (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E))) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro F _ _ _
  exact ⟨eigenCoordinateEquiv H.toHostRaw G F rfl
    (nativeDyadicGeometricHost_bar_eq e q d he hH) B hB⟩

end RHLean.Analysis.AlpogeThin

end
