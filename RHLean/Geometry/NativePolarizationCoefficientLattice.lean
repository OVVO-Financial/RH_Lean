import RHLean.Analysis.AlpogeThin.NativeDyadicHostPolarizationArithmetic

/-!
# The actual integral alternating coefficient lattice

For the half-different ideal constructed on the native field, its inverse
is a finite free integer lattice of the full field degree. The source
imaginary generator gives a perfect alternating trace form on this exact
lattice, with the original conjugate adjointness for the ring of integers.

This is the coefficient lattice in the source's polarization construction.
It does not replace the prescribed Hermitian spaces or their signatures:
forming the complete geometric `Datum` still requires those spaces and the
corresponding real and finite-place compatibility constructions.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/LocalToGlobal/ProjectiveLattices/`
`HalfOneAddSqrtNegIsIntegral.lean`, `intForm`, `efQ_alt`, `efQ_adj`, and
`HostInt.lean`, `trace_rep`, `trace_sep`, `efQ_surj`.
Here Mathlib's actual basis of a nonzero fractional ideal permits the
coefficient-lattice case without assuming a Hermitian-space datum.
The source archive/mirror states no license; attribution is retained
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField FractionalIdeal
open scoped Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

namespace NativeRawHostPolarization

variable {φ : Frame} (H : HostRaw φ)

abbrev coefficientIdeal (B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E :=
  (B : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹

theorem coefficientIdeal_finite (B : Ideal (𝓞 H.E)) :
    Module.Finite ℤ (coefficientIdeal H B) := inferInstance

theorem coefficientIdeal_free (B : Ideal (𝓞 H.E)) :
    Module.Free ℤ (coefficientIdeal H B) := inferInstance

theorem coefficientIdeal_finite_over_integers (B : Ideal (𝓞 H.E)) :
    Module.Finite (𝓞 H.E) (coefficientIdeal H B) :=
  Module.Finite.iff_fg.mpr
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl (coefficientIdeal H B))

theorem coefficientIdeal_projective (B : Ideal (𝓞 H.E)) :
    Module.Projective (𝓞 H.E) (coefficientIdeal H B) := by
  have := coefficientIdeal_finite_over_integers H B
  have := Module.finitePresentation_of_finite (𝓞 H.E) (coefficientIdeal H B)
  exact Module.Flat.projective_of_finitePresentation

theorem coefficientIdeal_isLocalized (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    IsLocalizedModule (𝓞 H.E)⁰
      (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).subtype where
  map_units s := by
    rw [← (Algebra.lmul (𝓞 H.E) H.E).commutes, Algebra.lmul_isUnit_iff,
      isUnit_iff_ne_zero]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  surj y := by
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj (𝓞 H.E)⁰ y
    have h1 : (1 : H.E) ∈ coefficientIdeal H B :=
      FractionalIdeal.one_mem_inv_coe_ideal
        (coeIdeal_ne_zero.mp (halfDifferent_ne_zero H B hB).1)
    have ha : (a : H.E) ∈ coefficientIdeal H B := by
      change algebraMap (𝓞 H.E) H.E a ∈
        (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)
      simpa only [Algebra.smul_def, mul_one] using
        (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).smul_mem a h1
    refine ⟨(⟨(a : H.E), ha⟩, s), ?_⟩
    change algebraMap (𝓞 H.E) H.E s * y = algebraMap (𝓞 H.E) H.E a
    rw [mul_comm]
    exact has
  exists_of_eq h := ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩

theorem coefficientIdeal_rank_over_integers (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    Module.finrank (𝓞 H.E) (coefficientIdeal H B) = 1 := by
  have := coefficientIdeal_isLocalized H B hB
  calc
    _ = Module.finrank (𝓞 H.E) H.E :=
      (IsLocalizedModule.finrank_eq (p := (𝓞 H.E)⁰)
        (f := (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).subtype) le_rfl).symm
    _ = Module.finrank H.E H.E :=
      (IsFractionRing.finrank_right_eq (R := 𝓞 H.E) (S := H.E) (N := H.E)).symm
    _ = 1 := Module.finrank_self H.E

theorem coefficientIdeal_rank (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    Module.finrank ℤ (coefficientIdeal H B) = Module.finrank ℚ H.E := by
  let I : (FractionalIdeal (𝓞 H.E)⁰ H.E)ˣ :=
    Units.mk0 (coefficientIdeal H B) (inv_ne_zero (halfDifferent_ne_zero H B hB).1)
  have h := NumberField.fractionalIdeal_rank H.E I
  change Module.finrank ℤ (coefficientIdeal H B) = Module.finrank ℤ (𝓞 H.E) at h
  rw [RingOfIntegers.rank] at h
  exact h

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  have h := congrArg (fun σ : H.E ≃ₐ[ℚ] H.E => σ x) (NativeRawHostDifferent.conj_sq H)
  simpa only [AlgEquiv.mul_apply, AlgEquiv.one_apply] using h

/-- The rational trace pairing restricted to the actual coefficient lattice. -/
def traceFormQ (B : Ideal (𝓞 H.E)) :
    coefficientIdeal H B →ₗ[ℤ] coefficientIdeal H B →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun x y => Algebra.trace ℚ H.E (xi H * H.conj x * y))
    (fun x x' y => by
      change Algebra.trace ℚ H.E (xi H * H.conj ((x : H.E) + x') * y) = _
      rw [map_add, mul_add, add_mul, map_add])
    (fun c x y => by
      change Algebra.trace ℚ H.E (xi H * H.conj (c • (x : H.E)) * y) =
        c • Algebra.trace ℚ H.E (xi H * H.conj x * y)
      rw [map_zsmul, mul_smul_comm, smul_mul_assoc, map_zsmul])
    (fun x y y' => by
      change Algebra.trace ℚ H.E (xi H * H.conj x * ((y : H.E) + y')) = _
      rw [mul_add, map_add])
    (fun c x y => by
      change Algebra.trace ℚ H.E (xi H * H.conj x * (c • (y : H.E))) =
        c • Algebra.trace ℚ H.E (xi H * H.conj x * y)
      rw [mul_smul_comm, map_zsmul])

theorem traceFormQ_integral (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (x y : coefficientIdeal H B) : ∃ n : ℤ, traceFormQ H B x y = n := by
  have hB0 : B ≠ ⊥ := coeIdeal_ne_zero.mp (halfDifferent_ne_zero H B hB).1
  have hx := (NativeRawHostDifferent.kc_mem_inv_smul H H.conj B hB0 (x : H.E)).mpr x.2
  have hmem : H.conj (x : H.E) * (y : H.E) ∈
      (B : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ *
      ((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ := by
    simpa only [mul_comm] using mul_mem_mul y.2 hx
  simpa only [traceFormQ, LinearMap.mk₂_apply, mul_assoc] using
    trace_integral_of_mem H B hB hmem

private theorem chosenInt_cast {M : Type} [AddCommGroup M]
    (F : M →ₗ[ℤ] M →ₗ[ℤ] ℚ) (h : ∀ x y, ∃ n : ℤ, F x y = n) (x y : M) :
    (((h x y).choose : ℤ) : ℚ) = F x y := (h x y).choose_spec.symm

private def ofIntegral {M : Type} [AddCommGroup M]
    (F : M →ₗ[ℤ] M →ₗ[ℤ] ℚ) (h : ∀ x y, ∃ n : ℤ, F x y = n) :
    LinearMap.BilinForm ℤ M :=
  LinearMap.mk₂ ℤ (fun x y => (h x y).choose)
    (fun x x' y => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, chosenInt_cast, chosenInt_cast, chosenInt_cast,
        map_add, LinearMap.add_apply]))
    (fun c x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, chosenInt_cast, chosenInt_cast,
        LinearMap.map_smul₂, zsmul_eq_mul]))
    (fun x y y' => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, chosenInt_cast, chosenInt_cast, chosenInt_cast, map_add]))
    (fun c x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, chosenInt_cast, chosenInt_cast,
        map_zsmul, zsmul_eq_mul]))

/-- The integral form is constructed from proved integrality. -/
def integralTraceForm (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    LinearMap.BilinForm ℤ (coefficientIdeal H B) :=
  ofIntegral (traceFormQ H B) (traceFormQ_integral H B hB)

theorem integralTraceForm_cast (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (x y : coefficientIdeal H B) :
    ((integralTraceForm H B hB x y : ℤ) : ℚ) =
      Algebra.trace ℚ H.E (xi H * H.conj x * y) :=
  chosenInt_cast (traceFormQ H B) (traceFormQ_integral H B hB) x y

theorem integralTraceForm_alternating (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (x : coefficientIdeal H B) : integralTraceForm H B hB x x = 0 := by
  have heq : H.conj (xi H * H.conj (x : H.E) * x) =
      -(xi H * H.conj (x : H.E) * x) := by
    rw [map_mul, map_mul, conj_xi, conj_conj]
    ring
  have ht := Algebra.trace_eq_of_algEquiv H.conj (xi H * H.conj (x : H.E) * x)
  rw [heq, map_neg] at ht
  apply Int.cast_injective (α := ℚ)
  rw [integralTraceForm_cast, Int.cast_zero]
  linarith

theorem integralTraceForm_adjoint (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (a : 𝓞 H.E) (x y : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) :
    integralTraceForm H B hB (a • x) y =
      integralTraceForm H B hB x ((H.conj • a) • y) := by
  apply Int.cast_injective (α := ℚ)
  rw [integralTraceForm_cast, integralTraceForm_cast]
  change Algebra.trace ℚ H.E (xi H * H.conj ((a : H.E) * x) * y) =
    Algebra.trace ℚ H.E (xi H * H.conj (x : H.E) * (H.conj (a : H.E) * y))
  rw [map_mul]
  congr 1
  ring

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Self-duality is derived from the principal identity, with the same
imaginary generator and conjugation as the integral form. -/
theorem mem_coefficientIdeal_iff (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (x : H.E) :
    x ∈ coefficientIdeal H B ↔
      ∀ y ∈ coefficientIdeal H B,
        Algebra.trace ℚ H.E (xi H * H.conj x * y) ∈ (algebraMap ℤ ℚ).range := by
  have hB0 := (halfDifferent_ne_zero H B hB).1
  have hA0 : coefficientIdeal H B ≠ 0 := inv_ne_zero hB0
  have hJ : spanSingleton (𝓞 H.E)⁰ (xi H) * coefficientIdeal H B *
      ((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
    rw [eq_inv_of_mul_eq_one_left (principalIdentity H B hB),
      coeIdeal_differentIdeal ℤ ℚ H.E (𝓞 H.E), inv_inv]
  have hdual : FractionalIdeal.dual ℤ ℚ (coefficientIdeal H B) =
      spanSingleton (𝓞 H.E)⁰ (xi H) *
      ((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ := by
    rw [FractionalIdeal.dual_eq_mul_inv, ← hJ]
    calc
      _ = (spanSingleton (𝓞 H.E)⁰ (xi H) *
          ((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) *
          (coefficientIdeal H B * (coefficientIdeal H B)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hA0, mul_one]
  have hmem : xi H * H.conj x ∈ FractionalIdeal.dual ℤ ℚ (coefficientIdeal H B) ↔
      x ∈ coefficientIdeal H B := by
    rw [hdual, mem_singleton_mul]
    constructor
    · rintro ⟨y, hy, hxy⟩
      apply (NativeRawHostDifferent.kc_mem_inv_smul H H.conj B
        (coeIdeal_ne_zero.mp hB0) x).mp
      rw [mul_left_cancel₀ (xi_ne_zero H) hxy]
      exact hy
    · intro hx
      exact ⟨H.conj x, (NativeRawHostDifferent.kc_mem_inv_smul H H.conj B
        (coeIdeal_ne_zero.mp hB0) x).mpr hx, rfl⟩
  simpa only [mem_dual hA0, Algebra.traceForm_apply] using hmem.symm

/-- The trace pairing separates points using an actual basis of the same
fractional ideal. -/
private theorem trace_separates (I : (FractionalIdeal (𝓞 H.E)⁰ H.E)ˣ) (z : H.E)
    (h : ∀ y : (I : FractionalIdeal (𝓞 H.E)⁰ H.E),
      Algebra.trace ℚ H.E (z * y) = 0) : z = 0 := by
  have hlin : Algebra.traceForm ℚ H.E z = 0 :=
    (NumberField.basisOfFractionalIdeal H.E I).ext fun i => by
      change Algebra.trace ℚ H.E (z * NumberField.basisOfFractionalIdeal H.E I i) = 0
      rw [NumberField.basisOfFractionalIdeal_apply]
      exact h (NumberField.fractionalIdealBasis H.E I.1 i)
  exact (traceForm_nondegenerate ℚ H.E).1 z fun y => LinearMap.congr_fun hlin y

/-- An integer linear functional on the same fractional ideal has a trace
representative. The dual basis is constructed, not assumed. -/
private theorem trace_represents (I : (FractionalIdeal (𝓞 H.E)⁰ H.E)ˣ)
    (f : (I : FractionalIdeal (𝓞 H.E)⁰ H.E) →ₗ[ℤ] ℤ) :
    ∃ z : H.E, ∀ y : (I : FractionalIdeal (𝓞 H.E)⁰ H.E),
      Algebra.trace ℚ H.E (z * y) = (f y : ℚ) := by
  classical
  let bZ := NumberField.fractionalIdealBasis H.E I.1
  let bQ := NumberField.basisOfFractionalIdeal H.E I
  have hnd := traceForm_nondegenerate ℚ H.E
  let db := (Algebra.traceForm ℚ H.E).dualBasis hnd bQ
  let z : H.E := ∑ i, (f (bZ i) : ℚ) • db i
  have key : ∀ i k, Algebra.trace ℚ H.E (db i * bQ k) = if k = i then 1 else 0 := by
    intro i k
    rw [← Algebra.traceForm_apply]
    exact (Algebra.traceForm ℚ H.E).apply_dualBasis_left hnd bQ i k
  let tr : (I : FractionalIdeal (𝓞 H.E)⁰ H.E) →ₗ[ℤ] ℚ :=
    { toFun := fun y => Algebra.trace ℚ H.E (z * y)
      map_add' := by intro x y; simp only [Submodule.coe_add, mul_add, map_add]
      map_smul' := by
        intro c y
        change Algebra.trace ℚ H.E (z * (c • (y : H.E))) =
          c • Algebra.trace ℚ H.E (z * y)
        rw [mul_smul_comm, map_zsmul] }
  let fQ : (I : FractionalIdeal (𝓞 H.E)⁰ H.E) →ₗ[ℤ] ℚ :=
    { toFun := fun y => (f y : ℚ)
      map_add' := by intro x y; simp
      map_smul' := by intro c y; simp }
  have heq : tr = fQ := bZ.ext fun k => by
    change Algebra.trace ℚ H.E (z * (bZ k : H.E)) = (f (bZ k) : ℚ)
    rw [show (bZ k : H.E) = bQ k from
      (NumberField.basisOfFractionalIdeal_apply H.E I k).symm]
    dsimp only [z]
    rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, map_smul, key]
    simp
  exact ⟨z, fun y => LinearMap.congr_fun heq y⟩

/-- The integral alternating form is perfect on the actual inverse ideal. -/
theorem integralTraceForm_bijective (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    Function.Bijective (integralTraceForm H B hB) := by
  let I : (FractionalIdeal (𝓞 H.E)⁰ H.E)ˣ :=
    Units.mk0 (coefficientIdeal H B) (inv_ne_zero (halfDifferent_ne_zero H B hB).1)
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hz : xi H * H.conj (x : H.E) = 0 :=
      trace_separates H I _ fun y => by
        have hval : integralTraceForm H B hB x y = 0 := LinearMap.congr_fun hx y
        calc
          Algebra.trace ℚ H.E (xi H * H.conj (x : H.E) * y) =
              ((integralTraceForm H B hB x y : ℤ) : ℚ) :=
            (integralTraceForm_cast H B hB x y).symm
          _ = 0 := by rw [hval, Int.cast_zero]
    have hx0 : H.conj (x : H.E) = 0 := (mul_eq_zero.mp hz).resolve_left (xi_ne_zero H)
    apply Subtype.ext
    exact H.conj.injective (hx0.trans (map_zero H.conj).symm)
  · intro f
    obtain ⟨z, hz⟩ := trace_represents H I f
    let x : H.E := H.conj.symm ((xi H)⁻¹ * z)
    have hx : xi H * H.conj x = z := by
      dsimp only [x]
      rw [AlgEquiv.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ (xi_ne_zero H), one_mul]
    have hxA : x ∈ coefficientIdeal H B := (mem_coefficientIdeal_iff H B hB x).mpr fun y hy => by
      rw [hx, hz ⟨y, hy⟩]
      exact ⟨f ⟨y, hy⟩, rfl⟩
    refine ⟨⟨x, hxA⟩, ?_⟩
    ext y
    apply Int.cast_injective (α := ℚ)
    rw [integralTraceForm_cast]
    change Algebra.trace ℚ H.E (xi H * H.conj x * y) = (f y : ℚ)
    rw [hx]
    exact hz y

end NativeRawHostPolarization

/-- Construct the actual coefficient ideal and its perfect alternating
integral form, preserving the original native degree and adjointness. -/
theorem nativeDyadicHostRaw_exists_polarizationCoefficientLattice
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      Module.finrank (𝓞 H.E) (NativeRawHostPolarization.coefficientIdeal H B) = 1 ∧
      Module.finrank ℤ (NativeRawHostPolarization.coefficientIdeal H B) = 4 * 2 ^ e ∧
      Function.Bijective (NativeRawHostPolarization.integralTraceForm H B hB) ∧
      (∀ x, NativeRawHostPolarization.integralTraceForm H B hB x x = 0) ∧
      (∀ (a : 𝓞 H.E) x y,
        NativeRawHostPolarization.integralTraceForm H B hB (a • x) y =
          NativeRawHostPolarization.integralTraceForm H B hB x ((H.conj • a) • y)) := by
  let H := nativeDyadicHostRaw e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv,
    NativeRawHostPolarization.coefficientIdeal_rank_over_integers H B hB, ?_,
    NativeRawHostPolarization.integralTraceForm_bijective H B hB,
    NativeRawHostPolarization.integralTraceForm_alternating H B hB,
    NativeRawHostPolarization.integralTraceForm_adjoint H B hB⟩
  rw [NativeRawHostPolarization.coefficientIdeal_rank H B hB,
    nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord]

end RHLean.Analysis.AlpogeThin

end
