import RHLean.Geometry.NativePolarizationRealCoordinates
import RHLean.Geometry.NativePrescribedPolarizationLattice

/-!
# Realize the same prescribed inverse-ideal lattice at its actual CM type

This constructs the real tensor equivalence needed by the source
`DatProofs.domFor_pm`, on the literal native product-span lattice. Its formula
is the original `DatTheta.theta` formula in the standard frame of W_j.
The coefficient ideal is the SAME inverse half-different, and the embeddings
are the SAME raw-host CM type already identified with the geometric signature.

Surjectivity is proved by the actual inclusion O(E)^N into (B^-1)^N: every
integral ideal's nonzero inverse contains 1. The source's finite-coordinate
embedding theorem supplies a preimage, and the existing exact integer rank
supplies injectivity after real base change. No independent realization,
spanning, injectivity or complex-structure premise is assumed.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean`, `theta`,
`theta_tmul`, `phiI_bijective`, `theta_bijective`; and `DatProofs.lean`,
`thW`, `thW_tmul`, `thW_bijective`. The proof here specializes their realization
to the constructed diagonal native lattice. The source mirror states no
license; attribution is retained without assigning one.

The subsequent complex structure, real positivity and its two exact trace
identities remain further work. The fixed native Hermitian form conjugates
its FIRST argument: its source positivity is `EF(J x, x) > 0`, with the
matching negative sign in `trace_R(J A) = -2 * Im(t)`. The realization does
not change that convention. This file does not assert a completed Datum
or a finite-adelic comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical TensorProduct Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativePolarizationRealCoordinates

namespace NativeRawHostPolarization

variable {φ : Frame} (H : HostRaw φ)

/-- The finite enumeration of the original raw-host CM type. -/
def cmTypeFinset : Finset (H.E →+* ℂ) :=
  Finset.univ.filter fun τ => τ ∈ H.cmType

@[simp] theorem mem_cmTypeFinset (τ : H.E →+* ℂ) :
    τ ∈ cmTypeFinset H ↔ τ ∈ H.cmType := by
  simp only [cmTypeFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem cmTypeFinset_conjugate (τ : H.E →+* ℂ) :
    τ ∈ cmTypeFinset H ↔ ComplexEmbedding.conjugate τ ∉ cmTypeFinset H := by
  simp only [mem_cmTypeFinset]
  exact NativeRawHostCore.cmType_iff H τ

/-- Every integral coordinate lies in the actual inverse half-different. -/
theorem integer_mem_coefficientIdeal (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (a : 𝓞 H.E) :
    (a : H.E) ∈ coefficientIdeal H B := by
  have h1 : (1 : H.E) ∈ coefficientIdeal H B :=
    FractionalIdeal.one_mem_inv_coe_ideal
      (FractionalIdeal.coeIdeal_ne_zero.mp (halfDifferent_ne_zero H B hB).1)
  change algebraMap (𝓞 H.E) H.E a ∈
    (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)
  simpa only [Algebra.smul_def, mul_one] using
    (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).smul_mem a h1

/-- The actual integral-coordinate inclusion into the same source lattice. -/
def integralCoordinates (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    (Fin N → 𝓞 H.E) →+ twistedLattice H B N where
  toFun v := ⟨fun i => (v i : H.E),
    (mem_twistedLattice H B N _).mpr fun i => integer_mem_coefficientIdeal H B hB (v i)⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The original coordinate embedding map on the real tensor of the literal
native product-span lattice, before proving it is an equivalence. -/
def twistedRealCoordinates (B : Ideal (𝓞 H.E)) (N : ℕ) :
    ℝ ⊗[ℤ] twistedLattice H B N →ₗ[ℝ] (cmTypeFinset H → Fin N → ℂ) :=
  theta (Pi.basisFun H.E (Fin N)) (cmTypeFinset H) (twistedLattice H B N)

theorem twistedRealCoordinates_tmul (B : Ideal (𝓞 H.E)) (N : ℕ)
    (a : ℝ) (v : twistedLattice H B N) :
    twistedRealCoordinates H B N (a ⊗ₜ v) =
      fun (τ : cmTypeFinset H) i => (a : ℂ) * (τ : H.E →+* ℂ) (v.1 i) := by
  simp only [twistedRealCoordinates, theta_tmul, Pi.basisFun_repr]

/-- The native tensor map agrees with the source's integral-coordinate
embedding after the actual integral inclusion. -/
theorem twistedRealCoordinates_integralCoordinates (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (t : ℝ ⊗[ℤ] (Fin N → 𝓞 H.E)) :
    twistedRealCoordinates H B N
        (LinearMap.baseChange ℝ (integralCoordinates H B hB N).toIntLinearMap t) =
      phiI (ι := Fin N) (cmTypeFinset H) t := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => rw [map_add, map_add, ht, hu, map_add]
  | tmul a v =>
    simp only [LinearMap.baseChange_tmul, twistedRealCoordinates_tmul, phiI_tmul,
      AddMonoidHom.coe_toIntLinearMap, integralCoordinates]
    rfl

/-- Surjectivity is constructed through the actual integral lattice; its
exact rank then proves injectivity on the same real tensor product. -/
theorem twistedRealCoordinates_bijective (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    Function.Bijective (twistedRealCoordinates H B N) := by
  have := twistedLattice_free_int H B N
  have := twistedLattice_finite_int H B N
  have hsurj : Function.Surjective (twistedRealCoordinates H B N) := by
    intro u
    obtain ⟨t, ht⟩ := (phiI_bijective (ι := Fin N) (cmTypeFinset_conjugate H)).2 u
    refine ⟨LinearMap.baseChange ℝ (integralCoordinates H B hB N).toIntLinearMap t, ?_⟩
    rw [twistedRealCoordinates_integralCoordinates, ht]
  have hdim : Module.finrank ℝ (ℝ ⊗[ℤ] twistedLattice H B N) =
      Module.finrank ℝ (cmTypeFinset H → Fin N → ℂ) := by
    rw [Module.finrank_baseChange, twistedLattice_rank_int H B hB N]
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe,
      nsmul_eq_mul, Nat.cast_id]
    rw [← two_card (cmTypeFinset_conjugate H)]
    ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- The actual real realization, with the proved source coordinate formula. -/
def twistedRealEquiv (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    (ℝ ⊗[ℤ] twistedLattice H B N) ≃ₗ[ℝ] (cmTypeFinset H → Fin N → ℂ) :=
  LinearEquiv.ofBijective (twistedRealCoordinates H B N)
    (twistedRealCoordinates_bijective H B hB N)

/-- Specialize to the full original rank `k + m - 1` of the prescribed W_j. -/
def prescribedRealEquiv (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m : ℕ) :
    (ℝ ⊗[ℤ] prescribedLattice H B k m) ≃ₗ[ℝ]
      (cmTypeFinset H → Fin (k + m - 1) → ℂ) :=
  twistedRealEquiv H B hB (k + m - 1)

theorem prescribedRealEquiv_tmul (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m : ℕ)
    (a : ℝ) (v : prescribedLattice H B k m) :
    prescribedRealEquiv H B hB k m (a ⊗ₜ v) =
      fun (τ : cmTypeFinset H) i => (a : ℂ) * (τ : H.E →+* ℂ) (v.1 i) :=
  twistedRealCoordinates_tmul H B (k + m - 1) a v

end NativeRawHostPolarization

open NativeRawHostPolarization

/-- A single constructed half-different gives the real coordinate realization
of every prescribed rank on the same native field and original CM type. -/
theorem nativeDyadicHostRaw_exists_prescribedRealization
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (_hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ k m : ℕ, ∃ θ : (ℝ ⊗[ℤ] prescribedLattice H B k m) ≃ₗ[ℝ]
          (cmTypeFinset H → Fin (k + m - 1) → ℂ),
        ∀ (a : ℝ) (v : prescribedLattice H B k m),
          θ (a ⊗ₜ v) = fun (τ : cmTypeFinset H) i =>
            (a : ℂ) * (τ : H.E →+* ℂ) (v.1 i) := by
  let H := nativeDyadicHostRaw e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro k m
  exact ⟨prescribedRealEquiv H B hB k m, prescribedRealEquiv_tmul H B hB k m⟩

end RHLean.Analysis.AlpogeThin

end
