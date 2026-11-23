import RHLean.Geometry.NativePrescribedPolarizationLattice

/-!
# Actual lattice counts for the finite theta-orbit torsion argument

The coefficient-twisted lattice already constructed on the native arithmetic
host is finite projective over `O_E` and free over `Z`. We retain that lattice
and prove its exact residue and rational-level quotient cardinalities.

For a maximal ideal `I` the exponent is the `O_E`-rank `N`, and the base is
`absNorm I`. For a rational integer level `g`, the base is `g` and the
exponent is the full integer rank `N * [E : Q]`. A prime of residue norm `g`
is not silently supplied. These are the finite counts needed before applying
the primary-torsion theorem; the geometric Tate/level identification and
divisibility of the corresponding primary torsion remain separate steps.

Source: `GlobalTheory.natCard_quot_maximal_smul_top_eq` in
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
`NatCardQuotSmulTopLePowFinrank.lean`, at
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The actual host-lattice specialization uses the native finite-projective
construction and both of its proved ranks. The source archive/mirror states
no license; attribution is retained without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped Pointwise

namespace RHLean.Geometry.NativeThetaOrbitTorsion

open TensorProduct in
/-- Exact residue cardinality for the original finite flat module; no basis
over the integral coefficient ring is chosen. -/
theorem natCard_quot_maximal_smul_top_eq
    {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M]
    (P : Ideal R) [P.IsMaximal] :
    Nat.card (M ⧸ (P • (⊤ : Submodule R M))) =
      Nat.card (R ⧸ P) ^ Module.finrank R M := by
  letI := Ideal.Quotient.field P
  let e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  rw [← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]
  congr 1
  let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) =
      Module.finrank R M := by
    rw [Module.rankAtStalk_eq]
    exact Ideal.finrank_fiber_eq_finrank _
  rw [← h2, ← h1]
  rfl

end RHLean.Geometry.NativeThetaOrbitTorsion

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativeThetaOrbitTorsion

variable {φ : Frame} (H : HostRaw φ)

/-- The actual inverse-ideal lattice has exactly the residue-norm power
predicted by its proved integral coefficient rank. -/
theorem twistedLattice_residue_card
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (N : ℕ) (I : Ideal (𝓞 H.E)) [I.IsMaximal] :
    Nat.card (twistedLattice H B N ⧸
      (I • (⊤ : Submodule (𝓞 H.E) (twistedLattice H B N)))) =
        Ideal.absNorm I ^ N := by
  letI := twistedLattice_finite H B N
  letI := twistedLattice_projective H B N
  rw [natCard_quot_maximal_smul_top_eq,
    twistedLattice_rank H B hB N, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- At a rational integer level, the full integer rank is retained. This
quotient is the actual additive lattice modulo multiplication by `g`. -/
theorem twistedLattice_integer_level_card
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (N g : ℕ) :
    Nat.card (twistedLattice H B N ⧸
      (nsmulAddMonoidHom (α := twistedLattice H B N) g).range) =
        g ^ (N * Module.finrank ℚ H.E) := by
  letI := twistedLattice_free_int H B N
  letI := twistedLattice_finite_int H B N
  change (nsmulAddMonoidHom (α := twistedLattice H B N) g).range.index = _
  rw [AddSubgroup.index_range_nsmul, twistedLattice_rank_int H B hB N]

/-- Nonzero rational levels give genuine finite quotients of that same
lattice, with no substitute coordinate module. -/
theorem twistedLattice_integer_level_finite
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (N g : ℕ) (hg : g ≠ 0) :
    Finite (twistedLattice H B N ⧸
      (nsmulAddMonoidHom (α := twistedLattice H B N) g).range) := by
  apply Nat.finite_of_card_ne_zero
  rw [twistedLattice_integer_level_card H B hB N g]
  exact pow_ne_zero _ hg

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
