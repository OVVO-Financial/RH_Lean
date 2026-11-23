import RHLean.Geometry.NativeCMSerreTensor

/-!
# The finite-place degree correction of the actual coefficient module

The Serre coefficient module is literally B^-1. The different twist occurring
in the CM eigenline degree is therefore B^-1 D(E/K) = conjugate(B), and its
normalized log norm is exactly half the root-discriminant difference. The
same correction is preserved under the actual extension of fractional ideals
to any number field containing E. No principal replacement for B, arithmetic
Lie metric, or assigned CM height is introduced.

This supplies the finite-ideal calculation in the source degree formula.
Identifying that ideal with an integral scheme-theoretic Lie eigenspace and
computing the mean of its actual archimedean Lie norms remain separate
geometric obligations.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/
QuadraticCharNegOne.lean (`absNorm_smul`) and
Proofs/CubicalLineBundles/OneMulConjFracOneEqInvDifferent.lean
(`absNorm_extendedHom`, `log_rootDiscr_tower`, and the finite part of
`two_mul_deg_lineHerm_different`). Source attribution is retained; the
archive states no license.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField Module
open scoped Pointwise nonZeroDivisors

namespace RHLean.Geometry.NativeCM.FiniteDegree

theorem absNorm_galois_smul {E : Type} [Field E] [NumberField E]
    (c : E ≃ₐ[ℚ] E) (B : Ideal (𝓞 E)) :
    Ideal.absNorm (c • B) = Ideal.absNorm B := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv B (c • B)
    (MulSemiringAction.toRingEquiv _ _ c) rfl).toEquiv).symm

theorem absNorm_extendedHom {E L : Type} [Field E] [NumberField E]
    [Field L] [NumberField L] [Algebra E L]
    (A : FractionalIdeal (𝓞 E)⁰ E) :
    FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) A) =
      FractionalIdeal.absNorm A ^ finrank E L := by
  have key : ∀ I : Ideal (𝓞 E),
      FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L)
        (I : FractionalIdeal (𝓞 E)⁰ E)) =
        FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 E)⁰ E) ^ finrank E L := by
    intro I
    rw [FractionalIdeal.extendedHom_coeIdeal_eq_map, FractionalIdeal.coeIdeal_absNorm,
      FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_algebraMap,
      ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L, Nat.cast_pow]
  have h := A.den_mul_self_eq_num'
  rw [← FractionalIdeal.coeIdeal_span_singleton] at h
  have h0 : FractionalIdeal.absNorm
      ((Ideal.span {(A.den : 𝓞 E)} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    simp
  have h1 := key A.num
  rw [← h, map_mul, map_mul, map_mul, key, mul_pow] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ h0) h1

theorem normalized_logNorm_extendedHom {E L : Type} [Field E] [NumberField E]
    [Field L] [NumberField L] [Algebra E L]
    (A : FractionalIdeal (𝓞 E)⁰ E) :
    Real.log (FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) A)) /
        (finrank ℚ L : ℝ) =
      Real.log (FractionalIdeal.absNorm A) / (finrank ℚ E : ℝ) := by
  have h1 : (0 : ℝ) < finrank E L := by exact_mod_cast finrank_pos
  have h2 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  rw [absNorm_extendedHom, Rat.cast_pow, Real.log_pow,
    ← finrank_mul_finrank ℚ E L, Nat.cast_mul]
  field_simp

theorem log_rootDiscr_tower {E L : Type} [Field E] [NumberField E]
    [Field L] [NumberField L] [Algebra E L] :
    Real.log (rootDiscr L) =
      Real.log (Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L))) / finrank ℚ L +
        Real.log (rootDiscr E) := by
  have h1 : (0 : ℝ) < finrank E L := by exact_mod_cast finrank_pos
  have h2 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow E (𝓞 E) L (𝓞 L)
  have h3 : Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L)) ≠ 0 := fun h0 => by
    simp [h0, discr_ne_zero] at h
  have h4 := congrArg (fun m : ℕ => Real.log (m : ℝ)) h
  have p : ∀ m : ℤ, m ≠ 0 → (0 : ℝ) < (|m| : ℤ) := fun m hm => by
    exact_mod_cast abs_pos.2 hm
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs] at h4
  rw [Real.log_mul (by exact_mod_cast h3) (pow_ne_zero _ (p _ (discr_ne_zero E)).ne'),
    Real.log_pow] at h4
  rw [rootDiscr_def, rootDiscr_def, Real.log_rpow (p _ (discr_ne_zero L)),
    Real.log_rpow (p _ (discr_ne_zero E)), h4,
    ← finrank_mul_finrank ℚ E L, Nat.cast_mul]
  field_simp

end RHLean.Geometry.NativeCM.FiniteDegree

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativeCM.FiniteDegree

variable {φ : Frame} (H : HostRaw φ)

/-- The different twist is computed on the actual projective coefficient
ideal, rather than on a substituted principal lattice. -/
theorem coefficientDifferent_eq_conjHalf (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    coefficientIdeal H B *
        (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  rw [coefficientIdeal, hB, FractionalIdeal.coeIdeal_mul,
    inv_mul_cancel_left₀ (halfDifferent_ne_zero H B hB).1]

theorem halfDifferent_absNorm_sq (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    Ideal.absNorm B ^ 2 = Ideal.absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E)) := by
  rw [hB, map_mul, absNorm_galois_smul, pow_two]

/-- The exact normalized finite-ideal log norm, which is subtracted in
twice the CM eigenline degree. No archimedean Lie norm is assigned here. -/
theorem coefficientDifferent_normalized_logNorm (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    2 * Real.log (FractionalIdeal.absNorm (coefficientIdeal H B *
      (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E))) /
        (finrank ℚ H.E : ℝ) =
      Real.log (rootDiscr H.E) - Real.log (rootDiscr H.K) := by
  rw [coefficientDifferent_eq_conjHalf H B hB, FractionalIdeal.coeIdeal_absNorm,
    Rat.cast_natCast, absNorm_galois_smul]
  have hnorm := congrArg (fun n : ℕ => Real.log (n : ℝ))
    (halfDifferent_absNorm_sq H B hB)
  rw [Nat.cast_pow, Real.log_pow] at hnorm
  rw [show (2 : ℝ) * Real.log (Ideal.absNorm B) =
      Real.log (Ideal.absNorm (differentIdeal (𝓞 H.K) (𝓞 H.E))) from by
    simpa using hnorm]
  have h := log_rootDiscr_tower (E := H.K) (L := H.E)
  linarith

/-- Retain the negative finite-place contribution in the source degree
convention; the root-discriminant correction has this specific sign. -/
theorem coefficientDifferent_degree_correction (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    2 * (-Real.log (FractionalIdeal.absNorm (coefficientIdeal H B *
      (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E))) /
        (finrank ℚ H.E : ℝ)) =
      Real.log (rootDiscr H.K) - Real.log (rootDiscr H.E) := by
  calc
    _ = -(2 * Real.log (FractionalIdeal.absNorm (coefficientIdeal H B *
        (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E))) /
          (finrank ℚ H.E : ℝ)) := by ring
    _ = _ := by rw [coefficientDifferent_normalized_logNorm H B hB]; ring

/-- Extending the actual coefficient ideal preserves the normalized finite
degree correction, with the full extension degree cancelling exactly. -/
theorem coefficientDifferent_baseChange_logNorm (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (L : Type) [Field L] [NumberField L] [Algebra H.E L] :
    2 * Real.log (FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L)
      (coefficientIdeal H B *
        (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E)))) /
        (finrank ℚ L : ℝ) =
      Real.log (rootDiscr H.E) - Real.log (rootDiscr H.K) := by
  rw [mul_div_assoc, normalized_logNorm_extendedHom, ← mul_div_assoc]
  exact coefficientDifferent_normalized_logNorm H B hB

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
