import RHLean.Analysis.AlpogeNativeIntegralQuadraticRoot
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRaw
import RHLean.Analysis.AlpogeThin.Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity

/-!
# Integral ray-norm elements in the same native host

The existing native IsNormOne predicate uses the integral basis
1, (1 + sqrt(-d))/2. Its integer coordinates are converted to the literal
source coordinates A, B with A^2 + d B^2 = 4 p, M | B and
2 M | A - 2 - B. The element u + v (1 + sqrt(-d))/2 is then constructed
in the ring of integers of the SAME HostRaw field. Its quadratic-subfield
membership, norm under the actual host involution, and ray congruence are
proved. The native specialization uses the canonical Gauss root already
used to construct the host.

This is the algebraic norm-coordinate supplier used after a level prime
has been chosen. It does not assert prime existence in a short window,
choose a different prime, or restrict the physical TT family.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Definitions/Foundations/RayPrimes.lean,
GlobalTheory.Mem.An.NormOne;
src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/
NormOneIffOfSqrt.lean, normOne_iff_of_sqrt (forward construction);
src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/
NormOnePrimeElements.lean, GlobalTheory.EX.normOne_host.
The actual short-window consumer is ExistsLevChOfLevelPrime.lean,
GlobalTheory.EX.OB.exists_levCh_of_levelPrime. The source archive/mirror
states no license; attribution is preserved without assigning one.
No source compiled artifact or terminal RH theorem is imported.
-/

set_option autoImplicit false

noncomputable section

open NumberField

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open Formalism.HermitianLattices.ZeroFreeRegionGL2

namespace NativeRawHostRayNorm

/-- The existing integral-basis predicate is exactly the source's pair of
half-root coordinates, with the original factor 4 and both congruences. -/
theorem isNormOne_iff_halfRootCoordinates (d M p : ℕ) (hd4 : d % 4 = 3) :
    IsNormOne d M p ↔
      ∃ A B : ℤ, A ^ 2 + (d : ℤ) * B ^ 2 = 4 * (p : ℤ) ∧
        (M : ℤ) ∣ B ∧ 2 * (M : ℤ) ∣ A - 2 - B := by
  have hc : 4 * (((d + 1) / 4 : ℕ) : ℤ) = (d : ℤ) + 1 := by
    exact_mod_cast (show 4 * ((d + 1) / 4) = d + 1 by omega)
  constructor
  · rintro ⟨u, v, ⟨a, ha⟩, hv, hp⟩
    refine ⟨2 * u + v, v, ?_, hv, a, ?_⟩
    · linear_combination -4 * hp - v ^ 2 * hc
    · linear_combination 2 * ha
  · rintro ⟨A, B, hp, hB, ⟨a, ha⟩⟩
    let u : ℤ := 1 + M * a
    have hA : A = 2 * u + B := by
      dsimp [u]
      linear_combination ha
    have hfour : 4 * (p : ℤ) =
        4 * (u ^ 2 + u * B + (((d + 1) / 4 : ℕ) : ℤ) * B ^ 2) := by
      calc
        4 * (p : ℤ) = (2 * u + B) ^ 2 + (d : ℤ) * B ^ 2 := by
          rw [← hA]
          exact hp.symm
        _ = _ := by linear_combination -(B ^ 2) * hc
    exact ⟨u, B, ⟨a, by dsimp [u]; ring⟩, hB,
      mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) hfour⟩

variable {φ : Frame} (H : HostRaw φ)

private theorem d_mod_four : H.d % 4 = 3 := by
  have := H.hyp.2.2.2.1
  omega

/-- The integral half-root of this host's own distinguished square root. -/
def halfRoot : 𝓞 H.E :=
  ⟨(1 + H.sqd) / 2,
    NativeIntegralQuadratic.halfRoot_integral (d_mod_four H) H.sqd_sq⟩

/-- The actual integral element attached to the existing norm coordinates. -/
def element (u v : ℤ) : 𝓞 H.E := (u : 𝓞 H.E) + (v : 𝓞 H.E) * halfRoot H

theorem element_coe (u v : ℤ) :
    (element H u v : H.E) = (u : H.E) + (v : H.E) * ((1 + H.sqd) / 2) := rfl

theorem element_halfRootCoordinates (u v : ℤ) :
    (element H u v : H.E) = (((2 * u + v : ℤ) : H.E) + (v : H.E) * H.sqd) / 2 := by
  rw [element_coe]
  push_cast
  ring

private theorem conj_sqd : H.conj H.sqd = -H.sqd := by
  rw [H.gal_sqd, HostRaw.conj, MulEquiv.apply_symm_apply]
  simp [Frame.cc, c0]

/-- The norm is computed with the host's actual Galois involution. -/
theorem element_norm (u v : ℤ) :
    (element H u v : H.E) * H.conj (element H u v : H.E) =
      (u : H.E) ^ 2 + (u : H.E) * v +
        (((H.d + 1) / 4 : ℕ) : H.E) * (v : H.E) ^ 2 := by
  have hc : (4 : H.E) * (((H.d + 1) / 4 : ℕ) : H.E) = (H.d : H.E) + 1 := by
    have hd4 := d_mod_four H
    exact_mod_cast (show 4 * ((H.d + 1) / 4) = H.d + 1 by omega)
  simp only [element_coe, map_add, map_mul, map_intCast, map_div₀, map_one,
    map_ofNat, conj_sqd H]
  linear_combination -(v : H.E) ^ 2 / 4 * H.sqd_sq - (v : H.E) ^ 2 / 4 * hc

theorem element_mem_K (u v : ℤ) : (element H u v : H.E) ∈ H.K := by
  rw [element_coe]
  exact add_mem (intCast_mem _ _)
    (mul_mem (intCast_mem _ _)
      (div_mem (add_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self ℚ _))
        (ofNat_mem _ 2)))

/-- Both coordinate congruences produce an explicit multiple of M in O(E). -/
theorem element_sub_one_mem (M : ℕ) (u v : ℤ)
    (hu : (M : ℤ) ∣ u - 1) (hv : (M : ℤ) ∣ v) :
    element H u v - 1 ∈ Ideal.span {(M : 𝓞 H.E)} := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have hu' : u = 1 + M * a := by linarith
  have hshape : element H u v - 1 =
      (M : 𝓞 H.E) * ((a : 𝓞 H.E) + (b : 𝓞 H.E) * halfRoot H) := by
    rw [element, hu', hb]
    push_cast
    ring
  rw [hshape]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- The existing arithmetic predicate supplies an actual integral ray-norm
element in this host's literal quadratic subfield. No primality is needed
for this algebraic construction. -/
theorem exists_integral_of_isNormOne (M p : ℕ) (h : IsNormOne H.d M p) :
    (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧
      (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧
      π - 1 ∈ Ideal.span {(M : 𝓞 H.E)}) ∧ p % M = 1 % M := by
  have hmod : p % M = 1 % M :=
    Int.natCast_modEq_iff.mp (norm_one_congruence H.d M p h).1
  obtain ⟨u, v, hu, hv, hp⟩ := h
  refine ⟨⟨element H u v, element_mem_K H u v, ?_,
    element_sub_one_mem H M u v hu hv⟩, hmod⟩
  rw [element_norm]
  have hnorm := congrArg (fun z : ℤ => (z : H.E)) hp.symm
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hnorm

/-- The original A,B normalization feeds the same actual construction. -/
theorem exists_integral_of_halfRootCoordinates (M p : ℕ)
    (h : ∃ A B : ℤ, A ^ 2 + (H.d : ℤ) * B ^ 2 = 4 * (p : ℤ) ∧
      (M : ℤ) ∣ B ∧ 2 * (M : ℤ) ∣ A - 2 - B) :
    (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧
      (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧
      π - 1 ∈ Ideal.span {(M : 𝓞 H.E)}) ∧ p % M = 1 % M :=
  exists_integral_of_isNormOne H M p
    ((isNormOne_iff_halfRootCoordinates H.d M p (d_mod_four H)).mpr h)

end NativeRawHostRayNorm

/-- The half-root is literally the canonical integral Gauss half-root used
elsewhere in the same native host, with no field or root transport. -/
theorem nativeDyadicHostRaw_rayHalfRoot
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) (hd4 : d % 4 = 3) :
    NativeRawHostRayNorm.halfRoot (nativeDyadicHostRaw e q d he hH) =
      alpogeNativeIntegralHalfRoot e q d hd4 := rfl

/-- Same-host endpoint for the actual arithmetic norm-prime predicate. -/
theorem nativeDyadicHostRaw_exists_rayNormElement
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) (M p : ℕ) (h : IsNormOne d M p) :
    let H := nativeDyadicHostRaw e q d he hH
    (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧
      (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧
      π - 1 ∈ Ideal.span {(M : 𝓞 H.E)}) ∧ p % M = 1 % M :=
  NativeRawHostRayNorm.exists_integral_of_isNormOne
    (nativeDyadicHostRaw e q d he hH) M p h

/-- Literal source NormOne coordinates, on the same constructed native host. -/
theorem nativeDyadicHostRaw_exists_rayNormElement_of_coordinates
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) (M p : ℕ)
    (h : ∃ A B : ℤ, A ^ 2 + (d : ℤ) * B ^ 2 = 4 * (p : ℤ) ∧
      (M : ℤ) ∣ B ∧ 2 * (M : ℤ) ∣ A - 2 - B) :
    let H := nativeDyadicHostRaw e q d he hH
    (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧
      (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧
      π - 1 ∈ Ideal.span {(M : 𝓞 H.E)}) ∧ p % M = 1 % M :=
  NativeRawHostRayNorm.exists_integral_of_halfRootCoordinates
    (nativeDyadicHostRaw e q d he hH) M p h

end RHLean.Analysis.AlpogeThin

end
