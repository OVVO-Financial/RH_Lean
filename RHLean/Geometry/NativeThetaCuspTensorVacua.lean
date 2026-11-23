import RHLean.Geometry.NativeThetaCuspTensorLattices
import RHLean.Geometry.NativeThetaCuspShiftedVacua

/-!
# Normalized vacua for the complete native auxiliary lattice family

Every member of the original auxiliary Hermitian lattice family is tensored
with the actual projective trace lattice inside the unchanged field ambient.
The same global rational symplectic coordinates and the same actual half-root
phase construct its normalized Schwartz–Bruhat vacuum. The overlap is the
exact relative-index formula on the literal tensor lattices, including the
original exponent when only the physical lattice changes.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/
TensorLatticeVacuaExistUnique.lean (`vacua`) and
TensorLatticeSelfDualSemicharacterIndex.lean. This completes the finite
tensor-vacuum input. Analytic Weil covariance and the global cusp-form span
are separate remaining suppliers. The source mirror states no license;
attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix
open scoped Pointwise nonZeroDivisors BigOperators TensorProduct Classical ComplexConjugate

namespace RHLean.Geometry.NativeTheta.Cusp.TensorVacua

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativePrescribedHermitian NativeIntegralSymplectic
open AuxiliaryLattices TensorLattices ShiftedLattice

variable {φ : Frame} (H : HostRaw φ)

section Prescribed

variable [IsCMField H.E]
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m)
    {n : ℕ} {ι : Type} [Fintype ι]
    (b : Basis (ι ⊕ ι) ℤ (prescribedLattice H B k m))
    (hb : IsSymplecticBasis
      (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj).EF b)

/-- The coordinate image of the literal tensor lattice. -/
def lattice (Λ : Lt H.E n) (L : Lt H.E (k + m - 1)) :
    AddSubgroup (Matrix (Fin n) ι ℚ × Matrix (Fin n) ι ℚ) :=
  (tens Λ L).map (ShiftedVacua.coordinates H B hB b).toLinearMap.toAddMonoidHom

omit [IsCMField H.E] in
/-- A change to the proved common coordinates preserves the actual index. -/
theorem relativeIndex (A A' : AddSubgroup (Matrix (Fin n) (Fin (k + m - 1)) H.E)) :
    (A'.map (ShiftedVacua.coordinates H B hB b).toLinearMap.toAddMonoidHom).relIndex
        (A.map (ShiftedVacua.coordinates H B hB b).toLinearMap.toAddMonoidHom) =
      A'.relIndex A := by
  symm
  let e := ShiftedVacua.coordinates H B hB b (κ := Fin n)
  refine PseudoBasis.relIndex_eq_of_hom e.toLinearMap.toAddMonoidHom
    (fun y hy => AddSubgroup.mem_map_of_mem _ hy) (fun y hy => ?_) ?_
  · exact AddSubgroup.mem_map_iff_mem e.injective
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [sub_self]; exact zero_mem _⟩

include hΨ hconj hbar hk hj hb in
/-- The complete finite-vacuum hypotheses are proved on every actual
auxiliary tensor lattice in the source family. -/
theorem good_tensor {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M)
    {L : Lt H.E (k + m - 1)}
    (hL : SelfDual H (negTail (k + m - 1) (m - j)) L) :
    FiniteOverlap.Good (ShiftedVacua.phase H B hB G k m j b)
      (lattice H B hB k m b Λ L) := by
  let e := ShiftedVacua.coordinates H B hB b (κ := Fin n)
  have hp (y y' : Matrix (Fin n) (Fin (k + m - 1)) H.E) :
      FiniteOverlap.omega (e y) (e y') =
        ∑ a, Ambient.pair H (negTail (k + m - 1) (m - j)) (y a) (y' a) :=
    ShiftedVacua.coordinates_pairing H B hB G hΨ hconj hbar k m j hk hj b hb y y'
  refine ⟨Vac.fg_map (tens_fg H hΛ hL.1) _, ?_, ?_⟩
  · intro p
    constructor
    · rintro ⟨y, hy, rfl⟩ p' ⟨y', hy', rfl⟩
      obtain ⟨z, hz⟩ := (tens_selfDual H hΛ hL y).1 hy y' hy'
      exact ⟨z, by rw [hp, hz]⟩
    · intro h
      have hy : e.symm p ∈ tens Λ L := by
        apply (tens_selfDual H hΛ hL _).2
        intro y' hy'
        obtain ⟨z, hz⟩ := h (e y') (AddSubgroup.mem_map_of_mem _ hy')
        refine ⟨z, ?_⟩
        rw [← hp, e.apply_symm_apply]
        exact hz
      have hm := AddSubgroup.mem_map_of_mem e.toLinearMap.toAddMonoidHom hy
      simpa only [LinearEquiv.apply_symm_apply] using hm
  · rintro _ ⟨y, hy, rfl⟩
    have hs := phase_semichar H hΛ hL G.w0 (ShiftedPhase.prescribed_halfRoot H G hbar) hy
    constructor
    · simpa only [ShiftedVacua.phase, LinearEquiv.symm_apply_apply] using hs.1
    · rintro _ ⟨y', hy', rfl⟩
      change ShiftedPhase.phase H _ G.w0 (e.symm (e y + e y')) =
        ShiftedPhase.phase H _ G.w0 (e.symm (e y)) *
          ShiftedPhase.phase H _ G.w0 (e.symm (e y')) *
            Complex.exp (Real.pi * Complex.I * ((FiniteOverlap.omega (e y) (e y') : ℚ) : ℂ))
      rw [map_add, e.symm_apply_apply, e.symm_apply_apply, hp]
      exact hs.2 y' hy'

include hΨ hconj hbar hk hj hb in
/-- Constructed normalized vacua, uniqueness, actual finite projection and
exact overlap for the complete native auxiliary family. -/
theorem vacua {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M)
    {L : Lt H.E (k + m - 1)}
    (hL : SelfDual H (negTail (k + m - 1) (m - j)) L) :
    let ε := ShiftedVacua.phase H B hB G k m j b
    let A := lattice H B hB k m b Λ L
    (∃ v, FiniteOverlap.IsVac ε A v) ∧
      (∀ v v', FiniteOverlap.IsVac ε A v → IsSB v' →
        (∀ y ∈ A, ε y • FiniteOverlap.heis y v' = v') → v' = ip v' v • v) ∧
      (∀ f : Matrix (Fin n) ι ℚ → ℂ, IsSB f → ∀ v, FiniteOverlap.IsVac ε A v →
        FiniteOverlap.projA ε A f = ip f v • v) ∧
      ∀ L', SelfDual H (negTail (k + m - 1) (m - j)) L' → ∀ Λ' ∈ Vset H n M,
        ∀ v v', FiniteOverlap.IsVac ε A v →
          FiniteOverlap.IsVac ε (lattice H B hB k m b Λ' L') v' →
            ((tens Λ' L').relIndex (tens Λ L) : ℝ) * ‖ip v v'‖ ^ 2 = 1 := by
  have hgood := good_tensor H B hB G hΨ hconj hbar k m j hk hj b hb hΛ hL
  have hε0 := ShiftedVacua.phase_zero H B hB G k m j b (κ := Fin n)
  have hεunit := ShiftedVacua.phase_mul_conj H B hB G k m j b (κ := Fin n)
  refine ⟨(FiniteOverlap.Good.vac hgood).imp fun v hv => hv.1,
    fun v v' hv hv' h => FiniteOverlap.Good.uniq hgood hv hv' h,
    fun f hf v hv => (FiniteOverlap.Good.proj hε0 hεunit hgood hf hv).2, ?_⟩
  intro L' hL' Λ' hΛ' v v' hv hv'
  have he := FiniteOverlap.Good.overlap hε0 hεunit hgood
    (good_tensor H B hB G hΨ hconj hbar k m j hk hj b hb hΛ' hL') hv hv'
  simpa only [lattice, relativeIndex] using he

include hΨ hconj hbar hk hj hb in
/-- The physical-lattice overlap has exactly the source's auxiliary rank
exponent, with the original subgroup index in its original direction. -/
theorem overlap_index_power {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M)
    {L L' : Lt H.E (k + m - 1)}
    (hL : SelfDual H (negTail (k + m - 1) (m - j)) L)
    (hL' : SelfDual H (negTail (k + m - 1) (m - j)) L')
    {v v' : Matrix (Fin n) ι ℚ → ℂ}
    (hv : FiniteOverlap.IsVac (ShiftedVacua.phase H B hB G k m j b)
      (lattice H B hB k m b Λ L) v)
    (hv' : FiniteOverlap.IsVac (ShiftedVacua.phase H B hB G k m j b)
      (lattice H B hB k m b Λ L') v') :
    ((L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ n) * ‖ip v v'‖ ^ 2 = 1 := by
  have he := (vacua H B hB G hΨ hconj hbar k m j hk hj b hb hΛ hL).2.2.2
    L' hL' Λ hΛ v v' hv hv'
  rwa [(tens_relative_indices H hΛ hL).1 L' hL', Nat.cast_pow] at he

include hΨ hconj hbar hk hj hb in
/-- All auxiliary lattices have actual normalized vacua for both the
unchanged projective lattice and its literal conjugate-level shift. -/
theorem shifted_family {P : Ideal (𝓞 H.E)} (hP0 : P ≠ ⊥) (hP1 : P ≠ ⊤)
    (hPc : IsCoprime P (H.conj • P)) :
    let L := prescribedLattice H B k m
    let L' := idq P (H.conj • P) L
    ∀ M, ∀ Λ ∈ Vset H n M, ∃ v v' : Matrix (Fin n) ι ℚ → ℂ,
      FiniteOverlap.IsVac (ShiftedVacua.phase H B hB G k m j b)
        (lattice H B hB k m b Λ L) v ∧
      FiniteOverlap.IsVac (ShiftedVacua.phase H B hB G k m j b)
        (lattice H B hB k m b Λ L') v' ∧
      ((L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ n) * ‖ip v v'‖ ^ 2 = 1 := by
  intro M Λ hΛ
  have hL := twisted_selfDual H B hB (negTail (k + m - 1) (m - j))
  have hL' := selfDual_idq H (negTail (k + m - 1) (m - j)) hP0 hP1 hPc hL
  obtain ⟨v, hv⟩ := (vacua H B hB G hΨ hconj hbar k m j hk hj b hb hΛ hL).1
  obtain ⟨v', hv'⟩ := (vacua H B hB G hΨ hconj hbar k m j hk hj b hb hΛ hL').1
  exact ⟨v, v', hv, hv',
    overlap_index_power H B hB G hΨ hconj hbar k m j hk hj b hb hΛ hL hL' hv hv'⟩

end Prescribed

/-- Construct the entire normalized auxiliary tensor-vacuum family for the
same native datum and the same actual fixed-five conjugate level. -/
theorem exists_native_tensor_vacua
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) (n : ℕ) :
    let H := nativeDyadicHostRaw e q d he hH
    let _ : IsCMField (nativeDyadicHostAx e q d he hH).E :=
      (nativeDyadicHostAx e q d he hH).der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    let g := finrank ℚ H.E / 2 * (D.p + D.q)
    ∃ b : Basis (Fin g ⊕ Fin g) ℤ D.La, IsSymplecticBasis D.EF b ∧
      ∃ P : Ideal (𝓞 H.E), P ≠ ⊤ ∧ P ≠ ⊥ ∧ IsCoprime P (H.conj • P) ∧
        IsCoprime P (Ideal.span {(2 : 𝓞 H.E)}) ∧
        P * (H.conj • P) = Ideal.span {(5 : 𝓞 H.E)} ∧
        let L := prescribedLattice H B k m
        let L' := idq P (H.conj • P) L
        ∀ M, ∀ Λ ∈ Vset H n M, ∃ v v' : Matrix (Fin n) (Fin g) ℚ → ℂ,
          FiniteOverlap.IsVac (ShiftedVacua.phase H B hB G k m j b)
            (lattice H B hB k m b Λ L) v ∧
          FiniteOverlap.IsVac (ShiftedVacua.phase H B hB G k m j b)
            (lattice H B hB k m b Λ L') v' ∧
          ((L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ n) * ‖ip v v'‖ ^ 2 = 1 := by
  let H := nativeDyadicHostRaw e q d he hH
  let _ : IsCMField (nativeDyadicHostAx e q d he hH).E :=
    (nativeDyadicHostAx e q d he hH).der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  obtain ⟨b, hb, P, hP1, hP0, hPc, hPo, hP5, -⟩ :=
    ShiftedVacua.exists_native_shifted_vacua e q d he hH B hB k m j hk hj n
  refine ⟨b, hb, P, hP1, hP0, hPc, hPo, hP5, ?_⟩
  exact shifted_family H B hB G
    (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH)
    (nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH)
    (nativeDyadicGeometricHost_bar_eq e q d he hH)
    k m j hk hj b hb hP0 hP1 hPc

end RHLean.Geometry.NativeTheta.Cusp.TensorVacua
