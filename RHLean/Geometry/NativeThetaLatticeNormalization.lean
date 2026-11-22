import RHLean.Geometry.NativeHermitianShortVectors
import RHLean.Geometry.NativePolarizationCoefficientLattice

/-!
# The original lattice and level inputs for short theta values

This file constructs an admissible odd level from the original coprime
denominator witness, derives finite generation from self-duality at that
level, and supplies the existing short-vector theorem on the SAME lattice.
The two finite indices in the short-theta formula are literal relative
indices, with their exact multiplicative relation and positivity proved.

These are lattice inputs to `ShortValAt`; a polarized Datum, its semiabelian
scheme, the theta sections and their geometric evaluation rule are still
separate constructions. No cusp-spanning or theta-norm estimate is assumed.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/LocalToGlobal/ProjectiveLattices/ThShort.lean`,
`stdLat`, `GenLat.Ln`, `GenLat.LevOK`, `GenLat.Unimod`, `GenLat.mIdx`, `GenLat.zCard`;
`src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FgOfSmulLe.lean`,
`GenLatCmp.mem_std`, `std_eq`, `span_smul_le`, `fg_of_smul_le`,
`unimod_iff`, `smul_mem_std`, `genLat_vset`;
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`NormShortGeneratorEvalLeOrthonormalFrame.lean`, `ShortPoint.index_Ln`, `zCard_eq`.
The finite quotient construction is the proof of `ShortValue.finite_levelQuotient`
in `ShortThetaValueExistsUniqueNaturalOfLaws.lean`, specialized also to the
already constructed native inverse-ideal coefficient lattice.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped Pointwise

namespace RHLean.Geometry.NativeTheta.Lattice

open Paired NativeHermitianLattice

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/-- The literal standard integral lattice used by `GenLat`. -/
def standard (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => 1

def intersection (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ ⊓ standard E n

def levelLattice (E : Type) [Field E] [NumberField E] (n N : ℕ) :
    Submodule (𝓞 E) (Fin n → E) := Ideal.span {(N : 𝓞 E)} • standard E n

/-- This is exactly the source's denominator index `GenLat.mIdx`. -/
def normalizationIndex (Λ : Submodule (𝓞 E) (Fin n → E)) (N r : ℕ) : ℕ :=
  ((levelLattice E n N).toAddSubgroup.addSubgroupOf
    (intersection Λ).toAddSubgroup).index ^ r

/-- This is exactly the source's translation count `GenLat.zCard`. -/
def translationCount (Λ : Submodule (𝓞 E) (Fin n → E)) (N r : ℕ) : ℕ :=
  ((levelLattice E n N).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index ^ r

def intersectionIndex (Λ : Submodule (𝓞 E) (Fin n → E)) : ℕ :=
  ((intersection Λ).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).index

omit [NumberField E] in
theorem mem_range_iff_integral (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_standard (v : Fin n → E) :
    v ∈ standard E n ↔ ∀ i, IsIntegral ℤ (v i) := by
  simp only [standard, Submodule.mem_pi, Set.mem_univ, forall_const, Submodule.mem_one]
  exact forall_congr' fun i => mem_range_iff_integral (v i)

theorem standard_eq_span :
    standard E n = Submodule.span (𝓞 E) (Set.range fun i : Fin n =>
      (Pi.single i 1 : Fin n → E)) := by
  classical
  apply le_antisymm
  · intro v hv
    have hi := (mem_standard v).mp hv
    have hsum : v = ∑ i, (⟨v i, hi i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply]
      change v j = ∑ i : Fin n, v i * (Pi.single i 1 : Fin n → E) j
      simp [Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_standard]
    intro j
    by_cases h : j = i
    · subst h
      simpa using (isIntegral_one : IsIntegral ℤ (1 : E))
    · simpa [Pi.single_apply, h] using (isIntegral_zero : IsIntegral ℤ (0 : E))

theorem standard_fg : (standard E n).FG := by
  rw [standard_eq_span]
  exact Submodule.fg_span (Set.finite_range _)

/-- The source's original standard lattice itself has the required level
inclusion at every integer level. -/
theorem standard_level (N : ℕ) :
    levelLattice E n N ≤ intersection (standard E n) :=
  le_inf Submodule.smul_le_right Submodule.smul_le_right

omit [NumberField E] in
theorem span_nat_smul_le (N : ℕ) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(N : 𝓞 E)} • A ≤ B ↔ ∀ v ∈ A, (N : E) • v ∈ B := by
  have he (v : Fin n → E) : (N : 𝓞 E) • v = (N : E) • v := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    rw [← he]
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv
    rw [he]
    exact h w hw

omit [NumberField E] in
theorem nat_smul_mem (N : ℕ) {A : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E}
    (hv : v ∈ A) : (N : E) • v ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact A.toAddSubgroup.nsmul_mem hv N

/-- A source denominator witness constructs the actual level `N = s*M`.
No change of lattice, Hermitian form or coefficient field occurs. -/
theorem exists_odd_level (Λ : Submodule (𝓞 E) (Fin n → E)) {M : ℕ}
    (hM : Odd M)
    (hden : ∃ s : ℕ, Nat.Coprime s (2 * M) ∧
      Ideal.span {(s : 𝓞 E)} • standard E n ≤ Λ) :
    ∃ N : ℕ, Odd N ∧ M ∣ N ∧ levelLattice E n N ≤ intersection Λ := by
  obtain ⟨s, hs, hΛ⟩ := hden
  have hs2 : Nat.Coprime s 2 := hs.coprime_dvd_right (dvd_mul_right 2 M)
  refine ⟨s * M, (Nat.coprime_two_right.mp hs2).mul hM,
    ⟨s, Nat.mul_comm s M⟩, ?_⟩
  rw [levelLattice, span_nat_smul_le]
  intro v hv
  refine ⟨?_, nat_smul_mem _ hv⟩
  rw [Nat.mul_comm s M, Nat.cast_mul, mul_smul]
  exact nat_smul_mem M ((span_nat_smul_le s _ _).mp hΛ v hv)

section CM

variable [IsCMField E]

/-- The literal source self-duality property, with conjugation on the first
argument and values in the range of the original ring of integers. -/
def Unimodular (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ,
    (∑ i, IsCMField.complexConj E (x i) * y i) ∈ (algebraMap (𝓞 E) E).range

theorem unimodular_iff (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Unimodular Λ ↔ ∀ x, x ∈ Λ ↔
      ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y) := by
  refine forall_congr' fun x => iff_congr Iff.rfl (forall₂_congr fun y _ => ?_)
  have he : (∑ i, IsCMField.complexConj E (x i) * y i) = hermPairing E n y x := by
    rw [hermPairing_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [he, mem_range_iff_integral]
  constructor
  · intro h
    rw [hermPairing_symm x y]
    exact isIntegral_cc h
  · intro h
    rw [hermPairing_symm y x]
    exact isIntegral_cc h

/-- A genuine instance of the source condition on its original standard
lattice. This does not assert that one lattice spans every geometric genus. -/
theorem standard_unimodular : Unimodular (standard E n) := by
  classical
  apply (unimodular_iff (standard E n)).mpr
  intro x
  constructor
  · intro hx y hy
    rw [hermPairing_apply]
    exact IsIntegral.sum _ fun i _ => ((mem_standard x).mp hx i).mul
      (isIntegral_cc ((mem_standard y).mp hy i))
  · intro hx
    rw [mem_standard]
    intro i
    have hi : (Pi.single i 1 : Fin n → E) ∈ standard E n := by
      rw [standard_eq_span]
      exact Submodule.subset_span ⟨i, rfl⟩
    have h := hx _ hi
    simpa [hermPairing_apply, Pi.single_apply] using h

/-- Self-duality turns the admissible inclusion `N*O(E)^n ⊆ Λ` into the
opposite denominator inclusion `N*Λ ⊆ O(E)^n`. -/
theorem smul_mem_standard (Λ : Submodule (𝓞 E) (Fin n → E))
    (hU : Unimodular Λ) {N : ℕ}
    (hN : levelLattice E n N ≤ intersection Λ) :
    ∀ v ∈ Λ, (N : E) • v ∈ standard E n := by
  classical
  intro v hv
  rw [mem_standard]
  intro i
  have hei : (Pi.single i 1 : Fin n → E) ∈ standard E n := by
    rw [standard_eq_span]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hvi := ((unimodular_iff Λ).mp hU v).mp hv
    ((N : E) • Pi.single i 1)
    (((span_nat_smul_le N _ _).mp hN _ hei).1)
  have he : hermPairing E n v ((N : E) • Pi.single i 1) = (N : E) * v i := by
    simp [hermPairing_apply, Pi.single_apply, mul_comm]
  simpa only [Pi.smul_apply, smul_eq_mul, he] using hvi

/-- Finite generation is derived from the source lattice conditions; it is
not supplied as a new short-family assumption. -/
theorem fg_of_level (Λ : Submodule (𝓞 E) (Fin n → E))
    (hU : Unimodular Λ) {N : ℕ} (hN0 : N ≠ 0)
    (hN : levelLattice E n N ≤ intersection Λ) : Λ.FG := by
  have hfg := (standard_fg (E := E) (n := n)).map
    ((LinearMap.lsmul E (Fin n → E) (N : E)⁻¹).restrictScalars (𝓞 E))
  refine hfg.of_le fun v hv => ⟨(N : E) • v, smul_mem_standard Λ hU hN v hv, ?_⟩
  have hcast : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  simp [smul_smul, hcast]

/-- The existing short-vector construction now consumes the literal source
lattice and admissible level, retaining its full discriminant radius. -/
theorem exists_short_vectors_of_level (Λ : Submodule (𝓞 E) (Fin n → E))
    (hU : Unimodular Λ) {N : ℕ} (hN0 : N ≠ 0)
    (hN : levelLattice E n N ≤ intersection Λ) :
    ∃ v : Fin (2 * halfDegree E * n) → Fin n → E,
      (∀ i, v i ∈ Λ) ∧ LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = ⊤ ∧
      ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤
        (2 * (halfDegree E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rootDiscr E) ^ 2 := by
  have hself := (unimodular_iff Λ).mp hU
  exact NativeHermitianLattice.exists_short_vectors Λ (fg_of_level Λ hU hN0 hN)
    (fun x hx => (hself x).mp hx) (fun x hx => (hself x).mpr hx)

end CM

theorem intersectionIndex_eq_relIndex (Λ : Submodule (𝓞 E) (Fin n → E)) :
    intersectionIndex Λ = (standard E n).toAddSubgroup.relIndex Λ.toAddSubgroup := by
  rw [← AddSubgroup.inf_relIndex_left]
  rfl

/-- The source's translation multiplicity is exactly the denominator index
times the intersection index, with the same exponent on all three terms. -/
theorem translationCount_eq (Λ : Submodule (𝓞 E) (Fin n → E)) {N : ℕ}
    (hN : levelLattice E n N ≤ intersection Λ) (r : ℕ) :
    translationCount Λ N r = normalizationIndex Λ N r * intersectionIndex Λ ^ r := by
  rw [translationCount, normalizationIndex, intersectionIndex, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _
    (Submodule.toAddSubgroup_mono hN)
    (Submodule.toAddSubgroup_mono (inf_le_left : intersection Λ ≤ Λ))).symm

theorem intersectionIndex_pos [IsCMField E]
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hU : Unimodular Λ) {N : ℕ}
    (hN0 : N ≠ 0) (hN : levelLattice E n N ≤ intersection Λ) :
    0 < intersectionIndex Λ := by
  have : (standard E n).toAddSubgroup.IsFiniteRelIndex Λ.toAddSubgroup :=
    Submodule.isFiniteRelIndex_of_map_linearMapMulLeft_le
      (A := Λ) (B := standard E n) hN0
      (fg_of_level Λ hU hN0 hN) (by
        rintro _ ⟨v, hv, rfl⟩
        change (N : E) • v ∈ standard E n
        exact smul_mem_standard Λ hU hN v hv)
  rw [intersectionIndex_eq_relIndex]
  exact Nat.pos_of_ne_zero AddSubgroup.relIndex_ne_zero

theorem normalizationIndex_pos (Λ : Submodule (𝓞 E) (Fin n → E)) {N : ℕ}
    (hN0 : N ≠ 0) (r : ℕ) : 0 < normalizationIndex Λ N r := by
  have : (levelLattice E n N).toAddSubgroup.IsFiniteRelIndex (standard E n).toAddSubgroup :=
    Submodule.isFiniteRelIndex_of_map_linearMapMulLeft_le
      (A := standard E n) (B := levelLattice E n N) hN0 standard_fg (by
      rintro _ ⟨v, hv, rfl⟩
      change (N : E) • v ∈ levelLattice E n N
      exact (span_nat_smul_le N _ _).mp le_rfl v hv)
  have : (levelLattice E n N).toAddSubgroup.IsFiniteRelIndex (intersection Λ).toAddSubgroup :=
    AddSubgroup.isFiniteRelIndex_of_le_right _
      (Submodule.toAddSubgroup_mono (inf_le_right : intersection Λ ≤ standard E n))
  change 0 < ((levelLattice E n N).toAddSubgroup.relIndex
    (intersection Λ).toAddSubgroup) ^ r
  exact pow_pos (Nat.pos_of_ne_zero AddSubgroup.relIndex_ne_zero) r

theorem translationCount_pos [IsCMField E]
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hU : Unimodular Λ) {N : ℕ}
    (hN0 : N ≠ 0) (hN : levelLattice E n N ≤ intersection Λ) (r : ℕ) :
    0 < translationCount Λ N r := by
  rw [translationCount_eq Λ hN r]
  exact Nat.mul_pos (normalizationIndex_pos Λ hN0 r)
    (pow_pos (intersectionIndex_pos Λ hU hN0 hN) r)

/-- A nonzero level ideal gives the actual finite quotient of any finite
integral module, exactly as in the source definition of `LevQ`. -/
theorem finite_levelQuotient (M : Type*) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    Finite (M ⧸ (I • (⊤ : Submodule (𝓞 E) M))) := by
  have : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  exact Submodule.finite_quotient_smul I Module.Finite.fg_top

/-- The same theta lattice has a finite level quotient; finite generation
is obtained from its actual admissible level and self-duality. -/
theorem finite_lattice_levelQuotient [IsCMField E]
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hU : Unimodular Λ) {N : ℕ}
    (hN0 : N ≠ 0) (hN : levelLattice E n N ≤ intersection Λ)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    Finite (Λ ⧸ (I • (⊤ : Submodule (𝓞 E) Λ))) := by
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr (fg_of_level Λ hU hN0 hN)
  exact finite_levelQuotient Λ I hI

end RHLean.Geometry.NativeTheta.Lattice

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits

variable {φ : Frame} (H : HostRaw φ)

/-- The actual inverse-ideal coefficient lattice has a finite level quotient.
No replacement free lattice is chosen. -/
theorem coefficientIdeal_finite_levelQuotient (B I : Ideal (𝓞 H.E)) (hI : I ≠ ⊥) :
    Finite (coefficientIdeal H B ⧸
      (I • (⊤ : Submodule (𝓞 H.E) (coefficientIdeal H B)))) := by
  have := coefficientIdeal_finite_over_integers H B
  exact RHLean.Geometry.NativeTheta.Lattice.finite_levelQuotient (coefficientIdeal H B) I hI

/-- The tuple count appearing in the short-value averaging denominator is
strictly positive for the same native coefficient lattice and level ideal. -/
theorem coefficientIdeal_levelTuples_card_pos (B I : Ideal (𝓞 H.E)) (hI : I ≠ ⊥) (n : ℕ) :
    0 < Nat.card (Fin n → coefficientIdeal H B ⧸
      (I • (⊤ : Submodule (𝓞 H.E) (coefficientIdeal H B)))) := by
  have := coefficientIdeal_finite_levelQuotient H B I hI
  exact Nat.card_pos

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
