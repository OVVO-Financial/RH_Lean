import RHLean.Geometry.NativeThetaCuspFiniteCoefficients

/-!
# The actual finite Fourier coefficient and its adjoint character law

The coefficient field is enlarged by the canonical fifth root of unity.
The finite transform uses the SAME integral EF, cHalf and quotient
representatives as the source's sixth PhiPin clause. Its integrality,
all-place cardinality bound, and inverse-adjoint character law are proved.
The label ideal is explicit, so this transform can be used at the actual
larger cover level without replacing its modulus by five.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsEquivariantFunOnSpanningFamilies.lean
(`exists_phiPin_of_character`, its finite transform),
src/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IsIntegralZpowOfPowEqOne.lean,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DatEqOfPhiHat.lean
(the exact root-of-unity congruence), and
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CmHostUnitAddConjEqOne.lean
(the finite-sum adjoint reindexing).
This does not identify the transform with a global algebraic section.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open NumberField Module
open scoped Classical Pointwise BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.FiniteFourier

open QuotientAdjoint

/-- The canonical source choice of the primitive fifth root. -/
def rootFive : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

theorem rootFive_primitive : IsPrimitiveRoot rootFive 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- Adjoin the required root to the already constructed coefficient field.
The original coefficients are retained through the literal inclusion. -/
theorem exists_root_extension (F : IntermediateField ℚ ℂ) [NumberField F] :
    ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F')
      (_hF : F ≤ F') (ζ : F'), (ζ : ℂ) = rootFive ∧ IsPrimitiveRoot ζ 5 := by
  let S : Set ℂ := {rootFive}
  have : Finite S := (Set.finite_singleton rootFive).to_subtype
  let C := IntermediateField.adjoin ℚ S
  have : FiniteDimensional ℚ C := IntermediateField.finiteDimensional_adjoin (fun z hz => by
    have hz' : z = rootFive := Set.mem_singleton_iff.mp hz
    rw [hz']
    exact (rootFive_primitive.isIntegral (by norm_num : 0 < 5)).tower_top)
  let F' := F ⊔ C
  have : FiniteDimensional ℚ F' := IntermediateField.finiteDimensional_sup F C
  let : NumberField F' := ⟨⟩
  have hm : rootFive ∈ F' :=
    (show C ≤ F' from le_sup_right) (IntermediateField.subset_adjoin ℚ S (by simp [S]))
  let ζ : F' := ⟨rootFive, hm⟩
  refine ⟨F', inferInstance, le_sup_left, ζ, rfl, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := F'.val) rootFive_primitive
    Subtype.val_injective

theorem isIntegral_zpow_of_pow_eq_one {F : Type} [Field F]
    {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) (a : ℤ) :
    IsIntegral ℤ (z ^ a) := by
  refine IsIntegral.of_pow hN ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm a, zpow_mul, zpow_natCast, hz, one_zpow]
  exact isIntegral_one

theorem zpow_eq_of_dvd_sub {F : Type} [Field F]
    (z : F) (N : ℕ) (hN : 0 < N) (hz : z ^ N = 1)
    {a b : ℤ} (h : (N : ℤ) ∣ a - b) : z ^ a = z ^ b := by
  obtain ⟨j, hj⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact zero_ne_one hz
  have he : a = b + N * j := by omega
  rw [he, zpow_add₀ hz0, zpow_mul, zpow_natCast, hz, one_zpow, mul_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : NativeGeometricHost E} (D : NativeGeometricDatum H)

/-- The exact sixth-clause finite sum, at a separately retained label ideal. -/
def transform {F : Type} [Field F] {n : ℕ} (P L : Ideal (𝓞 E))
    (ζ : F) (ph : (Fin n → JQuot D P) → F)
    (q : Fin n → IQuot D L) : F :=
  ∑ᶠ x : Fin n → JQuot D P, ph x *
    ζ ^ (∑ b, D.EF (qRep (x b)) (cHalf H P • qRep (q b)))

/-- The source arithmetic integrality holds for the constructed finite sum. -/
theorem transform_integral {F : Type} [Field F] {n : ℕ}
    (P L : Ideal (𝓞 E)) (ζ : F) (hζ : ζ ^ 5 = 1)
    (ph : (Fin n → JQuot D P) → F) (hph : ∀ x, IsIntegral ℤ (ph x))
    (q : Fin n → IQuot D L) : IsIntegral ℤ (transform D P L ζ ph q) := by
  unfold transform
  refine finsum_induction (fun y => IsIntegral ℤ y) isIntegral_zero
    (fun a b ha hb => ha.add hb) (fun x => ?_)
  exact (hph x).mul (isIntegral_zpow_of_pow_eq_one (by norm_num : 0 < 5) hζ _)

/-- Every embedding retains the actual finite quotient cardinality cost. -/
theorem transform_norm_le {F : Type} [Field F] {n : ℕ}
    (P L : Ideal (𝓞 E)) [Finite (JQuot D P)]
    (ζ : F) (hζ : ζ ^ 5 = 1) (ph : (Fin n → JQuot D P) → F)
    (hph : ∀ x (σ : F →+* ℂ), ‖σ (ph x)‖ ≤ 1)
    (q : Fin n → IQuot D L) (σ : F →+* ℂ) :
    ‖σ (transform D P L ζ ph q)‖ ≤ Nat.card (Fin n → JQuot D P) := by
  have : Fintype (Fin n → JQuot D P) := Fintype.ofFinite _
  have hz : ‖σ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
    (by rw [← map_pow, hζ, map_one]) (by norm_num : (5 : ℕ) ≠ 0)
  rw [transform, finsum_eq_sum_of_fintype, map_sum]
  calc
    ‖∑ x : Fin n → JQuot D P, σ (ph x *
      ζ ^ (∑ b, D.EF (qRep (x b)) (cHalf H P • qRep (q b))))‖
        ≤ ∑ x : Fin n → JQuot D P, ‖σ (ph x *
          ζ ^ (∑ b, D.EF (qRep (x b)) (cHalf H P • qRep (q b))))‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Fin n → JQuot D P, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [map_mul, map_zpow₀, norm_mul, norm_zpow, hz, one_zpow, mul_one]
      exact hph x σ
    _ = Nat.card (Fin n → JQuot D P) := by simp [Nat.card_eq_fintype_card]

/-- Reindexing by the constructed quotient adjoint gives the precise
inverse-character law for the finite Fourier coefficient. -/
theorem transform_adjoint {F : Type} [Field F] {n : ℕ}
    (P : Ideal (𝓞 E)) (ζ : F) (hζ : ζ ^ 5 = 1)
    (ph : (Fin n → JQuot D P) → F) (u : Fˣ)
    (k : IQuot D P ≃ₗ[𝓞 E] IQuot D P)
    (g : JQuot D P ≃ₗ[𝓞 E] JQuot D P)
    (hpair : ∀ a b : D.La, (5 : ℤ) ∣
      D.EF (qRep (g (Submodule.Quotient.mk a))) (cHalf H P • b) -
        D.EF a (cHalf H P • qRep (k (Submodule.Quotient.mk b))))
    (hph : ∀ x, ph (fun b => g (x b)) = (u : F) * ph x)
    (q : Fin n → IQuot D P) :
    transform D P P ζ ph (fun b => k.symm (q b)) =
      (u : F) * transform D P P ζ ph q := by
  unfold transform
  rw [mul_finsum, ← finsum_comp_equiv (Equiv.piCongrRight (fun _ : Fin n => g.toEquiv))]
  refine finsum_congr fun x => ?_
  change ph (fun b => g (x b)) *
    ζ ^ (∑ b, D.EF (qRep (g (x b))) (cHalf H P • qRep (k.symm (q b)))) = _
  rw [hph, mul_assoc]
  congr 1
  congr 1
  apply zpow_eq_of_dvd_sub ζ 5 (by norm_num) hζ
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro b _
  obtain ⟨t, ht⟩ := hpair (qRep (x b)) (qRep (k.symm (q b)))
  refine ⟨t, ?_⟩
  simpa only [qRep_mk, LinearEquiv.apply_symm_apply] using ht

end RHLean.Geometry.NativeTheta.Cusp.FiniteFourier
