import RHLean.Geometry.NativeThetaCuspFiniteFourier

/-!
# Constructed finite Fourier data on the native projective quotient

The first five arithmetic PhiPin properties are retained in one actual
number field containing the canonical fifth root of unity. Its sixth
coefficient is the literal finite transform, with proved integrality,
all-place norm control, and the precise inverse-adjoint character law.
The full label ideal is a separate argument throughout.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsEquivariantFunOnSpanningFamilies.lean
(`exists_phiPin_of_character`),
src/Formalism/LocalToGlobal/ProjectiveLattices/ThShort.lean (`DeltaDat.PhiPin`), and
src/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IsIntegralZpowOfPowEqOne.lean.
The number-field enlargement preserves the previously constructed actual
character and coefficients. No DeltaDat, PsiTie, algebraic section or
Petersson mass is assumed or asserted. The source mirror states no license;
attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open NumberField Module
open scoped Classical Pointwise BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.FiniteFourierCoefficients

open QuotientAdjoint FiniteFourier

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : NativeGeometricHost E}

/-- The arithmetic Fourier supplier, including the original normalized
nonzero spanning coefficient and the exact finite adjoint covariance. -/
theorem exists_five_fourier_coefficients (D : NativeGeometricDatum H)
    (P : Ideal (𝓞 E)) (hP : P ≠ ⊤) (hP0 : P ≠ ⊥)
    (hp : P * P.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(5 : 𝓞 E)})
    (hc : IsCoprime P (P.map (H.bar : 𝓞 E →+* 𝓞 E)))
    (hr : 1 ≤ D.p + D.q) (n : ℕ) (hn : D.p + D.q ≤ n) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F)
      (ψ : (IQuot D P ≃ₗ[𝓞 E] IQuot D P) →* Fˣ)
      (ph : (Fin n → JQuot D P) → F) (x₀ : Fin n → JQuot D P) (ζ : F),
      ψ ≠ 1 ∧
      (∀ x x', (∀ b : Fin n, b.val < D.p + D.q → x b = x' b) → ph x = ph x') ∧
      (∀ x, ph x ≠ 0 ↔ Submodule.span (𝓞 E) (x '' {b | b.val < D.p + D.q}) = ⊤) ∧
      (∀ (k : IQuot D P ≃ₗ[𝓞 E] IQuot D P) (g : JQuot D P ≃ₗ[𝓞 E] JQuot D P),
        (∀ u v : D.La, (5 : ℤ) ∣
          D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf H P • v) -
            D.EF u (cHalf H P • qRep (k (Submodule.Quotient.mk v)))) →
          ∀ x, ph (fun b => g (x b)) = (((ψ k)⁻¹ : Fˣ) : F) * ph x) ∧
      ph x₀ = 1 ∧ Submodule.span (𝓞 E) (x₀ '' {b | b.val < D.p + D.q}) = ⊤ ∧
      (∀ x, IsIntegral ℤ (ph x) ∧ ∀ σ : F →+* ℂ, ‖σ (ph x)‖ ≤ 1) ∧
      (ζ : ℂ) = rootFive ∧ IsPrimitiveRoot ζ 5 ∧
      (∀ (L : Ideal (𝓞 E)) (q : Fin n → IQuot D L),
        IsIntegral ℤ (transform D P L ζ ph q) ∧
          ∀ σ : F →+* ℂ, ‖σ (transform D P L ζ ph q)‖ ≤
            Nat.card (Fin n → JQuot D P)) ∧
      ∀ (k : IQuot D P ≃ₗ[𝓞 E] IQuot D P) (g : JQuot D P ≃ₗ[𝓞 E] JQuot D P),
        (∀ u v : D.La, (5 : ℤ) ∣
          D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf H P • v) -
            D.EF u (cHalf H P • qRep (k (Submodule.Quotient.mk v)))) →
          ∀ q : Fin n → IQuot D P,
            transform D P P ζ ph (fun b => k.symm (q b)) =
              (((ψ k)⁻¹ : Fˣ) : F) * transform D P P ζ ph q := by
  obtain ⟨F, hF, ψ, ph, x₀, hψ, hrows, hsupp, hact, hone, hspan, hbound⟩ :=
    FiniteCoefficients.exists_five_coefficients D P hP hP0 hp hc hr n hn
  let := hF
  obtain ⟨F', hF', hFF', ζ, hζc, hζ⟩ := exists_root_extension F
  let := hF'
  let ι : F →ₐ[ℚ] F' := IntermediateField.inclusion hFF'
  let ψ' : (IQuot D P ≃ₗ[𝓞 E] IQuot D P) →* F'ˣ :=
    (Units.map ι.toRingHom.toMonoidHom).comp ψ
  let ph' : (Fin n → JQuot D P) → F' := fun x => ι (ph x)
  have hψ' : ψ' ≠ 1 := by
    intro h
    apply hψ
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply ι.injective
    have he := congrArg (fun f : (IQuot D P ≃ₗ[𝓞 E] IQuot D P) →* F'ˣ =>
      (f g : F')) h
    simpa [ψ'] using he
  have hact' : ∀ (k : IQuot D P ≃ₗ[𝓞 E] IQuot D P)
      (g : JQuot D P ≃ₗ[𝓞 E] JQuot D P),
      (∀ u v : D.La, (5 : ℤ) ∣
        D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf H P • v) -
          D.EF u (cHalf H P • qRep (k (Submodule.Quotient.mk v)))) →
      ∀ x, ph' (fun b => g (x b)) = (((ψ' k)⁻¹ : F'ˣ) : F') * ph' x := by
    intro k g h x
    simpa [ph', ψ'] using congrArg ι (hact k g h x)
  have hbound' : ∀ x, IsIntegral ℤ (ph' x) ∧ ∀ σ : F' →+* ℂ, ‖σ (ph' x)‖ ≤ 1 := by
    intro x
    exact ⟨(hbound x).1.map ι.toRingHom.toIntAlgHom,
      fun σ => (hbound x).2 (σ.comp ι.toRingHom)⟩
  have hJ0 : P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot] at hp
    have hzero : (5 : 𝓞 E) = 0 := Ideal.span_singleton_eq_bot.mp hp.symm
    norm_num at hzero
  have : Finite (𝓞 E ⧸ P.map (H.bar : 𝓞 E →+* 𝓞 E)) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hJ0
  have := D.fin
  have := D.proj
  obtain ⟨eJ⟩ := NativeThetaFullLevelCost.nonempty_equiv_mod (𝓞 E) D.La
    (P.map (H.bar : 𝓞 E →+* 𝓞 E)) (D.p + D.q) D.rank
  have : Finite (JQuot D P) := Finite.of_equiv _ eJ.symm.toEquiv
  refine ⟨F', hF', ψ', ph', x₀, ζ, hψ', ?_, ?_, hact', ?_, hspan,
    hbound', hζc, hζ, ?_, ?_⟩
  · intro x x' hx
    exact congrArg ι (hrows x x' hx)
  · intro x
    simpa only [ph', ne_eq, map_eq_zero] using hsupp x
  · change ι (ph x₀) = 1
    rw [hone, map_one]
  · intro L q
    exact ⟨transform_integral D P L ζ hζ.pow_eq_one ph' (fun x => (hbound' x).1) q,
      fun σ => transform_norm_le D P L ζ hζ.pow_eq_one ph'
        (fun x => (hbound' x).2) q σ⟩
  · intro k g h q
    exact transform_adjoint D P ζ hζ.pow_eq_one ph' (ψ' k)⁻¹ k g h (hact' k g h) q


open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization

/-- The actual native split ideal and projective trace lattice supply all
arithmetic Fourier data, with every coefficient property retained. -/
theorem exists_native_five_fourier_coefficients
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) (n : ℕ) (hn : k + m - 1 ≤ n) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    ∃ P : Ideal (𝓞 H.E), P ≠ ⊤ ∧ P ≠ ⊥ ∧
      IsCoprime P (P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)) ∧
      IsCoprime P (Ideal.span {(2 : 𝓞 H.E)}) ∧
      P * P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = Ideal.span {(5 : 𝓞 H.E)} ∧
      ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F)
        (ψ : (IQuot D P ≃ₗ[𝓞 H.E] IQuot D P) →* Fˣ)
        (ph : (Fin n → JQuot D P) → F) (x₀ : Fin n → JQuot D P) (ζ : F),
        ψ ≠ 1 ∧
        (∀ x x', (∀ b : Fin n, b.val < D.p + D.q → x b = x' b) → ph x = ph x') ∧
        (∀ x, ph x ≠ 0 ↔ Submodule.span (𝓞 H.E) (x '' {b | b.val < D.p + D.q}) = ⊤) ∧
        (∀ (k : IQuot D P ≃ₗ[𝓞 H.E] IQuot D P) (g : JQuot D P ≃ₗ[𝓞 H.E] JQuot D P),
          (∀ u v : D.La, (5 : ℤ) ∣
            D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf G P • v) -
              D.EF u (cHalf G P • qRep (k (Submodule.Quotient.mk v)))) →
            ∀ x, ph (fun b => g (x b)) = (((ψ k)⁻¹ : Fˣ) : F) * ph x) ∧
        ph x₀ = 1 ∧ Submodule.span (𝓞 H.E) (x₀ '' {b | b.val < D.p + D.q}) = ⊤ ∧
        (∀ x, IsIntegral ℤ (ph x) ∧ ∀ σ : F →+* ℂ, ‖σ (ph x)‖ ≤ 1) ∧
        (ζ : ℂ) = rootFive ∧ IsPrimitiveRoot ζ 5 ∧
        (∀ (L : Ideal (𝓞 H.E)) (q : Fin n → IQuot D L),
          IsIntegral ℤ (transform D P L ζ ph q) ∧
            ∀ σ : F →+* ℂ, ‖σ (transform D P L ζ ph q)‖ ≤
              Nat.card (Fin n → JQuot D P)) ∧
        ∀ (k : IQuot D P ≃ₗ[𝓞 H.E] IQuot D P) (g : JQuot D P ≃ₗ[𝓞 H.E] JQuot D P),
          (∀ u v : D.La, (5 : ℤ) ∣
            D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf G P • v) -
              D.EF u (cHalf G P • qRep (k (Submodule.Quotient.mk v)))) →
            ∀ q : Fin n → IQuot D P,
              transform D P P ζ ph (fun b => k.symm (q b)) =
                (((ψ k)⁻¹ : Fˣ) : F) * transform D P P ζ ph q := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
  obtain ⟨P, hP1, hP0, hPc, hPo, hP5⟩ :
      ∃ P : Ideal (𝓞 H.E), P ≠ ⊤ ∧ P ≠ ⊥ ∧
        IsCoprime P (H.conj • P) ∧ IsCoprime P (Ideal.span {(2 : 𝓞 H.E)}) ∧
        P * (H.conj • P) = Ideal.span {(5 : 𝓞 H.E)} :=
    SplitLevel.exists_five_split_level e q d he hH
  have hmap : P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = H.conj • P := by
    rw [Ideal.pointwise_smul_def]
    congr 1
    ext a
    exact congrArg (fun z : 𝓞 H.E => (z : H.E))
      (nativeDyadicGeometricHost_bar_eq e q d he hH a)
  have hc : IsCoprime P (P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)) := by
    rw [hmap]
    exact hPc
  have hp : P * P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = Ideal.span {(5 : 𝓞 H.E)} := by
    rw [hmap]
    exact hP5
  have hrank : D.p + D.q = k + m - 1 := by
    change k + j - 1 + (m - j) = k + m - 1
    omega
  have hr : 1 ≤ D.p + D.q := by rw [hrank]; omega
  have hn' : D.p + D.q ≤ n := by rwa [hrank]
  exact ⟨P, hP1, hP0, hc, hPo, hp, exists_five_fourier_coefficients D P hP1 hP0 hp hc hr n hn'⟩


end RHLean.Geometry.NativeTheta.Cusp.FiniteFourierCoefficients
