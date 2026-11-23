import RHLean.Geometry.NativeThetaCuspFiniteCharacter

/-!
# Constructed equivariant coefficients on the actual finite quotient

The first rows of a quotient family determine a finite coefficient. It
vanishes precisely off the spanning frames, equals 1 at a constructed
frame, and transforms by the inverse of the character of the actual
adjoint. The quotient coordinates and adjoint are constructed on the
original finite projective integral module.

All nonzero coefficients are roots of unity in an actual number field;
their integrality and all-place unit norm are proved. This supplies the
arithmetic fields of PhiPin. Identifying its finite Fourier transform with
an actual section on a geometric cover remains a separate obligation.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HalvesFreeAndAdjoint.lean
(`exists_equiv_of_span`, `exists_span`, `existsUnique_equiv`) and
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsEquivariantFunOnSpanningFamilies.lean
(`exists_equivariant_fun_on_spanning_families`).
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module
open scoped BigOperators Pointwise Classical

namespace RHLean.Geometry.NativeTheta.Cusp.FiniteCoefficients

theorem exists_equiv_of_span {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (x : Fin r → Q) (hx : Submodule.span R (Set.range x) = ⊤) :
    ∃ ψ : (Fin r → R ⧸ I) ≃ₗ[R] Q, ∀ b, ψ (Pi.single b 1) = x b := by
  have hk : ∀ a ∈ I, ∀ q : Q, a • q = 0 := by
    intro a ha q
    apply e.injective
    rw [map_smul, map_zero]
    funext i
    rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
    rfl
  let f : Fin r → ((R ⧸ I) →ₗ[R] Q) := fun b =>
    Submodule.liftQ I (LinearMap.toSpanSingleton R Q (x b)) (fun a ha => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hk a ha _)
  have hf : ∀ b, f b 1 = x b := fun b => by
    have : f b (Submodule.Quotient.mk (1 : R)) = x b := by
      simp only [f, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    exact this
  let ψ : (Fin r → R ⧸ I) →ₗ[R] Q := ∑ b, (f b) ∘ₗ LinearMap.proj b
  have hψ : ∀ b, ψ (Pi.single b 1) = x b := fun b => by
    simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single b]
    · rw [Pi.single_eq_same, hf]
    · intro i _ hi; rw [Pi.single_eq_of_ne hi, map_zero]
    · simp
  have hs : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hx, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact ⟨_, hψ b⟩
  have hi : Function.Injective (e.toLinearMap ∘ₗ ψ) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hs)
  exact ⟨LinearEquiv.ofBijective ψ ⟨Function.Injective.of_comp (f := e) hi, hs⟩, hψ⟩

theorem exists_span {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) : ∃ x : Fin r → Q, Submodule.span R (Set.range x) = ⊤ := by
  refine ⟨fun b => e.symm (Pi.single b 1), eq_top_iff.2 fun q _ => ?_⟩
  have h : q = ∑ b, e.symm (Pi.single b (e q b)) := by
    rw [← map_sum, Finset.univ_sum_single, e.symm_apply_apply]
  rw [h]
  refine Submodule.sum_mem _ fun b _ => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e q b)
  have : (Pi.single b (e q b) : Fin r → R ⧸ I) = a • Pi.single b 1 := by
    rw [← Pi.single_smul, ← ha, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem existsUnique_equiv {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (x x' : Fin r → Q) (hx : Submodule.span R (Set.range x) = ⊤)
    (hx' : Submodule.span R (Set.range x') = ⊤) : ∃! g : Q ≃ₗ[R] Q, ∀ b, g (x b) = x' b := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_of_span I r e x hx
  obtain ⟨ψ', hψ'⟩ := exists_equiv_of_span I r e x' hx'
  have h0 : ∀ b, (ψ.symm ≪≫ₗ ψ') (x b) = x' b := fun b => by
    rw [LinearEquiv.trans_apply, ← hψ, ψ.symm_apply_apply, hψ']
  refine ⟨ψ.symm ≪≫ₗ ψ', h0, fun g hg => ?_⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on_range hx fun b => ?_
  exact (hg b).trans (h0 b).symm

theorem exists_equivariant_fun_on_spanning_families {R M G F : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Group G] [Field F] {r n : ℕ} (hrn : r ≤ n)
    (h0 : ∃ x₀ : Fin r → M, Submodule.span R (Set.range x₀) = ⊤)
    (h1 : ∀ x x' : Fin r → M, Submodule.span R (Set.range x) = ⊤ → Submodule.span R (Set.range x') = ⊤ →
      ∃! g : M ≃ₗ[R] M, ∀ b, g (x b) = x' b)
    (adj : (M ≃ₗ[R] M) → G) (hadj : ∀ g g', adj (g * g') = adj g' * adj g) (ψ : G →* Fˣ) :
    ∃ (ph : (Fin n → M) → F) (x₀ : Fin n → M),
      (∀ x x' : Fin n → M, (∀ b : Fin n, b.val < r → x b = x' b) → ph x = ph x') ∧
      (∀ x, ph x ≠ 0 → Submodule.span R (x '' {b | b.val < r}) = ⊤) ∧
      (∀ (kst : M ≃ₗ[R] M) x, ph (fun b => kst (x b)) = (((ψ (adj kst))⁻¹ : Fˣ) : F) * ph x) ∧
      ph x₀ = 1 ∧ Submodule.span R (x₀ '' {b | b.val < r}) = ⊤ := by
  classical
  obtain ⟨y, hy⟩ := h0
  have himg : ∀ x : Fin n → M, x '' {b | b.val < r} = Set.range (fun b : Fin r => x (Fin.castLE hrn b)) := by
    intro x
    ext m
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hrn b, b.2, rfl⟩
  have hadj1 : adj 1 = 1 := by
    have := hadj 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  let f : (Fin r → M) → F := fun z =>
    if h : Submodule.span R (Set.range z) = ⊤ then (((ψ (adj (h1 y z hy h).exists.choose))⁻¹ : Fˣ) : F) else 0
  have hf : ∀ (z : Fin r → M) (g : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ → (∀ b, g (y b) = z b) →
      f z = (((ψ (adj g))⁻¹ : Fˣ) : F) := by
    intro z g hz hg
    have : (h1 y z hy hz).exists.choose = g :=
      (h1 y z hy hz).unique (h1 y z hy hz).exists.choose_spec hg
    simp only [f, dite_eq_left hz, this]
  have hspan : ∀ (z : Fin r → M) (k : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ →
      Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
    intro z k hz
    have e : (Set.range fun b => k (z b)) = (k : M →ₗ[R] M) '' Set.range z := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hz, Submodule.map_top, LinearEquiv.range]
  let x₀ : Fin n → M := fun b => if h : b.val < r then y ⟨b.val, h⟩ else 0
  have hx₀ : (fun b : Fin r => x₀ (Fin.castLE hrn b)) = y := by
    funext b
    simp [x₀]
  refine ⟨fun x => f (fun b => x (Fin.castLE hrn b)), x₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' h
    have : (fun b : Fin r => x (Fin.castLE hrn b)) = fun b => x' (Fin.castLE hrn b) :=
      funext fun b => h _ b.2
    simp only [this]
  · intro x hx
    rw [himg]
    by_contra hz
    exact hx (by simp only [f, dite_eq_right hz])
  · intro k x
    set z : Fin r → M := fun b => x (Fin.castLE hrn b) with hzdef
    change f (fun b => k (z b)) = _ * f z
    by_cases hz : Submodule.span R (Set.range z) = ⊤
    · obtain ⟨g, hg, -⟩ := h1 y z hy hz
      rw [hf z g hz hg, hf _ (k * g) (hspan z k hz) (fun b => by simp [hg b]), hadj, map_mul, mul_inv,
        Units.val_mul, mul_comm]
    · have hz' : ¬ Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
        intro h
        have := hspan _ k.symm h
        simp only [LinearEquiv.symm_apply_apply] at this
        exact hz this
      simp only [f, dite_eq_right hz, dite_eq_right hz', mul_zero]
  · change f (fun b : Fin r => x₀ (Fin.castLE hrn b)) = 1
    rw [hx₀, hf y 1 hy (fun b => rfl), hadj1]
    simp
  · rw [himg, hx₀, hy]

open QuotientAdjoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : NativeGeometricHost E}

/-- Construct the arithmetic coefficient, including its exact original
adjoint congruence, on the literal two half-level quotients of D.La. -/
theorem exists_five_coefficients (D : NativeGeometricDatum H)
    (P : Ideal (𝓞 E)) (hP : P ≠ ⊤) (hP0 : P ≠ ⊥)
    (hp : P * P.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(5 : 𝓞 E)})
    (hc : IsCoprime P (P.map (H.bar : 𝓞 E →+* 𝓞 E)))
    (hr : 1 ≤ D.p + D.q) (n : ℕ) (hn : D.p + D.q ≤ n) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F)
      (ψ : (IQuot D P ≃ₗ[𝓞 E] IQuot D P) →* Fˣ)
      (ph : (Fin n → JQuot D P) → F) (x₀ : Fin n → JQuot D P),
      ψ ≠ 1 ∧
      (∀ x x', (∀ b : Fin n, b.val < D.p + D.q → x b = x' b) → ph x = ph x') ∧
      (∀ x, ph x ≠ 0 ↔ Submodule.span (𝓞 E) (x '' {b | b.val < D.p + D.q}) = ⊤) ∧
      (∀ (k : IQuot D P ≃ₗ[𝓞 E] IQuot D P) (g : JQuot D P ≃ₗ[𝓞 E] JQuot D P),
        (∀ u v : D.La, (5 : ℤ) ∣
          D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf H P • v) -
            D.EF u (cHalf H P • qRep (k (Submodule.Quotient.mk v)))) →
          ∀ x, ph (fun b => g (x b)) = (((ψ k)⁻¹ : Fˣ) : F) * ph x) ∧
      ph x₀ = 1 ∧ Submodule.span (𝓞 E) (x₀ '' {b | b.val < D.p + D.q}) = ⊤ ∧
      ∀ x, IsIntegral ℤ (ph x) ∧ ∀ σ : F →+* ℂ, ‖σ (ph x)‖ ≤ 1 := by
  have h5 : (5 : 𝓞 E) ∈ P := by
    apply (show Ideal.span {(5 : 𝓞 E)} ≤ P from by
      rw [← hp]
      exact Ideal.mul_le_left)
    exact Ideal.mem_span_singleton_self _
  obtain ⟨F, hF, ψ, hψ, hψval⟩ := FiniteCharacter.exists_five_character D P hP hP0 h5 hr
  let := hF
  have hJ0 : P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot] at hp
    have hzero : (5 : 𝓞 E) = 0 := by
      exact Ideal.span_singleton_eq_bot.mp hp.symm
    norm_num at hzero
  let : Finite (𝓞 E ⧸ P.map (H.bar : 𝓞 E →+* 𝓞 E)) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hJ0
  let := D.fin
  let := D.proj
  obtain ⟨e⟩ := NativeThetaFullLevelCost.nonempty_equiv_mod (𝓞 E) D.La
    (P.map (H.bar : 𝓞 E →+* 𝓞 E)) (D.p + D.q) D.rank
  obtain ⟨adj, hadj, hiff⟩ := exists_adjoint_halves D 5 P hp hc
  obtain ⟨ph, x₀, hrows, hsupp, hact, h1, hspan⟩ :=
    exists_equivariant_fun_on_spanning_families hn
      (exists_span _ _ e) (existsUnique_equiv _ _ e) adj hadj ψ
  have himg : ∀ x : Fin n → JQuot D P,
      x '' {b | b.val < D.p + D.q} =
        Set.range (fun b : Fin (D.p + D.q) => x (Fin.castLE hn b)) := by
    intro x
    ext m
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hn b, b.2, rfl⟩
  have hvalue : ∀ x, Submodule.span (𝓞 E) (x '' {b | b.val < D.p + D.q}) = ⊤ →
      ∃ k : IQuot D P ≃ₗ[𝓞 E] IQuot D P, ph x = (ψ k : F) := by
    intro x hx
    obtain ⟨g, hg, -⟩ := existsUnique_equiv _ _ e
      (fun b => x₀ (Fin.castLE hn b)) (fun b => x (Fin.castLE hn b))
      (by rwa [← himg]) (by rwa [← himg])
    refine ⟨(adj g)⁻¹, ?_⟩
    calc
      ph x = ph (fun b => g (x₀ b)) := hrows _ _ fun b hb => by
        have hi : Fin.castLE hn ⟨b.val, hb⟩ = b := Fin.ext rfl
        simpa only [hi] using (hg ⟨b.val, hb⟩).symm
      _ = (ψ ((adj g)⁻¹) : F) := by rw [hact, h1, mul_one, map_inv]
  refine ⟨F, hF, ψ, ph, x₀, hψ, hrows, fun x => ⟨hsupp x, fun hx => ?_⟩,
    fun k g h => ?_, h1, hspan, fun x => ?_⟩
  · obtain ⟨k, hk⟩ := hvalue x hx
    rw [hk]
    exact (ψ k).ne_zero
  · have he : k = adj g := (hiff k g).mp h
    rw [he]
    exact hact g
  · by_cases hx : ph x = 0
    · rw [hx]
      exact ⟨isIntegral_zero, fun σ => by rw [map_zero, norm_zero]; exact zero_le_one⟩
    · obtain ⟨k, hk⟩ := hvalue x (hsupp x hx)
      rw [hk]
      exact ⟨(hψval k).1, fun σ => le_of_eq ((hψval k).2 σ)⟩

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization

/-- The split ideal, nontrivial finite character, and normalized equivariant
coefficient are constructed together on the prescribed native trace lattice. -/
theorem exists_native_five_coefficients
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
        (ph : (Fin n → JQuot D P) → F) (x₀ : Fin n → JQuot D P),
        ψ ≠ 1 ∧
        (∀ x x', (∀ b : Fin n, b.val < D.p + D.q → x b = x' b) → ph x = ph x') ∧
        (∀ x, ph x ≠ 0 ↔ Submodule.span (𝓞 H.E) (x '' {b | b.val < D.p + D.q}) = ⊤) ∧
        (∀ (a : IQuot D P ≃ₗ[𝓞 H.E] IQuot D P) (g : JQuot D P ≃ₗ[𝓞 H.E] JQuot D P),
          (∀ u v : D.La, (5 : ℤ) ∣
            D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf G P • v) -
              D.EF u (cHalf G P • qRep (a (Submodule.Quotient.mk v)))) →
            ∀ x, ph (fun b => g (x b)) = (((ψ a)⁻¹ : Fˣ) : F) * ph x) ∧
        ph x₀ = 1 ∧ Submodule.span (𝓞 H.E) (x₀ '' {b | b.val < D.p + D.q}) = ⊤ ∧
        ∀ x, IsIntegral ℤ (ph x) ∧ ∀ σ : F →+* ℂ, ‖σ (ph x)‖ ≤ 1 := by
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
    exact nativeDyadicGeometricHost_bar_eq e q d he hH a
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
  exact ⟨P, hP1, hP0, hc, hPo, hp, exists_five_coefficients D P hP1 hP0 hp hc hr n hn'⟩

end RHLean.Geometry.NativeTheta.Cusp.FiniteCoefficients

