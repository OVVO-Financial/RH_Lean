import RHLean.Geometry.NativePrescribedGeometricDatum
import RHLean.Geometry.NativeThetaCuspSplitLevel

/-!
# The actual adjoint between the conjugate finite level quotients

The original integer trace polarization induces the source pairing between
the two quotient modules. Its nondegeneracy follows from unimodularity;
representability follows by projectively lifting an actual ZMod-valued
functional to an integer functional. This constructs the adjoint, including
its reversed multiplication and the literal cHalf/qRep divisibility law.

The native endpoint uses the constructed projective coefficient lattice and
the actual conjugate half of (5). No quotient adjoint, coefficient character,
global section, or geometric PhiPin identity is supplied as a premise.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HalvesFreeAndAdjoint.lean
(`exists_adjoint`, `exists_adjoint_halves`),
src/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean
(`exists_eq_smul_of_dvd`), and
src/Formalism/LocalToGlobal/ProjectiveLattices/ThShort.lean (`cHalf`, `qRep`).
Only these algebraic declarations are reconstructed; their moduli imports
are not used. The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module
open scoped Pointwise Classical

namespace RHLean.Geometry.NativeTheta.Cusp.QuotientAdjoint

section Algebra

variable {R P Q Z : Type} [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z]

private theorem exists_adjoint (s : R → R) (B : P → Q → Z)
    (hadd : ∀ u v w, B u (v + w) = B u v + B u w)
    (hbal : ∀ a u v, B u (a • v) = B (s a • u) v)
    (hnd : ∀ v w, (∀ u, B u v = B u w) → v = w)
    (hrep : ∀ (g : P →ₗ[R] P) (v : Q), ∃ w, ∀ u, B (g u) v = B u w) :
    ∃ adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q),
      (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : Q ≃ₗ[R] Q) (g : P ≃ₗ[R] P),
        (∀ u v, B (g u) v = B u (k v)) ↔ k = adj g := by
  choose w hw using hrep
  let a : (P →ₗ[R] P) → (Q →ₗ[R] Q) := fun g =>
    { toFun := w g
      map_add' := fun v v' => hnd _ _ fun u => by rw [← hw, hadd, hadd, hw, hw]
      map_smul' := fun r v => hnd _ _ fun u => by
        rw [← hw, RingHom.id_apply, hbal, hbal, ← map_smul, hw] }
  have ha : ∀ g u v, B (g u) v = B u (a g v) := fun g u v => hw g v u
  have hinv : ∀ g g' : P →ₗ[R] P, (∀ u, g (g' u) = u) →
      a g' ∘ₗ a g = LinearMap.id := fun g g' h => by
    ext v
    refine hnd _ _ fun u => ?_
    rw [LinearMap.comp_apply, ← ha, ← ha, h, LinearMap.id_apply]
  let adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q) := fun g =>
    LinearEquiv.ofLinearMap (a g) (a g.symm) (hinv _ _ fun u => g.symm_apply_apply u)
      (hinv _ _ fun u => g.apply_symm_apply u)
  have hadj : ∀ (g : P ≃ₗ[R] P) u v, B (g u) v = B u (adj g v) :=
    fun g u v => ha g u v
  refine ⟨adj, fun g g' => ?_, fun k g => ⟨fun h => ?_, fun h => h ▸ hadj g⟩⟩
  · ext v
    refine hnd _ _ fun u => ?_
    rw [← hadj, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hadj, ← hadj]
  · ext v
    exact hnd _ _ fun u => by rw [← h, hadj]

end Algebra

section Representative

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- The original quotient representative, chosen inside the actual module. -/
def qRep {K : Submodule R M} (q : M ⧸ K) : M :=
  Classical.choose (Submodule.Quotient.mk_surjective _ q)

theorem qRep_mk {K : Submodule R M} (q : M ⧸ K) :
    Submodule.Quotient.mk (qRep q) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

end Representative

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- The source's literal choice of the conjugate-half separator. -/
def cHalf (H : NativeGeometricHost E) (I : Ideal (𝓞 E)) : 𝓞 E :=
  if h : ∃ c, c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I then h.choose else 0

theorem cHalf_spec (H : NativeGeometricHost E) (I : Ideal (𝓞 E))
    (hI : IsCoprime I (I.map (H.bar : 𝓞 E →+* 𝓞 E))) :
    cHalf H I ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ cHalf H I - 1 ∈ I := by
  have h : ∃ c, c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I := by
    obtain ⟨a, ha, c, hc, hac⟩ := Ideal.isCoprime_iff_exists.mp hI
    refine ⟨c, hc, ?_⟩
    have he : c - 1 = -a := by linear_combination hac
    rw [he]
    exact I.neg_mem ha
  unfold cHalf
  rw [dite_eq_left h]
  exact h.choose_spec

private theorem bar_bar (H : NativeGeometricHost E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

private theorem bar_mem (H : NativeGeometricHost E) {I : Ideal (𝓞 E)} {a : 𝓞 E}
    (ha : a ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) : H.bar a ∈ I := by
  obtain ⟨b, hb, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).mp ha
  change H.bar (H.bar b) ∈ I
  rwa [bar_bar]

variable {H : NativeGeometricHost E} (D : NativeGeometricDatum H)

/-- The two actual ideal quotients of the polarized integral module. -/
abbrev JQuot (I : Ideal (𝓞 E)) :=
  D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)

abbrev IQuot (I : Ideal (𝓞 E)) := D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)

private theorem ef_swap (x y : D.La) : D.EF y x = -D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt] at h
  linarith

/-- Divisibility of all actual integer pairings gives a multiple in the
same integral module, by the original unimodular polarization. -/
theorem exists_eq_smul_of_dvd (x : D.La) (m : ℕ)
    (h : ∀ y, (m : ℤ) ∣ D.EF x y) : ∃ z, x = (m : ℤ) • z := by
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => D.EF x y / m
      map_add' := fun a b => by rw [map_add, Int.add_ediv_of_dvd_left (h a)]
      map_smul' := fun k a => by
        rw [map_zsmul]
        simp only [smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc _ (h a) }
  obtain ⟨z, hz⟩ := D.unimod.2 f
  refine ⟨z, D.unimod.1 ?_⟩
  ext y
  rw [map_zsmul, hz]
  simp only [LinearMap.smul_apply, smul_eq_mul, f, LinearMap.coe_mk, AddHom.coe_mk]
  exact (Int.mul_ediv_cancel' (h y)).symm

private theorem dvd_of_mem (N : ℕ) (x y : D.La) {a : 𝓞 E}
    (ha : a ∈ Ideal.span {(N : 𝓞 E)}) : (N : ℤ) ∣ D.EF x (a • y) := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have he : (b * (N : 𝓞 E)) • y = (N : ℤ) • (b • y) := by
    rw [mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul (𝓞 E)]
    simp
  rw [he, map_zsmul]
  exact Dvd.intro _ rfl

/-- The literal source half-pairing, with its fixed separator and actual
quotient representatives. -/
def halfPairing (I : Ideal (𝓞 E)) (N : ℕ) (u : JQuot D I) (v : IQuot D I) : ZMod N :=
  (D.EF (qRep u) (cHalf H I • qRep v) : ℤ)

/-- Construct the quotient adjoint and its exact integer divisibility law.
The only pairing is the original perfect EF on D.La. -/
theorem exists_adjoint_halves (N : ℕ) (I : Ideal (𝓞 E))
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : IsCoprime I (I.map (H.bar : 𝓞 E →+* 𝓞 E))) :
    ∃ adj : (JQuot D I ≃ₗ[𝓞 E] JQuot D I) → (IQuot D I ≃ₗ[𝓞 E] IQuot D I),
      (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : IQuot D I ≃ₗ[𝓞 E] IQuot D I) (g : JQuot D I ≃ₗ[𝓞 E] JQuot D I),
        (∀ u v : D.La, (N : ℤ) ∣
          D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf H I • v) -
            D.EF u (cHalf H I • qRep (k (Submodule.Quotient.mk v)))) ↔ k = adj g := by
  obtain ⟨hc, hc1⟩ := cHalf_spec H I hI
  set c := cHalf H I
  have hmul : ∀ a ∈ I, a * c ∈ Ideal.span {(N : 𝓞 E)} :=
    fun a ha => hp ▸ Ideal.mul_mem_mul ha hc
  have hright : ∀ x, ∀ y ∈ (I • ⊤ : Submodule (𝓞 E) D.La), (N : ℤ) ∣ D.EF x (c • y) := by
    intro x y hy
    refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul, mul_comm]
      exact dvd_of_mem D _ _ _ (hmul a ha)
    · rw [smul_add, map_add]
      exact dvd_add hu hv
  have hleft : ∀ x ∈ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La),
      ∀ y, (N : ℤ) ∣ D.EF x (c • y) := by
    intro x hx y
    refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) (fun u v hu hv => ?_)
    · rw [D.adj, ← mul_smul]
      exact dvd_of_mem D _ _ _ (hmul _ (bar_mem H ha))
    · rw [map_add, LinearMap.add_apply]
      exact dvd_add hu hv
  let B := halfPairing D I N
  have hB : ∀ u v, B (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      ((D.EF u (c • v) : ℤ) : ZMod N) := by
    intro u v
    change ((D.EF (qRep (Submodule.Quotient.mk u : JQuot D I))
      (c • qRep (Submodule.Quotient.mk v : IQuot D I)) : ℤ) : ZMod N) = _
    rw [eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h1 := (Submodule.Quotient.eq _).mp
      (qRep_mk (Submodule.Quotient.mk u : JQuot D I))
    have h2 := (Submodule.Quotient.eq _).mp
      (qRep_mk (Submodule.Quotient.mk v : IQuot D I))
    have h3 := dvd_add (hleft _ h1 (qRep (Submodule.Quotient.mk v : IQuot D I))) (hright u _ h2)
    rwa [map_sub, LinearMap.sub_apply, smul_sub, map_sub, sub_add_sub_cancel] at h3
  have haddr : ∀ u v w, B u (v + w) = B u v + B u w := by
    intro u v w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_add, hB, hB, hB, smul_add, map_add, Int.cast_add]
  have haddl : ∀ u u' v, B (u + u') v = B u v + B u' v := by
    intro u v w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_add, hB, hB, hB, map_add, LinearMap.add_apply, Int.cast_add]
  have hbal : ∀ (a : 𝓞 E) u v, B u (a • v) = B (H.bar a • u) v := by
    intro a u v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hB, hB, D.adj,
      bar_bar, smul_comm]
  have hNI : (N : 𝓞 E) ∈ I := by
    have hle : Ideal.span {(N : 𝓞 E)} ≤ I := hp ▸ Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self _)
  have hnd : ∀ v w, (∀ u, B u v = B u w) → v = w := by
    intro v w h
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [eq_comm, Submodule.Quotient.eq]
    obtain ⟨z, hz⟩ := exists_eq_smul_of_dvd D (c • (w - v)) N (fun y => by
      have h := h (Submodule.Quotient.mk y)
      rw [hB, hB, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
      rw [ef_swap, dvd_neg, smul_sub, map_sub]
      exact h)
    have he : w - v = (N : 𝓞 E) • z - (c - 1) • (w - v) := by
      rw [sub_smul, one_smul, hz, ← Int.cast_smul_eq_zsmul (𝓞 E)]
      simp
    rw [he]
    exact sub_mem (Submodule.smul_mem_smul hNI Submodule.mem_top)
      (Submodule.smul_mem_smul hc1 Submodule.mem_top)
  have hrep : ∀ (g : JQuot D I →ₗ[𝓞 E] JQuot D I) (v : IQuot D I),
      ∃ w, ∀ u, B (g u) v = B u w := by
    intro g v
    let := D.proj
    let : Module.Projective ℤ D.La := by
      let := D.fin
      obtain ⟨m, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) D.La
      exact Module.Projective.of_split (s.restrictScalars ℤ) (p.restrictScalars ℤ)
        (LinearMap.ext fun x => LinearMap.congr_fun hps x)
    let f : D.La →+ ZMod N := AddMonoidHom.mk'
      (fun u => B (g (Submodule.Quotient.mk u)) v)
      (fun u u' => by simp only [Submodule.Quotient.mk_add, map_add, haddl])
    obtain ⟨F, hF⟩ := Module.projective_lifting_property
      (Int.castAddHom (ZMod N)).toIntLinearMap f.toIntLinearMap ZMod.intCast_surjective
    obtain ⟨w, hw⟩ := D.unimod.2 F
    have hF' : ∀ u, ((D.EF w u : ℤ) : ZMod N) = f u := fun u => by
      rw [hw]
      exact LinearMap.congr_fun hF u
    refine ⟨Submodule.Quotient.mk (-w), fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : f (H.bar (c - 1) • u) = 0 := by
      have he : (Submodule.Quotient.mk (H.bar (c - 1) • u) : JQuot D I) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul
          (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc1) Submodule.mem_top
      change B (g (Submodule.Quotient.mk _)) v = 0
      rw [he, map_zero]
      have h := haddl 0 0 v
      rw [add_zero] at h
      exact left_eq_add.mp h
    change f u = _
    have h1 : D.EF u (c • -w) = D.EF w (H.bar (c - 1) • u) + D.EF w u := by
      rw [← D.adj, ef_swap, sub_smul, one_smul, smul_neg, map_neg, map_sub]
      simp
    rw [hB, h1, Int.cast_add, hF', hF', h0, zero_add]
  obtain ⟨adj, h1, h2⟩ := exists_adjoint (fun a => H.bar a) B haddr hbal hnd hrep
  refine ⟨adj, h1, fun k g => ?_⟩
  rw [← h2]
  have key : ∀ u v : D.La, ((N : ℤ) ∣
      D.EF (qRep (g (Submodule.Quotient.mk u))) (c • v) -
        D.EF u (c • qRep (k (Submodule.Quotient.mk v)))) ↔
      B (g (Submodule.Quotient.mk u)) (Submodule.Quotient.mk v) =
        B (Submodule.Quotient.mk u) (k (Submodule.Quotient.mk v)) := by
    intro u v
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ← hB, ← hB, qRep_mk, qRep_mk, eq_comm]
  constructor
  · intro h u v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact (key u v).mp (h u v)
  · intro h u v
    exact (key u v).mpr (h _ _)

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization

/-- The literal five-level adjoint on the actual native prescribed module,
with the original signed integer trace form and conjugate ideals. -/
theorem exists_native_five_adjoint
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    ∃ P : Ideal (𝓞 H.E), P ≠ ⊤ ∧ P ≠ ⊥ ∧
      IsCoprime P (P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)) ∧
      IsCoprime P (Ideal.span {(2 : 𝓞 H.E)}) ∧
      P * P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = Ideal.span {(5 : 𝓞 H.E)} ∧
      ∃ adj : (JQuot D P ≃ₗ[𝓞 H.E] JQuot D P) → (IQuot D P ≃ₗ[𝓞 H.E] IQuot D P),
        (∀ g g', adj (g * g') = adj g' * adj g) ∧
        ∀ (a : IQuot D P ≃ₗ[𝓞 H.E] IQuot D P) (g : JQuot D P ≃ₗ[𝓞 H.E] JQuot D P),
          (∀ u v : D.La, (5 : ℤ) ∣
            D.EF (qRep (g (Submodule.Quotient.mk u))) (cHalf G P • v) -
              D.EF u (cHalf G P • qRep (a (Submodule.Quotient.mk v)))) ↔ a = adj g := by
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
  have hc : IsCoprime P (P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)) := by rw [hmap]; exact hPc
  have hp : P * P.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = Ideal.span {(5 : 𝓞 H.E)} := by
    rw [hmap]
    exact hP5
  exact ⟨P, hP1, hP0, hc, hPo, hp, exists_adjoint_halves D 5 P hp hc⟩

end RHLean.Geometry.NativeTheta.Cusp.QuotientAdjoint
