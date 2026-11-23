import RHLean.Geometry.NativeThetaCuspFlagDomain

/-!
# Finite index of the literal principal congruence subgroup

Finite generation gives a finite reduction of the actual integral lattice.
Its finitely many generator images supply coset representatives inside the
full unitary lattice stabilizer, with the original congruence condition.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open NumberField Matrix
open scoped nonZeroDivisors
open RHLean.Geometry.NativeTheta.Cusp

namespace RHLean.Geometry.NativeTheta.Cusp.FlagCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}

omit [NumberField E] [IsCMField E] in
theorem mul_mulVec (γ δ : GL (Fin r) E) (v : Fin r → E) :
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

omit [NumberField E] [IsCMField E] in
theorem mulVec_inv_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

omit [NumberField E] [IsCMField E] in
theorem inv_mulVec_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)
      = v := by
  rw [← mul_mulVec, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem isUStab_one : FlagDomain.IsUStab Gm Λ 1 := by
  unfold FlagDomain.IsUStab
  exact ⟨fun x y => by simp, fun x => by simp⟩

theorem isUStab_mul {γ δ : GL (Fin r) E} (hγ : FlagDomain.IsUStab Gm Λ γ) (hδ : FlagDomain.IsUStab Gm Λ δ) :
    FlagDomain.IsUStab Gm Λ (γ * δ) := by
  unfold FlagDomain.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [mul_mulVec, mul_mulVec, hγ.1, hδ.1]
  · rw [mul_mulVec]
    exact (hδ.2 x).trans (hγ.2 _)

theorem isUStab_inv {γ : GL (Fin r) E} (hγ : FlagDomain.IsUStab Gm Λ γ) :
    FlagDomain.IsUStab Gm Λ γ⁻¹ := by
  unfold FlagDomain.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h := hγ.1 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
    rw [mulVec_inv_mulVec, mulVec_inv_mulVec] at h
    exact h.symm
  · have h := hγ.2 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
    rw [mulVec_inv_mulVec] at h
    exact h.symm

def congruenceSubgroup (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (M : ℕ) : Subgroup (GL (Fin r) E) where
  carrier := {γ | FlagDomain.IsUStab Gm Λ γ ∧
    (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)}
  one_mem' := ⟨isUStab_one, fun v _ => ⟨0, Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro γ δ ⟨hγ, hγ'⟩ ⟨hδ, hδ'⟩
    refine ⟨isUStab_mul hγ hδ, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hδ' v hv
    obtain ⟨w', hw', e'⟩ := hγ' _ ((hδ.2 v).1 hv)
    refine ⟨w + w', Λ.add_mem hw hw', ?_⟩
    rw [mul_mulVec, e', e, smul_add, add_assoc]
  inv_mem' := by
    rintro γ ⟨hγ, hγ'⟩
    refine ⟨isUStab_inv hγ, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hγ' _ (((isUStab_inv hγ).2 v).1 hv)
    rw [mulVec_inv_mulVec] at e
    refine ⟨-w, Λ.neg_mem hw, ?_⟩
    rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact e.symm

omit [IsCMField E] in
theorem finite_quotient (hΛ : Λ.FG) {M : ℕ} (hM : 0 < M) :
    Finite (Λ ⧸ (nsmulAddMonoidHom M : Λ →+ Λ).range) := by
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ hM.ne'
  infer_instance

private theorem inv_mul_mem_congruenceSubgroup_of_agree_mod {T : Finset (Fin r → E)}
    (hT : Submodule.span (𝓞 E) (T : Set (Fin r → E)) = Λ) {M : ℕ} {s γ : GL (Fin r) E}
    (hs : FlagDomain.IsUStab Gm Λ s) (hγ : FlagDomain.IsUStab Gm Λ γ)
    (h : ∀ t ∈ T, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ t =
      (s : Matrix (Fin r) (Fin r) E) *ᵥ t + M • w) :
    s⁻¹ * γ ∈ congruenceSubgroup Gm Λ M := by
  have hsi := isUStab_inv hs
  refine ⟨isUStab_mul hsi hγ, fun v hv => ?_⟩
  rw [← hT] at hv
  induction hv using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨w, hw, e⟩ := h t ht
    refine ⟨((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w, (hsi.2 w).1 hw, ?_⟩
    have hst := mulVec_inv_mulVec s⁻¹ t
    rw [inv_inv] at hst
    rw [mul_mulVec, e, Matrix.mulVec_add, hst, Matrix.mulVec_smul]
  | zero => exact ⟨0, Λ.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, ex⟩ := hx
    obtain ⟨w', hw', ey⟩ := hy
    refine ⟨w + w', Λ.add_mem hw hw', ?_⟩
    rw [Matrix.mulVec_add, ex, ey, smul_add]
    abel
  | smul a x _ hx =>
    obtain ⟨w, hw, ex⟩ := hx
    refine ⟨a • w, Λ.smul_mem a hw, ?_⟩
    rw [Matrix.mulVec_smul, ex, smul_add, smul_comm a M w]

theorem exists_finset_cosets (hΛ : Λ.FG) {M : ℕ} (hM : 0 < M) :
    ∃ S : Finset (GL (Fin r) E), ∀ γ, FlagDomain.IsUStab Gm Λ γ →
      ∃ s ∈ S, s⁻¹ * γ ∈ congruenceSubgroup Gm Λ M := by
  classical
  obtain ⟨T, hT⟩ := id hΛ
  set I : Ideal (𝓞 E) := Ideal.span {(M : 𝓞 E)} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  have : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ
  have : Subsingleton (Λ ⧸ (⊤ : Submodule (𝓞 E) Λ)) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  have : Finite (Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top)
  let St := {γ : GL (Fin r) E // FlagDomain.IsUStab Gm Λ γ}
  let Φ : St → (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) := fun γ t =>
    Submodule.Quotient.mk ⟨(γ.1 : Matrix (Fin r) (Fin r) E) *ᵥ t.1,
      (γ.2.2 t.1).1 (hT ▸ Submodule.subset_span t.2)⟩
  have : Fintype (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) := Fintype.ofFinite _
  let rep : (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) → GL (Fin r) E := fun x =>
    if h : ∃ γ : St, Φ γ = x then h.choose.1 else 1
  refine ⟨Finset.univ.image rep, fun γ hγ =>
    ⟨rep (Φ ⟨γ, hγ⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
  have hex : ∃ δ : St, Φ δ = Φ ⟨γ, hγ⟩ := ⟨_, rfl⟩
  have hrep : rep (Φ ⟨γ, hγ⟩) = hex.choose.1 := dite_eq_left hex
  rw [hrep]
  refine inv_mul_mem_congruenceSubgroup_of_agree_mod hT hex.choose.2 hγ (fun t ht => ?_)
  have hq := congrFun hex.choose_spec ⟨t, ht⟩
  have hmem := (Submodule.Quotient.eq _).1 hq.symm
  have hdiv : ∀ x : Λ, x ∈ I • (⊤ : Submodule (𝓞 E) Λ) → ∃ b : Λ, (M : 𝓞 E) • b = x := by
    intro x hx
    rw [hIdef, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hdiv _ hmem
  refine ⟨b.1, b.2, ?_⟩
  have hb' := congrArg Subtype.val hb
  simp only [Submodule.coe_smul, Submodule.coe_sub] at hb'
  rw [Nat.cast_smul_eq_nsmul] at hb'
  rw [hb']
  abel


theorem congruence_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → 0 < M → ∃ Γ : Subgroup (GL (Fin r) E), (∀ γ, γ ∈ Γ ↔ FlagDomain.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∃ S : Finset (GL (Fin r) E), ∀ γ, FlagDomain.IsUStab Gm Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ := by
  intro E _ _ _ r M Gm Λ hΛ hM
  exact ⟨congruenceSubgroup Gm Λ M, fun γ => Iff.rfl,
    exists_finset_cosets (Gm := Gm) hΛ hM⟩

end RHLean.Geometry.NativeTheta.Cusp.FlagCongruence
