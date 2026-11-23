import RHLean.Geometry.NativeCMWeierstrassRationalIsogeny

/-!
# Algebraicity of the actual finite torsion coordinates

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralJAndAlgebraicData.lean`.
Only `exists_algHom_apply_eq`, `isAlgebraic_of_torsion`, and
`weierstrassP_mem` are reconstructed. Algebraicity follows from the proved
finite torsion root set and extension of field embeddings; no CM curve
algebraicity, moduli theorem, or scheme endomorphism is assumed.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open NumberField Classical IntermediateField
open scoped Topology

noncomputable section

namespace RHLean.Geometry.NativeCM.Weierstrass.TorsionAlgebraicity

/-- The actual algebraic closure of the rationals inside C. -/
abbrev algebraicNumbers : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

theorem exists_algHom_apply_eq {k : Type} [Field k] [Algebra k ℂ] {x x' : ℂ}
    (hx : Transcendental k x) (hx' : Transcendental k x')
    (hm : x ∈ (algebraicClosure k⟮x⟯ ℂ)) :
    ∃ σ : (algebraicClosure k⟮x⟯ ℂ) →ₐ[k] ℂ, σ ⟨x, hm⟩ = x' := by
  let τ : k⟮x⟯ →ₐ[k] ℂ := (k⟮x'⟯.val).comp
    ((RatFunc.algEquivOfTranscendental x' hx').toAlgHom.comp
      (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom)
  have hτ : τ (IntermediateField.AdjoinSimple.gen k x) = x' := by
    change ((RatFunc.algEquivOfTranscendental x' hx')
      ((RatFunc.algEquivOfTranscendental x hx).symm
        (IntermediateField.AdjoinSimple.gen k x)) : ℂ) = x'
    rw [RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.algEquivOfTranscendental_X]
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := k) (L := k⟮x⟯)
    (M := ℂ) (E := algebraicClosure k⟮x⟯ ℂ) τ
  refine ⟨σ, ?_⟩
  rw [← hτ, ← hσ]
  rfl

theorem isAlgebraic_of_torsion {k : Type} [Field k] [CharZero k] [Algebra k ℂ]
    (W : WeierstrassCurve.Affine k) (V : WeierstrassCurve.Affine ℂ) (hV : W.baseChange ℂ = V)
    (m : ℕ) (S : Set ℂ) (hS : S.Finite)
    (hmem : ∀ x y (h : V.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h) = 0 → x ∈ S)
    {x y : ℂ} (h : V.Nonsingular x y) (h0 : m • (WeierstrassCurve.Affine.Point.some x y h) = 0)
    (hy : IsAlgebraic k⟮x⟯ y) : IsAlgebraic k x := by
  subst hV
  by_contra hx
  let F := algebraicClosure k⟮x⟯ ℂ
  have hxF : x ∈ F := F.algebraMap_mem (IntermediateField.AdjoinSimple.gen k x)
  have hyF : y ∈ F := mem_algebraicClosure_iff.mpr hy
  let ι : F →ₐ[k] ℂ := F.val.restrictScalars k
  have hι : Function.Injective ι := ι.toRingHom.injective
  have hF : (W.baseChange F).Nonsingular ⟨x, hxF⟩ ⟨y, hyF⟩ :=
    (W.baseChange_nonsingular hι _ _).mp h
  have h1 : m • (WeierstrassCurve.Affine.Point.some _ _ hF) = 0 := by
    apply WeierstrassCurve.Affine.Point.map_injective (W' := W) ι
    rw [map_nsmul, map_zero, WeierstrassCurve.Affine.Point.map_some]
    exact h0
  have h2 : ∀ n : ℕ, x + n ∈ S := fun n => by
    have hn : Transcendental k (x + n) := fun ha => hx (by
      have := ha.sub (isAlgebraic_natCast (R := k) (A := ℂ) n)
      simpa using this)
    obtain ⟨σ, hσ⟩ := exists_algHom_apply_eq hx hn hxF
    have h3 := congrArg (WeierstrassCurve.Affine.Point.map (W' := W) σ) h1
    rw [map_nsmul, map_zero, WeierstrassCurve.Affine.Point.map_some] at h3
    exact hσ ▸ hmem _ _ _ h3
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => x + n) ?_ h2 hS
  intro a b hab
  simpa using hab

theorem weierstrassP_mem (L : PeriodPair) (h2 : L.g₂ ∈ algebraicNumbers) (h3 : L.g₃ ∈ algebraicNumbers) {m : ℕ}
    (hm : 0 < m) {t : ℂ} (ht : t ∉ L.lattice) (hmt : (m : ℂ) * t ∈ L.lattice) :
    L.weierstrassP t ∈ algebraicNumbers ∧ L.derivWeierstrassP t ∈ algebraicNumbers := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmul : ∀ z : ℂ, m • latticePoint L z = latticePoint L ((m : ℂ) * z) := fun z => by
    rw [← latticePointHom_apply, ← latticePointHom_apply, ← map_nsmul, nsmul_eq_mul]
  obtain ⟨A, D, -, -, hD, -, -, -, -, hroot, -⟩ := exists_weierstrassP_mul_eq_div (L := L) (L' := L)
    hm0 (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl m) ⊤ trivial trivial trivial
    (fun _ _ _ => trivial)
  have hsq := L.derivWeierstrassP_sq t ht
  have hx : IsAlgebraic algebraicNumbers (L.weierstrassP t) := by
    refine isAlgebraic_of_torsion
      (⟨0, 0, 0, -⟨L.g₂, h2⟩ / 4, -⟨L.g₃, h3⟩ / 4⟩ : WeierstrassCurve algebraicNumbers) (latticeCurve L).toAffine ?_ m
      (D.rootSet ℂ) (D.rootSet_finite ℂ) ?_ (latticeCurve_nonsingular L ht) ?_ ?_
    · ext <;> simp [latticeCurve, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange] <;> rfl
    · intro x y h h0
      obtain ⟨z, hz⟩ := latticePoint_surjective L (.some x y h)
      have hz' : z ∉ L.lattice := fun hc => by
        rw [latticePoint_of_mem L hc] at hz
        exact WeierstrassCurve.Affine.Point.some_ne_zero _ hz.symm
      rw [← hz, hmul, latticePoint_eq_zero_iff] at h0
      rw [latticePoint_of_notMem L hz'] at hz
      obtain ⟨rfl, -⟩ := WeierstrassCurve.Affine.Point.some.inj hz
      rw [Polynomial.mem_rootSet]
      exact ⟨hD.ne_zero, (hroot z hz').mpr h0⟩
    · rw [← latticePoint_of_notMem L ht, hmul, latticePoint_eq_zero_iff]
      exact hmt
    · set F := (↥algebraicNumbers)⟮L.weierstrassP t⟯
      have e1 : L.weierstrassP t ∈ F := IntermediateField.mem_adjoin_simple_self _ _
      have e2 : L.g₂ ∈ F := F.algebraMap_mem ⟨L.g₂, h2⟩
      have e3 : L.g₃ ∈ F := F.algebraMap_mem ⟨L.g₃, h3⟩
      have e4 : (L.derivWeierstrassP t / 2) ^ 2 ∈ F := by
        rw [div_pow, hsq]
        refine div_mem (sub_mem (sub_mem (mul_mem (ofNat_mem F 4) (pow_mem e1 3)) (mul_mem e2 e1)) e3)
          (pow_mem (ofNat_mem F 2) 2)
      exact IsAlgebraic.of_pow two_pos (isAlgebraic_algebraMap (⟨_, e4⟩ : F))
  have hx' : L.weierstrassP t ∈ algebraicNumbers :=
    haveI : Algebra.IsAlgebraic ℚ algebraicNumbers := algebraicClosure.isAlgebraic ℚ ℂ
    mem_algebraicClosure_iff.mpr (hx.restrictScalars ℚ)
  refine ⟨hx', mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)⟩
  rw [hsq, ← mem_algebraicClosure_iff]
  exact sub_mem (sub_mem (mul_mem (ofNat_mem _ 4) (pow_mem hx' 3)) (mul_mem h2 hx')) h3

end RHLean.Geometry.NativeCM.Weierstrass.TorsionAlgebraicity

end
