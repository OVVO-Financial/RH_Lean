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

open NumberField Classical IntermediateField Polynomial PeriodPair
open scoped Topology BigOperators

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


/-- The actual finite-index period inclusion kills its kernel by the
positive index. This is the same quotient and representative theorem
used in the existing rational formula. No kernel bound is assumed. -/
theorem exists_latticeKernel_annihilator {L L' : PeriodPair} {α : ℂ}
    (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : ℂ, α * z ∈ L'.lattice → (n : ℂ) * z ∈ L.lattice := by
  obtain ⟨Q, hQ, hfin, _, hcard, _, _, _, _, _⟩ := exists_representatives hα0 hα
  let _ : AddCommGroup Q := hQ
  let _ : Finite Q := hfin
  let _ : Fintype Q := Fintype.ofFinite Q
  refine ⟨Nat.card Q, by rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos, ?_⟩
  intro z hz
  have hh := (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).nsmul_relIndex_mem
    (K := L'.lattice.toAddSubgroup) hz
  rw [← hcard] at hh
  obtain ⟨l, hl, he⟩ := hh
  change α * l = Nat.card Q • (α * z) at he
  rw [nsmul_eq_mul] at he
  have hlz : l = (Nat.card Q : ℂ) * z := mul_left_cancel₀ hα0 (by
    calc
      α * l = (Nat.card Q : ℂ) * (α * z) := he
      _ = α * ((Nat.card Q : ℂ) * z) := by ring)
  exact hlz ▸ hl

/-- At least one nonzero two-torsion point has nonzero x-coordinate.
Use the actual nonsingular cubic and the existing uniformization;
this does not choose a new period lattice. -/
theorem exists_nonzero_twoTorsion_wp (L : PeriodPair) :
    ∃ z ∉ L.lattice, (2 : ℂ) * z ∈ L.lattice ∧ L.weierstrassP z ≠ 0 := by
  have hΔ := latticeCurve_Δ_ne_zero L
  rw [latticeCurve_Δ] at hΔ
  have hx : ∃ x : ℂ, x ≠ 0 ∧ (0 : ℂ) = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by
    by_cases h3 : L.g₃ = 0
    · have h2 : L.g₂ ≠ 0 := by
        intro h
        simp [h, h3] at hΔ
      let p : ℂ[X] := X ^ 2 - C (L.g₂ / 4)
      have hp : p.degree ≠ 0 := by
        intro hd
        have hlt : p.degree < ((2 : ℕ) : WithBot ℕ) := by rw [hd]; norm_num
        have he := coeff_eq_zero_of_degree_lt hlt
        norm_num [p, coeff_sub, coeff_X_pow] at he
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p hp
      have hr : x ^ 2 - L.g₂ / 4 = 0 := by
        simpa [p, Polynomial.IsRoot] using hx
      refine ⟨x, ?_, ?_⟩
      · intro h
        rw [h] at hr
        exact h2 (by linear_combination -4 * hr)
      · rw [h3]
        linear_combination -4 * x * hr
    · let p : ℂ[X] := X ^ 3 - C (L.g₂ / 4) * X - C (L.g₃ / 4)
      have hp : p.degree ≠ 0 := by
        intro hd
        have hlt : p.degree < ((3 : ℕ) : WithBot ℕ) := by rw [hd]; norm_num
        have he := coeff_eq_zero_of_degree_lt hlt
        norm_num [p, coeff_sub, coeff_X_pow, coeff_C_mul] at he
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p hp
      have hr : x ^ 3 - (L.g₂ / 4) * x - L.g₃ / 4 = 0 := by
        simpa [p, Polynomial.IsRoot] using hx
      refine ⟨x, ?_, ?_⟩
      · intro h
        rw [h] at hr
        exact h3 (by linear_combination -4 * hr)
      · linear_combination -4 * hr
  obtain ⟨x, hx0, hx⟩ := hx
  obtain ⟨z, hz, hzx, hzy⟩ :=
    exists_weierstrassP_eq_and_derivWeierstrassP_eq L (x := x) (y := 0) (by simpa using hx)
  refine ⟨z, hz, ?_, hzx.symm ▸ hx0⟩
  rw [two_mul]
  exact (derivWeierstrassP_eq_zero_iff L hz).mp hzy

/-- The multiplier of the actual finite-index map between two algebraic
period equations is algebraic. Apply the existing kernel sum identity to
a preimage of the target nonzero two-torsion x-coordinate: all terms of
the source sum are torsion coordinates, with a common positive killing
integer. The target coordinate is nonzero and algebraic, so division
and the existing algebraicity-of-powers theorem give the original α.
This uses the actual `weierstrassP_mul_eq_sum` and torsion proof from
Alpoge's pinned source; there is no new isogeny existence premise. -/
theorem latticeMultiplier_mem {L L' : PeriodPair} {α : ℂ}
    (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (h2 : L.g₂ ∈ algebraicNumbers) (h3 : L.g₃ ∈ algebraicNumbers)
    (h2' : L'.g₂ ∈ algebraicNumbers) (h3' : L'.g₃ ∈ algebraicNumbers) :
    α ∈ algebraicNumbers := by
  classical
  obtain ⟨n, hn, hkill⟩ := exists_latticeKernel_annihilator hα0 hα
  obtain ⟨w, hw, hw2, hw0⟩ := exists_nonzero_twoTorsion_wp L'
  let z := α⁻¹ * w
  have hz : α * z = w := mul_inv_cancel_left₀ hα0 w
  have hz2 : α * (2 * z) ∈ L'.lattice := by
    rw [show α * (2 * z) = 2 * w by rw [← hz]; ring]
    exact hw2
  have hzt : ((n * 2 : ℕ) : ℂ) * z ∈ L.lattice := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hkill (2 * z) hz2
  obtain ⟨Q, hQ, hfin, r, _, hr1, hr2, _, _, hr5⟩ := exists_representatives hα0 hα
  let _ : AddCommGroup Q := hQ
  let _ : Finite Q := hfin
  let _ : Fintype Q := Fintype.ofFinite Q
  have hrt (t : Q) : ((n * 2 : ℕ) : ℂ) * r t ∈ L.lattice := by
    have h := hkill (r t) (hr1 t)
    rw [show ((n * 2 : ℕ) : ℂ) * r t =
        (n : ℂ) * r t + (n : ℂ) * r t by push_cast; ring]
    exact add_mem h h
  have hcoord (v : ℂ) (hv : ((n * 2 : ℕ) : ℂ) * v ∈ L.lattice) :
      L.weierstrassP v ∈ algebraicNumbers := by
    by_cases hvL : v ∈ L.lattice
    · have he := L.weierstrassP_coe ⟨v, hvL⟩
      change L.weierstrassP v = 0 at he
      rw [he]
      exact zero_mem _
    · exact (weierstrassP_mem L h2 h3 (Nat.mul_pos hn (by decide : 0 < 2)) hvL hv).1
  have hs : α ^ 2 * L'.weierstrassP w ∈ algebraicNumbers := by
    rw [← hz, weierstrassP_mul_eq_sum hα0 hα r hr1 (fun s t h => (hr2 s t).mp h) hr5 z]
    exact sum_mem fun t _ => sub_mem
      (hcoord (z - r t) (by rw [mul_sub]; exact sub_mem hzt (hrt t)))
      (hcoord (r t) (hrt t))
  have htarget : L'.weierstrassP w ∈ algebraicNumbers :=
    (weierstrassP_mem L' h2' h3' (by decide : 0 < 2) hw hw2).1
  have hα2 : α ^ 2 ∈ algebraicNumbers := by
    have h := div_mem hs htarget
    rwa [mul_div_cancel_right₀ _ hw0] at h
  exact mem_algebraicClosure_iff.mpr
    (IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.mp hα2))

/-- Descend the same actual rational isogeny formula between two algebraic
equations to a finite extension of their common field of definition.
Only the actual multiplier and finitely many kernel coordinates are
adjoined; algebraicity of the multiplier has just been proved rather
than imposed on the class model. -/
theorem exists_finite_field_rational_latticeIsogeny
    (M : IntermediateField ℚ ℂ) [NumberField M] {L L' : PeriodPair} {α : ℂ}
    (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (h₂ : L.g₂ ∈ M) (h₃ : L.g₃ ∈ M) (h₂' : L'.g₂ ∈ M) (h₃' : L'.g₃ ∈ M) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (A D : ℂ[X]),
      M ≤ F ∧ α ∈ F ∧
      (∀ i, A.coeff i ∈ F) ∧ (∀ i, D.coeff i ∈ F) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = Nat.card (latticeIsogeny α hα).ker ∧ D.natDegree + 1 = A.natDegree ∧
      (∀ (x y : ℂ) (h : (latticeCurve L).toAffine.Nonsingular x y),
        (D.eval x = 0 → latticeIsogeny α hα (.some x y h) = 0) ∧
        (D.eval x ≠ 0 → ∃ h', latticeIsogeny α hα (.some x y h) =
          .some (A.eval x / D.eval x)
            (α⁻¹ * ((derivative A * D - A * derivative D).eval x / D.eval x ^ 2) * y) h')) := by
  classical
  have hMalg : ∀ z : ℂ, z ∈ M → z ∈ algebraicNumbers := fun z hz =>
    mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨z, hz⟩ : M)).algHom M.val)
  have ha := latticeMultiplier_mem hα0 hα (hMalg _ h₂) (hMalg _ h₃)
    (hMalg _ h₂') (hMalg _ h₃')
  obtain ⟨n, hn, hkill⟩ := exists_latticeKernel_annihilator hα0 hα
  obtain ⟨Q, hQ, hfin, r, _, hr1, _, _, hr4, hr5⟩ := exists_representatives hα0 hα
  let _ : AddCommGroup Q := hQ
  let _ : Finite Q := hfin
  let ι := {t : Q // t ≠ 0}
  let S : Set ℂ := insert α (Set.range (fun t : ι => L.weierstrassP (r t)))
  have hS : S.Finite := (Set.finite_range _).insert _
  let _ : Finite S := hS.to_subtype
  have hSint : ∀ z ∈ S, IsIntegral ℚ z := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | ⟨t, rfl⟩
    · exact (mem_algebraicClosure_iff.mp ha).isIntegral
    · have htz : r t ∉ L.lattice := (hr4 t).not.mpr t.property
      exact (mem_algebraicClosure_iff.mp
        (weierstrassP_mem L (hMalg _ h₂) (hMalg _ h₃)
          hn htz (hkill _ (hr1 t))).1).isIntegral
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hSint
  let F : IntermediateField ℚ ℂ := M ⊔ IntermediateField.adjoin ℚ S
  let _ : NumberField F := ⟨⟩
  have hMF : M ≤ F := le_sup_left
  have hSF : S ⊆ F := fun _ hz => (le_sup_right : IntermediateField.adjoin ℚ S ≤ F)
    (IntermediateField.subset_adjoin ℚ S hz)
  have hαF : α ∈ F := hSF (Set.mem_insert _ _)
  have hker : ∀ z ∉ L.lattice, α * z ∈ L'.lattice → L.weierstrassP z ∈ F := by
    intro z hz hαz
    obtain ⟨t, ht⟩ := hr5 z hαz
    have ht0 : t ≠ 0 := by
      intro h0
      exact hz (by simpa using! add_mem ht ((hr4 t).mpr h0))
    have hrt : r t ∉ L.lattice := (hr4 t).not.mpr ht0
    rw [(weierstrassP_eq_iff L hz hrt).mpr (.inl ht)]
    exact hSF (Set.mem_insert_of_mem _ ⟨⟨t, ht0⟩, rfl⟩)
  obtain ⟨A, D, hA, hD, hm, hlc, hc, hdA, hdD, he⟩ :=
    exists_latticeIsogeny_eq_div hα0 hα F.toSubfield (hMF h₂) (hMF h₃) hαF hker
  exact ⟨F, inferInstance, A, D, hMF, hαF, hA, hD, hm, hlc, hc, hdA, hdD, he⟩

end RHLean.Geometry.NativeCM.Weierstrass.TorsionAlgebraicity

end
