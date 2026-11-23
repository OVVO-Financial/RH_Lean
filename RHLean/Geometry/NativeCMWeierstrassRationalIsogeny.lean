import RHLean.Geometry.NativeCMWeierstrassRationalNumerator

/-!
# The exact rational formula for the actual CM point isogeny

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean`.
Only the declarations through `exists_latticeIsogeny_eq_div` are reconstructed.
The degree is the actual kernel cardinality; the x leading coefficient is
alpha^-2 and the derivative factor in the y coordinate is alpha^-1.
This proves a rational point formula, not an integral scheme endomorphism.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology

noncomputable section

namespace RHLean.Geometry.NativeCM.Weierstrass

variable {L L' : PeriodPair} {α : ℂ}

def latticeIsogeny (α : ℂ) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    (latticeCurve L).toAffine.Point →+ (latticeCurve L').toAffine.Point :=
  (QuotientAddGroup.lift L.lattice.toAddSubgroup
    ((latticePointHom L').comp (AddMonoidHom.mulLeft α))
    fun l hl ↦ latticePoint_of_mem L' (hα l hl)).comp (latticePointEquiv L).symm.toAddMonoidHom

@[simp] lemma latticeIsogeny_latticePoint (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) (z : ℂ) :
    latticeIsogeny α hα (latticePoint L z) = latticePoint L' (α * z) := by
  rw [← latticePointEquiv_mk]
  simp [latticeIsogeny, -latticePointEquiv_mk]
  rfl

theorem card_ker_latticeIsogeny (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    Nat.card (latticeIsogeny α hα).ker =
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup := by
  have h1 : (latticeIsogeny α hα).ker =
      (L'.lattice.toAddSubgroup.comap (AddMonoidHom.mulLeft α)).map (latticePointHom L) := by
    ext P
    obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    rw [AddMonoidHom.mem_ker, latticeIsogeny_latticePoint, latticePoint_eq_zero_iff]
    refine ⟨fun h ↦ ⟨z, h, rfl⟩, ?_⟩
    rintro ⟨w, hw, e⟩
    have hw' : α * w ∈ L'.lattice := hw
    simpa [mul_sub] using sub_mem hw' (hα _ ((latticePoint_eq_iff L).mp e))
  have h2 : (L'.lattice.toAddSubgroup.comap (AddMonoidHom.mulLeft α)).map
      (AddMonoidHom.mulLeft α) = L'.lattice.toAddSubgroup :=
    AddSubgroup.map_comap_eq_self_of_surjective (mul_left_surjective₀ hα0) _
  rw [h1, ← AddSubgroup.relIndex_ker, ker_latticePointHom,
    ← AddSubgroup.relIndex_map_map_of_injective (f := AddMonoidHom.mulLeft α) _ _
      (mul_right_injective₀ hα0), h2]

lemma derivWeierstrassP_mul_eq (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) {A D : ℂ[X]}
    (h : ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z))
    {z : ℂ} (hz : α * z ∉ L'.lattice) (hD : D.eval (℘[L] z) ≠ 0) :
    α * ℘'[L'] (α * z) =
      (derivative A * D - A * derivative D).eval (℘[L] z) / D.eval (℘[L] z) ^ 2 * ℘'[L] z := by
  have d := hasDerivAt_weierstrassP L (z := z) fun h ↦ hz (hα z h)
  have d1 := (hasDerivAt_weierstrassP L' hz).comp z ((hasDerivAt_id z).const_mul α)
  have d2 := ((A.hasDerivAt _).comp z d).div ((D.hasDerivAt _).comp z d) hD
  have := d1.unique (d2.congr_of_eventuallyEq (by
    filter_upwards [(continuous_const_mul α).continuousAt.eventually
      (eventually_notMem_periodLattice L' hz)] with w hw using h w hw))
  simp only [Function.comp_apply, mul_one] at this
  rw [mul_comm, this]
  simp only [eval_sub, eval_mul]
  ring

theorem exists_latticeIsogeny_eq_div (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (k : Subfield ℂ) (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L'.lattice → ℘[L] t ∈ k) :
    ∃ A D : ℂ[X], (∀ i, A.coeff i ∈ k) ∧ (∀ i, D.coeff i ∈ k) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = Nat.card (latticeIsogeny α hα).ker ∧ D.natDegree + 1 = A.natDegree ∧
      ∀ (x y : ℂ) (h : (latticeCurve L).toAffine.Nonsingular x y),
        (D.eval x = 0 → latticeIsogeny α hα (.some x y h) = 0) ∧
        (D.eval x ≠ 0 → ∃ h', latticeIsogeny α hα (.some x y h) = .some (A.eval x / D.eval x)
          (α⁻¹ * ((derivative A * D - A * derivative D).eval x / D.eval x ^ 2) * y) h') := by
  obtain ⟨A, D, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk
  refine ⟨A, D, c1, c2, c3, c4, c5, by rw [c6, card_ker_latticeIsogeny hα0], c7, fun x y h ↦ ?_⟩
  obtain ⟨z, hz⟩ := latticePoint_surjective L (.some x y h)
  have hzL : z ∉ L.lattice := fun h' ↦
    Affine.Point.some_ne_zero _ (hz.symm.trans (latticePoint_of_mem L h'))
  rw [← hz, latticeIsogeny_latticePoint]
  rw [latticePoint_of_notMem L hzL, Affine.Point.some.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  refine ⟨fun h0 ↦ latticePoint_of_mem L' ((c8 z hzL).mp h0), fun h0 ↦ ?_⟩
  have hz' := (c8 z hzL).not.mp h0
  have e : α⁻¹ * ((derivative A * D - A * derivative D).eval (℘[L] z) / D.eval (℘[L] z) ^ 2) *
      (℘'[L] z / 2) = ℘'[L'] (α * z) / 2 := by
    rw [mul_assoc, ← mul_div_assoc, ← derivWeierstrassP_mul_eq hα c9 hz' h0]
    field_simp
  rw [e, ← c9 z hz']
  exact ⟨_, latticePoint_of_notMem L' hz'⟩

end RHLean.Geometry.NativeCM.Weierstrass

end
