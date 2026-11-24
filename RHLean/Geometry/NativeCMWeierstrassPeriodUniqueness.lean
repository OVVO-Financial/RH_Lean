import RHLean.Geometry.NativeCMAllPlaceAppellHumbert
import RHLean.Geometry.NativeCMWeierstrassPAddition
import RHLean.Geometry.NativeCMIntegralClassPeriodMean

/-!
# Exact independence of the period comparison for the same equation

Equality of the actual Weierstrass invariants determines the original
lattice. Two coordinate comparisons of one equation therefore differ by
the precise homothety u'/u. Its covolume factor cancels against the actual
integral tangent scale, proving independence of the chosen uniformization.

The lattice-determination declarations are a native cut from Levent Alpöge
(with Claude), CocoSgt/riemann-hypothesis-lean@
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean.
The equation and tangent comparison is native glue on the same witnesses.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter PeriodPair NumberField
open scoped Topology

namespace RHLean.Geometry.NativeCM.Weierstrass

theorem lattice_le_of_g₂_eq_of_g₃_eq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by
  have hz := L.ω₁_div_two_notMem_lattice
  set z := L.ω₁ / 2
  obtain ⟨w, hw, hw1, hw2⟩ := exists_weierstrassP_eq_and_derivWeierstrassP_eq L'
    (x := ℘[L] z) (y := ℘'[L] z)
    (by rw [← h₂, ← h₃]; exact L.derivWeierstrassP_sq z hz)
  obtain ⟨c, rfl⟩ : ∃ c, w = z + c := ⟨w - z, by ring⟩
  have h1 := eventuallyEq_of_weierstrass_system
    (weierstrass_system_add_const L 0 (z := z) (by simpa using! hz))
    (h₂ ▸ weierstrass_system_add_const L' c hw) (by simp [hw1]) (by simp [hw2])
  have h2 := eqOn_compl_of_countable
    ((countable_add_mem_periodLattice L 0).union (countable_add_mem_periodLattice L' c))
    (fun t ht => analyticAt_weierstrassP_add L 0 fun h => ht (.inl h))
    (fun t ht => analyticAt_weierstrassP_add L' c fun h => ht (.inr h))
    (z := z) (by rintro (h | h); exacts [hz (by simpa using! h), hw h]) h1
  have key : ∀ l ∈ L.lattice, l + c ∈ L'.lattice := fun l hl => by
    by_contra h0
    refine not_eventually_weierstrassP_eq L hl
      (analyticAt_weierstrassP_add L' c h0).continuousAt ?_
    filter_upwards [eventually_ne_notMem_periodLattice L l, mem_nhdsWithin_of_mem_nhds
      ((continuous_add_const c).continuousAt.eventually
        (eventually_notMem_periodLattice L' h0))] with t h3 h4
    simpa using! h2 (x := t) (by rintro (h | h); exacts [h3 (by simpa using! h), h4 h])
  intro l hl
  simpa using! sub_mem (key l hl) (key 0 (zero_mem _))

theorem lattice_eq_of_g₂_eq_of_g₃_eq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice :=
  le_antisymm (lattice_le_of_g₂_eq_of_g₃_eq h₂ h₃)
    (lattice_le_of_g₂_eq_of_g₃_eq h₂.symm h₃.symm)

/-- The two actual equation comparisons force their precise lattice
homothety; no arbitrary homothety scalar is chosen. -/
theorem equation_comparison_homothety (W : _root_.WeierstrassCurve ℂ)
    (L L' : PeriodPair) (C C' : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • W = latticeCurve L) (hC' : C' • W = latticeCurve L') :
    IsHomothetic ((C'.u : ℂ) / (C.u : ℂ)) L L' := by
  have h4 : (C.u : ℂ) ^ 4 * (12 * L.g₂) = W.c₄ := by
    rw [← latticeCurve_c₄, ← hC, _root_.WeierstrassCurve.variableChange_c₄,
      ← mul_assoc, ← mul_pow]
    simp
  have h4' : (C'.u : ℂ) ^ 4 * (12 * L'.g₂) = W.c₄ := by
    rw [← latticeCurve_c₄, ← hC', _root_.WeierstrassCurve.variableChange_c₄,
      ← mul_assoc, ← mul_pow]
    simp
  have h6 : (C.u : ℂ) ^ 6 * (216 * L.g₃) = W.c₆ := by
    rw [← latticeCurve_c₆, ← hC, _root_.WeierstrassCurve.variableChange_c₆,
      ← mul_assoc, ← mul_pow]
    simp
  have h6' : (C'.u : ℂ) ^ 6 * (216 * L'.g₃) = W.c₆ := by
    rw [← latticeCurve_c₆, ← hC', _root_.WeierstrassCurve.variableChange_c₆,
      ← mul_assoc, ← mul_pow]
    simp
  let c : ℂ := (C'.u : ℂ) / (C.u : ℂ)
  have hc : c ≠ 0 := div_ne_zero C'.u.ne_zero C.u.ne_zero
  have hs := isHomothetic_scalePeriods L c hc
  have he : (scalePeriods L c hc).lattice = L'.lattice := by
    apply lattice_eq_of_g₂_eq_of_g₃_eq
    · rw [hs.g₂_eq]
      change (((C'.u : ℂ) / (C.u : ℂ)) ^ 4)⁻¹ * L.g₂ = L'.g₂
      rw [div_pow, inv_div, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 4 C'.u.ne_zero)]
      linear_combination (1 / 12 : ℂ) * h4 - (1 / 12 : ℂ) * h4'
    · rw [hs.g₃_eq]
      change (((C'.u : ℂ) / (C.u : ℂ)) ^ 6)⁻¹ * L.g₃ = L'.g₃
      rw [div_pow, inv_div, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 6 C'.u.ne_zero)]
      linear_combination (1 / 216 : ℂ) * h6 - (1 / 216 : ℂ) * h6'
  intro z
  exact he ▸ hs z

/-- The integral tangent length is independent of every auxiliary
uniformization choice, with the original scale retained on both sides. -/
theorem equation_comparison_tangent_length (W : _root_.WeierstrassCurve ℂ)
    (L L' : PeriodPair) (C C' : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • W = latticeCurve L) (hC' : C' • W = latticeCurve L') :
    Real.pi * ‖(C'.u : ℂ)‖ ^ 2 / ZLattice.covolume L'.lattice =
      Real.pi * ‖(C.u : ℂ)‖ ^ 2 / ZLattice.covolume L.lattice := by
  have h := equation_comparison_homothety W L L' C C' hC hC'
  let c : ℂ := (C'.u : ℂ) / (C.u : ℂ)
  have hc : c ≠ 0 := div_ne_zero C'.u.ne_zero C.u.ne_zero
  have hs : (C'.u : ℂ) = c * (C.u : ℂ) := by
    dsimp [c]
    exact (div_mul_cancel₀ _ C.u.ne_zero).symm
  have ha : PeriodMean.latticeArea L' = ‖c‖ ^ 2 * PeriodMean.latticeArea L := h.latticeArea_eq
  have hn : ‖(C'.u : ℂ)‖ ^ 2 = ‖c‖ ^ 2 * ‖(C.u : ℂ)‖ ^ 2 := by
    rw [hs, norm_mul, mul_pow]
  change Real.pi * ‖(C'.u : ℂ)‖ ^ 2 / PeriodMean.latticeArea L' =
    Real.pi * ‖(C.u : ℂ)‖ ^ 2 / PeriodMean.latticeArea L
  rw [ha, hn]
  field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hc), (PeriodMean.latticeArea_pos L).ne'] <;> ring

/-- The exact logarithmic period also belongs to the equation itself,
independently of its chosen analytic comparison. -/
theorem equation_comparison_logarithmic_period (W : _root_.WeierstrassCurve ℂ)
    (L L' : PeriodPair) (C C' : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • W = latticeCurve L) (hC' : C' • W = latticeCurve L') :
    PeriodArithmetic.latticeLogPeriod L' = PeriodArithmetic.latticeLogPeriod L := by
  rw [PeriodMean.latticeLogPeriod_eq_normDisc, PeriodMean.latticeLogPeriod_eq_normDisc,
    (equation_comparison_homothety W L L' C C' hC hC').latticeNormDisc_eq]

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.AllPlaceTangentPeriod

variable {F : Type} [Field F] (W : _root_.WeierstrassCurve (𝓞 F)) (hΔ : W.Δ = 1)

/-- Any exact comparison of the same complex equation yields the same
place profile used by the original all-embedding degree. -/
theorem comparison_tangent_eq_placeProfile (v : InfinitePlace F)
    (L : PeriodPair) (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • complexEquation W v = Weierstrass.latticeCurve L) :
    Real.pi * ‖(C.u : ℂ)‖ ^ 2 / ZLattice.covolume L.lattice = placeProfile W hΔ v :=
  Weierstrass.equation_comparison_tangent_length (complexEquation W v)
    (lattice W hΔ v) L (coordinateChange W hΔ v) C (comparison W hΔ v) hC

include hΔ in
/-- Its negative logarithm is the logarithmic period of that same
arbitrary comparison, not merely that of the chosen representative. -/
theorem comparison_neg_log_tangent (v : InfinitePlace F)
    (L : PeriodPair) (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • complexEquation W v = Weierstrass.latticeCurve L) :
    -Real.log (Real.pi * ‖(C.u : ℂ)‖ ^ 2 / ZLattice.covolume L.lattice) =
      PeriodArithmetic.latticeLogPeriod L := by
  rw [comparison_tangent_eq_placeProfile W hΔ v L C hC, neg_log_placeProfile]
  exact (Weierstrass.equation_comparison_logarithmic_period (complexEquation W v)
    (lattice W hΔ v) L (coordinateChange W hΔ v) C (comparison W hΔ v) hC).symm

end RHLean.Geometry.NativeCM.AllPlaceTangentPeriod
