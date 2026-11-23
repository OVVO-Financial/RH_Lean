import RHLean.Geometry.NativeCMWeierstrassSeed
import RHLean.Geometry.NativeCMWeierstrassLatticeCurve

/-!
# Exact invariant comparison with the same native CM period lattice

The integral equation constructed in `NativeCMWeierstrassSeed` is now compared
with the actual analytic Weierstrass equation formed from the lattice sums
`g₂` and `g₃` of the same seed. Equality of the actual `j` invariants produces
a concrete complex change of Weierstrass coordinates. Its unit `u` retains
all scale information: the comparison proves the exact fourth, sixth, and
twelfth-power relations for `c₄`, `c₆`, and the discriminant.

This equation comparison does not identify the scheme-theoretic integral
tangent with the analytic tangent. That remaining identification must use
an algebraic uniformization proof and cannot be replaced by choosing `u=1`.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/`
`ExistsVariableChangeEqLatticeCurve.lean`, particularly `latticeCurve_j`, and
Mathlib's `WeierstrassCurve.exists_variableChange_of_j_eq`.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField

namespace RHLean.Geometry.NativeCM.Weierstrass

theorem latticeCurve_c₆ (L : PeriodPair) : (latticeCurve L).c₆ = 216 * L.g₃ := by
  simp only [latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ)

/-- Mathlib's analytic period-pair data on the actual native lattice. -/
def periodPair : PeriodPair := Weierstrass.periodPairOfTau (upperPeriod H τ)

theorem periodPair_lattice : (periodPair H τ).lattice = lattice H τ := by
  rw [lattice_eq_span_upperPeriod]
  ext z
  simp only [periodPair, Weierstrass.mem_lattice_periodPairOfTau, one_mul,
    Submodule.mem_span_pair, zsmul_eq_mul, mul_one]

theorem periodCurve_j :
    (Weierstrass.latticeCurve (periodPair H τ)).j =
      Weierstrass.modularJ (upperPeriod H τ) :=
  Weierstrass.latticeCurve_j one_ne_zero
    (Weierstrass.mem_lattice_periodPairOfTau (upperPeriod H τ))

theorem periodCurve_discriminant :
    (Weierstrass.latticeCurve (periodPair H τ)).Δ =
      (2 * (Real.pi : ℂ)) ^ 12 * ModularForm.discriminant (upperPeriod H τ) := by
  simpa using Weierstrass.latticeCurve_Δ_eq_discriminant one_ne_zero
    (Weierstrass.mem_lattice_periodPairOfTau (upperPeriod H τ))

end RHLean.Geometry.NativeCM.EllipticSeed

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed

/-- The arithmetic equation and the actual analytic lattice equation are
related by a genuine change of Weierstrass coordinates. The scale is retained
exactly in all three classical invariants and in the analytic discriminant. -/
theorem exists_integral_equation_with_exact_period_invariants
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
      (W : WeierstrassCurve (𝓞 M)) (w : 𝓞 M)
      (C : WeierstrassCurve.VariableChange ℂ) (hΔ : W.Δ = 1),
      let φ : 𝓞 M →+* ℂ :=
        (M.val : M →+* ℂ).comp (algebraMap (𝓞 M) M)
      (∀ a : E, τ a ∈ M) ∧
      ((w : M) : ℂ) = omega H τ ∧
      (periodPair H τ).lattice = lattice H τ ∧
      C • W.map φ = latticeCurve (periodPair H τ) ∧
      (C.u : ℂ) ^ 4 * (12 * (periodPair H τ).g₂) = φ W.c₄ ∧
      (C.u : ℂ) ^ 6 * (216 * (periodPair H τ).g₃) = φ W.c₆ ∧
      (C.u : ℂ) ^ 12 * (latticeCurve (periodPair H τ)).Δ = 1 ∧
      (C.u : ℂ) ^ 12 *
        ((2 * (Real.pi : ℂ)) ^ 12 * ModularForm.discriminant (upperPeriod H τ)) = 1 ∧
      (let _ : W.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
       φ W.j = modularJ (upperPeriod H τ)) := by
  obtain ⟨M, hM, W, w, hΔ, hhost, hw, -, -, hj⟩ :=
    exists_integral_equation_for_seed H τ
  let _ : NumberField M := hM
  let _ : W.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
  let φ : 𝓞 M →+* ℂ :=
    (M.val : M →+* ℂ).comp (algebraMap (𝓞 M) M)
  have hWCΔ : (W.map φ).Δ = 1 := by
    rw [WeierstrassCurve.map_Δ, hΔ, map_one]
  have hWCj : (W.map φ).j = modularJ (upperPeriod H τ) := by
    rw [WeierstrassCurve.map_j]
    exact hj
  obtain ⟨C, hC⟩ := (W.map φ).exists_variableChange_of_j_eq
    (latticeCurve (periodPair H τ)) (by rw [hWCj, periodCurve_j])
  have h4 : (C.u : ℂ) ^ 4 * (latticeCurve (periodPair H τ)).c₄ = φ W.c₄ := by
    rw [← hC, WeierstrassCurve.variableChange_c₄, ← mul_assoc, ← mul_pow]
    simp [WeierstrassCurve.map_c₄]
  have h6 : (C.u : ℂ) ^ 6 * (latticeCurve (periodPair H τ)).c₆ = φ W.c₆ := by
    rw [← hC, WeierstrassCurve.variableChange_c₆, ← mul_assoc, ← mul_pow]
    simp [WeierstrassCurve.map_c₆]
  have h12 : (C.u : ℂ) ^ 12 * (latticeCurve (periodPair H τ)).Δ = 1 := by
    rw [← hC, WeierstrassCurve.variableChange_Δ, ← mul_assoc, ← mul_pow]
    simp [hWCΔ]
  refine ⟨M, hM, W, w, C, hΔ, hhost, hw, periodPair_lattice H τ, hC,
    ?_, ?_, h12, ?_, hj⟩
  · simpa only [latticeCurve_c₄] using h4
  · simpa only [latticeCurve_c₆] using h6
  · simpa only [periodCurve_discriminant] using h12

end RHLean.Geometry.NativeCM.Weierstrass

end
