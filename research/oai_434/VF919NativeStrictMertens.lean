import «research.oai_434.VF919NativeStrictSevenEighths»

/-!
# Strict native Mertens and complete signed-pair consequences

The transfer uses the exact Dirichlet-to-Hecke L-function product and the
proved native Mertens converse. It never identifies rational Moebius signs
with ideal-character phases. The signed-pair conclusion retains its actual
squarefree diagonal and holds at every natural prefix.
-/
noncomputable section
namespace RHLean.Analysis
open MertensExponent
open OAI.SevenEighths
open OAI.SevenEighths.RHLeanNativeSevenEighthsReplay

/-- Every actual nontrivial zeta zero belongs to the zero set bounded by the
same Hecke supremum, through the exact modulus-one product identity. -/
theorem native_zeta_zero_re_le_hecke_beta {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    ρ.re≤HeckeZeroSupremum.beta := by
  have h0 : ρ≠0 := by
    intro h
    have hh := hρ.2.1
    simpa only [h,Complex.zero_re,lt_self_iff_false] using hh
  have h1 : ρ≠1 := by
    intro h
    have hh := hρ.2.2
    simpa only [h,Complex.one_re,lt_self_iff_false] using hh
  have hproduct := HeckeDirichlet.LFunction_eq_dirichlet_product
    (1 : DirichletCharacter ℂ 1) h0 h1
  have hz : HeckeFamily.LFunction
      (HeckeDirichlet.character (1 : DirichletCharacter ℂ 1)) ρ=0 := by
    rw [hproduct,DirichletCharacter.LFunction_modOne_eq,hρ.1,zero_mul]
  exact HeckeZeroSupremum.zero_re_le_beta _ hρ.2.1 (Or.inl h1) hz

/-- The native independently defined rightmost zeta-zero coordinate is
bounded by the actual Hecke supremum, including the empty-set convention. -/
theorem native_zeta_rightmost_le_hecke_beta :
    zetaRightmostRealPart≤HeckeZeroSupremum.beta := by
  apply Real.sSup_le _ (by linarith [HeckeZeroSupremum.half_le_beta])
  rintro x ⟨ρ,hρ,rfl⟩
  exact native_zeta_zero_re_le_hecke_beta hρ

/-- The existing complete converse supplies all positive-loss Mertens
bounds at the Hecke supremum. -/
theorem native_mertens_growth_at_hecke_beta :
    MertensGrowthAtMost HeckeZeroSupremum.beta :=
  (growthAtMost_iff_rightmost_le
    (by linarith [HeckeZeroSupremum.half_le_beta])).mpr native_zeta_rightmost_le_hecke_beta

/-- Strict improvement of the independently defined native arithmetic
power-growth exponent. No zero-free or growth bound is assumed. -/
theorem native_mertens_growth_exponent_lt_seven_eighths :
    mertensGrowthExponent<7/8 := by
  rw [growthExponent_eq_rightmost]
  exact native_zeta_rightmost_le_hecke_beta.trans_lt native_beta_lt_seven_eighths

/-- One positive saving precedes every loss and every natural prefix. -/
theorem native_mertens_uniform_strict_gap :
    ∃gap : ℝ,0<gap ∧ MertensGrowthAtMost (7/8-gap) := by
  refine ⟨7/8-HeckeZeroSupremum.beta,by linarith [native_beta_lt_seven_eighths],?_⟩
  convert native_mertens_growth_at_hecke_beta using 1; ring

/-- A fixed improved power envelope, after spending half the positive gap. -/
theorem native_mertens_fixed_strict_power :
    ∃gap : ℝ,0<gap ∧ MertensPowerBound (7/8-gap) := by
  obtain ⟨gap,hgap,hgrowth⟩ := native_mertens_uniform_strict_gap
  refine ⟨gap/2,by positivity,?_⟩
  convert hgrowth (gap/2) (by positivity) using 1; ring

/-- Complete actual signed covariance, with its squarefree diagonal retained.
The fixed positive exponent saving is uniform in all prefixes. -/
theorem native_signed_pair_uniform_strict_gap :
    ∃gap : ℝ,0<gap ∧ ∀ε : ℝ,0<ε →
      ∃C : ℝ,0≤C ∧ ∀x : ℕ,1≤x →
        2*realMertensPositiveLagPairSum (x+1)≤
          (C*Real.rpow (x:ℝ) (7/8-gap+ε))^2-realMertensDiagonal (x+1) := by
  obtain ⟨gap,hgap,hgrowth⟩ := native_mertens_uniform_strict_gap
  refine ⟨gap,hgap,?_⟩
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := hgrowth ε hε
  refine ⟨C,hC,?_⟩
  intro x hx
  have hsquare : ‖mertensSummatory x‖^2≤
      (C*Real.rpow (x:ℝ) (7/8-gap+ε))^2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))).mpr (hbound x hx)
  rw [vf919_mertens_sq_eq_signedPair] at hsquare
  linarith only [hsquare]

#check native_mertens_growth_exponent_lt_seven_eighths
#print axioms native_mertens_growth_exponent_lt_seven_eighths
#print axioms native_mertens_uniform_strict_gap
#print axioms native_mertens_fixed_strict_power
#print axioms native_signed_pair_uniform_strict_gap
end RHLean.Analysis
