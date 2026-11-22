import RHLean.Geometry.NativeGradedShortSectionConstruction

/-!
# Absorb the explicit constructed-section cost at the original source scales

This is the numerical argument in `GlobalTheory.ShortGenComp.short_generator_comparison`
and `GlobalTheory.ShortDet.exists_short_integral_vector`, respectively in
`HodgeBundleWeights/ShortGeneratorNormComparison.lean` and
`HodgeBundleWeights/ExistsShortIntegralVectorOfDeterminantBound.lean`, at
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

The field degree and discriminant are the actual invariants of the coefficient
field. The rank is the same component-rank bound used by the finite section
constructor, and the group size is its actual cardinality. The assumptions are
the original separate degree, root-discriminant, rank, short theta spanning
size and pointwise comparison scales. The total Hodge-weight size is bounded
by `z^5`, as in the source's chosen weight calculation.

The proof retains the source constants `Cgen = 2000 + Crank + Ctheta` and
`C = 3 * Cgen + 240 + Csup`. It proves the bound on the complete section cost;
that bound, a multiplier-operator bound, and a geometric existence conclusion
are not premises. Constructing the actual theta family, component lattices,
evaluation atlas and their size estimates remains a separate obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField

namespace RHLean.Geometry

/-- The original separate arithmetic and theta scales pay the exact cost of
the SAME finite section constructor. No bound on their product is assumed. -/
theorem nativeShortSectionCost_le_exp_of_source_scales
    (K H : Type) [Field K] [NumberField K] [Fintype H]
    (r : ℕ) {A beta z o S Crank Ctheta Csup : ℝ}
    (hA0 : 0 ≤ A) (hbeta0 : 0 ≤ beta) (hz : 1 ≤ z)
    (hCrank : 0 ≤ Crank) (hCtheta : 0 ≤ Ctheta) (hCsup : 0 ≤ Csup)
    (hdegree : Real.log (Module.finrank ℚ K : ℝ) ≤ o)
    (hdisc : Real.log |(NumberField.discr K : ℝ)| ≤ (Module.finrank ℚ K : ℝ) * o)
    (ho : o ≤ 391 * z ^ 2)
    (hrank : Real.log (r : ℝ) ≤ Crank * z ^ 3)
    (hsize : S ≤ z ^ 5)
    (htheta : Real.log A ≤ Ctheta * (z ^ 3 * S + z ^ 5))
    (hsup : beta ≤ Real.exp (Csup * z ^ 3))
    (hgroup : Real.log (Fintype.card H : ℝ) ≤ 120 * z ^ 2) :
    ((2 * Module.finrank ℚ K * r : ℕ) : ℝ) *
        ((Fintype.card H : ℝ) ^ 2 * (beta *
          max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (r : ℝ) *
            |(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A))) ≤
      Real.exp ((3 * (2000 + Crank + Ctheta) + 240 + Csup) * z ^ 9) := by
  let d : ℝ := Module.finrank ℚ K
  let rd : ℝ := |(NumberField.discr K : ℝ)| ^ (1 / d)
  let Cgen : ℝ := 2000 + Crank + Ctheta
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hdisc0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  have hrd0 : 0 ≤ rd := Real.rpow_nonneg (abs_nonneg _) _
  have hz0 : 0 ≤ z := (by norm_num : (0 : ℝ) ≤ 1).trans hz
  have hCgen : 0 ≤ Cgen := by dsimp [Cgen]; positivity
  have hz13 : (1 : ℝ) ≤ z ^ 3 := one_le_pow₀ hz
  have hz23 : z ^ 2 ≤ z ^ 3 := pow_le_pow_right₀ hz (by norm_num)
  have hz29 : z ^ 2 ≤ z ^ 9 := pow_le_pow_right₀ hz (by norm_num)
  have hz39 : z ^ 3 ≤ z ^ 9 := pow_le_pow_right₀ hz (by norm_num)
  have hz59 : z ^ 5 ≤ z ^ 9 := pow_le_pow_right₀ hz (by norm_num)
  have hz89 : z ^ 8 ≤ z ^ 9 := pow_le_pow_right₀ hz (by norm_num)
  have hde : d ≤ Real.exp (391 * z ^ 2) :=
    (Real.le_exp_log d).trans (Real.exp_le_exp.2 (hdegree.trans ho))
  have hrdlog : Real.log rd ≤ o := by
    dsimp [rd]
    rw [Real.log_rpow hdisc0]
    have h : Real.log |(NumberField.discr K : ℝ)| / d ≤ o :=
      (div_le_iff₀ hd).2 (by simpa only [mul_comm] using hdisc)
    rw [one_div]
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hrde : rd ≤ Real.exp (391 * z ^ 2) :=
    (Real.le_exp_log rd).trans (Real.exp_le_exp.2 (hrdlog.trans ho))
  have hre : (r : ℝ) ≤ Real.exp (Crank * z ^ 3) :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 hrank)
  have hS : z ^ 3 * S ≤ z ^ 8 := by
    calc
      _ ≤ z ^ 3 * z ^ 5 := mul_le_mul_of_nonneg_left hsize (pow_nonneg hz0 _)
      _ = _ := by ring
  have hAe : A ≤ Real.exp (2 * Ctheta * z ^ 9) := by
    refine (Real.le_exp_log A).trans (Real.exp_le_exp.2 (htheta.trans ?_))
    calc
      _ ≤ Ctheta * (2 * z ^ 9) :=
        mul_le_mul_of_nonneg_left (by linarith) hCtheta
      _ = _ := by ring
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hcount : ((2 * Module.finrank ℚ K * r : ℕ) : ℝ) ≤
      Real.exp (Cgen * z ^ 3) := by
    push_cast
    change 2 * d * (r : ℝ) ≤ _
    calc
      _ ≤ Real.exp 1 * Real.exp (391 * z ^ 2) * Real.exp (Crank * z ^ 3) :=
        mul_le_mul (mul_le_mul htwo hde hd.le (Real.exp_pos _).le) hre
          (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (1 + 391 * z ^ 2 + Crank * z ^ 3) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (Cgen * z ^ 3) := by
        apply Real.exp_le_exp.2
        have htheta0 : 0 ≤ Ctheta * z ^ 3 := mul_nonneg hCtheta (pow_nonneg hz0 _)
        dsimp [Cgen]
        nlinarith
  have hscale : d ^ 4 * (r : ℝ) * rd * A ≤ Real.exp (2 * Cgen * z ^ 9) := by
    have hraw : d ^ 4 * (r : ℝ) * rd * A ≤
        Real.exp (391 * z ^ 2) ^ 4 * Real.exp (Crank * z ^ 3) *
          Real.exp (391 * z ^ 2) * Real.exp (2 * Ctheta * z ^ 9) :=
      mul_le_mul
        (mul_le_mul
          (mul_le_mul (pow_le_pow_left₀ hd.le hde 4) hre
            (Nat.cast_nonneg _) (by positivity)) hrde hrd0 (by positivity))
        hAe hA0 (by positivity)
    refine hraw.trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hCrank39 := mul_le_mul_of_nonneg_left hz39 hCrank
    have hCrank90 : 0 ≤ Crank * z ^ 9 := mul_nonneg hCrank (pow_nonneg hz0 _)
    dsimp [Cgen]
    nlinarith [pow_nonneg hz0 9]
  have hLambda0 : 0 ≤ max 1 (d ^ 4 * (r : ℝ) * rd * A) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hLambda : max 1 (d ^ 4 * (r : ℝ) * rd * A) ≤
      Real.exp (2 * Cgen * z ^ 9) :=
    max_le (Real.one_le_exp (by positivity)) hscale
  have hHe : (Fintype.card H : ℝ) ≤ Real.exp (120 * z ^ 2) :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 hgroup)
  have hbetaLambda := mul_le_mul hsup hLambda hLambda0 (Real.exp_pos _).le
  have hgroupProduct := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hHe 2)
    hbetaLambda (mul_nonneg hbeta0 hLambda0) (sq_nonneg _)
  have hcost := mul_le_mul hcount hgroupProduct
    (mul_nonneg (sq_nonneg _) (mul_nonneg hbeta0 hLambda0)) (Real.exp_pos _).le
  refine hcost.trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hCgen39 := mul_le_mul_of_nonneg_left hz39 hCgen
  have hCsup39 := mul_le_mul_of_nonneg_left hz39 hCsup
  change Cgen * z ^ 3 + ((2 : ℝ) * (120 * z ^ 2) +
      (Csup * z ^ 3 + 2 * Cgen * z ^ 9)) ≤
    (3 * Cgen + 240 + Csup) * z ^ 9
  nlinarith

end RHLean.Geometry

end
