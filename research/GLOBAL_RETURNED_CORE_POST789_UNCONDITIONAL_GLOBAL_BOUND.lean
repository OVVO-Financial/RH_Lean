import Mathlib
import RHLean.Analysis.NativePNTQuantitativeStatements
import RHLean.Analysis.StrongMertensLogNineBalance
import «research.GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE»

/-!
# Unconditional global bound for the post-#789 signed remainder

The repository already compiles the unconditional zero-free-region estimate
`strongNativeMertensSubexp`:

  |M(N)| <= C N exp(-c (log N)^(1/10)),   N >= 3.

Feeding it through the Young comparison of
`GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE` gives a bound on the
signed remainder that holds for every `R >= 56`, with no envelope hypothesis:

  X_R <= (1/4) E_R + 4 B(R^2 - 1)^2 + 4 B(R - 1)^2,
  B(x) = C x exp(-c (log x)^(1/10)).

This is the strongest global bound on `X_R` currently available from compiled
unconditional input.  It is not the RH consumer's bound.  The consumer needs
`X_R <= (3/2) E_R + C R^2 K`, while `B(R^2 - 1)^2` is of size
`R^4 exp(-c' (log R)^(1/10))`.  The gap is a factor
`R^2 exp(-c' (log R)^(1/10))`.  By the lower comparison
`(1/2) corr^2 - (1/2) E - 3 R^2 <= X_R`, that gap cannot be closed inside
`X_R`: closing it is an RH-strength top-endpoint Mertens estimate.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Pure algebra: a Young bound plus a triangle bound on the correlation
norm. -/
private theorem post789_global_bound_algebra
    {X E n bR bN : ℝ}
    (hY : X ≤ (1 + 1) * n ^ 2 + 1 / 4 * E)
    (hn0 : 0 ≤ n) (hn : n ≤ bR + bN) :
    X ≤ 1 / 4 * E + 4 * bN ^ 2 + 4 * bR ^ 2 := by
  nlinarith [sq_nonneg (bR - bN), mul_nonneg hn0 (sub_nonneg.mpr hn),
    sq_nonneg (bR + bN - n)]

/-- **Unconditional global bound.** For every `R >= 56` the post-#789 signed
remainder is at most a quarter of the q² energy plus the squared
zero-free-region Mertens envelopes at the two correlation endpoints. -/
theorem post789SignedRemainder_unconditional_global_bound :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ R : ℕ, 56 ≤ R →
        lowOwnerPost789SignedCrossDiagonalRemainder R ≤
          (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
            4 * (C * (squareRootEndpoint R : ℝ) *
              Real.exp (-c * (Real.log (squareRootEndpoint R : ℝ)) ^
                ((1 : ℝ) / 10))) ^ 2 +
            4 * (C * ((R - 1 : ℕ) : ℝ) *
              Real.exp (-c * (Real.log ((R - 1 : ℕ) : ℝ)) ^
                ((1 : ℝ) / 10))) ^ 2 := by
  rcases strongNativeMertensSubexp with ⟨c, C, hc, hC, hM⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro R hR
  have hN : 3 ≤ squareRootEndpoint R := by
    have hsquare : 2 ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left (by omega : 2 ≤ R) 2
    unfold squareRootEndpoint
    omega
  have hMN := hM (squareRootEndpoint R) hN
  have hMR := hM (R - 1) (by omega)
  rw [← norm_mertensSummatory_eq_abs_nativeMertensSummatory] at hMN
  rw [← norm_mertensSummatory_eq_abs_nativeMertensSummatory] at hMR
  have hcorr :=
    (norm_sub_le (mertensSummatory (R - 1))
      (mertensSummatory (squareRootEndpoint R))).trans (add_le_add hMR hMN)
  rw [← squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
    R (by omega)] at hcorr
  have hY := post789SignedRemainder_le_correlationSq_young
    (R := R) (by omega) (a := 1) (b := 1 / 4) (by norm_num) (by norm_num)
  exact post789_global_bound_algebra hY (norm_nonneg _) hcorr


/-- **Explicit unconditional quartic baseline.**

For every root R >= 56, the signed post-#789 remainder has the all-scale bound

  S_R <= E_R / 4 + 8 R^4.

This uses only the trivial Mertens bound, the exact correlation dictionary,
and the existing Young comparison. It is deliberately weaker than the target
A E_R + C R^2 K: the point is a fixed explicit finite rung from which later
scale improvements can be measured. -/
theorem post789SignedRemainder_unconditional_quartic_bound
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPost789SignedCrossDiagonalRemainder R ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        8 * (R : ℝ) ^ 4 := by
  have hMR :=
    norm_mertensSummatory_sub_le 0 (R - 1) (Nat.zero_le (R - 1))
  rw [mertensSummatory_zero, sub_zero] at hMR
  have hMX :=
    norm_mertensSummatory_sub_le 0 (squareRootEndpoint R)
      (Nat.zero_le (squareRootEndpoint R))
  rw [mertensSummatory_zero, sub_zero] at hMX
  have hRmNat : R - 1 ≤ R := Nat.sub_le R 1
  have hXNat : squareRootEndpoint R ≤ R ^ 2 := by
    unfold squareRootEndpoint
    omega
  have hRm : (((R - 1 : ℕ) : ℝ)) ≤ (R : ℝ) := by
    exact_mod_cast hRmNat
  have hX : (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hXNat
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hRleR2 : (R : ℝ) ≤ (R : ℝ) ^ 2 := by
    have hRone : (1 : ℝ) ≤ R := by
      exact_mod_cast (show 1 ≤ R by omega)
    nlinarith
  have hcorr :
      ‖squareRootCanonicalRoughCorrelation R‖ ≤ 2 * (R : ℝ) ^ 2 := by
    rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
      R (by omega)]
    calc
      ‖mertensSummatory (R - 1) -
          mertensSummatory (squareRootEndpoint R)‖ ≤
          ‖mertensSummatory (R - 1)‖ +
            ‖mertensSummatory (squareRootEndpoint R)‖ := norm_sub_le _ _
      _ ≤ (((R - 1 : ℕ) : ℝ)) + (squareRootEndpoint R : ℝ) :=
        add_le_add hMR hMX
      _ ≤ 2 * (R : ℝ) ^ 2 := by
        nlinarith
  have hcorr0 : 0 ≤ ‖squareRootCanonicalRoughCorrelation R‖ := norm_nonneg _
  have hcorrSq :
      ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
        4 * (R : ℝ) ^ 4 := by
    nlinarith [sq_nonneg (2 * (R : ℝ) ^ 2 -
      ‖squareRootCanonicalRoughCorrelation R‖)]
  have hY := post789SignedRemainder_le_correlationSq_young
    (R := R) (by omega) (a := 1) (b := 1 / 4) (by norm_num) (by norm_num)
  nlinarith



/-- **Loose-first target at the sharpened remainder coefficient.**

The daughter coefficient is already the RH-sufficient value `2`; only the
unconditional surplus is still quartic.  This makes the next tightening target
purely a scale problem: replace `8 R^4` by `C R^2 K` without changing the
daughter coefficient. -/
theorem post789SignedRemainder_unconditional_two_q2_add_quartic
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPost789SignedCrossDiagonalRemainder R ≤
      2 * canonicalRoughLowQ2DaughterEnergy R +
        8 * (R : ℝ) ^ 4 := by
  have h :=
    post789SignedRemainder_unconditional_quartic_bound R hR
  have hE : 0 ≤ canonicalRoughLowQ2DaughterEnergy R := by
    unfold canonicalRoughLowQ2DaughterEnergy
    apply Finset.sum_nonneg
    intro q _hq
    unfold rawQ2ChildEnergyReal
    positivity
  nlinarith

/-- **Loose-first target at the sharpened FinalStokes coefficient.**

The exact quarter frame upgrades the preceding theorem to the final-Stokes
coefficient `9/4`, again with only a quartic surplus. -/
theorem finalStokes_unconditional_nineQuarters_q2_add_quartic
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R ≤
      (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        8 * (R : ℝ) ^ 4 := by
  have hS :=
    post789SignedRemainder_unconditional_two_q2_add_quartic R hR
  have hQ :=
    lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_q2Sq_add_post789Remainder
    hR]
  nlinarith

end RHLean.Proof
