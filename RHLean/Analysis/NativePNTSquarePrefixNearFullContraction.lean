import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge

/-!
# Near-full square-prefix PNT contraction

The existing square-prefix compensation theorem spends only one quarter of the
certified good-mass deficit on slope improvement and reserves the other three
quarters to absorb lower-order `N * log N` terms.  That split is convenient but
not intrinsic.  Since the good-mass deficit is quadratic in `log N` while the
remaining overhead is only linear in `log N`, any fixed positive fraction of
the deficit may be reserved for the overhead.

This module makes that tradeoff explicit.  For every `0 < theta < 1`, the same
square-prefix compensated recurrence and the same good-mass hypothesis imply

```text
alpha -> alpha - theta * (alpha - beta) * c.
```

Thus the previous factor `1/4` is replaced by an arbitrary fraction strictly
below one.  No analytic premise is strengthened and no sign is discarded beyond
what the existing compensated recurrence already discards.

At the low-slope optimum `beta = 2 * alpha / 3` and with the proved
square-prefix good-mass coefficient `beta^2 / 6600000`, the gross cubic
coefficient is

```text
1 / 44550000.
```

It is a supremal coefficient for this particular asymptotic absorption step:
we can realize every fixed fraction below it, but not the full coefficient by
this argument because a positive reserve is still needed for the lower-order
terms.  The concrete `theta = 99/100` checkpoint gives

```text
alpha -> alpha - alpha^3 / 45000000,
```

which is exactly `99/25 = 3.96` times the previous proved square-prefix
low-slope decrement `alpha^3 / 178200000`.

The gain is deliberately not advertised as a physical-scale improvement.
As `theta` approaches one, the reserved fraction `1-theta` shrinks and the
large-`N` onset needed to absorb the lower-order terms increases.  The missing
RH-scale theorem remains quantitative control of that onset.  The final
checkpoint below pairs this stronger square-prefix slope statement with the
exact signed prime-wheel frontier identity without conflating the two.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.vonMangoldt BigOperators Topology

namespace RHLean.Analysis

/-- The full low-slope cubic coefficient available before reserving any fixed
positive fraction of the square-prefix good-mass deficit for lower-order
absorption. -/
def nativePNTSquarePrefixLowSlopeGrossCubicConstant : ℝ := 1 / 44550000

/-- The gross coefficient is four times the previously exposed `1/4`-reserve
coefficient. -/
theorem nativePNTSquarePrefixLowSlopeGrossCubicConstant_eq_four_mul_current :
    nativePNTSquarePrefixLowSlopeGrossCubicConstant =
      4 * nativePNTSquarePrefixLowSlopeCubicConstant := by
  norm_num [nativePNTSquarePrefixLowSlopeGrossCubicConstant,
    nativePNTSquarePrefixLowSlopeCubicConstant]

/-- **Fractional good-mass absorption.**  Any fixed fraction `theta < 1` of the
quadratic good-mass deficit can be spent on slope contraction.  The remaining
fraction absorbs all terms that are only linear in `log N` after moving far
enough out on the tail.

This is the same Möbius-rederived square-prefix compensated recurrence used by
`nativePNTSquarePrefixHasAffineEnvelope_improve_of_goodMass`; only the arbitrary
`1/4` budget split is removed. -/
theorem nativePNTSquarePrefixHasAffineEnvelope_improve_of_goodMass_fraction
    (alpha beta c theta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 ≤ beta) (hba : beta < alpha)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    (hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - theta * ((alpha - beta) * c)) := by
  rcases henv with ⟨D, hD, henv⟩
  let gross : ℝ := (alpha - beta) * c
  let reserve : ℝ := (1 - theta) * gross
  let delta : ℝ := theta * gross
  have habpos : 0 < alpha - beta := sub_pos.mpr hba
  have hgross : 0 < gross := by
    dsimp [gross]
    positivity
  have hreserve : 0 < reserve := by
    dsimp [reserve]
    exact mul_pos (sub_pos.mpr htheta1) hgross
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact mul_pos htheta hgross
  have hsplit : reserve + delta = gross := by
    dsimp [reserve, delta]
    ring
  have hable : alpha - beta ≤ alpha := by linarith
  have hgrossle : gross ≤ alpha := by
    have hmul := mul_le_mul hable hc1 hc.le halpha.le
    simpa [gross] using hmul
  have hdeltagross : delta ≤ gross := by
    dsimp [delta]
    exact mul_le_of_le_one_left hgross.le htheta.le htheta1.le
  have hdeltale : delta ≤ alpha := hdeltagross.trans hgrossle
  have hnewnonneg : 0 ≤ alpha - delta := sub_nonneg.mpr hdeltale
  let C0 : ℝ := 3000 * alpha + 784 * D + 3000
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hlogTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop 1
  have hlogC : ∀ᶠ N : ℕ in atTop,
      C0 / reserve ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop (C0 / reserve)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      |nativePNTError N| ≤ (alpha - delta) * (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 3, hgood, hlog1, hlogC]
      with N hN hgoodN hL1 hLC
    have hN1 : 1 ≤ N := by omega
    have hNR0 : 0 ≤ (N : ℝ) := by positivity
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    let L : ℝ := Real.log (N : ℝ)
    have hL1' : (1 : ℝ) ≤ L := by simpa [L] using hL1
    have hL0 : 0 ≤ L := le_trans (by norm_num) hL1'
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1'
    have hCLe0 : C0 ≤ L * reserve := by
      exact (div_le_iff₀ hreserve).mp (by simpa [L] using hLC)
    have hCLe : C0 ≤ reserve * L := by
      simpa [mul_comm] using hCLe0
    have hB0 : 0 ≤ 2000 * alpha + 782 * D := by positivity
    have hBLe :
        2000 * alpha + 782 * D ≤
          (2000 * alpha + 782 * D) * L := by
      have h := mul_le_mul_of_nonneg_left hL1' hB0
      simpa using h
    have hleft :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤ C0 * L := by
      dsimp [C0]
      nlinarith [hBLe]
    have hCLmul : C0 * L ≤ (reserve * L) * L :=
      mul_le_mul_of_nonneg_right hCLe hL0
    have hinner :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤
          reserve * L ^ 2 := by
      calc
        alpha * (1000 * L + 2000) +
              D * (2 * L + 782) + 3000 * L ≤ C0 * L := hleft
        _ ≤ (reserve * L) * L := hCLmul
        _ = reserve * L ^ 2 := by ring
    have hD600 : D * 600 ≤ D * 600 * (N : ℝ) := by
      have h600D : 0 ≤ D * 600 := by positivity
      have h := mul_le_mul_of_nonneg_left hN1R h600D
      simpa [mul_assoc] using h
    have hinnerN := mul_le_mul_of_nonneg_left hinner hNR0
    have hoverhead :
        alpha * (N : ℝ) * (1000 * L + 2000) +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L ≤
          reserve * (N : ℝ) * L ^ 2 := by
      have hreshape :
          alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L ≤
            (N : ℝ) *
              (alpha * (1000 * L + 2000) +
                D * (2 * L + 782) + 3000 * L) := by
        nlinarith [hD600]
      calc
        alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L ≤
            (N : ℝ) *
              (alpha * (1000 * L + 2000) +
                D * (2 * L + 782) + 3000 * L) := hreshape
        _ ≤ (N : ℝ) * (reserve * L ^ 2) := hinnerN
        _ = reserve * (N : ℝ) * L ^ 2 := by ring
    have hcoef0 : 0 ≤ (alpha - beta) * (N : ℝ) :=
      mul_nonneg habpos.le hNR0
    have hgoodN' : c * L ^ 2 ≤ nativeLambdaTwoGoodRecipMass N beta := by
      simpa [L] using hgoodN
    have hgoodMul := mul_le_mul_of_nonneg_left hgoodN' hcoef0
    have hdeficit :
        -(alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta ≤
          -gross * (N : ℝ) * L ^ 2 := by
      calc
        -(alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta =
            -((alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta) := by ring
        _ ≤ -((alpha - beta) * (N : ℝ) * (c * L ^ 2)) :=
          neg_le_neg hgoodMul
        _ = -gross * (N : ℝ) * L ^ 2 := by
          dsimp [gross]
          ring
    have htail :
        (alpha * (N : ℝ) * (1000 * L + 2000) +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L) +
          (-(alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta) ≤
          -delta * (N : ℝ) * L ^ 2 := by
      calc
        (alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L) +
            (-(alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta) ≤
            reserve * (N : ℝ) * L ^ 2 - gross * (N : ℝ) * L ^ 2 :=
          add_le_add hoverhead hdeficit
        _ = -delta * (N : ℝ) * L ^ 2 := by
          rw [← hsplit]
          ring
    have hrec := nativePNTError_abs_log_sq_le_affine_compensated_mobius_rederived
      N hN alpha beta D halpha.le hbeta hba.le hD henv
    have hrearrange :
        alpha * (N : ℝ) *
              (L ^ 2 + 1000 * L + 2000) -
            (alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L =
          alpha * (N : ℝ) * L ^ 2 +
            ((alpha * (N : ℝ) * (1000 * L + 2000) +
                D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                3000 * (N : ℝ) * L) +
              (-(alpha - beta) * (N : ℝ) *
                nativeLambdaTwoGoodRecipMass N beta)) := by
      ring
    have hsq :
        |nativePNTError N| * L ^ 2 ≤
          (alpha - delta) * (N : ℝ) * L ^ 2 := by
      have hrec' :
          |nativePNTError N| * L ^ 2 ≤
            alpha * (N : ℝ) * L ^ 2 +
              ((alpha * (N : ℝ) * (1000 * L + 2000) +
                  D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                  3000 * (N : ℝ) * L) +
                (-(alpha - beta) * (N : ℝ) *
                  nativeLambdaTwoGoodRecipMass N beta)) := by
        simpa [L, hrearrange] using hrec
      calc
        |nativePNTError N| * L ^ 2 ≤
            alpha * (N : ℝ) * L ^ 2 +
              ((alpha * (N : ℝ) * (1000 * L + 2000) +
                  D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                  3000 * (N : ℝ) * L) +
                (-(alpha - beta) * (N : ℝ) *
                  nativeLambdaTwoGoodRecipMass N beta)) := hrec'
        _ ≤ alpha * (N : ℝ) * L ^ 2 - delta * (N : ℝ) * L ^ 2 := by
          simpa [sub_eq_add_neg] using
            (add_le_add_left htail (alpha * (N : ℝ) * L ^ 2))
        _ = (alpha - delta) * (N : ℝ) * L ^ 2 := by ring
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hsq' :
        |nativePNTError N| * L ^ 2 ≤
          ((alpha - delta) * (N : ℝ)) * L ^ 2 := by
      simpa [mul_assoc] using hsq
    exact (mul_le_mul_iff_left₀ hLsq).mp hsq'
  rcases eventually_atTop.1 hlarge with ⟨M, hM⟩
  refine ⟨D + delta * (M : ℝ), ?_, ?_⟩
  · positivity
  · intro N
    by_cases hMN : M ≤ N
    · exact (hM N hMN).trans
        (le_add_of_nonneg_right (by positivity))
    · have hNM : N ≤ M := Nat.le_of_lt (lt_of_not_ge hMN)
      have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
      have hdeltaNM := mul_le_mul_of_nonneg_left hNMR hdelta.le
      have hold := henv N
      have htarget :
          alpha * (N : ℝ) + D ≤
            (alpha - delta) * (N : ℝ) +
              (D + delta * (M : ℝ)) := by
        nlinarith
      exact hold.trans htarget

/-- At the optimal low-slope threshold, the unreserved good-mass decrement is
`alpha^3 / 44550000`.  Every fixed fraction below this value is therefore
available as a proved affine-envelope contraction. -/
theorem nativePNTSquarePrefixHasAffineEnvelope_lowSlope_fraction_cubic_step
    (theta alpha : ℝ)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - theta * nativePNTSquarePrefixLowSlopeGrossCubicConstant * alpha ^ 3) := by
  let beta : ℝ := 2 * alpha / 3
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have hbeta0 : 0 ≤ beta := hbeta.le
  have hbeta1 : beta ≤ 1 := by
    dsimp [beta]
    nlinarith
  have hba : beta < alpha := by
    dsimp [beta]
    nlinarith
  let c : ℝ := beta ^ 2 / 6600000
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hsq : beta ^ 2 ≤ 1 := by
    have hprod : 0 ≤ beta * (1 - beta) :=
      mul_nonneg hbeta0 (sub_nonneg.mpr hbeta1)
    nlinarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    nlinarith
  have hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta := by
    simpa [c] using
      nativeLambdaTwoGoodRecipMass_eventually_quadratic_squarePrefix_rate
        beta hbeta hbeta1
  have himp := nativePNTSquarePrefixHasAffineEnvelope_improve_of_goodMass_fraction
    alpha beta c theta halpha hbeta0 hba hc hc1 htheta htheta1 hgood henv
  have hcoef :
      alpha - theta * ((alpha - beta) * c) =
        alpha - theta * nativePNTSquarePrefixLowSlopeGrossCubicConstant * alpha ^ 3 := by
    dsimp [beta, c, nativePNTSquarePrefixLowSlopeGrossCubicConstant]
    ring
  rw [hcoef] at himp
  exact himp

/-- A concrete aggressive checkpoint using 99 percent of the available
quadratic good-mass deficit. -/
def nativePNTSquarePrefixNearFullCubicConstant : ℝ := 1 / 45000000

/-- The 99-percent coefficient is exactly `99/25` times the previous
square-prefix low-slope coefficient. -/
theorem nativePNTSquarePrefixNearFullCubicConstant_eq_scaled :
    nativePNTSquarePrefixNearFullCubicConstant =
      (99 / 25 : ℝ) * nativePNTSquarePrefixLowSlopeCubicConstant := by
  norm_num [nativePNTSquarePrefixNearFullCubicConstant,
    nativePNTSquarePrefixLowSlopeCubicConstant]

/-- The concrete 99-percent contraction. -/
theorem nativePNTSquarePrefixHasAffineEnvelope_lowSlope_nearFull_cubic_step
    (alpha : ℝ) (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - nativePNTSquarePrefixNearFullCubicConstant * alpha ^ 3) := by
  have h := nativePNTSquarePrefixHasAffineEnvelope_lowSlope_fraction_cubic_step
    (99 / 100 : ℝ) alpha (by norm_num) (by norm_num)
    halpha halphaSmall henv
  have hcoef :
      (99 / 100 : ℝ) * nativePNTSquarePrefixLowSlopeGrossCubicConstant =
        nativePNTSquarePrefixNearFullCubicConstant := by
    norm_num [nativePNTSquarePrefixLowSlopeGrossCubicConstant,
      nativePNTSquarePrefixNearFullCubicConstant]
  simpa [hcoef] using h

/-- The near-full update is strictly smaller than the previous low-slope
square-prefix update for every positive slope. -/
theorem nativePNTSquarePrefixNearFull_step_lt_current_step
    (alpha : ℝ) (halpha : 0 < alpha) :
    alpha - nativePNTSquarePrefixNearFullCubicConstant * alpha ^ 3 <
      alpha - nativePNTSquarePrefixLowSlopeCubicConstant * alpha ^ 3 := by
  have hC : nativePNTSquarePrefixLowSlopeCubicConstant <
      nativePNTSquarePrefixNearFullCubicConstant := by
    norm_num [nativePNTSquarePrefixNearFullCubicConstant,
      nativePNTSquarePrefixLowSlopeCubicConstant]
  have hpow : 0 < alpha ^ 3 := pow_pos halpha 3
  have hmul := mul_lt_mul_of_pos_right hC hpow
  linarith

/-- Public bound-level acceptance theorem for the 99-percent checkpoint. -/
theorem nativePNTSquarePrefixLowSlope_nearFull_affineEnvelope_strictly_tighter
    (alpha : ℝ) (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
        (alpha - nativePNTSquarePrefixNearFullCubicConstant * alpha ^ 3) ∧
      alpha - nativePNTSquarePrefixNearFullCubicConstant * alpha ^ 3 <
        alpha - nativePNTSquarePrefixLowSlopeCubicConstant * alpha ^ 3 := by
  exact ⟨
    nativePNTSquarePrefixHasAffineEnvelope_lowSlope_nearFull_cubic_step
      alpha halpha halphaSmall henv,
    nativePNTSquarePrefixNearFull_step_lt_current_step alpha halpha⟩

/-- Architecture checkpoint: retain the exact signed prime-wheel frontier while
advancing the proved square-prefix affine PNT bound.  The conjunction is
intentional: it records both acceptance coordinates without pretending that the
frontier identity itself supplies the slope gain. -/
theorem nativePNTSignedSecondSelbergFrontier_and_nearFullContraction
    {y N : ℕ} (hscale : N < 2 * y ^ 2)
    (alpha : ℝ) (halpha : 0 < alpha) (halphaSmall : alpha ≤ 3 / 2)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTSignedSecondSelbergWheelFrontierErrorMass y N =
        -nativePNTSignedSecondSelbergWheelFrontierCharge y N ∧
      nativePNTHasAffineEnvelope
        (alpha - nativePNTSquarePrefixNearFullCubicConstant * alpha ^ 3) := by
  exact ⟨
    nativePNTSignedSecondSelbergWheelFrontierErrorMass_eq_neg_charge hscale,
    nativePNTSquarePrefixHasAffineEnvelope_lowSlope_nearFull_cubic_step
      alpha halpha halphaSmall henv⟩

end RHLean.Analysis

end