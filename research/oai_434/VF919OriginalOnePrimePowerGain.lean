import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified
import «research.oai_434.VF919ActualSexticLocalResonanceAndCompensation»

/-!
# ORIGINAL OAI unramified one-prime gain BEFORE absolute-value summation

The pinned original
  HighRowsSelectedUnramified.unramifiedSelected_error_bound
proves only a constant 720 bound for
  unramifiedSelected Q A eta v x w z
    + unramifiedClosed Q A eta v x w z * star v.

This file RETAINS THE DISCARDED POWERS in the same original OAI
HighRowsSelectedError.unramified_marked_error_bound source proof
instead of replacing the actual marked error with Pstar = -V.

Under Q>=4, x.re>=7/8, w.re>=0, z.re>=17/50
assumptions and unit eta/v phases, we show:
   |Pstar + D| <= 28 Q^(-7/8)
   |B| |Pstar + D| <= 28 Q^(-7/8)
and feed them into ORIGINAL OAI ProbeLocal.compensated_phase_error_bound
to obtain the true one-prime O(Q^(-7/8)) signed remainder.

This tests LOCAL unramified cancellation, not the *global* physical
Gaussian source l65 or the uniform sixth-moment bound. Row-dependent
Mellin weights, ramified contributions, multiplicities and the exact
normalizer remain source-specific global obligations.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.ProbeEuler
open ProbeLocal

/-- Sharp one-prime SOURCE estimate for the ACTUAL marked profile, where
    Pstar is unramifiedMarked (not -V), D is coordD, and the giant
    multiplier B=star eta*Q^x is retained. -/
theorem oai_one_prime_actual_marked_error_power
    (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (hx : (7 / 8 : ℝ) ≤ x.re)
    (hw : (0 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖unramifiedMarked Q A eta v x w z + coordD Q eta v x‖ ≤
        28 * Q ^ (-(7 / 8 : ℝ)) ∧
    ‖star eta * (Q : ℂ) ^ x‖ *
      ‖unramifiedMarked Q A eta v x w z + coordD Q eta v x‖ ≤
        28 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta * (Q : ℂ) ^ x
  let P := unramifiedMarked Q A eta v x w z
  let T : ℝ := Q ^ (-(7 / 8 : ℝ))
  have hR : ‖R‖ ≤ Q ^ (4 - 6 * x.re - 6 * z.re) :=
    coordR_norm_le Q hQ0 A x z hA
  have hV : ‖V‖ = Q ^ (-6 * z.re) := coordV_norm Q hQ0 z
  have hD : ‖D‖ ≤ Q ^ (-x.re) :=
    coordD_norm_le Q hQ0 eta v x heta.le hv.le
  have hK : ‖K‖ ≤ Q ^ (1 - x.re - w.re) :=
    coordK_norm_le Q hQ1 eta x w heta.le
  have hW : ‖W‖ ≤ 1 :=
    (coordW_norm_le Q hQ0 v w hv.le).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hB : ‖B‖ ≤ Q ^ x.re := by
    dsimp only [B]
    rw [norm_mul, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hQ0,
      heta, one_mul]
  have hRh : ‖R‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hVh : ‖V‖ ≤ 1 / 2 := by
    rw [hV]
    exact rpow_le_half Q _ hQ (by linarith)
  have hDh : ‖D‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ)
      (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q ^ aa) (hbb : b ≤ Q ^ bb)
      (he : aa + bb ≤ c) : a * b ≤ Q ^ c := by
    calc
      a * b ≤ Q ^ aa * Q ^ bb :=
        mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (aa + bb) := (Real.rpow_add hQ0 aa bb).symm
      _ ≤ Q ^ c := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hRT : ‖R‖ ≤ T := by
    exact hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by
      linarith))
  have hKV : ‖K‖ * ‖V‖ ≤ T := by
    have hVle : ‖V‖ ≤ Q ^ (-6 * z.re) := hV.le
    exact hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      hK hVle (by linarith)
  have hBR : ‖B‖ * ‖R‖ ≤ T :=
    hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      hB hR (by linarith)
  have hKVpow :
      ‖K‖ * ‖V‖ ≤ Q ^ (1 - x.re - w.re - 6 * z.re) := by
    exact hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      hK hV.le (by linarith)
  have hBKV : ‖B‖ * (‖K‖ * ‖V‖) ≤ T :=
    hprod _ _ _ _ _ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      hB hKVpow (by linarith)
  have hraw := unramified_marked_error_bound R V (Q : ℂ)⁻¹ K W D
    hRh hVh hqi hDh
  have hP : ‖P + D‖ ≤ 12 * ‖R‖ * (1 + ‖W‖) +
      4 * ‖K‖ * ‖V‖ := by
    change ‖P + D‖ ≤ _ at hraw
    exact hraw
  have hP' : ‖P + D‖ ≤ 24 * ‖R‖ + 4 * (‖K‖ * ‖V‖) := by
    have hRW := mul_le_mul_of_nonneg_left hW (norm_nonneg R)
    nlinarith [hP, hRW, norm_nonneg R]
  have hPT : ‖P + D‖ ≤ 28 * T := by
    nlinarith [hP', hRT, hKV]
  have hBPT : ‖B‖ * ‖P + D‖ ≤ 28 * T := by
    have hscaled := mul_le_mul_of_nonneg_left hP' (norm_nonneg B)
    nlinarith [hscaled, hBR, hBKV]
  exact ⟨hPT, hBPT⟩

/-- Sharpen the upstream unramifiedSelected_error_bound from 720 to
    720*Q^(-7/8) for the *signed compensated pair*, WITHOUT a narrow
    prime window and without Pstar=-V. This is an actual OAI source
    local analytic estimate, not a generic abstract residual. -/
theorem oai_one_prime_unramified_compensated_power_gain
    (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (hx : (7 / 8 : ℝ) ≤ x.re)
    (hw : (0 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖unramifiedSelected Q A eta v x w z +
        unramifiedClosed Q A eta v x w z * star v‖ ≤
      720 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let P := unramifiedMarked Q A eta v x w z
  let B := star eta * (Q : ℂ) ^ x
  let q := (Q : ℂ) ^ (-w)
  let vInv := star v
  let T : ℝ := Q ^ (-(7 / 8 : ℝ))
  have hV : ‖V‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : ‖D‖ ≤ 1 / 2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (rpow_le_half Q _ hQ (by linarith))
  have hW : ‖W‖ ≤ 1 :=
    (coordW_norm_le Q hQ0 v w hv.le).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖q‖ ≤ 1 := by
    dsimp [q]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have hVT : ‖V‖ ≤ T := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖D‖ ≤ T :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hP := oai_one_prime_actual_marked_error_power Q A eta v x w z
    hQ hA heta hv hx hw hz
  have hphase := selected_phase_identities Q eta v x w
    hQ0 heta hv
  have hh := compensated_phase_error_bound V W D P B q vInv T
    (Real.rpow_nonneg hQ0.le _) hV hW hD hq
    hVT hDT hP.1 hP.2 (by change ‖star v‖ ≤ 1; rw [norm_star, hv])
    hphase.1 hphase.2
  change ‖compensatedReplacement V W D P B q +
    continuedCorrection V W D P * vInv‖ ≤ 720 * T
  exact hh


/-- Apply the source-faithful signed one-prime bound on the ACTUAL
    central contour.  The original source coordinates are
      x.re = a + 16*e, w.re = 1 - a - 6*e, z.re = 17/50.
    At a=7/8, w.re is close to 1/8, so a spurious w.re>=1/2
    assumption would make the local estimate unusable there.
    This theorem requires the explicit subregion a+6*e<=1,
    and makes NO claim about the remaining negative-w contour,
    conductor summation, Gaussian/Mellin transport, or NNS energy. -/
theorem oai_one_prime_physical_central_contour_power_gain
    (Q : ℝ) (A eta v x w z : ℂ) (a e : ℝ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (ha : (7 / 8 : ℝ) ≤ a)
    (haTop : a + 6 * e ≤ 1)
    (he : 0 ≤ e)
    (hx : x.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) :
    ‖unramifiedSelected Q A eta v x w z +
        unramifiedClosed Q A eta v x w z * star v‖ ≤
      720 * Q ^ (-(7 / 8 : ℝ)) := by
  apply oai_one_prime_unramified_compensated_power_gain
    Q A eta v x w z hQ hA heta hv
  · rw [hx]
    linarith
  · rw [hw]
    linarith
  · rw [hz]


/-- The ORIGINAL central-contour coordinates, not an invented
    independent half-plane choice, satisfy the one-prime compensated
    Q^(-7/8) estimate as soon as 7/8 <= a and a+6*e <= 1.
    In particular w.re=1-a-6*e is near 1/8 at a=7/8,
    NOT >= 1/2. The theorem consumes ONLY the source-local estimate. -/
theorem oai_one_prime_compensated_source_contour_rate
    (Q : ℝ) (A eta v x w z : ℂ) (a e : ℝ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (ha : (7 / 8 : ℝ) ≤ a)
    (he : 0 < e) (_heMax : e ≤ 1 / 1000)
    (haUpper : a + 6 * e ≤ 1)
    (hx : x.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) :
    ‖unramifiedSelected Q A eta v x w z +
        unramifiedClosed Q A eta v x w z * star v‖ ≤
      720 * Q ^ (-(7 / 8 : ℝ)) := by
  apply oai_one_prime_unramified_compensated_power_gain
    Q A eta v x w z hQ hA heta hv
  · rw [hx]
    linarith
  · rw [hw]
    linarith
  · rw [hz]

/-- A GENUINE weighted energy rate for the recombined, single-prime,
    original OAI source residual, including arbitrary NONNEGATIVE
    physical row weights and row-dependent unit phases.
    No complete-uniform-orbit hypothesis, no high-row target, and no
    phase-orthogonality assumption is used. This is deliberately
    a ONE-prime source bound, not the summed effective-ideal family. -/
theorem oai_one_prime_compensated_weighted_l2_rate
    {ι : Type*} (rows : Finset ι) (rho : ι → ℝ)
    (Q : ℝ) (A eta x w z : ℂ) (v : ι → ℂ) (a e : ℝ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hv : ∀ u ∈ rows, ‖v u‖ = 1)
    (hrho : ∀ u ∈ rows, 0 ≤ rho u)
    (ha : (7 / 8 : ℝ) ≤ a)
    (he : 0 < e) (heMax : e ≤ 1 / 1000)
    (haUpper : a + 6 * e ≤ 1)
    (hx : x.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) :
    (∑ u ∈ rows, rho u *
       ‖unramifiedSelected Q A eta (v u) x w z +
           unramifiedClosed Q A eta (v u) x w z * star (v u)‖ ^ 2) ≤
      (720 * Q ^ (-(7 / 8 : ℝ))) ^ 2 *
        (∑ u ∈ rows, rho u) := by
  let r : ι → ℂ := fun u =>
    unramifiedSelected Q A eta (v u) x w z +
      unramifiedClosed Q A eta (v u) x w z * star (v u)
  let C : ℝ := 720 * Q ^ (-(7 / 8 : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint (u : ι) (hu : u ∈ rows) : ‖r u‖ ≤ C := by
    dsimp [r, C]
    exact oai_one_prime_compensated_source_contour_rate
      Q A eta (v u) x w z a e
      hQ hA heta (hv u hu) ha he heMax haUpper hx hw hz
  have hsq (u : ι) (hu : u ∈ rows) : ‖r u‖ ^ 2 ≤ C ^ 2 := by
    have hprod : 0 ≤ (C - ‖r u‖) * (C + ‖r u‖) :=
      mul_nonneg (sub_nonneg.mpr (hpoint u hu))
        (add_nonneg hC (norm_nonneg _))
    nlinarith
  change (∑ u ∈ rows, rho u * ‖r u‖ ^ 2) ≤
    C ^ 2 * (∑ u ∈ rows, rho u)
  calc
    _ ≤ ∑ u ∈ rows, rho u * C ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hsq u hu) (hrho u hu)
    _ = ∑ u ∈ rows, C ^ 2 * rho u := by
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = C ^ 2 * (∑ u ∈ rows, rho u) := by
      rw [Finset.mul_sum]

/-! ## Source-exact three-tier algebra; no projected phase cancellation -/

/-- Algebraically exact reassembly of the original marked factor.
    In particular the marked correction is NOT -V and the source
    retains the original R and K*V interactions. -/
theorem oai_actual_marked_factor_plus_D_exact
    (R V qInv K W D : ℂ)
    (hV : 1 - V ≠ 0) (hR : 1 - R ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * (1 - qInv + (1 - V) * (W - D)) - K * V) /
        ((1 - V) * (1 - R)) := by
  unfold markedFactor
  field_simp
  ring

/-- Exact original ProbeLocal compensation split BEFORE estimating any
    norms. These three sums ARE REAL SOURCE ALGEBRAIC TERMS, whereas
    BR=B*R and BKV=B*K*V alone are only pieces of their envelopes.

    D-tier retains (vInv-q) and the V,D rational term.
    BR-tier has the full original marked R correction.
    BKV-tier retains the actual (B+vInv-q) multiplier.
    Every denominator and scalar phase remains visible. -/
theorem oai_actual_one_prime_exact_three_tier
    (R V qInv K W D B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hR : 1 - R ≠ 0)
    (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D
        (markedFactor R V qInv K (-D + W * R) 1) B q +
      continuedCorrection V W D
        (markedFactor R V qInv K (-D + W * R) 1) * vInv =
      ((1 - V) * (1 - W) / (1 - D)) *
          (vInv - q) * (V / (1 - V) - D) +
      ((1 - W) / (1 - D)) * (B + vInv - q) *
          R * (1 - qInv + (1 - V) * (W - D)) / (1 - R) -
      ((1 - W) / (1 - D)) * (B + vInv - q) *
          (K * V) / (1 - R) := by
  have hid := continued_normalized_cancellation V W D
    (markedFactor R V qInv K (-D + W * R) 1)
    B q vInv hV hD hBD hvW
  rw [hid, oai_actual_marked_factor_plus_D_exact R V qInv K W D hV hR]
  field_simp
  ring

/-- The *actual* BR coordinate has 2.415 powers of prime-ideal norm,
    strictly better than the formerly flattened 7/8 exponent. -/
theorem oai_actual_BR_source_bound
    (Q : ℝ) (A eta x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1)
    (hx : (7 / 8 : ℝ) ≤ x.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖(star eta * (Q : ℂ) ^ x) * coordR Q A x z‖ ≤
      Q ^ (-(483 / 200 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB :
      ‖star eta * (Q : ℂ) ^ x‖ ≤ Q ^ x.re := by
    rw [norm_mul, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hQ0,
      heta, one_mul]
  have hR :
      ‖coordR Q A x z‖ ≤ Q ^ (4 - 6 * x.re - 6 * z.re) :=
    coordR_norm_le Q hQ0 A x z hA
  calc
    ‖(star eta * (Q : ℂ) ^ x) * coordR Q A x z‖ =
      ‖star eta * (Q : ℂ) ^ x‖ * ‖coordR Q A x z‖ :=
        norm_mul _ _
    _ ≤ Q ^ x.re * Q ^ (4 - 6 * x.re - 6 * z.re) :=
      mul_le_mul hB hR (norm_nonneg _)
        (Real.rpow_nonneg hQ0.le _)
    _ = Q ^ (4 - 5 * x.re - 6 * z.re) := by
      rw [← Real.rpow_add hQ0]
      congr 1
      ring
    _ ≤ Q ^ (-(483 / 200 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)

/-- The *actual* BKV coordinate retains exactly the original contour
    exponent 1 - Re(w) - 6*Re(z), with NO a priori sextic gain. -/
theorem oai_actual_BKV_source_bound
    (Q : ℝ) (eta x w z : ℂ)
    (hQ : 4 ≤ Q) (heta : ‖eta‖ = 1) :
    ‖(star eta * (Q : ℂ) ^ x) * coordK Q eta x w *
        coordV Q z‖ ≤ Q ^ (1 - w.re - 6 * z.re) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB :
      ‖star eta * (Q : ℂ) ^ x‖ ≤ Q ^ x.re := by
    rw [norm_mul, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hQ0,
      heta, one_mul]
  have hK :
      ‖coordK Q eta x w‖ ≤ Q ^ (1 - x.re - w.re) :=
    coordK_norm_le Q hQ1 eta x w heta.le
  have hV : ‖coordV Q z‖ = Q ^ (-6 * z.re) :=
    coordV_norm Q hQ0 z
  have hBK :
      ‖star eta * (Q : ℂ) ^ x‖ * ‖coordK Q eta x w‖ ≤
        Q ^ (1 - w.re) := by
    calc
      _ ≤ Q ^ x.re * Q ^ (1 - x.re - w.re) :=
        mul_le_mul hB hK (norm_nonneg _)
          (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (1 - w.re) := by
        rw [← Real.rpow_add hQ0]
        congr 1
        ring
  calc
    ‖(star eta * (Q : ℂ) ^ x) * coordK Q eta x w *
        coordV Q z‖ =
      (‖star eta * (Q : ℂ) ^ x‖ * ‖coordK Q eta x w‖) *
        ‖coordV Q z‖ := by rw [norm_mul, norm_mul]
    _ ≤ Q ^ (1 - w.re) * Q ^ (-6 * z.re) := by
      rw [hV]
      exact mul_le_mul_of_nonneg_right hBK
        (Real.rpow_nonneg hQ0.le _)
    _ = Q ^ (1 - w.re - 6 * z.re) := by
      rw [← Real.rpow_add hQ0]
      congr 1
      ring

/-- Thus the BKV leading source envelope has -1.04 exponent at w>=0.
    This by itself DOES NOT pay the full BKV tier prefactor or cross
    correlations; that is the exact extraction obligation above. -/
theorem oai_actual_BKV_source_contour_power
    (Q : ℝ) (eta x w z : ℂ)
    (hQ : 4 ≤ Q) (heta : ‖eta‖ = 1)
    (hw : 0 ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖(star eta * (Q : ℂ) ^ x) * coordK Q eta x w *
        coordV Q z‖ ≤ Q ^ (-(26 / 25 : ℝ)) := by
  have hQ1 : 1 ≤ Q := by linarith
  exact (oai_actual_BKV_source_bound Q eta x w z hQ heta).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))

/-- The leading B*K*V algebraic product has NO sextic ROW dependence:
    eta has canceled against conjugate eta; V itself has no row phase.
    This constant-phase part cannot be fed into a nonprincipal
    character-moment saving without further signed cancellation. -/
theorem oai_actual_BKV_leading_phase_free
    (Q : ℝ) (eta x w z : ℂ)
    (hQ : 0 < Q) (heta : ‖eta‖ = 1) :
    (star eta * (Q : ℂ) ^ x) * coordK Q eta x w *
        coordV Q z =
      ((Q - 1 : ℝ) : ℂ) * (Q : ℂ) ^ (-w) * coordV Q z := by
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hpow :
      (Q : ℂ) ^ x * (Q : ℂ) ^ (-x - w) =
        (Q : ℂ) ^ (-w) := by
    calc
      _ = (Q : ℂ) ^ (x + (-x - w)) :=
        (Complex.cpow_add _ _ hQne).symm
      _ = (Q : ℂ) ^ (-w) := by congr 1; ring
  have hunit : star eta * eta = 1 :=
    PrincipalSlotEstimate.unit_phase_inverse eta heta
  have hQcast : ((Q - 1 : ℝ) : ℂ) = (Q : ℂ) - 1 := by
    push_cast
    ring
  unfold coordK
  rw [hQcast]
  calc
    (star eta * (Q : ℂ) ^ x) *
        (eta * ((Q : ℂ) - 1) * (Q : ℂ) ^ (-x - w)) *
        coordV Q z =
      (star eta * eta) * ((Q : ℂ) - 1) *
        ((Q : ℂ) ^ x * (Q : ℂ) ^ (-x - w)) *
        coordV Q z := by ring
    _ = ((Q : ℂ) - 1) * (Q : ℂ) ^ (-w) *
        coordV Q z := by rw [hunit, hpow]; ring

end SevenEighths.ProbeEuler

end

#print axioms SevenEighths.ProbeEuler.oai_one_prime_actual_marked_error_power
#print axioms SevenEighths.ProbeEuler.oai_one_prime_unramified_compensated_power_gain
#print axioms SevenEighths.ProbeEuler.oai_one_prime_physical_central_contour_power_gain

#print axioms SevenEighths.ProbeEuler.oai_one_prime_compensated_source_contour_rate
#print axioms SevenEighths.ProbeEuler.oai_one_prime_compensated_weighted_l2_rate
#print axioms SevenEighths.ProbeEuler.oai_actual_marked_factor_plus_D_exact
#print axioms SevenEighths.ProbeEuler.oai_actual_one_prime_exact_three_tier
#print axioms SevenEighths.ProbeEuler.oai_actual_BR_source_bound
#print axioms SevenEighths.ProbeEuler.oai_actual_BKV_source_bound
#print axioms SevenEighths.ProbeEuler.oai_actual_BKV_source_contour_power
#print axioms SevenEighths.ProbeEuler.oai_actual_BKV_leading_phase_free

end OAI
