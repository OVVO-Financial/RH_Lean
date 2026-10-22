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
      dsimp [T]
      linarith))
  have hKV : ‖K‖ * ‖V‖ ≤ T := by
    have hVle : ‖V‖ ≤ Q ^ (-6 * z.re) := hV.le
    exact hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      hK hVle (by dsimp [T]; linarith)
  have hBR : ‖B‖ * ‖R‖ ≤ T :=
    hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      hB hR (by dsimp [T]; linarith)
  have hKVpow :
      ‖K‖ * ‖V‖ ≤ Q ^ (1 - x.re - w.re - 6 * z.re) := by
    exact hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
      hK hV.le (by ring)
  have hBKV : ‖B‖ * (‖K‖ * ‖V‖) ≤ T :=
    hprod _ _ _ _ _ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      hB hKVpow (by dsimp [T]; linarith)
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
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [T]; linarith)
  have hDT : ‖D‖ ≤ T :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [T]; linarith))
  have hP := oai_one_prime_actual_marked_error_power Q A eta v x w z
    hQ hA heta hv hx hw hz
  have hphase := selected_phase_identities Q eta v x w
    hQ0 heta hv
  have hh := compensated_phase_error_bound V W D P B q vInv T
    (Real.rpow_nonneg hQ0.le _) hV hW hD hq
    hVT hDT hP.1 hP.2 (by dsimp [vInv]; rw [norm_star, hv])
    hphase.1 hphase.2
  simpa only [unramifiedSelected, unramifiedClosed, unramifiedMarked]
    using hh


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


end SevenEighths.ProbeEuler

end

#print axioms SevenEighths.ProbeEuler.oai_one_prime_actual_marked_error_power
#print axioms SevenEighths.ProbeEuler.oai_one_prime_unramified_compensated_power_gain
#print axioms SevenEighths.ProbeEuler.oai_one_prime_physical_central_contour_power_gain

end OAI
