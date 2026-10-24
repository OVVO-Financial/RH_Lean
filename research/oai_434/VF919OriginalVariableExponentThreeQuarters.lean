import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified
import OAI.NumberTheory.DirichletL.PrimeRows.CentralSlots

/-!
# Original OAI local exponent down to 51/100; actual a=3/4 contour

The upstream local compensated prime estimate uses the true
unramifiedMarked profile, norm Q, row character, eta phase, and B=conj(eta)Q^x.
Its algebra is not restricted to a=7/8. Here we retain every Q exponent and
parameterize the saving on a in [51/100,1], assuming Re x>=a, Re w>=0,
Re z>=17/50 and the actual unit/source masks.

This is a genuine stronger pointwise original-source statement.
It is NOT a 3/4 global zeta theorem; there is no inference from this local
estimate to the Gaussian/Mellin detector or the de Faveri character family.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.ProbeEuler
open ProbeLocal

/-- Sharp one-prime SOURCE estimate for the ACTUAL marked profile, where
    Pstar is unramifiedMarked (not -V), D is coordD, and the giant
    multiplier B=star eta*Q^x is retained. -/
theorem oai_variable_a_actual_marked_error_power
    (Q a : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (ha : (51 / 100 : ℝ) ≤ a)
    (haTop : a ≤ 1)
    (hx : a ≤ x.re)
    (hw : (0 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖unramifiedMarked Q A eta v x w z + coordD Q eta v x‖ ≤
        28 * Q ^ (-a) ∧
    ‖star eta * (Q : ℂ) ^ x‖ *
      ‖unramifiedMarked Q A eta v x w z + coordD Q eta v x‖ ≤
        28 * Q ^ (-a) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta * (Q : ℂ) ^ x
  let P := unramifiedMarked Q A eta v x w z
  let T : ℝ := Q ^ (-a)
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
theorem oai_variable_a_unramified_compensated_power_gain
    (Q a : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (ha : (51 / 100 : ℝ) ≤ a)
    (haTop : a ≤ 1)
    (hx : a ≤ x.re)
    (hw : (0 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖unramifiedSelected Q A eta v x w z +
        unramifiedClosed Q A eta v x w z * star v‖ ≤
      720 * Q ^ (-a) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let P := unramifiedMarked Q A eta v x w z
  let B := star eta * (Q : ℂ) ^ x
  let q := (Q : ℂ) ^ (-w)
  let vInv := star v
  let T : ℝ := Q ^ (-a)
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
  have hP := oai_variable_a_actual_marked_error_power Q a A eta v x w z
    hQ hA heta hv ha haTop hx hw hz
  have hphase := selected_phase_identities Q eta v x w
    hQ0 heta hv
  have hh := compensated_phase_error_bound V W D P B q vInv T
    (Real.rpow_nonneg hQ0.le _) hV hW hD hq
    hVT hDT hP.1 hP.2 (by change ‖star v‖ ≤ 1; rw [norm_star, hv])
    hphase.1 hphase.2
  change ‖compensatedReplacement V W D P B q +
    continuedCorrection V W D P * vInv‖ ≤ 720 * T
  exact hh


/-- Original central contour, with a left variable a rather than
hardwiring 7/8. All parameters are the ACTUAL x,w,z coordinates. -/
theorem oai_variable_a_physical_contour_rate
    (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (ha : (51 / 100 : ℝ) ≤ a)
    (haTop : a ≤ 1) (hae : a + 6 * e ≤ 1) (he : 0 ≤ e)
    (hx : x.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) :
    ‖unramifiedSelected Q A eta v x w z +
      unramifiedClosed Q A eta v x w z * star v‖ ≤
      720 * Q ^ (-a) := by
  apply oai_variable_a_unramified_compensated_power_gain
    Q a A eta v x w z hQ hA heta hv ha haTop
  · rw [hx]
    linarith
  · rw [hw]
    linarith
  · rw [hz]

/-- Concrete central a=3/4 gives Q^(-3/4) before any prime summation. -/
theorem oai_three_quarters_original_contour_rate
    (Q e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1)
    (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (he : 0 ≤ e) (heMax : e ≤ 1 / 1000)
    (hx : x.re = (3 / 4 : ℝ) + 16 * e)
    (hw : w.re = (1 / 4 : ℝ) - 6 * e)
    (hz : z.re = 17 / 50) :
    ‖unramifiedSelected Q A eta v x w z +
      unramifiedClosed Q A eta v x w z * star v‖ ≤
      720 * Q ^ (-(3 / 4 : ℝ)) := by
  apply oai_variable_a_physical_contour_rate
    Q (3 / 4) e A eta v x w z hQ hA heta hv
  · norm_num
  · norm_num
  · linarith
  · exact he
  · exact hx
  · convert hw using 1
    ring
  · exact hz

end SevenEighths.ProbeEuler

namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

/-- A REAL OpenAI high prime/FreeRow specialization at a=3/4. The
physical Supported/coprimality/conductor masks and sextic residue are
unchanged from actual_central_unramified_error. No hypothetical atom. -/
theorem actual_central_unramified_three_quarters
    (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val ∣ Ideal.span {u.val})
    (hη : IsCoprime P.val η.modulus)
    (e : ℝ) (x w z : ℂ)
    (hQ : (4 : ℝ) ≤ P.val.absNorm)
    (he : 0 < e) (he1 : e ≤ 1 / 1000)
    (hx : x.re = (3 / 4 : ℝ) + 16 * e)
    (hw : w.re = (1 / 4 : ℝ) - 6 * e)
    (hz : z.re = 17 / 50) :
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val) * (P.val.absNorm : ℂ) ^ x)
        ((P.val.absNorm : ℂ) ^ (-w)) +
      idealUnramifiedCorrection η u P x w z *
        star (idealRowHom u.val P.val)‖ ≤
        720 * (P.val.absNorm : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hQ0 : (0 : ℝ) < P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖ < 1 := by
    rw [coordV_norm _ hQ0]
    exact (rpow_le_half _ _ hQ (by rw [hz]; norm_num)).trans_lt (by norm_num)
  have hR :
      ‖coordR P.val.absNorm
        (actualAPhase η (primaryGenerator P.val)) x z‖ < 1 :=
    (coordR_norm_le _ hQ0 _ x z
      (actualAPhase_norm_le_one η _)).trans_lt
      ((rpow_le_half _ _ hQ (by rw [hx, hz]; linarith)).trans_lt
        (by norm_num))
  rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
  exact oai_three_quarters_original_contour_rate
    (P.val.absNorm : ℝ) e
    (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val)
    (idealRowHom u.val P.val) x w z
    hQ (actualAPhase_norm_le_one η _)
    (PrincipalSignalComparison.idealCoeff_norm_one_of_coprime
      η P.val P.property.ne_zero hη)
    (row_phase_norm_one_of_not_dvd u P hs hn)
    he.le he1 hx hw hz

end SevenEighths.ProbeHighRowFamily
end
end OAI

#print axioms OAI.SevenEighths.ProbeEuler.oai_variable_a_actual_marked_error_power
#print axioms OAI.SevenEighths.ProbeEuler.oai_variable_a_unramified_compensated_power_gain
#print axioms OAI.SevenEighths.ProbeEuler.oai_variable_a_physical_contour_rate
#print axioms OAI.SevenEighths.ProbeEuler.oai_three_quarters_original_contour_rate
#print axioms OAI.SevenEighths.ProbeHighRowFamily.actual_central_unramified_three_quarters
