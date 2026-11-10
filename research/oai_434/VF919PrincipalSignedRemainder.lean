import OAI.NumberTheory.DirichletL.PrincipalSlotEstimate

/-!
# Retain the signed principal-slot response

Claim 20261110-analytic-2/RD1, independently accepted in
20261110-referee-2/SR. This is the original principal slot, with its
`-eta * Q^(-s)` response retained. The result is local and uniform in height;
the finite product, same-signal Mellin response and complete return are
separate obligations. No global Mertens improvement is asserted here.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.PrincipalSlotEstimate
open ProbeEuler ProbeLocal

/-- The exact principal residue keeps the factor `Q - 1` in `coordK`. -/
theorem principal_K_signed {Q : ℝ} (hQ : 0 < Q) (eta s : ℂ) :
    coordK Q eta s 1 = (1 - (Q : ℂ)⁻¹) * coordD Q eta 1 s := by
  have hQc : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold coordK coordD
  simp only [star_one, mul_one]
  rw [show -s - 1 = -s + (-1 : ℂ) by ring,
    Complex.cpow_add _ _ hQc, Complex.cpow_neg_one]
  field_simp

/-- Recover the first signed correction before taking the absolute value.
The hypotheses and carrier are exactly those of the original slot estimate. -/
theorem principal_slot_signed_error {Q : ℝ} {A eta s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    ‖principalSlot Q A eta s + 1 + eta * (Q : ℂ) ^ (-s)‖ ≤
      12 * Q ^ (-(11 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQc : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  let q : ℂ := (Q : ℂ)⁻¹
  let R := coordR Q A s (1 / 6)
  let D := coordD Q eta 1 s
  let B := star eta * (Q : ℂ) ^ s
  let U := 1 - (q * R + (1 - q) * D)
  let T : ℝ := Q ^ (-(11 / 8 : ℝ))
  have hpow (a b : ℝ) (h : a ≤ b) : Q ^ a ≤ Q ^ b :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hqnorm : ‖q‖ = Q ^ (-1 : ℝ) := by
    simp only [q, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hQ0, Real.rpow_neg_one]
  have hqi : Q⁻¹ ≤ (1 / 4 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hQ0).mpr (by linarith)
  have hqquarter : ‖q‖ ≤ 1 / 4 := by
    rw [hqnorm, Real.rpow_neg_one]
    exact hqi
  have hq0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQ0.le
  have h1q : ‖1 - q‖ ≤ 1 := by
    change ‖(1 : ℂ) - (Q : ℂ)⁻¹‖ ≤ 1
    rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - Q⁻¹)]
    linarith
  have h2q : ‖2 * q - q ^ 2‖ ≤ 2 * Q ^ (-1 : ℝ) := by
    have hid : 2 * q - q ^ 2 = ((2 * Q⁻¹ - (Q⁻¹) ^ 2 : ℝ) : ℂ) := by
      simp [q]
    rw [hid, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith : 0 ≤ 2 * Q⁻¹ - (Q⁻¹) ^ 2), Real.rpow_neg_one]
    nlinarith [sq_nonneg (Q⁻¹)]
  have hR : ‖R‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖D‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 eta 1 s heta.le (by simp)
  have hB : ‖B‖ = Q ^ s.re := principal_B_norm hQ0 eta s heta
  have hRquarter : ‖R‖ ≤ 1 / 4 := by
    apply (hR.trans (hpow _ (-1) (by linarith))).trans
    simpa only [Real.rpow_neg_one] using hqi
  have hDquarter : ‖D‖ ≤ 1 / 4 := by
    apply (hD.trans (hpow _ (-(1 / 2)) (by linarith))).trans
    rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow, inv_eq_one_div]
    have hroot : (4 : ℝ) ≤ Real.sqrt Q :=
      (Real.le_sqrt (by norm_num) hQ0.le).mpr (by linarith)
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hQ0)).mpr (by linarith)
  have hsmall : ‖q * R + (1 - q) * D‖ ≤ 1 / 2 := by
    calc
      _ ≤ ‖q‖ * ‖R‖ + ‖1 - q‖ * ‖D‖ := by
        simpa only [norm_mul] using norm_add_le (q * R) ((1 - q) * D)
      _ ≤ (1 / 4 : ℝ) * (1 / 4) + 1 * (1 / 4) := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hU : U ≠ 0 := one_sub_ne_zero_of_norm_le_half _ hsmall
  have hUinv : ‖U⁻¹‖ ≤ 2 := inv_one_sub_norm_le_two _ hsmall
  have h1R : 1 - R ≠ 0 := one_sub_ne_zero_of_norm_le_half R (by linarith)
  have h1qn : 1 - q ≠ 0 := one_sub_ne_zero_of_norm_le_half q (by linarith)
  have hpqn : 1 + q ≠ 0 := by
    have h := one_sub_ne_zero_of_norm_le_half (-q) (by simpa using hqquarter.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))
    simpa using h
  have hmarked : principalMarked Q A eta s = (1 + q) * (R - D) / (1 - R) := by
    unfold principalMarked
    rw [principal_V, principal_W, principal_K_signed hQ0]
    change markedFactor R q q ((1 - q) * D) (-D + q * R) 1 = _
    unfold markedFactor
    simp only [pow_one]
    field_simp
    ring
  have hratio : principalSlot Q A eta s = (1 - q) * (B * R - 1) / U - q := by
    rw [principal_slot_eq_raw hQ hA heta.le hs, principalRawFactor,
      principal_V, principal_W, hmarked, Complex.cpow_neg_one]
    change B * ((1 + q) * (R - D) / (1 - R)) /
      localFactor q q ((1 + q) * (R - D) / (1 - R)) - q = _
    have hraw : localFactor q q ((1 + q) * (R - D) / (1 - R)) =
        (1 + q) * U / ((1 - q) * (1 - R)) := by
      unfold localFactor U
      field_simp
      ring
    rw [hraw]
    calc
      _ = (1 - q) * (B * R - B * D) / U - q := by field_simp
      _ = _ := by rw [show B * D = 1 from principal_coord_cancellation hQ0 eta s heta]
  have hid : principalSlot Q A eta s + 1 + D =
      ((1 - q) * (B * R) - q * (1 - q) * R + (2 * q - q ^ 2) * D -
        q * R * D - (1 - q) * D ^ 2) / U := by
    rw [hratio]
    apply (eq_div_iff hU).mpr
    rw [add_mul, add_mul, sub_mul, div_mul_cancel₀ _ hU]
    dsimp only [U]
    ring
  have hBR : ‖B * R‖ ≤ T := by
    rw [norm_mul, hB]
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by gcongr
      _ = Q ^ (s.re + (3 - 6 * s.re)) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := hpow _ _ (by linarith)
  have hqR : ‖q‖ * ‖R‖ ≤ T := by
    rw [hqnorm]
    calc
      _ ≤ Q ^ (-1 : ℝ) * Q ^ (3 - 6 * s.re) := by gcongr
      _ = Q ^ ((-1 : ℝ) + (3 - 6 * s.re)) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := hpow _ _ (by linarith)
  have hqD : Q ^ (-1 : ℝ) * ‖D‖ ≤ T := by
    calc
      _ ≤ Q ^ (-1 : ℝ) * Q ^ (-s.re) := by gcongr
      _ = Q ^ ((-1 : ℝ) + -s.re) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := hpow _ _ (by linarith)
  have hqRD : ‖q * R * D‖ ≤ T := by
    rw [norm_mul, norm_mul, hqnorm]
    calc
      _ ≤ Q ^ (-1 : ℝ) * Q ^ (3 - 6 * s.re) * Q ^ (-s.re) := by gcongr
      _ = Q ^ ((-1 : ℝ) + (3 - 6 * s.re) + -s.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
      _ ≤ T := hpow _ _ (by linarith)
  have hDD : ‖D ^ 2‖ ≤ T := by
    rw [pow_two, norm_mul]
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-s.re) := by gcongr
      _ = Q ^ (-s.re + -s.re) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := hpow _ _ (by linarith)
  have hn : ‖(1 - q) * (B * R) - q * (1 - q) * R +
      (2 * q - q ^ 2) * D - q * R * D - (1 - q) * D ^ 2‖ ≤ 6 * T := by
    have hn1 : ‖(1 - q) * (B * R)‖ ≤ T := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right h1q (norm_nonneg _)).trans (by simpa using hBR)
    have hn2 : ‖q * (1 - q) * R‖ ≤ T := by
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖q‖ * 1 * ‖R‖ := by gcongr
        _ ≤ T := by simpa using hqR
    have hn3 : ‖(2 * q - q ^ 2) * D‖ ≤ 2 * T := by
      rw [norm_mul]
      calc
        _ ≤ (2 * Q ^ (-1 : ℝ)) * ‖D‖ := by gcongr
        _ ≤ 2 * T := by nlinarith
    have hn5 : ‖(1 - q) * D ^ 2‖ ≤ T := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right h1q (norm_nonneg _)).trans (by simpa using hDD)
    calc
      _ ≤ ‖(1 - q) * (B * R) - q * (1 - q) * R + (2 * q - q ^ 2) * D - q * R * D‖ +
          ‖(1 - q) * D ^ 2‖ := norm_sub_le _ _
      _ ≤ (‖(1 - q) * (B * R) - q * (1 - q) * R + (2 * q - q ^ 2) * D‖ +
          ‖q * R * D‖) + ‖(1 - q) * D ^ 2‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖(1 - q) * (B * R) - q * (1 - q) * R‖ + ‖(2 * q - q ^ 2) * D‖) +
          ‖q * R * D‖) + ‖(1 - q) * D ^ 2‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (((‖(1 - q) * (B * R)‖ + ‖q * (1 - q) * R‖) + ‖(2 * q - q ^ 2) * D‖) +
          ‖q * R * D‖) + ‖(1 - q) * D ^ 2‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ 6 * T := by linarith
  have hDident : D = eta * (Q : ℂ) ^ (-s) := by simp [D, coordD]
  rw [← hDident, hid, div_eq_mul_inv, norm_mul]
  exact (mul_le_mul hn hUinv (norm_nonneg _) (by dsimp [T]; positivity)).trans_eq (by ring)

/-- The original genuine ideal coefficient, without a surrogate phase. -/
theorem actual_principal_slot_signed_error (eta : HeckeFamily.Character)
    (p : HeckeFamily.O) (hp : IsUnit (Ideal.Quotient.mk eta.modulus p))
    (s : ℂ) (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hs : 7 / 8 ≤ s.re) :
    ‖principalSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
        (HeckeFamily.elementCoeff eta p) s + 1 +
      HeckeFamily.elementCoeff eta p * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-s)‖ ≤
      12 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(11 / 8 : ℝ)) :=
  principal_slot_signed_error hQ (actualAPhase_norm_le_one eta p)
    (actual_target_norm eta p hp) hs

/-- Preserve an arbitrary original nonnegative slot mask and all signed responses. -/
theorem weighted_principal_slot_signed_error {i : Type*} (S : Finset i)
    (w Q : i → ℝ) (A eta : i → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ j ∈ S, 0 ≤ w j) (hQ : ∀ j ∈ S, P ≤ Q j)
    (hA : ∀ j ∈ S, ‖A j‖ ≤ 1) (heta : ∀ j ∈ S, ‖eta j‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    ‖(∑ j ∈ S, (w j : ℂ) * principalSlot (Q j) (A j) (eta j) s) +
        (∑ j ∈ S, w j : ℝ) +
        ∑ j ∈ S, (w j : ℂ) * eta j * (Q j : ℂ) ^ (-s)‖ ≤
      (12 * P ^ (-(11 / 8 : ℝ))) * ∑ j ∈ S, w j := by
  have hid : (∑ j ∈ S, (w j : ℂ) * principalSlot (Q j) (A j) (eta j) s) +
      (∑ j ∈ S, w j : ℝ) + ∑ j ∈ S, (w j : ℂ) * eta j * (Q j : ℂ) ^ (-s) =
      ∑ j ∈ S, (w j : ℂ) *
        (principalSlot (Q j) (A j) (eta j) s + 1 + eta j * (Q j : ℂ) ^ (-s)) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, Complex.ofReal_sum, mul_assoc]
  rw [hid]
  calc
    _ ≤ ∑ j ∈ S, ‖(w j : ℂ) *
        (principalSlot (Q j) (A j) (eta j) s + 1 + eta j * (Q j : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ S, (12 * P ^ (-(11 / 8 : ℝ))) * w j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j hj)]
      have he := principal_slot_signed_error (hP.trans (hQ j hj)) (hA j hj) (heta j hj) hs
      have ht : ‖principalSlot (Q j) (A j) (eta j) s + 1 + eta j * (Q j : ℂ) ^ (-s)‖ ≤
          12 * P ^ (-(11 / 8 : ℝ)) := he.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
          (by linarith) (hQ j hj) (by norm_num)) (by norm_num))
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left ht (hw j hj)
    _ = _ := by rw [Finset.mul_sum]

/-- The original negative normalizer turns the retained correction into a
PLUS response. No outer-scale weights are changed. -/
theorem weighted_principal_slot_signed_relative_error {i : Type*} (S : Finset i)
    (w Q : i → ℝ) (A eta : i → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ j ∈ S, 0 ≤ w j) (hQ : ∀ j ∈ S, P ≤ Q j)
    (hA : ∀ j ∈ S, ‖A j‖ ≤ 1) (heta : ∀ j ∈ S, ‖eta j‖ = 1)
    (hs : 7 / 8 ≤ s.re) (hM : 0 < ∑ j ∈ S, w j) :
    ‖(∑ j ∈ S, (w j : ℂ) * principalSlot (Q j) (A j) (eta j) s) /
          (-(∑ j ∈ S, w j : ℝ) : ℂ) - 1 -
        (∑ j ∈ S, (w j : ℂ) * eta j * (Q j : ℂ) ^ (-s)) /
          (∑ j ∈ S, w j : ℝ)‖ ≤ 12 * P ^ (-(11 / 8 : ℝ)) := by
  have hMc : ((∑ j ∈ S, w j : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hM.ne'
  have hid :
      (∑ j ∈ S, (w j : ℂ) * principalSlot (Q j) (A j) (eta j) s) /
          (-(∑ j ∈ S, w j : ℝ) : ℂ) - 1 -
        (∑ j ∈ S, (w j : ℂ) * eta j * (Q j : ℂ) ^ (-s)) /
          (∑ j ∈ S, w j : ℝ) =
      -((∑ j ∈ S, (w j : ℂ) * principalSlot (Q j) (A j) (eta j) s) +
          (∑ j ∈ S, w j : ℝ) +
          ∑ j ∈ S, (w j : ℂ) * eta j * (Q j : ℂ) ^ (-s)) /
        (∑ j ∈ S, w j : ℝ) := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  exact (div_le_iff₀ hM).mpr
    (weighted_principal_slot_signed_error S w Q A eta s P hP hw hQ hA heta hs)

end SevenEighths.PrincipalSlotEstimate
end
end OAI
