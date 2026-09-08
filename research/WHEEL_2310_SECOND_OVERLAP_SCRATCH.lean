import RHLean.Proof.PostRootCovarianceWheelCounting

/-!
# Second 2310 overlap scratch

The first 2310 estimate cancels the overlap between the negative 11-child of
the top band and the positive 15-band.  A second opposite-sign overlap remains:

* `+(B/154,B/77]`,
* `-(B/210,B/105]`.

Their common interval `(B/154,B/105]` cancels exactly.  This scratch checks the
resulting full 2310 identity and the corresponding finite counting coefficient
before promoting it into the main proof module.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

set_option maxRecDepth 10000 in
private theorem roughWheelResidues_card_2310_secondScratch :
    (roughWheelResidues 2310).card = 480 := by
  decide

/-- Both opposite-sign overlaps visible at wheel 2310 have now been removed
before taking any absolute value. -/
theorem roughMertens_one_eq_2310Wheel_twoOverlapsCancelled (B : ℕ) :
    roughMertens 1 B =
      roughInterval 2310 (B / 2) B
      - roughInterval 2310 (B / 15) (B / 11)
      - roughInterval 2310 (B / 14) (B / 7)
      + roughInterval 2310 (B / 105) (B / 77)
      - roughInterval 2310 (B / 10) (B / 5)
      + roughInterval 2310 (B / 110) (B / 55)
      + roughInterval 2310 (B / 70) (B / 35)
      - roughInterval 2310 (B / 770) (B / 385)
      - roughInterval 2310 (B / 6) (B / 3)
      + roughInterval 2310 (B / 66) (B / 33)
      + roughInterval 2310 (B / 42) (B / 21)
      - roughInterval 2310 (B / 462) (B / 231)
      + roughInterval 2310 (B / 30) (B / 22)
      - roughInterval 2310 (B / 330) (B / 165)
      - roughInterval 2310 (B / 210) (B / 154)
      + roughInterval 2310 (B / 2310) (B / 1155) := by
  rw [roughMertens_one_eq_2310Wheel_overlapCancelled]
  unfold roughInterval
  ring

/-- Counting only after both opposite-sign overlaps are cancelled lowers the
2310 leading coefficient from `17648/88935` to `17536/88935`. -/
theorem abs_realMertensLength_succ_le_2310Wheel_twoOverlaps (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (17536 / 88935 : ℝ) * B + 15364 := by
  have h0 := abs_roughInterval_le_density (W := 2310)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h0
  norm_num at h0
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  have h1 := abs_roughInterval_le_density (W := 2310)
    (a := B / 15) (b := B / 11) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h1
  norm_num at h1
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  have h2 := abs_roughInterval_le_density (W := 2310)
    (a := B / 14) (b := B / 7) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h2
  norm_num at h2
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  have h3 := abs_roughInterval_le_density (W := 2310)
    (a := B / 105) (b := B / 77) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h3
  norm_num at h3
  obtain ⟨h3lo, h3hi⟩ := abs_le.mp h3
  have h4 := abs_roughInterval_le_density (W := 2310)
    (a := B / 10) (b := B / 5) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h4
  norm_num at h4
  obtain ⟨h4lo, h4hi⟩ := abs_le.mp h4
  have h5 := abs_roughInterval_le_density (W := 2310)
    (a := B / 110) (b := B / 55) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h5
  norm_num at h5
  obtain ⟨h5lo, h5hi⟩ := abs_le.mp h5
  have h6 := abs_roughInterval_le_density (W := 2310)
    (a := B / 70) (b := B / 35) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h6
  norm_num at h6
  obtain ⟨h6lo, h6hi⟩ := abs_le.mp h6
  have h7 := abs_roughInterval_le_density (W := 2310)
    (a := B / 770) (b := B / 385) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h7
  norm_num at h7
  obtain ⟨h7lo, h7hi⟩ := abs_le.mp h7
  have h8 := abs_roughInterval_le_density (W := 2310)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h8
  norm_num at h8
  obtain ⟨h8lo, h8hi⟩ := abs_le.mp h8
  have h9 := abs_roughInterval_le_density (W := 2310)
    (a := B / 66) (b := B / 33) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h9
  norm_num at h9
  obtain ⟨h9lo, h9hi⟩ := abs_le.mp h9
  have h10 := abs_roughInterval_le_density (W := 2310)
    (a := B / 42) (b := B / 21) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h10
  norm_num at h10
  obtain ⟨h10lo, h10hi⟩ := abs_le.mp h10
  have h11 := abs_roughInterval_le_density (W := 2310)
    (a := B / 462) (b := B / 231) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h11
  norm_num at h11
  obtain ⟨h11lo, h11hi⟩ := abs_le.mp h11
  have h12 := abs_roughInterval_le_density (W := 2310)
    (a := B / 30) (b := B / 22) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h12
  norm_num at h12
  obtain ⟨h12lo, h12hi⟩ := abs_le.mp h12
  have h13 := abs_roughInterval_le_density (W := 2310)
    (a := B / 330) (b := B / 165) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h13
  norm_num at h13
  obtain ⟨h13lo, h13hi⟩ := abs_le.mp h13
  have h14 := abs_roughInterval_le_density (W := 2310)
    (a := B / 210) (b := B / 154) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h14
  norm_num at h14
  obtain ⟨h14lo, h14hi⟩ := abs_le.mp h14
  have h15 := abs_roughInterval_le_density (W := 2310)
    (a := B / 2310) (b := B / 1155) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310_secondScratch] at h15
  norm_num at h15
  obtain ⟨h15lo, h15hi⟩ := abs_le.mp h15
  have hwidthNat :
      1155 * (B + B / 11 + B / 7 + B / 77 + B / 5 + B / 55 +
        B / 35 + B / 385 + B / 3 + B / 33 + B / 21 + B / 231 +
        B / 22 + B / 165 + B / 154 + B / 1155) ≤
      1096 * B + 1155 * (B / 2 + B / 15 + B / 14 + B / 105 +
        B / 10 + B / 110 + B / 70 + B / 770 + B / 6 + B / 66 +
        B / 42 + B / 462 + B / 30 + B / 330 + B / 210 + B / 2310) +
        18480 := by
    omega
  have hwidth :
      (1155 : ℝ) * ((B : ℝ) +
        ((B / 11 : ℕ) : ℝ) +
        ((B / 7 : ℕ) : ℝ) +
        ((B / 77 : ℕ) : ℝ) +
        ((B / 5 : ℕ) : ℝ) +
        ((B / 55 : ℕ) : ℝ) +
        ((B / 35 : ℕ) : ℝ) +
        ((B / 385 : ℕ) : ℝ) +
        ((B / 3 : ℕ) : ℝ) +
        ((B / 33 : ℕ) : ℝ) +
        ((B / 21 : ℕ) : ℝ) +
        ((B / 231 : ℕ) : ℝ) +
        ((B / 22 : ℕ) : ℝ) +
        ((B / 165 : ℕ) : ℝ) +
        ((B / 154 : ℕ) : ℝ) +
        ((B / 1155 : ℕ) : ℝ)) ≤
      1096 * (B : ℝ) + 1155 * (
        ((B / 2 : ℕ) : ℝ) +
        ((B / 15 : ℕ) : ℝ) +
        ((B / 14 : ℕ) : ℝ) +
        ((B / 105 : ℕ) : ℝ) +
        ((B / 10 : ℕ) : ℝ) +
        ((B / 110 : ℕ) : ℝ) +
        ((B / 70 : ℕ) : ℝ) +
        ((B / 770 : ℕ) : ℝ) +
        ((B / 6 : ℕ) : ℝ) +
        ((B / 66 : ℕ) : ℝ) +
        ((B / 42 : ℕ) : ℝ) +
        ((B / 462 : ℕ) : ℝ) +
        ((B / 30 : ℕ) : ℝ) +
        ((B / 330 : ℕ) : ℝ) +
        ((B / 210 : ℕ) : ℝ) +
        ((B / 2310 : ℕ) : ℝ)) + 18480 := by
    exact_mod_cast hwidthNat
  rw [realMertensLength_succ_eq_roughMertens_one,
    roughMertens_one_eq_2310Wheel_twoOverlapsCancelled]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The second-overlap gain transfers unchanged to the exact post-root Bessel
remainder majorant. -/
theorem postRootCovarianceRemainder_le_2310Wheel_twoOverlapsSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((17536 / 88935 : ℝ) * W + 15364) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_2310Wheel_twoOverlaps W)

end RHLean.Proof
