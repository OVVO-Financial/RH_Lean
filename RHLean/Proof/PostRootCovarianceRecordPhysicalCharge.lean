import RHLean.Proof.PostRootCovarianceRecordSquareChargeClosure

/-!
# Charge post-root records to the physical square step

The cumulative square gap of #601 can be reduced further. At an active high
record, put `u = mu(c)`, `x = M(W+1)`, and `y = M(c)`. The outer row is
`r = -u * (x+y) > 0`, and #601 proves `r <= x^2-y^2`. Since `u^2 = 1`,

`x^2-y^2 = r * u * (y-x)`.

Cancelling the positive row gives `1 <= u * (y-x)`, which is exactly the
inequality needed for

`r <= x^2-(x+u)^2 = Delta M^2(W+1)`.

Thus the charge no longer spans the interval from the cofactor to the physical
endpoint. Each non-wall record charges only its own positive physical square
step. The finite-horizon bound retains the record indicator and the explicit
prime-square departures.

This removes overlap between prefix intervals, but it does not prove summable
record-selected positive variation. Distinct outward steps can revisit the
same square levels after intervening decreases. No global exponent improvement
or unconditional terminal criterion is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- A positive unit-signed row already charged to a square gap can be charged
to the physical one-step square increment. -/
private theorem signed_sum_le_physical_square_step
    {u x y : ℝ} (hu : u ^ 2 = 1)
    (hrow : 0 < -u * (x + y))
    (hcharge : -u * (x + y) ≤ x ^ 2 - y ^ 2) :
    -u * (x + y) ≤ x ^ 2 - (x + u) ^ 2 := by
  have hfactor :
      (-u * (x + y)) * (u * (y - x)) = x ^ 2 - y ^ 2 := by
    calc
      (-u * (x + y)) * (u * (y - x)) = u ^ 2 * (x ^ 2 - y ^ 2) := by ring
      _ = x ^ 2 - y ^ 2 := by rw [hu, one_mul]
  have hmul :
      (-u * (x + y)) * 1 ≤ (-u * (x + y)) * (u * (y - x)) := by
    simpa only [mul_one, hfactor] using hcharge
  have hunit : 1 ≤ u * (y - x) := (mul_le_mul_iff_right₀ hrow).mp hmul
  nlinarith

/-- **Physical square-step charge.** At an active high record, the outer row
is at most the single physical Mertens-square increment, improving the
cumulative cofactor-to-endpoint gap of #601. -/
theorem postRootRecordOuterRowNumerator_le_physicalSquareStep
    (ε : ℝ) (hε : 0 ≤ ε) {W p : ℕ} (hW : 2 ≤ W)
    (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W ≤
      realMertensSquareStep (W + 1) := by
  let c := (W + 1) / p
  have hpRoot := (mem_postRootPrimeFamilySet.mp hmem).1
  have hc : c < p :=
    (Nat.div_lt_iff_lt_mul hp.pos).2 ((Nat.sqrt_lt).1 hpRoot)
  have hmul : p * c = W + 1 := Nat.mul_div_cancel' hdvd
  have hmu : realMoebiusStep (W + 1) = -realMoebiusStep c := by
    rw [← hmul, realMoebiusStep_prime_mul_of_lt hp hc]
  have hphys := realMertensLength_succ (W + 1)
  have hlow := realMertensLength_succ c
  have hW2 : W + 1 + 1 = W + 2 := by omega
  rw [hW2, hmu] at hphys
  have hsum :
      realMertensLength (W + 1) + realMertensLength c =
        realMertensLength (W + 2) + realMertensLength (c + 1) := by
    rw [hphys, hlow]
    ring
  have houterEq :
      realMoebiusStep (W + 1) * realMertensLength (W + 1) -
          postRootPrimeFamilyCovarianceRowTotal W =
        -realMoebiusStep c *
          (realMertensLength (W + 2) + realMertensLength (c + 1)) := by
    have h := postRootRecordOuterRowNumerator_eq_complementaryPrefix hp hmem hdvd
    change _ = -realMoebiusStep c *
      (realMertensLength (W + 1) + realMertensLength c) at h
    rw [hsum] at h
    exact h
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hW hrec
  rw [postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor
    hp hmem hdvd] at hthr
  have hleft :
      0 ≤ postRootCovariancePowerEnvelope ε (W + 1) *
        Real.rpow ((W + 1 : ℕ) : ℝ) ε :=
    mul_nonneg (postRootCovariancePowerEnvelope_nonneg ε (W + 1))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have houterPos := lt_of_le_of_lt hleft hthr
  have hmunz : realMoebiusStep c ≠ 0 := by
    intro hz
    rw [houterEq, hz] at houterPos
    norm_num at houterPos
  have hmusq : realMoebiusStep c ^ 2 = 1 := by
    rcases ArithmeticFunction.moebius_eq_or c with h | h | h
    · simp [realMoebiusStep, h] at hmunz
    · simp [realMoebiusStep, h]
    · simp [realMoebiusStep, h]
  have hcharge := postRootRecordOuterRowNumerator_le_currentSquare_sub_lowerSquare
    ε hε hW hp hmem hdvd hrec
  have hcharge' :
      -realMoebiusStep c *
          (realMertensLength (W + 2) + realMertensLength (c + 1)) ≤
        realMertensLength (W + 2) ^ 2 - realMertensLength (c + 1) ^ 2 := by
    rw [← houterEq]
    exact hcharge
  have hpos :
      0 < -realMoebiusStep c *
        (realMertensLength (W + 2) + realMertensLength (c + 1)) := by
    rw [← houterEq]
    exact houterPos
  have hold : realMertensLength (W + 1) =
      realMertensLength (W + 2) + realMoebiusStep c := by linarith
  rw [houterEq]
  unfold realMertensSquareStep
  rw [hW2, hold]
  exact signed_sum_le_physical_square_step hmusq hpos hcharge'

/-- At a high record the physical square step is strictly positive. -/
theorem realMertensSquareStep_pos_of_activePostRoot_record
    (ε : ℝ) (hε : 0 ≤ ε) {W p : ℕ} (hW : 2 ≤ W)
    (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    0 < realMertensSquareStep (W + 1) := by
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hW hrec
  rw [postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor
    hp hmem hdvd] at hthr
  have hleft := mul_nonneg (postRootCovariancePowerEnvelope_nonneg ε (W + 1))
    (Real.rpow_nonneg (Nat.cast_nonneg (W + 1)) ε)
  exact lt_of_lt_of_le (lt_of_le_of_lt hleft hthr)
    (postRootRecordOuterRowNumerator_le_physicalSquareStep ε hε hW hp hmem hdvd hrec)

/-- Every positive record away from a prime-square wall creates positive
physical Mertens-square energy. Inward physical square steps cannot be records. -/
theorem realMertensSquareStep_pos_of_record_of_not_primeSquare
    (ε : ℝ) (hε : 0 ≤ ε) {W : ℕ} (hW : 2 ≤ W)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W)
    (hwall : ∀ p : ℕ, p.Prime → p * p ≠ W + 1) :
    0 < realMertensSquareStep (W + 1) := by
  by_cases hex : ∃ p ∈ postRootPrimeFamilySet (W + 1), p ∣ W + 1
  · obtain ⟨p, hpMem, hpDvd⟩ := hex
    exact realMertensSquareStep_pos_of_activePostRoot_record ε hε hW
      (mem_postRootPrimeFamilySet.mp hpMem).2.2 hpMem hpDvd hrec
  · have hno : ∀ p ∈ postRootPrimeFamilySet (W + 1), ¬ p ∣ W + 1 := by
      intro p hpMem hpDvd
      exact hex ⟨p, hpMem, hpDvd⟩
    have hrows := postRootPrimeFamilyCovarianceRowTotal_eq_zero_of_no_active_divisor hno
    have hdep := postRootPrimeFamilyCovarianceDeparture_eq_zero_of_not_primeSquare hwall
    have hthr :=
      postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
        ε hε hW hrec
    rw [postRootCovarianceLocalInnovation_eq_row_sub_inherited_add_departure,
      hrows, hdep, sub_zero, add_zero] at hthr
    have hleft := mul_nonneg (postRootCovariancePowerEnvelope_nonneg ε (W + 1))
      (Real.rpow_nonneg (Nat.cast_nonneg (W + 1)) ε)
    have hrow := lt_of_le_of_lt hleft hthr
    rw [realMertensSquareStep_eq_diagonal_add_two_mul_row]
    nlinarith [sq_nonneg (realMoebiusStep (W + 1))]

/-- The normalized high-record excess is charged to its own physical square
step, with no interval extending down to the cofactor. -/
theorem postRootCovariancePowerRecordExcess_le_physicalSquareStep_of_activePostRoot
    (ε : ℝ) (hε : 0 < ε) {W p : ℕ} (hW : 2 ≤ W)
    (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    postRootCovariancePowerRecordExcess ε W ≤
      realMertensSquareStep (W + 1) /
        Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) := by
  have hbudget := postRootCovariancePowerRecordExcess_le_localInnovationBudget ε hε hW
  have hbound := postRootRecordOuterRowNumerator_le_physicalSquareStep
    ε hε.le hW hp hmem hdvd hrec
  have hstep := realMertensSquareStep_pos_of_activePostRoot_record
    ε hε.le hW hp hmem hdvd hrec
  have hscale := Real.rpow_nonneg (Nat.cast_nonneg (W + 1)) (1 + ε)
  unfold postRootCovariancePowerLocalInnovationBudget at hbudget
  rw [postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor
    hp hmem hdvd] at hbudget
  exact hbudget.trans (max_le (div_nonneg hstep.le hscale)
    (div_le_div_of_nonneg_right hbound hscale))

/-- The high and low cases now share the same physical one-step charge.
The low estimate retains its sharper factor one half in its original theorem. -/
theorem postRootRecordOuterRowSeat_le_twice_physicalSquareStepSeat_of_record
    (ε : ℝ) (hε : 0 ≤ ε) {W : ℕ} (hW : 2 ≤ W)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    postRootRecordOuterRowSeat ε W ≤
      2 * postRootRecordPhysicalSquareStepSeat ε W := by
  by_cases hex : ∃ p ∈ postRootPrimeFamilySet (W + 1), p ∣ W + 1
  · obtain ⟨p, hpMem, hpDvd⟩ := hex
    have hpPrime := (mem_postRootPrimeFamilySet.mp hpMem).2.2
    have hraw := postRootRecordOuterRowNumerator_le_physicalSquareStep
      ε hε hW hpPrime hpMem hpDvd hrec
    have hscale := Real.rpow_nonneg (Nat.cast_nonneg (W + 1)) (1 + ε)
    have hdiv :
        (realMoebiusStep (W + 1) * realMertensLength (W + 1) -
            postRootPrimeFamilyCovarianceRowTotal W) /
              Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) ≤
          realMertensSquareStep (W + 1) /
            Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) :=
      div_le_div_of_nonneg_right hraw hscale
    have hseat :
        (realMertensSquareStep (W + 1) / 2) /
            Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) ≤
          postRootRecordPhysicalSquareStepSeat ε W := le_max_right _ _
    unfold postRootRecordOuterRowSeat
    apply max_le
    · exact mul_nonneg (by norm_num) (postRootRecordPhysicalSquareStepSeat_nonneg ε W)
    · refine hdiv.trans ?_
      calc
        realMertensSquareStep (W + 1) /
            Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε) =
          2 * ((realMertensSquareStep (W + 1) / 2) /
            Real.rpow ((W + 1 : ℕ) : ℝ) (1 + ε)) := by ring
        _ ≤ 2 * postRootRecordPhysicalSquareStepSeat ε W :=
          mul_le_mul_of_nonneg_left hseat (by norm_num)
  · have hno : ∀ p ∈ postRootPrimeFamilySet (W + 1), ¬ p ∣ W + 1 := by
      intro p hpMem hpDvd
      exact hex ⟨p, hpMem, hpDvd⟩
    have hlow := postRootRecordOuterRowSeat_le_physicalSquareStepSeat_of_no_active_divisor
      ε hno
    have hnonneg := postRootRecordPhysicalSquareStepSeat_nonneg ε W
    linarith

/-- The full physical square-step positive part, charged only at records. -/
def postRootRecordPhysicalSquareVariationSeat (ε : ℝ) (W : ℕ) : ℝ :=
  if 0 < postRootCovariancePowerRecordExcess ε W then
    2 * postRootRecordPhysicalSquareStepSeat ε W
  else 0

theorem postRootRecordPhysicalSquareVariationSeat_nonneg (ε : ℝ) (W : ℕ) :
    0 ≤ postRootRecordPhysicalSquareVariationSeat ε W := by
  unfold postRootRecordPhysicalSquareVariationSeat
  split
  · exact mul_nonneg (by norm_num) (postRootRecordPhysicalSquareStepSeat_nonneg ε W)
  · exact le_rfl

/-- Every record excess is paid by the record-selected physical square step
and the explicitly retained square-wall departure. -/
theorem postRootCovariancePowerRecordExcess_le_physicalVariation_add_departure
    (ε : ℝ) (hε : 0 < ε) {W : ℕ} (hW : 2 ≤ W) :
    postRootCovariancePowerRecordExcess ε W ≤
      postRootRecordPhysicalSquareVariationSeat ε W +
        postRootRecordDepartureSeat ε W := by
  by_cases hrec : 0 < postRootCovariancePowerRecordExcess ε W
  · have hbudget := postRootCovariancePowerRecordExcess_le_localInnovationBudget ε hε hW
    rw [postRootCovariancePowerLocalInnovationBudget_eq_outerRow_add_departure] at hbudget
    unfold postRootRecordPhysicalSquareVariationSeat
    rw [if_pos hrec]
    exact hbudget.trans (add_le_add_right
      (postRootRecordOuterRowSeat_le_twice_physicalSquareStepSeat_of_record
        ε hε.le hW hrec) _)
  · have hzero : postRootCovariancePowerRecordExcess ε W = 0 :=
      le_antisymm (not_lt.mp hrec) (postRootCovariancePowerRecordExcess_nonneg ε W)
    unfold postRootRecordPhysicalSquareVariationSeat
    rw [if_neg hrec, hzero, zero_add]
    exact postRootRecordDepartureSeat_nonneg ε W

/-- **Finite physical-step packing.** Each record charges a distinct physical
time step. The right side is selected positive variation, not a telescoping
endpoint difference, and its uniform boundedness remains open. -/
theorem postRootCovariancePowerEnvelope_le_anchor_add_physicalVariation_add_departure
    (ε : ℝ) (hε : 0 < ε) {X : ℕ} (hX : 2 ≤ X) :
    postRootCovariancePowerEnvelope ε X ≤
      postRootCovariancePowerEnvelope ε 2 +
        (∑ W ∈ Finset.Ico 2 X, postRootRecordPhysicalSquareVariationSeat ε W) +
        ∑ W ∈ Finset.Ico 2 X, postRootRecordDepartureSeat ε W := by
  rw [postRootCovariancePowerEnvelope_eq_anchor_add_tailRecordExcess ε hX]
  have hsum :
      (∑ W ∈ Finset.Ico 2 X, postRootCovariancePowerRecordExcess ε W) ≤
        (∑ W ∈ Finset.Ico 2 X, postRootRecordPhysicalSquareVariationSeat ε W) +
          ∑ W ∈ Finset.Ico 2 X, postRootRecordDepartureSeat ε W := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun W hW =>
      postRootCovariancePowerRecordExcess_le_physicalVariation_add_departure
        ε hε (Finset.mem_Ico.mp hW).1
  linarith

end RHLean.Proof
