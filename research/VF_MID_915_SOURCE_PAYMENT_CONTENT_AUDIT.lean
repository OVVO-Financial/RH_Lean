import Mathlib
import «research.VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE»
import «research.VF_CANONICAL_SQRT_TWO_VON_KOCH»

/-!
# Content audit of the #915 first-bad source-payment statement

`VFMid915FirstBadSourcePaymentStatement` (equivalently, by identical body,
`VFMidFirstBadSourceToSectorSixInletStatement`) asks, for every `R >= 8` with
a first bad successor `R + 1` at `K = 2`,

`2 * Source(R)^2 <= TotalMass(R)`.

This module records exactly what that statement says.

1. **The inequality is false on its whole hypothesis domain.**  The compiled
   victory theorem already forces `TotalMass(R) < 2 * Source(R)^2` at every
   first-bad successor; we state it positively.  Hence the payment statement
   is *equivalent* to the absence of first-bad successors (it can only hold
   vacuously).
2. **Two-number reduction.**  For each `R >= 8` the payment inequality depends
   on the block only through the actual prime supply `P_R` and on the history
   only through the endpoint defect `D_R`:
   `2 (D_R + P_R - m_R)^2 <= (|D_R| + w_R R + (1 - 2 w_R) P_R)^2`.
   Owner, ancestry, multiplicity, mask and clip data cannot change its truth
   value.
3. **Block-scale sandwich.**  Writing `D' = D + delta` with `|delta| <= beta`,
   the inequality `2 D'^2 <= (|D| + beta)^2` holds when
   `|D'| <= (1 + sqrt 2) (beta - |delta|)` and fails when
   `|D'| > 2 (1 + sqrt 2) beta`.  It is a block-scale envelope, not a ledger
   identity.
4. **Explicit-envelope form.**  With the finite base window `2..8` good at
   `K = 2`, payment is exactly the explicit envelope `|D_R| <= 2 R log R` for
   all `R >= 2`, and it implies the square-endpoint and canonical von-Koch
   targets.  Without the base, payment is exactly
   "some base scale is bad, or no scale `>= 2` is bad".

Mathematical status: logical audit only.  Nothing here proves the payment,
the envelope, a prime-counting estimate, or RH.  The finite base window is
a hypothesis, verified numerically outside Lean in the session report.

Research claim IDs: CL-20261014-3, CL-20261014-3', CL-20261014-4,
CL-20261014-6, CL-20261014-7 (Claude direct session, 2026-10-14).
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## 1. The payment inequality fails wherever it is required -/

/-- The source-to-sector-six inlet and the #915 payment statement have the
same body. -/
theorem vfMidFirstBadSourceToSectorSixInlet_iff_915SourcePayment :
    VFMidFirstBadSourceToSectorSixInletStatement ↔
      VFMid915FirstBadSourcePaymentStatement :=
  Iff.rfl

/-- **Strict failure on the hypothesis domain.**  At every first-bad
successor the total mass is strictly smaller than twice the squared source,
i.e. the payment inequality is false there. -/
theorem vfMid915FirstBad_totalMass_lt_twice_sourceSq
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidFirstBadZeroTargetTotalMass R <
      2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 := by
  by_contra hcon
  exact vfMidActualPrimeFirstBadAt_two_succ_victory_of_sourceInlet hR hfirst
    (not_lt.mp hcon)

/-- The #915 payment statement is EXACTLY the absence of first-bad
successors above root 8.  The reverse direction is vacuous. -/
theorem vfMid915FirstBadSourcePayment_iff_noFirstBad :
    VFMid915FirstBadSourcePaymentStatement ↔
      ∀ R : ℕ, 8 ≤ R → ¬ VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) := by
  constructor
  · intro hpay R hR hfirst
    exact vfMid915FirstBad_closed_of_sourcePayment hpay hR hfirst
  · intro hno R hR hfirst
    exact (hno R hR hfirst).elim

/-- Least-bad-scale induction.  This is the same argument as
`vfV2ActualPrime_allInside_of_noFirstBad_and_base` in
`VF_MID_FIRST_BAD_ACTUAL_ADMISSIBILITY_CERTIFICATE`, restated here so that this
audit does not import that module's opt-in native dependency graph. -/
private theorem vfMid915Audit_allInside_of_noFirstBad_and_base
    (hbase : ∀ B : ℕ, 2 ≤ B → B ≤ 8 →
      ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) B)
    (hno : ∀ R : ℕ, 8 ≤ R →
      ¬ VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    ∀ B : ℕ, 2 ≤ B →
      ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) B := by
  intro B
  induction B using Nat.strong_induction_on with
  | h B ih =>
      intro hB
      by_cases hsmall : B ≤ 8
      · exact hbase B hB hsmall
      · have hlarge : 9 ≤ B := by omega
        intro hbad
        have hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) B := by
          constructor
          · exact hbad
          · intro S hS hSB
            exact ih S hSB hS
        have hnot := hno (B - 1) (by omega : 8 ≤ B - 1)
        have hBdecomp : B - 1 + 1 = B := Nat.sub_add_cancel (by omega : 1 ≤ B)
        rw [hBdecomp] at hnot
        exact hnot hfirst

/-- Without any base hypothesis: no first-bad successor above root 8 holds
exactly when some base scale in `2..8` is already bad, or no scale `>= 2` is
bad at all.  (Least-bad-scale argument.) -/
theorem vfMid_noFirstBadTwo_iff_baseBad_or_allInside :
    (∀ R : ℕ, 8 ≤ R → ¬ VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) ↔
      ((∃ B : ℕ, 2 ≤ B ∧ B ≤ 8 ∧
          VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) B) ∨
        ∀ R : ℕ, 2 ≤ R →
          ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) R) := by
  constructor
  · intro hno
    by_cases hb : ∃ B : ℕ, 2 ≤ B ∧ B ≤ 8 ∧
        VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) B
    · exact Or.inl hb
    · right
      have hbase : ∀ B : ℕ, 2 ≤ B → B ≤ 8 →
          ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) B :=
        fun B hB2 hB8 hbad => hb ⟨B, hB2, hB8, hbad⟩
      exact vfMid915Audit_allInside_of_noFirstBad_and_base hbase hno
  · rintro (⟨B, hB2, hB8, hbad⟩ | hall) R _hR hfirst
    · exact hfirst.2 B hB2 (by omega) hbad
    · exact hall (R + 1) (by omega) hfirst.1

/-- **Explicit-envelope form.**  With the finite base window good at `K = 2`,
the #915 payment statement is exactly the explicit envelope
`|D_R| <= 2 R log R` for every `R >= 2`. -/
theorem vfMid915FirstBadSourcePayment_iff_radialTwoEnvelope_of_base
    (hbase : ∀ B : ℕ, 2 ≤ B → B ≤ 8 →
      ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) B) :
    VFMid915FirstBadSourcePaymentStatement ↔
      ∀ R : ℕ, 2 ≤ R →
        |vfMidActualPrimeEndpointDefect R| ≤
          2 * vfMidSyntheticRadialScale R := by
  rw [vfMid915FirstBadSourcePayment_iff_noFirstBad]
  constructor
  · intro hno R hR
    exact le_of_not_gt
      (vfMid915Audit_allInside_of_noFirstBad_and_base hbase hno R hR)
  · intro henv R _hR hfirst
    have hbad := hfirst.1
    unfold VFMidSyntheticBadAt at hbad
    have hin := henv (R + 1) (by omega)
    linarith [hbad, hin]

/-- Payment plus the finite base window gives the legacy square-endpoint
von-Koch target with explicit constant `2`. -/
theorem vfMidSquareEndpointVonKochBounded_of_915SourcePayment_and_base
    (hbase : ∀ B : ℕ, 2 ≤ B → B ≤ 8 →
      ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) B)
    (hpay : VFMid915FirstBadSourcePaymentStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  have henv :=
    (vfMid915FirstBadSourcePayment_iff_radialTwoEnvelope_of_base hbase).mp hpay
  have hrad :
      VFMidSyntheticRadialBounded
        (fun R => vfMidPrimeError ((R : ℝ) ^ 2)) := by
    refine ⟨2, by norm_num, ?_⟩
    intro R hR
    exact henv R hR
  exact vfMidActualRadialBounded_iff_squareEndpoint.mp hrad

/-- Canonical form: payment plus the finite base window gives the public
canonical sqrt-two von-Koch target. -/
theorem vfCanonicalSquareVonKoch_of_915SourcePayment_and_base
    (hbase : ∀ B : ℕ, 2 ≤ B → B ≤ 8 →
      ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect (2 : ℝ) B)
    (hpay : VFMid915FirstBadSourcePaymentStatement) :
    VFCanonicalSquareVonKochStatement :=
  vfCanonicalSquareVonKoch_iff_legacy.mpr
    (vfMidSquareEndpointVonKochBounded_of_915SourcePayment_and_base hbase hpay)

/-! ## 2. The payment inequality is a two-number statement -/

/-- Exact block recursion in the block-supply currency used by the seat
charges: `D_(R+1) = D_R + P_R - m_R`. -/
theorem vfMidActualPrimeEndpointDefect_succ_eq_add_blockSupply
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidActualPrimeEndpointDefect (R + 1) =
      vfMidActualPrimeEndpointDefect R +
        ((vfMidIntegerBlockPrimeSupply R : ℝ) - vfMidBandMass R) := by
  have hstep := vfMidDirectSquareEndpointError_succ R hR
  rw [vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR,
    vfMidDirectSquareEndpointError_eq_vfMidPrimeError
      (by omega : 2 ≤ R + 1)] at hstep
  have hband :
      vfMidDirectBandError R =
        (vfMidIntegerBlockPrimeSupply R : ℝ) - vfMidBandMass R := rfl
  unfold vfMidActualPrimeEndpointDefect
  rw [hstep, hband]

/-- Total absolute seat charge of block `R` (`R >= 3`): composite seats carry
`w_R`, prime seats carry `1 - w_R`. -/
theorem vfMidOddSignedSeatCharge_absSum_eq
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddSignedSeatCharge R n|) =
      vfMidOddFractionalPrimeSeatWeight R * (R : ℝ) +
        (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
          (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  have hR2 : 2 ≤ R := by omega
  have hw0 := vfMidOddFractionalPrimeSeatWeight_nonneg R hR2
  have hw1 := vfMidOddFractionalPrimeSeatWeight_le_one_of_three_le R hR
  have hpoint :
      ∀ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddSignedSeatCharge R n| =
          vfMidOddFractionalPrimeSeatWeight R +
            (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
              vfMidActualPrimeSeatMass n := by
    intro n _hn
    by_cases hp : n.Prime
    · rw [vfMidOddSignedSeatCharge_of_prime R n hp]
      have hcomp : 0 ≤ 1 - vfMidOddFractionalPrimeSeatWeight R := by
        linarith
      rw [abs_neg, abs_of_nonneg hcomp]
      simp [vfMidActualPrimeSeatMass, hp]
      ring
    · rw [vfMidOddSignedSeatCharge_of_not_prime R n hp,
        abs_of_nonneg hw0]
      simp [vfMidActualPrimeSeatMass, hp]
  calc
    _ = ∑ n ∈ vfMidOddCandidateSeats R,
          (vfMidOddFractionalPrimeSeatWeight R +
            (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
              vfMidActualPrimeSeatMass n) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hpoint n hn
    _ = (∑ _n ∈ vfMidOddCandidateSeats R,
            vfMidOddFractionalPrimeSeatWeight R) +
          (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
            (∑ n ∈ vfMidOddCandidateSeats R,
              vfMidActualPrimeSeatMass n) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
          rw [vfMidActualPrimeSeatMass_sum_oddCandidates R hR2,
            Finset.sum_const, nsmul_eq_mul, vfMidOddCandidateSeats_card]
          ring

/-- **Two-number reduction.**  For `R >= 8` the payment inequality at `R`
is literally an inequality between the endpoint defect `D_R` and the block
prime supply `P_R` (the VF mass `m_R` and seat weight `w_R` are
deterministic). -/
theorem vfMid915SourcePaymentAt_iff_twoParameter
    {R : ℕ} (hR : 8 ≤ R) :
    (2 * vfMidFirstBadDecompressedHistoricalSource R ^ 2 ≤
        vfMidFirstBadZeroTargetTotalMass R) ↔
      2 * (vfMidActualPrimeEndpointDefect R +
          ((vfMidIntegerBlockPrimeSupply R : ℝ) - vfMidBandMass R)) ^ 2 ≤
        (|vfMidActualPrimeEndpointDefect R| +
          (vfMidOddFractionalPrimeSeatWeight R * (R : ℝ) +
            (1 - 2 * vfMidOddFractionalPrimeSeatWeight R) *
              (vfMidIntegerBlockPrimeSupply R : ℝ))) ^ 2 := by
  rw [← vfMidActualPrimeEndpointDefect_succ_eq_decompressedHistoricalSource hR,
    vfMidActualPrimeEndpointDefect_succ_eq_add_blockSupply (by omega : 2 ≤ R),
    vfMidFirstBadZeroTargetTotalMass_eq,
    vfMidOddSignedSeatCharge_absSum_eq R (by omega)]

/-! ## 3. Block-scale sandwich (pure real arithmetic) -/

/-- Payment holds whenever the next defect is within `(1 + sqrt 2)` times
the unsigned block slack `beta - |delta|`. -/
theorem vfMid915_payment_of_endpoint_le_blockSlack
    {D δ β : ℝ}
    (h : |D + δ| ≤ (1 + Real.sqrt 2) * (β - |δ|)) :
    2 * (D + δ) ^ 2 ≤ (|D| + β) ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by
    have h12 : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_one] at h12
  have hprod : (Real.sqrt 2 - 1) * (1 + Real.sqrt 2) = 1 := by
    linear_combination hss
  have hstep : (Real.sqrt 2 - 1) * |D + δ| ≤ β - |δ| := by
    have hmul :
        (Real.sqrt 2 - 1) * |D + δ| ≤
          (Real.sqrt 2 - 1) * ((1 + Real.sqrt 2) * (β - |δ|)) :=
      mul_le_mul_of_nonneg_left h (by linarith [hs1])
    have hid :
        (Real.sqrt 2 - 1) * ((1 + Real.sqrt 2) * (β - |δ|)) = β - |δ| := by
      calc
        (Real.sqrt 2 - 1) * ((1 + Real.sqrt 2) * (β - |δ|)) =
            ((Real.sqrt 2 - 1) * (1 + Real.sqrt 2)) * (β - |δ|) := by ring
        _ = β - |δ| := by rw [hprod, one_mul]
    linarith [hmul, hid]
  have htri : |D + δ| ≤ |D| + |δ| := abs_add_le D δ
  have hexp :
      (Real.sqrt 2 - 1) * |D + δ| = Real.sqrt 2 * |D + δ| - |D + δ| := by
    ring
  have hlow : Real.sqrt 2 * |D + δ| ≤ |D| + β := by
    linarith [hstep, htri, hexp]
  have hsa0 : 0 ≤ Real.sqrt 2 * |D + δ| := mul_nonneg hs0 (abs_nonneg _)
  have hsq :
      (Real.sqrt 2 * |D + δ|) * (Real.sqrt 2 * |D + δ|) ≤
        (|D| + β) * (|D| + β) :=
    mul_self_le_mul_self hsa0 hlow
  have hleft :
      (Real.sqrt 2 * |D + δ|) * (Real.sqrt 2 * |D + δ|) =
        2 * (D + δ) ^ 2 := by
    calc
      (Real.sqrt 2 * |D + δ|) * (Real.sqrt 2 * |D + δ|) =
          (Real.sqrt 2 * Real.sqrt 2) * (|D + δ| * |D + δ|) := by ring
      _ = 2 * (D + δ) ^ 2 := by
          rw [hss, abs_mul_abs_self]
          ring
  have hright : (|D| + β) * (|D| + β) = (|D| + β) ^ 2 := by ring
  linarith [hsq, hleft, hright]

/-- Payment fails whenever the next defect exceeds `2 (1 + sqrt 2)` times the
absolute block mass `beta` (with `|delta| <= beta`). -/
theorem vfMid915_payment_fails_of_endpoint_gt_blockMass
    {D δ β : ℝ} (hδ : |δ| ≤ β)
    (h : 2 * (1 + Real.sqrt 2) * β < |D + δ|) :
    (|D| + β) ^ 2 < 2 * (D + δ) ^ 2 := by
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hprod : (Real.sqrt 2 - 1) * (1 + Real.sqrt 2) = 1 := by
    linear_combination hss
  have hs1 : 1 < Real.sqrt 2 := by
    have h12 : Real.sqrt 1 < Real.sqrt 2 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at h12
  have hβ0 : 0 ≤ β := le_trans (abs_nonneg δ) hδ
  have hD : |D| ≤ |D + δ| + |δ| := by
    have h1 := abs_add_le (D + δ) (-δ)
    rw [abs_neg, add_neg_cancel_right] at h1
    exact h1
  have h2β : 2 * β < (Real.sqrt 2 - 1) * |D + δ| := by
    have hmul :
        (Real.sqrt 2 - 1) * (2 * (1 + Real.sqrt 2) * β) <
          (Real.sqrt 2 - 1) * |D + δ| :=
      mul_lt_mul_of_pos_left h (by linarith [hs1])
    have hid :
        (Real.sqrt 2 - 1) * (2 * (1 + Real.sqrt 2) * β) = 2 * β := by
      calc
        (Real.sqrt 2 - 1) * (2 * (1 + Real.sqrt 2) * β) =
            2 * ((Real.sqrt 2 - 1) * (1 + Real.sqrt 2)) * β := by ring
        _ = 2 * β := by rw [hprod, mul_one]
    linarith [hmul, hid]
  have hexp :
      (Real.sqrt 2 - 1) * |D + δ| = Real.sqrt 2 * |D + δ| - |D + δ| := by
    ring
  have hupper : |D| + β < Real.sqrt 2 * |D + δ| := by
    linarith [hD, hδ, h2β, hexp]
  have hL0 : 0 ≤ |D| + β := by linarith [abs_nonneg D, hβ0]
  have hsq :
      (|D| + β) * (|D| + β) <
        (Real.sqrt 2 * |D + δ|) * (Real.sqrt 2 * |D + δ|) :=
    mul_self_lt_mul_self hL0 hupper
  have hright :
      (Real.sqrt 2 * |D + δ|) * (Real.sqrt 2 * |D + δ|) =
        2 * (D + δ) ^ 2 := by
    calc
      (Real.sqrt 2 * |D + δ|) * (Real.sqrt 2 * |D + δ|) =
          (Real.sqrt 2 * Real.sqrt 2) * (|D + δ| * |D + δ|) := by ring
      _ = 2 * (D + δ) ^ 2 := by
          rw [hss, abs_mul_abs_self]
          ring
  have hleft : (|D| + β) * (|D| + β) = (|D| + β) ^ 2 := by ring
  linarith [hsq, hright, hleft]

/-! ## Axiom audit (compile-time)

Each `#guard_msgs` fails the warning-fatal build unless the theorem depends on
exactly the standard axioms `propext`, `Classical.choice`, `Quot.sound`. -/

/-- info: 'RHLean.Analysis.vfMidFirstBadSourceToSectorSixInlet_iff_915SourcePayment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidFirstBadSourceToSectorSixInlet_iff_915SourcePayment

/-- info: 'RHLean.Analysis.vfMid915FirstBad_totalMass_lt_twice_sourceSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMid915FirstBad_totalMass_lt_twice_sourceSq

/-- info: 'RHLean.Analysis.vfMid915FirstBadSourcePayment_iff_noFirstBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMid915FirstBadSourcePayment_iff_noFirstBad

/-- info: 'RHLean.Analysis.vfMid_noFirstBadTwo_iff_baseBad_or_allInside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMid_noFirstBadTwo_iff_baseBad_or_allInside

/-- info: 'RHLean.Analysis.vfMid915FirstBadSourcePayment_iff_radialTwoEnvelope_of_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMid915FirstBadSourcePayment_iff_radialTwoEnvelope_of_base

/-- info: 'RHLean.Analysis.vfMidSquareEndpointVonKochBounded_of_915SourcePayment_and_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidSquareEndpointVonKochBounded_of_915SourcePayment_and_base

/-- info: 'RHLean.Analysis.vfCanonicalSquareVonKoch_of_915SourcePayment_and_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfCanonicalSquareVonKoch_of_915SourcePayment_and_base

/-- info: 'RHLean.Analysis.vfMidActualPrimeEndpointDefect_succ_eq_add_blockSupply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidActualPrimeEndpointDefect_succ_eq_add_blockSupply

/-- info: 'RHLean.Analysis.vfMidOddSignedSeatCharge_absSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidOddSignedSeatCharge_absSum_eq

/-- info: 'RHLean.Analysis.vfMid915SourcePaymentAt_iff_twoParameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMid915SourcePaymentAt_iff_twoParameter

/-- info: 'RHLean.Analysis.vfMid915_payment_of_endpoint_le_blockSlack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMid915_payment_of_endpoint_le_blockSlack

/-- info: 'RHLean.Analysis.vfMid915_payment_fails_of_endpoint_gt_blockMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMid915_payment_fails_of_endpoint_gt_blockMass

end RHLean.Analysis
