import Mathlib
import «research.VF_MID_SIGNED_SEAT_CHARGE»

/-!
# Restricted genuine-prime owner ancestry: original-weight sign bounds

Claim IDs 20261014-owner-1 and 20261014-owner-2, accepted by Adversarial Referee as
PAPER_PROOF. The current semiprime seat has positive weight w(R);
its distinct historical prime q has negative charge -(1-w(sqrt q)).

These results hold only for R >= 1024*p. They are bounds for one
identified current/historical *pair*, NOT an unconditional global NNS
covariance payment: the actual history contains one tagged q, and
restoring all quadratic cross terms is mandatory.
-/

noncomputable section
namespace RHLean.Analysis

/-- Explicit lower bound for the midpoint logarithm, with t >= 2^k.
No asymptotic prime number estimate is involved. -/
private theorem vfMidMidpoint_log_gt_four_k_div_three
    {t B k : ℕ} (hk : 0 < k) (ht : B ≤ t)
    (hB : (B : ℝ) = (2 : ℝ) ^ k) :
    (4 * (k : ℝ)) / 3 < Real.log (vfMidBandMidpoint t) := by
  have htReal : (B : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hBpos : (0 : ℝ) < (B : ℝ) := by rw [hB]; positivity
  have hts : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have hsquare : (B : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((t : ℝ) - (B : ℝ))]
  have hmid : (B : ℝ) ^ 2 ≤ vfMidBandMidpoint t := by
    unfold vfMidBandMidpoint
    nlinarith
  have hloge :
      Real.log ((B : ℝ) ^ 2) = (2 * (k : ℝ)) * Real.log 2 := by
    rw [hB, ← pow_mul, Real.log_pow]
    push_cast
    ring
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hkReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hnumeric :
      (4 * (k : ℝ)) / 3 < (2 * (k : ℝ)) * Real.log 2 := by
    have hmul :=
      mul_lt_mul_of_pos_left hlog2
        (show (0 : ℝ) < 2 * (k : ℝ) by positivity)
    nlinarith
  have hlogmono :
      Real.log ((B : ℝ) ^ 2) ≤
        Real.log (vfMidBandMidpoint t) :=
    Real.log_le_log (by positivity) hmid
  rw [hloge] at hlogmono
  exact hnumeric.trans_le hlogmono

/-- Convert a numerically explicit log lower bound into an upper bound
on the ACTUAL VF odd seat weight, rather than a reweighted surrogate. -/
private theorem vfMidOddWeight_lt_of_log_and_num
    (t : ℕ) (c L : ℝ) (ht : 0 < t)
    (hc : 0 < c) (hL : 0 < L)
    (hlog : L < Real.log (vfMidBandMidpoint t))
    (hnum : 2 * (t : ℝ) + 1 < c * (t : ℝ) * L) :
    vfMidOddFractionalPrimeSeatWeight t < c := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hlogpos : 0 < Real.log (vfMidBandMidpoint t) :=
    hL.trans hlog
  have hupper :
      c * (t : ℝ) * L <
        c * (t : ℝ) * Real.log (vfMidBandMidpoint t) :=
    mul_lt_mul_of_pos_left hlog (mul_pos hc htpos)
  have hnumlog :
      2 * (t : ℝ) + 1 <
        c * (Real.log (vfMidBandMidpoint t) * (t : ℝ)) := by
    nlinarith
  unfold vfMidOddFractionalPrimeSeatWeight vfMidBandMass
  apply (div_lt_iff₀ htpos).2
  apply (div_lt_iff₀ hlogpos).2
  nlinarith [hnumlog]

/-- For every scale >=1024 the physical odd-seat weight is <99/640. -/
theorem vfMidOddWeight_lt_99_div_640
    {t : ℕ} (ht : 1024 ≤ t) :
    vfMidOddFractionalPrimeSeatWeight t < (99 / 640 : ℝ) := by
  have hlog :
      (40 / 3 : ℝ) < Real.log (vfMidBandMidpoint t) := by
    convert (vfMidMidpoint_log_gt_four_k_div_three
      (t := t) (B := 1024) (k := 10)
      (by norm_num) ht (by norm_num)) using 1
    norm_num
  have htReal : (1024 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hnum :
      2 * (t : ℝ) + 1 <
        (99 / 640 : ℝ) * (t : ℝ) * (40 / 3) := by
    nlinarith
  exact vfMidOddWeight_lt_of_log_and_num
    t (99 / 640) (40 / 3)
    (by omega) (by norm_num) (by norm_num) hlog hnum

/-- For every current scale >=2048 the actual odd-seat weight is <9/64. -/
theorem vfMidOddWeight_lt_9_div_64
    {t : ℕ} (ht : 2048 ≤ t) :
    vfMidOddFractionalPrimeSeatWeight t < (9 / 64 : ℝ) := by
  have hlog :
      (44 / 3 : ℝ) < Real.log (vfMidBandMidpoint t) := by
    convert (vfMidMidpoint_log_gt_four_k_div_three
      (t := t) (B := 2048) (k := 11)
      (by norm_num) ht (by norm_num)) using 1
    norm_num
  have htReal : (2048 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hnum :
      2 * (t : ℝ) + 1 <
        (9 / 64 : ℝ) * (t : ℝ) * (44 / 3) := by
    nlinarith
  exact vfMidOddWeight_lt_of_log_and_num
    t (9 / 64) (44 / 3)
    (by omega) (by norm_num) (by norm_num) hlog hnum

/-- Original current/child root arithmetic: the strong small-owner
condition R>=1024*p guarantees a genuine historical child root >=1024. -/
private theorem vfMidSmallOwner_child_root_ge_1024
    {R p q : ℕ} (hp : p.Prime)
    (hscale : 1024 * p ≤ R) (hlo : R ^ 2 < p * q) :
    1024 ≤ Nat.sqrt q := by
  have hpOne : 1 ≤ p := hp.one_le
  have hpSq : p ≤ p * p := by
    calc
      p = p * 1 := by omega
      _ ≤ p * p := Nat.mul_le_mul_left p hpOne
  have hscaled : p * (1024 ^ 2) ≤ (1024 * p) ^ 2 := by
    nlinarith
  have hrootSq : (1024 * p) ^ 2 ≤ R ^ 2 :=
    Nat.pow_le_pow_left hscale 2
  have hqGe : 1024 ^ 2 ≤ q := by
    by_contra h
    have hqLe : q ≤ 1024 ^ 2 := by omega
    have hprod : p * q ≤ p * (1024 ^ 2) :=
      Nat.mul_le_mul_left p hqLe
    omega
  exact (Nat.le_sqrt).2 hqGe

/-- Uniform owner-3 generalization for all genuine prime owners with
current block R>=1024*p. The original sign margin is less than -451/640. -/
theorem vfMidSmallOwner_original_signed_gap
    {R p q : ℕ} (hp : p.Prime) (_hq : q.Prime)
    (hscale : 1024 * p ≤ R)
    (hlo : R ^ 2 < p * q)
    (_hhi : p * q < (R + 1) ^ 2) :
    vfMidOddFractionalPrimeSeatWeight R +
        vfMidOddFractionalPrimeSeatWeight (Nat.sqrt q) - 1 <
      -(451 / 640 : ℝ) := by
  have hR : 2048 ≤ R := by
    have hp2 := hp.two_le
    omega
  have hr : 1024 ≤ Nat.sqrt q :=
    vfMidSmallOwner_child_root_ge_1024 hp hscale hlo
  have hx := vfMidOddWeight_lt_9_div_64 hR
  have hz := vfMidOddWeight_lt_99_div_640 hr
  linarith

/-- The original literal signed seat charges have the exact same gap.
A genuine composite current site carries +w(R), while the earlier actual
prime q carries -(1-w(floor sqrt q)). -/
theorem vfMidSmallOwner_original_seat_charge_gap
    {R p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hscale : 1024 * p ≤ R)
    (hlo : R ^ 2 < p * q)
    (hhi : p * q < (R + 1) ^ 2) :
    vfMidOddSignedSeatCharge R (p * q) +
        vfMidOddSignedSeatCharge (Nat.sqrt q) q <
      -(451 / 640 : ℝ) := by
  have hnNotPrime : ¬(p * q).Prime := by
    intro h
    have hdiv : p ∣ p * q := dvd_mul_right p q
    rcases (Nat.dvd_prime h).mp hdiv with hp1 | heq
    · exact hp.ne_one hp1
    · have hm : 2 * p ≤ p * q := by
        simpa [Nat.mul_comm] using! Nat.mul_le_mul_left p hq.two_le
      omega
  rw [vfMidOddSignedSeatCharge_of_not_prime R (p * q) hnNotPrime,
    vfMidOddSignedSeatCharge_of_prime (Nat.sqrt q) q hq]
  have hgap :=
    vfMidSmallOwner_original_signed_gap hp hq hscale hlo hhi
  linarith

/-- Genuine original-weight pair NNS slack is **strictly negative** in
this fixed-owner sector. This does not bound the whole covariance:
historical q availability and the M0,S0 cross terms remain unproved. -/
theorem vfMidSmallOwner_isolated_NNS_slack_lt
    {R p q : ℕ} (hp : p.Prime) (_hq : q.Prime)
    (hscale : 1024 * p ≤ R)
    (hlo : R ^ 2 < p * q)
    (_hhi : p * q < (R + 1) ^ 2) :
    let x := vfMidOddFractionalPrimeSeatWeight R
    let y := 1 - vfMidOddFractionalPrimeSeatWeight (Nat.sqrt q)
    6 * x * y - x ^ 2 - y ^ 2 < -(541 / 409600 : ℝ) := by
  dsimp
  have hR : 2048 ≤ R := by
    have hp2 := hp.two_le
    omega
  have hr : 1024 ≤ Nat.sqrt q :=
    vfMidSmallOwner_child_root_ge_1024 hp hscale hlo
  have hx := vfMidOddWeight_lt_9_div_64 hR
  have hz := vfMidOddWeight_lt_99_div_640 hr
  let x : ℝ := vfMidOddFractionalPrimeSeatWeight R
  let y : ℝ := 1 - vfMidOddFractionalPrimeSeatWeight (Nat.sqrt q)
  have hxBound : x < 90 / 640 := by dsimp [x]; norm_num at hx ⊢; linarith
  have hyBound : (541 / 640 : ℝ) < y := by dsimp [y]; linarith
  have hyPos : 0 < y := by linarith
  have hgap : (1 / 640 : ℝ) < y - 6 * x := by linarith
  have hprod1 :
      (541 / 640 : ℝ) * (1 / 640) < y * (1 / 640) :=
    mul_lt_mul_of_pos_right hyBound (by norm_num)
  have hprod2 :
      y * (1 / 640 : ℝ) < y * (y - 6 * x) :=
    mul_lt_mul_of_pos_left hgap hyPos
  have hxsq : 0 ≤ x ^ 2 := sq_nonneg x
  dsimp [x, y] at *
  nlinarith

/-- Fully expanded cross terms when a pair is adjoined to a residual
global zero-target energy. The isolated pair result does NOT dispose of
these terms or provide a historical source-multiplicity injection. -/
theorem vfMidNNS_pair_add_cross_terms
    (M₀ S₀ x y : ℝ) :
    (M₀ + x + y) ^ 2 - 2 * (S₀ + x - y) ^ 2 -
        (M₀ ^ 2 - 2 * S₀ ^ 2) =
      2 * M₀ * (x + y) - 4 * S₀ * (x - y) +
        (x + y) ^ 2 - 2 * (x - y) ^ 2 := by
  ring

#print axioms vfMidOddWeight_lt_99_div_640
#print axioms vfMidOddWeight_lt_9_div_64
#print axioms vfMidSmallOwner_original_signed_gap
#print axioms vfMidSmallOwner_original_seat_charge_gap
#print axioms vfMidSmallOwner_isolated_NNS_slack_lt
#print axioms vfMidNNS_pair_add_cross_terms

end RHLean.Analysis
