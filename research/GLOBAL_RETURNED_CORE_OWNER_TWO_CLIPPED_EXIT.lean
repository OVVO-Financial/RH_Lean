import Mathlib
import «research.GLOBAL_RETURNED_CORE_COMPENSATED_OWNER_BLOCK»
import «research.LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE»

/-!
# The owner-two clipped exit is the whole top Mertens value

The compensated first-owner block proves, for one owner `p` and one
lower-prime signature cell,

  base + child = compensatedInterior + clippedExit.

This file evaluates both sides exactly at the first owner `p = 2`.  No prime
lies below `2`, so the owner-two lower signature is always empty and there is
exactly one owner-two cell: it is already the global, fully reassembled cell.

On that cell:

* the p-free sites beyond the clip `X_R < 2a` all carry unit AMP weight, and
  the one-prime Möbius split `M(Y) = sum_{a odd, Y/2 < a <= Y} mu(a)` shows
  that the clipped exit is **exactly** `M(X_R)`;
* consequently the compensated interior is exactly `Q_R - M(R-1)`.

So summing with signs before squaring moves no top-scale mass into the
interior.  The interior satisfies a bound of the form
`I^2 <= 4 E_R + C R^2 K` unconditionally (here with `C = 8`), while the
packaged square-endpoint recurrence
`SquareEndpointRoundedOddQ2EnergyStep` is, verbatim, a bound on the square of
the owner-two clipped exit.  The open quantitative estimate therefore lives
entirely in the clipped exit; a bound on the compensated interior cannot
supply it.

Only exact finite identities, the compiled quarter frame, and the definition
of the lower critical envelope are used.  No Mertens magnitude estimate,
independence assumption, or new hypothesis is introduced.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## A one-prime split of the Mertens function -/

/-- The integer Mertens value as a real sum on the positive clock. -/
theorem mertensSummatoryInt_real_eq_sum_Icc_realMoebiusStep (Y : ℕ) :
    ((mertensSummatoryInt Y : ℤ) : ℝ) =
      ∑ n ∈ Finset.Icc 1 Y, realMoebiusStep n := by
  rw [mertensSummatoryInt_eq_Icc, Int.cast_sum]
  rfl

/-- A real Möbius interval sum is a difference of two Mertens values. -/
theorem sum_Icc_realMoebiusStep_eq_mertens_sub
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ n ∈ Finset.Icc a b, realMoebiusStep n) =
      ((mertensSummatoryInt b : ℤ) : ℝ) -
        ((mertensSummatoryInt (a - 1) : ℤ) : ℝ) := by
  rw [mertensSummatoryInt_real_eq_sum_Icc_realMoebiusStep,
    mertensSummatoryInt_real_eq_sum_Icc_realMoebiusStep]
  have h1 : Finset.Icc 1 b = Finset.Ioc 0 b := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h2 : Finset.Icc 1 (a - 1) = Finset.Ioc 0 (a - 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h3 : Finset.Icc a b = Finset.Ioc (a - 1) b := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [h1, h2, h3, ← Finset.sum_Ioc_consecutive realMoebiusStep
    (Nat.zero_le (a - 1)) (by omega : a - 1 ≤ b)]
  ring

/-- A site divisible by `p` twice has zero Möbius value. -/
theorem realMoebiusStep_prime_mul_eq_zero_of_dvd
    {p a : ℕ} (hp : p.Prime) (hpa : p ∣ a) :
    realMoebiusStep (p * a) = 0 := by
  have hnot : ¬ Squarefree (p * a) := by
    intro hsq
    have hunit : IsUnit p := hsq p (mul_dvd_mul_left p hpa)
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp hunit)
  unfold realMoebiusStep
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]
  simp

/-- The p-divisible part of the Möbius clock is the negative p-free clock on
the returned range `1 <= a <= Y/p`. -/
theorem sum_Icc_filter_prime_dvd_realMoebiusStep
    {p : ℕ} (hp : p.Prime) (Y : ℕ) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => p ∣ n), realMoebiusStep n) =
      -∑ a ∈ (Finset.Icc 1 Y).filter (fun a => ¬ p ∣ a ∧ p * a ≤ Y),
        realMoebiusStep a := by
  have hbij :
      (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => p ∣ n), realMoebiusStep n) =
        ∑ a ∈ Finset.Icc 1 (Y / p), realMoebiusStep (p * a) := by
    refine Finset.sum_nbij' (fun n => n / p) (fun a => p * a) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      rcases hn with ⟨⟨hn1, hnY⟩, hdvd⟩
      exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos,
        Nat.div_le_div_right hnY⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
      rcases ha with ⟨ha1, haY⟩
      have hmul : a * p ≤ Y := (Nat.le_div_iff_mul_le hp.pos).1 haY
      have hpos : 0 < p * a := Nat.mul_pos hp.pos (by omega)
      refine ⟨⟨by omega, ?_⟩, dvd_mul_right p a⟩
      rw [Nat.mul_comm]
      exact hmul
    · intro n hn
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
    · intro a _ha
      exact Nat.mul_div_cancel_left a hp.pos
    · intro n hn
      change realMoebiusStep n = realMoebiusStep (p * (n / p))
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]
  have hset :
      (Finset.Icc 1 (Y / p)).filter (fun a => ¬ p ∣ a) =
        (Finset.Icc 1 Y).filter (fun a => ¬ p ∣ a ∧ p * a ≤ Y) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨ha1, haY⟩, hpa⟩
      have hmul : a * p ≤ Y := (Nat.le_div_iff_mul_le hp.pos).1 haY
      have hap : a ≤ a * p :=
        calc
          a = a * 1 := (mul_one a).symm
          _ ≤ a * p := Nat.mul_le_mul_left a hp.one_lt.le
      exact ⟨⟨ha1, hap.trans hmul⟩, hpa, by rw [Nat.mul_comm]; exact hmul⟩
    · rintro ⟨⟨ha1, _haY⟩, hpa, hmul⟩
      refine ⟨⟨ha1, (Nat.le_div_iff_mul_le hp.pos).2 ?_⟩, hpa⟩
      rw [Nat.mul_comm]
      exact hmul
  rw [hbij, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (Y / p))
    (fun a => p ∣ a)]
  have hzero :
      (∑ a ∈ (Finset.Icc 1 (Y / p)).filter (fun a => p ∣ a),
        realMoebiusStep (p * a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact realMoebiusStep_prime_mul_eq_zero_of_dvd hp (Finset.mem_filter.mp ha).2
  have hflip :
      (∑ a ∈ (Finset.Icc 1 (Y / p)).filter (fun a => ¬ p ∣ a),
        realMoebiusStep (p * a)) =
        -∑ a ∈ (Finset.Icc 1 (Y / p)).filter (fun a => ¬ p ∣ a),
          realMoebiusStep a := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    exact realMoebiusStep_mul_prime_eq_neg hp (Finset.mem_filter.mp ha).2
  rw [hzero, hflip, hset, zero_add]

/-- **One-prime Mertens split.**  For every prime `p`, the p-free sites whose
p-multiple has left `[1, Y]` carry the entire Mertens value `M(Y)`. -/
theorem sum_Icc_pFree_clipped_realMoebiusStep_eq_mertens
    {p : ℕ} (hp : p.Prime) (Y : ℕ) :
    (∑ a ∈ (Finset.Icc 1 Y).filter (fun a => ¬ p ∣ a ∧ Y < p * a),
        realMoebiusStep a) =
      ((mertensSummatoryInt Y : ℤ) : ℝ) := by
  rw [mertensSummatoryInt_real_eq_sum_Icc_realMoebiusStep]
  have hmult := sum_Icc_filter_prime_dvd_realMoebiusStep hp Y
  have hpt : ∀ n ∈ Finset.Icc 1 Y,
      realMoebiusStep n =
        ((if p ∣ n then realMoebiusStep n else 0) +
          (if ¬ p ∣ n ∧ p * n ≤ Y then realMoebiusStep n else 0)) +
          (if ¬ p ∣ n ∧ Y < p * n then realMoebiusStep n else 0) := by
    intro n _hn
    by_cases h1 : p ∣ n
    · simp [h1]
    · by_cases h2 : p * n ≤ Y
      · have h3 : ¬ Y < p * n := not_lt.mpr h2
        simp [h1, h2, h3]
      · have h3 : Y < p * n := lt_of_not_ge h2
        simp [h1, h2, h3]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter, hmult]
  ring

/-! ## The single owner-two cell -/

/-- No prime coordinate lies below the first owner `2`. -/
theorem squarefreeLowerPrimeSignature_two (n : ℕ) :
    squarefreeLowerPrimeSignature 2 n = ∅ := by
  unfold squarefreeLowerPrimeSignature squarefreePrimeFace
  apply Finset.filter_false_of_mem
  intro q hq
  have hq2 := (Nat.prime_of_mem_primeFactors hq).two_le
  omega

/-- A site beyond the owner-two clip is past the root and past every odd
q² daughter cutoff, so its AMP weight is exactly one. -/
theorem lowOwnerZeroFrequencyMobiusWeight_eq_one_of_ownerTwo_clipped
    {R a : ℕ} (hR : 2 ≤ R) (ha : squareRootEndpoint R < 2 * a) :
    lowOwnerZeroFrequencyMobiusWeight R a = 1 := by
  have hRa : R ≤ a := by
    unfold squareRootEndpoint at ha
    have h1 : 2 * R ≤ R * R := Nat.mul_le_mul_right R hR
    rw [sq] at ha
    generalize R * R = s at ha h1
    omega
  have hrec : lowOwnerReciprocalDaughterWeight R a = 0 := by
    unfold lowOwnerReciprocalDaughterWeight
    apply Finset.sum_eq_zero
    intro q hq
    have hq' : q ∈ (primesUpTo (R - 1)).erase 2 := (Finset.mem_sdiff.mp hq).1
    rcases Finset.mem_erase.mp hq' with ⟨hq2, hqP⟩
    have hqprime : q.Prime := (mem_primesUpTo.mp hqP).1
    have hq3 : 3 ≤ q := by
      have := hqprime.two_le
      omega
    have hqq : 9 ≤ q * q := Nat.mul_le_mul hq3 hq3
    have hnot : ¬ a ≤ rawQ2ChildCutoff R q := by
      intro hle
      unfold rawQ2ChildCutoff at hle
      have hmul : a * (q * q) ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le (by omega)).1 hle
      have h9 : a * 9 ≤ a * (q * q) := Nat.mul_le_mul_left a hqq
      have hlt : a * 9 < 2 * a := lt_of_le_of_lt (h9.trans hmul) ha
      omega
    simp [hnot]
  unfold lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailWeight
  rw [if_pos hRa, hrec]
  norm_num

/-- **The owner-two clipped exit is the top Mertens value.** -/
theorem lowOwnerFirstOwnerClippedAmplitude_two_eq_topMertens
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerFirstOwnerClippedAmplitude R 2 ∅ =
      ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ) := by
  rw [← sum_Icc_pFree_clipped_realMoebiusStep_eq_mertens Nat.prime_two]
  unfold lowOwnerFirstOwnerClippedAmplitude lowOwnerFirstOwnerClippedBaseFiber
    lowOwnerFirstOwnerBaseFiber lowOwnerNonzeroMobiusCarrier
  rw [Finset.filter_filter, Finset.filter_filter, Finset.sum_filter,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [squarefreeLowerPrimeSignature_two, true_and]
  by_cases hP : ¬ 2 ∣ a ∧ squareRootEndpoint R < 2 * a
  · have hw := lowOwnerZeroFrequencyMobiusWeight_eq_one_of_ownerTwo_clipped hR hP.2
    by_cases hmu : realMoebiusStep a = 0
    · simp [hmu]
    · simp [hP, hmu, hw, lowOwnerZeroFrequencyMobiusSite]
  · rw [if_neg hP, if_neg]
    intro h
    apply hP
    tauto

/-- The two owner-two branches exhaust the whole physical clock. -/
theorem lowOwnerFirstOwnerBase_add_child_two_eq_amplitude (R : ℕ) :
    lowOwnerFirstOwnerBaseAmplitude R 2 ∅ +
        lowOwnerFirstOwnerChildAmplitude R 2 ∅ =
      lowOwnerZeroFrequencyMobiusAmplitude R := by
  unfold lowOwnerFirstOwnerBaseAmplitude lowOwnerFirstOwnerChildAmplitude
    lowOwnerFirstOwnerBaseFiber lowOwnerFirstOwnerChildFiber
    lowOwnerNonzeroMobiusCarrier lowOwnerZeroFrequencyMobiusAmplitude
  rw [Finset.filter_filter, Finset.filter_filter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [squarefreeLowerPrimeSignature_two, true_and,
    lowOwnerZeroFrequencyMobiusSite]
  by_cases hmu : realMoebiusStep n = 0
  · simp [hmu]
  · by_cases h2 : 2 ∣ n <;> simp [hmu, h2]

/-- **The owner-two compensated interior is `Q_R - M(R-1)`.** -/
theorem lowOwnerFirstOwnerCompensatedInteriorAmplitude_two_eq
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerFirstOwnerCompensatedInteriorAmplitude R 2 ∅ =
      lowOwnerReciprocalMertensColumnReal R -
        ((mertensSummatoryInt (R - 1) : ℤ) : ℝ) := by
  have hblock :=
    lowOwnerFirstOwnerBase_add_child_eq_compensated_add_clipped
      (R := R) (sig := ∅) Nat.prime_two
  rw [lowOwnerFirstOwnerBase_add_child_two_eq_amplitude,
    lowOwnerFirstOwnerClippedAmplitude_two_eq_topMertens hR,
    lowOwnerZeroFrequencyMobiusAmplitude_eq_tail_add_reciprocal,
    lowOwnerFarTailAmplitudeReal_eq_Icc R hR] at hblock
  have hRX : R ≤ squareRootEndpoint R := le_squareRootEndpoint_self hR
  have htail := sum_Icc_realMoebiusStep_eq_mertens_sub
    (a := R) (b := squareRootEndpoint R) (by omega) (by omega)
  rw [htail] at hblock
  linarith

/-- The owner-two exact block on the whole AMP amplitude.  With the two
evaluations above it reads `A_R = (Q_R - M(R-1)) + M(X_R)`. -/
theorem lowOwnerZeroFrequencyMobiusAmplitude_eq_ownerTwoInterior_add_clipped
    (R : ℕ) :
    lowOwnerZeroFrequencyMobiusAmplitude R =
      lowOwnerFirstOwnerCompensatedInteriorAmplitude R 2 ∅ +
        lowOwnerFirstOwnerClippedAmplitude R 2 ∅ := by
  rw [← lowOwnerFirstOwnerBase_add_child_two_eq_amplitude,
    lowOwnerFirstOwnerBase_add_child_eq_compensated_add_clipped Nat.prime_two]

/-! ## Consequences for the packaged recurrence -/

/-- The square-endpoint energy of the packaged recurrence is literally the
square of the owner-two clipped exit. -/
theorem squareEndpointMertensEnergyReal_eq_ownerTwoClipped_sq
    {R : ℕ} (hR : 2 ≤ R) :
    squareEndpointMertensEnergyReal R =
      lowOwnerFirstOwnerClippedAmplitude R 2 ∅ ^ 2 := by
  rw [lowOwnerFirstOwnerClippedAmplitude_two_eq_topMertens hR]
  rfl

/-- The packaged recurrence written on the owner-two clipped exit. -/
def OwnerTwoClippedExitRoundedOddQ2EnergyStep (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    2 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerFirstOwnerClippedAmplitude R 2 ∅ ^ 2 ≤
      C * (R : ℝ) ^ 2 * K +
        4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          squareEndpointMertensEnergyReal (roundedQ2ChildRoot R q)

/-- **Name-lock.**  The remaining square-endpoint recurrence is, with the same
constant, exactly a recurrence for the owner-two clipped exit.  It is not a
statement about the compensated interior. -/
theorem squareEndpointRoundedOddQ2EnergyStep_iff_ownerTwoClippedExit
    (C : ℝ) :
    SquareEndpointRoundedOddQ2EnergyStep C ↔
      OwnerTwoClippedExitRoundedOddQ2EnergyStep C := by
  constructor
  · intro h R K hR hK
    rw [← squareEndpointMertensEnergyReal_eq_ownerTwoClipped_sq hR]
    exact h R K hR hK
  · intro h R K hR hK
    rw [squareEndpointMertensEnergyReal_eq_ownerTwoClipped_sq hR]
    exact h R K hR hK

/-- The reciprocal column inherits the compiled quarter frame. -/
theorem lowOwnerReciprocalMertensColumnReal_sq_le_quarter_energy_ownerTwo
    (R : ℕ) :
    lowOwnerReciprocalMertensColumnReal R ^ 2 ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have h := lowOwnerCriticalMertensSynthesis_energy_le_quarter R 0
  rw [lowOwnerCriticalMertensSynthesis_zero_eq_reciprocalColumn R,
    ← lowOwnerReciprocalMertensColumnReal_cast R,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- **Unconditional interior bound.**  The globally reassembled owner-two
compensated interior needs no new arithmetic input: the quarter frame and the
envelope at the single root value `R-1` already give
`I^2 <= E_R/2 + 8 R K`. -/
theorem lowOwnerFirstOwnerCompensatedInteriorAmplitude_two_sq_le
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R) (hK : LowerMertensCriticalEnvelope R K) :
    lowOwnerFirstOwnerCompensatedInteriorAmplitude R 2 ∅ ^ 2 ≤
      (1 / 2 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        8 * (R : ℝ) * K := by
  rw [lowOwnerFirstOwnerCompensatedInteriorAmplitude_two_eq hR]
  have hQ := lowOwnerReciprocalMertensColumnReal_sq_le_quarter_energy_ownerTwo R
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  have hroot := hK.2 (R - 1) (by omega)
  have hsucc : ((R - 1 + 1 : ℕ) : ℝ) = (R : ℝ) := by
    congr 1
    omega
  rw [hsucc] at hroot
  set m : ℝ := ((mertensSummatoryInt (R - 1) : ℤ) : ℝ) with hm
  have hshift : (((mertensSummatoryInt (R - 1) - 1 : ℤ) : ℝ)) = m - 1 := by
    rw [hm]
    push_cast
    ring
  rw [hshift] at hroot
  set Q : ℝ := lowOwnerReciprocalMertensColumnReal R
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRK : 2 ≤ (R : ℝ) * K := by nlinarith
  have hm2 : m ^ 2 ≤ 4 * (R : ℝ) * K := by
    have hsplit : m ^ 2 ≤ 2 * (m - 1) ^ 2 + 2 := by
      nlinarith [sq_nonneg (m - 2)]
    have hroot' : (m - 1) ^ 2 ≤ (R : ℝ) * K := by
      linarith [mul_comm (R : ℝ) K]
    linarith
  have hQm : (Q - m) ^ 2 ≤ 2 * Q ^ 2 + 2 * m ^ 2 := by
    nlinarith [sq_nonneg (Q + m)]
  linarith

/-- **The proposed interior target is already a theorem.**  With exactly the
CORR-4 quantifiers, the globally reassembled owner-two compensated interior
satisfies `I^2 <= 4 E_R + 8 R^2 K` for every `R >= 2`.  Because this holds
unconditionally, an estimate of this form cannot be the missing quantitative
input: the endpoint value `M(X_R)` is carried entirely by the clipped exit. -/
theorem ownerTwoCompensatedInterior_fourEnergyBound_unconditional :
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      lowOwnerFirstOwnerCompensatedInteriorAmplitude R 2 ∅ ^ 2 ≤
        4 * canonicalRoughLowQ2DaughterEnergy R + 8 * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  have h := lowOwnerFirstOwnerCompensatedInteriorAmplitude_two_sq_le hR hK
  have hE := canonicalRoughLowQ2DaughterEnergy_nonneg R
  have hK0 : 0 ≤ K := hK.1
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hRR : (R : ℝ) * K ≤ (R : ℝ) ^ 2 * K := by
    refine mul_le_mul_of_nonneg_right ?_ hK0
    nlinarith
  nlinarith

end RHLean.Proof
