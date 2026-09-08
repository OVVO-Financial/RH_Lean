import RHLean.Proof.PostRootCovarianceRecordAbsorption

/-!
# Per-Mobius square-energy charge at post-root records

The record-step reduction leaves one physical outer covariance row after the
inherited high-prime row has been subtracted.  This file moves that object one
level deeper, to the individual Mobius square-energy increment.

At an active post-root divisor `p | W+1`, with cofactor `c = (W+1)/p`, fresh
prime transport gives `mu(W+1) = -mu(c)`.  The diagonal squares therefore
cancel exactly, and twice the surviving outer covariance row is the difference
of the two discrete Mertens-square increments:

`2 * outerRow = DeltaM2(W+1) - DeltaM2(c)`.

Thus a positive #600 record is not merely controlled by a cumulative family
sum: its individual Mobius row is paid by a literal difference of cumulative
Mertens square-energy rows.  The fresh-prime specialization has lower seat
`c=1`, so `DeltaM2(W+1) = 1 + 2 * innovation`.

The final section also records the sharp unconditional finite-horizon ceiling
coming directly from the already-proved `E(W) <= W^2`: for `0 <= eps <= 1`,
`envelope_eps(X) <= X^(1-eps)`.  This corrects the weaker constant-three
ceiling inherited from the source branch; it does not claim a subquadratic
remainder bound.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Discrete cumulative Mertens square-energy row belonging to the Mobius atom
at index `c`. -/
def realMertensSquareStep (c : ℕ) : ℝ :=
  realMertensLength (c + 1) ^ 2 - realMertensLength c ^ 2

/-- The square-energy row is its diagonal unit plus twice its covariance row. -/
theorem realMertensSquareStep_eq_diagonal_add_two_mul_row (c : ℕ) :
    realMertensSquareStep c =
      realMoebiusStep c ^ 2 + 2 * realMoebiusStep c * realMertensLength c := by
  unfold realMertensSquareStep
  exact realMertensLength_sq_succ_sub_eq_diagonal_add_two_mul_row c

/-- **Per-Mobius high-transport identity.**  On an active post-root divisor,
the physical row after subtracting its inherited lower row is exactly half the
difference of the corresponding cumulative square-energy rows.  The two
Mobius diagonals cancel because the fresh prime reverses the atom sign. -/
theorem two_mul_postRootRecordOuterRowNumerator_eq_squareStep_sub_lower
    {W p : ℕ} (hp : p.Prime)
    (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1) :
    2 * (realMoebiusStep (W + 1) * realMertensLength (W + 1) -
      postRootPrimeFamilyCovarianceRowTotal W) =
      realMertensSquareStep (W + 1) -
        realMertensSquareStep ((W + 1) / p) := by
  have hpRoot := (mem_postRootPrimeFamilySet.mp hmem).1
  have hlt : W + 1 < p * p := (Nat.sqrt_lt).1 hpRoot
  have hc : (W + 1) / p < p :=
    (Nat.div_lt_iff_lt_mul hp.pos).2 hlt
  have hmul : p * ((W + 1) / p) = W + 1 := Nat.mul_div_cancel' hdvd
  have hquot : W / p + 1 = (W + 1) / p := by
    rw [Nat.succ_div, if_pos hdvd]
  have hrow :
      postRootPrimeFamilyCovarianceRowTotal W =
        realMoebiusStep ((W + 1) / p) *
          realMertensLength ((W + 1) / p) := by
    rw [postRootPrimeFamilyCovarianceRowTotal_eq_single_of_dvd hmem hdvd,
      postRootLowerCovarianceRow_eq_ite, if_pos hdvd, hquot]
  have hmu :
      realMoebiusStep (W + 1) = -realMoebiusStep ((W + 1) / p) := by
    rw [← hmul, realMoebiusStep_prime_mul_of_lt hp hc]
  rw [hrow, realMertensSquareStep_eq_diagonal_add_two_mul_row,
    realMertensSquareStep_eq_diagonal_add_two_mul_row, hmu]
  ring

/-- An active post-root divisor rules out a simultaneous prime-square wall, so
the local innovation is exactly the physical outer row. -/
theorem postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor
    {W p : ℕ} (hp : p.Prime)
    (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1) :
    postRootCovarianceLocalInnovation W =
      realMoebiusStep (W + 1) * realMertensLength (W + 1) -
        postRootPrimeFamilyCovarianceRowTotal W := by
  have hdepart : postRootPrimeFamilyCovarianceDeparture W = 0 := by
    apply postRootPrimeFamilyCovarianceDeparture_eq_zero_of_not_primeSquare
    intro q hq hsq
    have hpdvd : p ∣ q * q := by
      rw [hsq]
      exact hdvd
    have hpq : p = q := by
      rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp h
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    have hroot := (mem_postRootPrimeFamilySet.mp hmem).1
    rw [hpq, ← hsq, Nat.sqrt_eq] at hroot
    exact lt_irrefl _ hroot
  rw [postRootCovarianceLocalInnovation_eq_row_sub_inherited_add_departure,
    hdepart, add_zero]

/-- **Record-row square charge.**  At a positive record carried by an active
post-root divisor, the whole new envelope times one endpoint power is strictly
below half the difference of the physical and inherited cumulative square rows.
This is the per-Mobius-to-cumulative bridge, before any family aggregation. -/
theorem two_mul_envelope_succ_mul_rpow_lt_squareStep_sub_lower_of_record
    (ε : ℝ) (hε : 0 ≤ ε) {W p : ℕ} (hW : 2 ≤ W)
    (hp : p.Prime) (hmem : p ∈ postRootPrimeFamilySet (W + 1))
    (hdvd : p ∣ W + 1)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    2 * postRootCovariancePowerEnvelope ε (W + 1) *
        Real.rpow ((W + 1 : ℕ) : ℝ) ε <
      realMertensSquareStep (W + 1) -
        realMertensSquareStep ((W + 1) / p) := by
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hW hrec
  have hlocal :=
    postRootCovarianceLocalInnovation_eq_outerRow_of_activePostRootDivisor hp hmem hdvd
  have hcharge :=
    two_mul_postRootRecordOuterRowNumerator_eq_squareStep_sub_lower hp hmem hdvd
  rw [hlocal] at hthr
  nlinarith

/-- At a fresh prime the lower square row is the unit row at `1`, hence the
physical square increment is exactly `1 + 2 * innovation`. -/
theorem realMertensSquareStep_eq_one_add_two_mul_localInnovation_of_prime
    {W : ℕ} (hprime : (W + 1).Prime) :
    realMertensSquareStep (W + 1) =
      1 + 2 * postRootCovarianceLocalInnovation W := by
  rw [realMertensSquareStep_eq_diagonal_add_two_mul_row,
    postRootCovarianceLocalInnovation_eq_neg_prefix_of_prime hprime]
  simp [realMoebiusStep, ArithmeticFunction.moebius_apply_prime hprime]
  ring

/-- Fresh-prime records are therefore paid directly by the positive square
energy created by that single prime step. -/
theorem two_mul_envelope_succ_mul_rpow_lt_squareStep_sub_one_of_prime_record
    (ε : ℝ) (hε : 0 ≤ ε) {W : ℕ} (hW : 2 ≤ W)
    (hprime : (W + 1).Prime)
    (hrec : 0 < postRootCovariancePowerRecordExcess ε W) :
    2 * postRootCovariancePowerEnvelope ε (W + 1) *
        Real.rpow ((W + 1 : ℕ) : ℝ) ε <
      realMertensSquareStep (W + 1) - 1 := by
  have hthr :=
    postRootCovariancePowerEnvelope_succ_mul_rpow_lt_localInnovation_of_recordExcess_pos
      ε hε hW hrec
  have hs := realMertensSquareStep_eq_one_add_two_mul_localInnovation_of_prime hprime
  nlinarith

/-! ## Sharp unconditional finite-horizon ceiling -/

private theorem endpoint_sq_div_postRootPower_eq_rpow_one_sub
    (ε : ℝ) {W : ℕ} (hW : 0 < W) :
    (W : ℝ) ^ 2 / Real.rpow (W : ℝ) (1 + ε) =
      Real.rpow (W : ℝ) (1 - ε) := by
  have hpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have htwo : Real.rpow (W : ℝ) (2 : ℝ) = (W : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (W : ℝ) 2
  calc
    (W : ℝ) ^ 2 / Real.rpow (W : ℝ) (1 + ε) =
        Real.rpow (W : ℝ) (2 : ℝ) / Real.rpow (W : ℝ) (1 + ε) := by
          rw [htwo]
    _ = Real.rpow (W : ℝ) ((2 : ℝ) - (1 + ε)) :=
      (Real.rpow_sub hpos (2 : ℝ) (1 + ε)).symm
    _ = Real.rpow (W : ℝ) (1 - ε) := by congr 1 <;> ring

/-- The quadratic physical carrier bound already gives the exact normalized
ceiling `W^(1-eps)` at one seat. -/
theorem postRootCovariancePowerSeat_le_rpow_one_sub
    (ε : ℝ) {W : ℕ} (hW : 2 ≤ W) :
    postRootCovariancePowerSeat ε W ≤ Real.rpow (W : ℝ) (1 - ε) := by
  have hWpos : 0 < W := by omega
  have hpowpos : 0 < Real.rpow (W : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hWpos) _
  unfold postRootCovariancePowerSeat
  rw [if_pos hW]
  apply max_le
  · exact Real.rpow_nonneg (Nat.cast_nonneg W) _
  · calc
      postRootCovarianceRemainder W /
          Real.rpow (W : ℝ) (1 + ε) ≤
        (W : ℝ) ^ 2 / Real.rpow (W : ℝ) (1 + ε) :=
          div_le_div_of_nonneg_right (postRootCovarianceRemainder_le_endpoint_sq W)
            hpowpos.le
      _ = Real.rpow (W : ℝ) (1 - ε) :=
        endpoint_sq_div_postRootPower_eq_rpow_one_sub ε hWpos

/-- **Sharp unconditional envelope ceiling.**  For `0 <= eps <= 1`, the running
#600 envelope is at most `X^(1-eps)`.  This is stronger than the inherited
constant-three record ceiling, but it is only a repackaging of `E(W) <= W^2`:
multiplying back by `W^(1+eps)` still gives the quadratic remainder bound. -/
theorem postRootCovariancePowerEnvelope_le_rpow_one_sub
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {X : ℕ} (hX : 2 ≤ X) :
    postRootCovariancePowerEnvelope ε X ≤ Real.rpow (X : ℝ) (1 - ε) := by
  have hexp : 0 ≤ 1 - ε := by linarith
  induction X, hX using Nat.le_induction with
  | base =>
      have hprev : postRootCovariancePowerEnvelope ε 1 = 0 := by
        simp [postRootCovariancePowerEnvelope, postRootCovariancePowerSeat]
      rw [show (2 : ℕ) = 1 + 1 by norm_num,
        postRootCovariancePowerEnvelope, hprev]
      rw [max_eq_right (postRootCovariancePowerSeat_nonneg ε 2)]
      exact postRootCovariancePowerSeat_le_rpow_one_sub ε (by norm_num)
  | succ N h2N ih =>
      rw [postRootCovariancePowerEnvelope]
      apply max_le
      · have hmono :
            Real.rpow (N : ℝ) (1 - ε) ≤
              Real.rpow ((N + 1 : ℕ) : ℝ) (1 - ε) := by
          refine Real.rpow_le_rpow (Nat.cast_nonneg N) ?_ hexp
          exact_mod_cast Nat.le_succ N
        exact ih.trans hmono
      · exact postRootCovariancePowerSeat_le_rpow_one_sub ε (by omega)

end RHLean.Proof
