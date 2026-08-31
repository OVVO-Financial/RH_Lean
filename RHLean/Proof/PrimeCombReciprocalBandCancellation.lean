import Mathlib
import RHLean.Proof.PrimeCombVisualizationDynamics

/-!
# Arbitrary-endpoint reciprocal-band cancellation in the prime comb

The prime-comb animation already proves the exact one-prime post-root score law

`Delta_p(W) = 2 * (1 - M(floor(W/p)))`.

This file packages that law on the reciprocal quotient bands

`W/(z+1) < p <= W/z`.

Every prime in one such band has the same quotient `floor(W/p)=z`, hence the
same proper-multiple seat set `{2,...,z}`, the same signed cofactor channel
`M(z)-1`, and the same score correction `2*(1-M(z))`.

The adjacent-band finite difference is especially important:

`D(z+1) - D(z) = -2 * mu(z+1)`.

Thus the reciprocal bands are constant-action cells of the literal ordered-prime
walk, and each newly exposed lower cofactor changes the next-band correction in
the opposite direction of its Mobius sign.  These are exact finite identities;
no asymptotic estimate or RH-scale saving is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Prime coordinates in the reciprocal quotient band with quotient `z`. -/
def primeCombReciprocalBand (W z : ℕ) : Finset ℕ :=
  (Finset.Ioc (W / (z + 1)) (W / z)).filter Nat.Prime

@[simp] theorem mem_primeCombReciprocalBand
    {W z p : ℕ} :
    p ∈ primeCombReciprocalBand W z ↔
      W / (z + 1) < p ∧ p ≤ W / z ∧ p.Prime := by
  simp [primeCombReciprocalBand, and_assoc]

/-- Every coordinate in a positive reciprocal band has the advertised exact
quotient `floor(W/p)=z`. -/
theorem primeCombReciprocalBand_div_eq
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    W / p = z := by
  rcases mem_primeCombReciprocalBand.mp hp with ⟨hlower, hupper, _hpPrime⟩
  have hlo : z * p ≤ W := by
    have h := (Nat.le_div_iff_mul_le hz).1 hupper
    simpa [Nat.mul_comm] using h
  have hhi : W < (z + 1) * p := by
    have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < z + 1)).1 hlower
    simpa [Nat.mul_comm] using h
  exact Nat.div_eq_of_lt_le hlo hhi

/-- Band membership already includes primality. -/
theorem primeCombReciprocalBand_prime
    {W z p : ℕ} (hp : p ∈ primeCombReciprocalBand W z) :
    p.Prime :=
  (mem_primeCombReciprocalBand.mp hp).2.2

/-- A prime in a reciprocal band lies inside the ambient block. -/
theorem primeCombReciprocalBand_le_endpoint
    {W z p : ℕ} (hp : p ∈ primeCombReciprocalBand W z) :
    p ≤ W := by
  have hupper := (mem_primeCombReciprocalBand.mp hp).2.1
  exact hupper.trans (Nat.div_le_self W z)

/-- The geometric rake on a reciprocal band is literally the fixed cofactor
interval `{2,...,z}`. -/
theorem primeCombReciprocalBand_multiplierSet_eq
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    primeCombProperMultiplierSet p W = Finset.Icc 2 z := by
  unfold primeCombProperMultiplierSet
  rw [primeCombReciprocalBand_div_eq hz hp]

/-- Hence every prime in the band has exactly `z-1` candidate proper-multiple
seats.  Squareful cofactors among these seats contribute zero to the signed
cofactor channel below through `mu(c)=0`. -/
theorem primeCombReciprocalBand_seatCount
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    (primeCombProperMultiplierSet p W).card = z - 1 := by
  rw [card_primeCombProperMultiplierSet,
    primeCombReciprocalBand_div_eq hz hp]

/-- The signed cofactor channel is constant on a reciprocal band and is exactly
`M(z)-1`. -/
theorem primeCombReciprocalBand_channelMass_eq
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    primeCombTailChannelMass W p =
      RHLean.Analysis.mertensSummatory z - 1 := by
  have hpPrime := primeCombReciprocalBand_prime hp
  have hpW := primeCombReciprocalBand_le_endpoint hp
  rw [primeCombTailChannelMass_eq_mertens_sub_one hpPrime.pos hpW,
    primeCombReciprocalBand_div_eq hz hp]

/-- The constant signed correction attached to quotient band `z`. -/
def primeCombReciprocalBandKernel (z : ℕ) : ℂ :=
  2 * (1 - RHLean.Analysis.mertensSummatory z)

/-- Every prime in the same reciprocal band has the same post-root tail
correction. -/
theorem primeCombReciprocalBand_signedDelta_eq
    {W z p : ℕ} (hz : 0 < z)
    (hp : p ∈ primeCombReciprocalBand W z) :
    primeCombTailSignedDelta W p =
      primeCombReciprocalBandKernel z := by
  have hpPrime := primeCombReciprocalBand_prime hp
  have hpW := primeCombReciprocalBand_le_endpoint hp
  unfold primeCombReciprocalBandKernel
  rw [primeCombTailSignedDelta_eq hpPrime.pos hpW,
    primeCombReciprocalBand_div_eq hz hp]

/-- Total signed correction of an entire reciprocal band. -/
def primeCombReciprocalBandSignedDelta (W z : ℕ) : ℂ :=
  ∑ p ∈ primeCombReciprocalBand W z, primeCombTailSignedDelta W p

/-- Band aggregation introduces no new arithmetic: it is simply the number of
prime coordinates in the band times the one common lower-prefix correction. -/
theorem primeCombReciprocalBandSignedDelta_eq_card_mul
    (W z : ℕ) (hz : 0 < z) :
    primeCombReciprocalBandSignedDelta W z =
      ((primeCombReciprocalBand W z).card : ℂ) *
        primeCombReciprocalBandKernel z := by
  unfold primeCombReciprocalBandSignedDelta
  calc
    (∑ p ∈ primeCombReciprocalBand W z, primeCombTailSignedDelta W p) =
        ∑ p ∈ primeCombReciprocalBand W z,
          primeCombReciprocalBandKernel z := by
      apply Finset.sum_congr rfl
      intro p hp
      exact primeCombReciprocalBand_signedDelta_eq hz hp
    _ = ((primeCombReciprocalBand W z).card : ℂ) *
          primeCombReciprocalBandKernel z := by
      simp

/-- **Adjacent-band cancellation law.**  Exposing one additional lower cofactor
changes the next reciprocal-band correction by the opposite of twice its
Mobius sign.

This is the exact negative-feedback identity visible in the prime-comb movie. -/
theorem primeCombReciprocalBandKernel_succ_sub
    (z : ℕ) :
    primeCombReciprocalBandKernel (z + 1) -
        primeCombReciprocalBandKernel z =
      -2 * (((μ (z + 1) : ℤ) : ℂ)) := by
  unfold primeCombReciprocalBandKernel
  rw [RHLean.Analysis.mertensSummatory_succ]
  ring

/-- Equivalent recurrence form of the adjacent-band law. -/
theorem primeCombReciprocalBandKernel_succ
    (z : ℕ) :
    primeCombReciprocalBandKernel (z + 1) =
      primeCombReciprocalBandKernel z -
        2 * (((μ (z + 1) : ℤ) : ℂ)) := by
  have h := primeCombReciprocalBandKernel_succ_sub z
  linear_combination h

end RHLean.Proof
