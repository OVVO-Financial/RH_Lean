import Mathlib
import RHLean.Proof.SignedTransportAmplificationAudit

/-!
# Strength of the packaged square-endpoint recurrence

`SquareEndpointRoundedOddQ2EnergyStep C` is the one quantitative input left
by the `17/18` terminal induction.  This file records how strong that single
inequality is, so that it is not mistaken for a routine bookkeeping bound.

The compiled closure turns the step into fixed endpoint amplification
`(M(R^2-1)-1)^2 <= A R^2 K`.  Here the amplification statement is iterated
without any epsilon loss:

* one squaring step: an envelope `K` at root `R` gives the envelope
  `(2A+8) K` at root `R^2`;
* hence, starting from the admissible unit envelope at `R = 2`, the envelope
  `B^j` holds at every root `2^(2^j)`, with `B = 2A+8`.

Unfolding the envelope, `(M(x)-1)^2 <= B^j (x+1)` for every `x < 2^(2^j)`.
Choosing the least such `j` gives `B^j <= B^2 (log_2 (x+1))^(log_2 B)`, i.e.
`M(x) = O(x^(1/2) (log x)^c)` for a fixed `c`.  That polylogarithmic Mertens
bound implies RH, and it is stronger than the bounds currently known to follow
from RH (which lose a factor `exp((log x)^(1/2) (log log x)^c)`).  This
literature comparison is commentary only; it is not formalized here.

Nothing in this file is assumed: every statement is an implication from the
open step, proved with the trivial Mertens increment bound only.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- Lower critical envelopes pass to smaller roots. -/
theorem lowerMertensCriticalEnvelope_mono_of_le
    {R S : ℕ} {K : ℝ} (hSR : S ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    LowerMertensCriticalEnvelope S K :=
  ⟨hK.1, fun y hy => hK.2 y (lt_of_lt_of_le hy hSR)⟩

/-- The integer Mertens increment is at most the length of the interval. -/
theorem abs_mertensSummatoryInt_sub_le
    {e y : ℕ} (hey : e ≤ y) :
    |((mertensSummatoryInt y : ℤ) : ℝ) - ((mertensSummatoryInt e : ℤ) : ℝ)| ≤
      ((y - e : ℕ) : ℝ) := by
  have h := norm_mertensSummatory_sub_le e y hey
  rw [← mertensSummatoryInt_cast y, ← mertensSummatoryInt_cast e,
    ← Int.cast_sub, Complex.norm_intCast, Int.cast_sub] at h
  exact h

/-- **One squaring step.**  Fixed endpoint amplification upgrades an envelope
at root `R` to the envelope `(2A+8) K` at root `R^2`. -/
theorem lowerMertensCriticalEnvelope_sq_of_amplification
    {A : ℝ} (hA : 0 ≤ A)
    (hamp : ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R → LowerMertensCriticalEnvelope R K →
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
          A * (R : ℝ) ^ 2 * K)
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    LowerMertensCriticalEnvelope (R ^ 2) ((2 * A + 8) * K) := by
  have hK1 : 1 ≤ K := one_le_of_lowerMertensCriticalEnvelope (by omega) hK
  have hK0 : 0 ≤ K := hK.1
  have hBK : 0 ≤ (2 * A + 8) * K := mul_nonneg (by linarith) hK0
  refine ⟨hBK, ?_⟩
  intro y hy
  by_cases hyR : y < R
  · have h := hK.2 y hyR
    have hKy : 0 ≤ K * ((y + 1 : ℕ) : ℝ) := by positivity
    have hextra : 0 ≤ (2 * A + 7) * (K * ((y + 1 : ℕ) : ℝ)) :=
      mul_nonneg (by linarith) hKy
    have hmono :
        K * ((y + 1 : ℕ) : ℝ) ≤ (2 * A + 8) * K * ((y + 1 : ℕ) : ℝ) := by
      linarith
    exact h.trans hmono
  · let S : ℕ := Nat.sqrt (y + 1)
    have hSsq : S ^ 2 ≤ y + 1 := Nat.sqrt_le' (y + 1)
    have hSlt : y + 1 < (S + 1) ^ 2 := Nat.lt_succ_sqrt' (y + 1)
    have hSR : S ≤ R := by
      have hmono : Nat.sqrt (y + 1) ≤ Nat.sqrt (R ^ 2) :=
        Nat.sqrt_le_sqrt (by omega)
      rwa [Nat.sqrt_eq'] at hmono
    have hSsqR : ((S : ℝ)) ^ 2 ≤ ((y + 1 : ℕ) : ℝ) := by
      exact_mod_cast hSsq
    by_cases hS2 : 2 ≤ S
    · have hampS := hamp S K hS2 (lowerMertensCriticalEnvelope_mono_of_le hSR hK)
      have hsq : (S + 1) ^ 2 = S ^ 2 + 2 * S + 1 := by ring
      have hey : squareRootEndpoint S ≤ y := by
        unfold squareRootEndpoint
        omega
      have hgapNat : y - squareRootEndpoint S ≤ 2 * S := by
        unfold squareRootEndpoint
        rw [hsq] at hSlt
        omega
      have hinc := abs_mertensSummatoryInt_sub_le hey
      have hgap : |((mertensSummatoryInt y : ℤ) : ℝ) -
          ((mertensSummatoryInt (squareRootEndpoint S) : ℤ) : ℝ)| ≤
            2 * (S : ℝ) :=
        hinc.trans (by exact_mod_cast hgapNat)
      set a : ℝ := ((mertensSummatoryInt (squareRootEndpoint S) : ℤ) : ℝ) - 1
        with ha
      set d : ℝ := ((mertensSummatoryInt y : ℤ) : ℝ) -
          ((mertensSummatoryInt (squareRootEndpoint S) : ℤ) : ℝ) with hd
      have hshiftS :
          (((mertensSummatoryInt (squareRootEndpoint S) - 1 : ℤ) : ℝ)) = a := by
        rw [ha]
        push_cast
        ring
      have hshiftY :
          (((mertensSummatoryInt y - 1 : ℤ) : ℝ)) = a + d := by
        rw [ha, hd]
        push_cast
        ring
      rw [hshiftS] at hampS
      rw [hshiftY]
      have hd2 : d ^ 2 ≤ 4 * (S : ℝ) ^ 2 := by
        have habs : |d| ≤ 2 * (S : ℝ) := hgap
        obtain ⟨hlo, hhi⟩ := abs_le.mp habs
        nlinarith
      have hsplit : (a + d) ^ 2 ≤ 2 * a ^ 2 + 2 * d ^ 2 := by
        nlinarith [sq_nonneg (a - d)]
      have hS0 : (0 : ℝ) ≤ (S : ℝ) ^ 2 := sq_nonneg _
      have hfinal :
          2 * (A * (S : ℝ) ^ 2 * K) + 8 * (S : ℝ) ^ 2 ≤
            (2 * A + 8) * K * (S : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hK1 hS0]
      have hscale :
          (2 * A + 8) * K * (S : ℝ) ^ 2 ≤
            (2 * A + 8) * K * ((y + 1 : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hSsqR hBK
      linarith
    · have hy2 : y ≤ 2 := by
        have hS1 : S + 1 ≤ 2 := by omega
        have h4 : (S + 1) ^ 2 ≤ 4 :=
          calc
            (S + 1) ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hS1 2
            _ = 4 := by norm_num
        omega
      have hnorm := norm_shiftedMertens_le_succ y
      have hen : shiftedMertensEnergy y ≤ ((y + 1 : ℕ) : ℝ) ^ 2 := by
        unfold shiftedMertensEnergy
        have hnn : 0 ≤ ‖RHLean.Analysis.mertensSummatory y - 1‖ := norm_nonneg _
        nlinarith [hnorm, hnn]
      rw [shiftedMertensEnergy_eq_intSquare] at hen
      have hy3 : ((y + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : y + 1 ≤ 3)
      have hsmall :
          ((y + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * A + 8) * K * ((y + 1 : ℕ) : ℝ) := by
        have h8 : 8 ≤ (2 * A + 8) * K := by
          nlinarith [mul_le_mul_of_nonneg_left hK1
            (by linarith : (0 : ℝ) ≤ 2 * A + 8)]
        have hy0 : (0 : ℝ) ≤ ((y + 1 : ℕ) : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h8 hy0,
          mul_le_mul_of_nonneg_right hy3 hy0]
      exact hen.trans hsmall

/-- **Double-exponential envelope.**  Fixed endpoint amplification gives the
envelope `B^j` at every root `2^(2^j)`. -/
theorem lowerMertensCriticalEnvelope_doubleExponential_of_amplification
    (hamp : SquareRootMertensEndpointAmplificationStatement) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ j : ℕ, LowerMertensCriticalEnvelope (2 ^ 2 ^ j) (B ^ j) := by
  rcases hamp with ⟨A, hA, hamp⟩
  refine ⟨2 * A + 8, by linarith, ?_⟩
  intro j
  induction j with
  | zero => simpa using lowerMertensCriticalEnvelope_two_one
  | succ j ih =>
      have hR : 2 ≤ 2 ^ 2 ^ j := by
        have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      have h := lowerMertensCriticalEnvelope_sq_of_amplification hA hamp hR ih
      have hpow : (2 ^ 2 ^ j) ^ 2 = 2 ^ 2 ^ (j + 1) := by
        rw [← pow_mul, ← pow_succ]
      rw [hpow] at h
      have hBpow : (2 * A + 8) ^ (j + 1) = (2 * A + 8) * (2 * A + 8) ^ j := by
        ring
      rw [hBpow]
      exact h

/-- **Strength of the open step.**  The packaged square-endpoint recurrence
forces the doubly-exponential envelope.  Unfolded: there is `B >= 1` such that
`(M(x)-1)^2 <= B^j (x+1)` whenever `x < 2^(2^j)`, a polylogarithmic
square-root Mertens bound. -/
theorem squareEndpointRoundedOddQ2EnergyStep_forces_polylogMertensEnvelope
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : SquareEndpointRoundedOddQ2EnergyStep C) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ j x : ℕ, x < 2 ^ 2 ^ j →
        (((mertensSummatoryInt x - 1 : ℤ) : ℝ) ^ 2) ≤
          B ^ j * ((x + 1 : ℕ) : ℝ) := by
  rcases lowerMertensCriticalEnvelope_doubleExponential_of_amplification
      (squareEndpointRoundedOddQ2EnergyStep_implies_endpointAmplification
        hC hstep) with ⟨B, hB, henv⟩
  exact ⟨B, hB, fun j x hx => (henv j).2 x hx⟩

end RHLean.Proof
