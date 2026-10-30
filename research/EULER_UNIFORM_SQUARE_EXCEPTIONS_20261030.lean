import Mathlib
import «research.EULER_UNIFORM_CLOSED_PACKETS_20261030»

/-!
# The square exceptions are original arithmetic and have root-scale mass

The uniform nonsquare packets do NOT cover the original columns 2*k^2.
This file proves their actual Mobius coefficient and an unconditional
pointwise/energy bound. No exception is silently hidden by centering.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- At a square only the diagonal survives in the actual convolution. -/
theorem eulerPacketMobiusConvolution_square (k : ℕ) :
    eulerPacketMobiusConvolution (k * k) = eulerMuQ k ^ 2 := by
  by_cases hk : k = 0
  · subst k
    simp [eulerPacketMobiusConvolution, eulerMuQ]
  unfold eulerPacketMobiusConvolution
  rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_eq_single (k, k)]
  · simp only [ArithmeticFunction.intCoe_apply, eulerMuQ]
    ring
  · intro p hp hne
    have hab : p.1 * p.2 = k * k := (Nat.mem_divisorsAntidiagonal.mp hp).1
    by_cases hma : μ p.1 = 0
    · simp [ArithmeticFunction.intCoe_apply, hma]
    by_cases hmb : μ p.2 = 0
    · simp [ArithmeticFunction.intCoe_apply, hmb]
    have hsa := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hma
    have hsb := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmb
    have hsab : IsSquare (p.1 * p.2) := ⟨k, hab⟩
    have hsba : IsSquare (p.2 * p.1) := by simpa only [mul_comm] using hsab
    have heq : p.1 = p.2 := Nat.dvd_antisymm
      (hsa.dvd_of_isSquare_mul hsab) (hsb.dvd_of_isSquare_mul hsba)
    have hpk : p.1 = k := by nlinarith
    have hpair : p = (k, k) := Prod.ext hpk (heq ▸ hpk)
    exact False.elim (hne hpair)
  · intro hnot
    have hmem : (k, k) ∈ (k * k).divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, mul_ne_zero hk hk⟩
    exact False.elim (hnot hmem)

/-- Genuine exceptional coefficient at twice an odd square, including k=1. -/
theorem eulerCompletedProductCoeff_double_square
    (k : ℕ) (hk : Odd k) :
    eulerCompletedProductCoeff (2 * (k * k)) = -(eulerMuQ k ^ 2) := by
  have hodd : Odd (k * k) := hk.mul hk
  have hpos : 0 < 2 * (k * k) := by have := hk.pos; positivity
  have hleft := eulerCompletedProductCoeff_twice_eq_convolution
    (2 * (k * k)) hpos (eulerOdd_double_not_square hodd)
  have hmul := eulerPacketMobiusConvolution_multiplicative.map_mul_of_coprime
    hodd.coprime_two_left
  have htwo : eulerPacketMobiusConvolution 2 = -2 := by decide +kernel
  rw [htwo, eulerPacketMobiusConvolution_square] at hmul
  linarith

/-- Actual square-clock residue, bounded at every modulus d>0. -/
theorem eulerPacketRemainder_bounds (R d : ℕ) (hd : 0 < d) :
    0 ≤ eulerPacketRemainder R d ∧ eulerPacketRemainder R d ≤ 1 := by
  have hq : (0 : ℚ) < d := by exact_mod_cast hd
  have hr : ((squareRootEndpoint R % d : ℕ) : ℚ) < d := by
    exact_mod_cast Nat.mod_lt (squareRootEndpoint R) hd
  unfold eulerPacketRemainder
  constructor
  · positivity
  · exact le_of_lt ((div_lt_iff₀ hq).mpr (by simpa using hr))

private theorem packetMuSquare_bounds (k : ℕ) :
    0 ≤ eulerMuQ k ^ 2 ∧ eulerMuQ k ^ 2 ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or k with h | h | h <;>
    simp [eulerMuQ, h]

/-- The literal exceptional original sum, indexed by its odd square roots. -/
def eulerClosedSquareException (R K : ℕ) : ℚ :=
  -2 * ∑ k ∈ Finset.Icc 1 K,
    if Odd k then eulerMuQ k ^ 2 * eulerPacketRemainder R (2 * (k * k)) else 0

/-- Uniform non-asymptotic signed exception payment: no Möbius cancellation
or imported growth theorem is needed. -/
theorem eulerClosedSquareException_abs_le (R K : ℕ) :
    |eulerClosedSquareException R K| ≤ 2 * (K : ℚ) := by
  let T : ℚ := ∑ k ∈ Finset.Icc 1 K,
    if Odd k then eulerMuQ k ^ 2 * eulerPacketRemainder R (2 * (k * k)) else 0
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      0 ≤ (if Odd k then eulerMuQ k ^ 2 *
        eulerPacketRemainder R (2 * (k * k)) else (0 : ℚ)) ∧
      (if Odd k then eulerMuQ k ^ 2 *
        eulerPacketRemainder R (2 * (k * k)) else (0 : ℚ)) ≤ 1 := by
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hf := eulerPacketRemainder_bounds R (2 * (k * k)) (by positivity)
    have hm := packetMuSquare_bounds k
    by_cases ho : Odd k
    · simp only [ite_eq_left ho]
      exact ⟨mul_nonneg hm.1 hf.1,
        (mul_le_mul hm.2 hf.2 hf.1 (by norm_num)).trans (by norm_num)⟩
    · simp only [ite_eq_right ho]
      norm_num
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun k hk => (hterm k hk).1)
  have hTK : T ≤ (K : ℚ) := by
    calc
      T ≤ ∑ _k ∈ Finset.Icc 1 K, (1 : ℚ) :=
        Finset.sum_le_sum (fun k hk => (hterm k hk).2)
      _ = (K : ℚ) := by simp [Nat.card_Icc]
  change |-2 * T| ≤ 2 * (K : ℚ)
  rw [abs_mul, abs_of_nonneg hT0]
  norm_num
  linarith

/-- The complete square-exception family has energy O(H Q) when K²≤Q.
This is an actual uniform source inequality, not a conditional consumer. -/
theorem eulerClosedSquareException_energy_le
    (I : Finset ℕ) (K Q : ℕ) (hK : K * K ≤ Q) :
    (∑ R ∈ I, eulerClosedSquareException R K ^ 2) ≤
      4 * (I.card : ℚ) * (Q : ℚ) := by
  have hKnat : K ^ 2 ≤ Q := by simpa only [pow_two] using hK
  have hKq : (K : ℚ) ^ 2 ≤ Q := by exact_mod_cast hKnat
  calc
    (∑ R ∈ I, eulerClosedSquareException R K ^ 2) ≤
        ∑ _R ∈ I, 4 * (Q : ℚ) := by
      apply Finset.sum_le_sum
      intro R _hR
      have h := eulerClosedSquareException_abs_le R K
      have hl := (abs_le.mp h).1
      have hr := (abs_le.mp h).2
      nlinarith [sq_nonneg (eulerClosedSquareException R K),
        mul_nonneg (sub_nonneg.mpr hr) (by linarith :
          0 ≤ eulerClosedSquareException R K + 2 * (K : ℚ))]
    _ = 4 * (I.card : ℚ) * (Q : ℚ) := by simp; ring

#print axioms eulerPacketMobiusConvolution_square
#print axioms eulerCompletedProductCoeff_double_square
#print axioms eulerClosedSquareException_abs_le
#print axioms eulerClosedSquareException_energy_le

end RHLean.Proof
