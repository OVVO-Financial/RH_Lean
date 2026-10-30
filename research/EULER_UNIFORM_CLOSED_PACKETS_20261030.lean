import Mathlib
import «research.EULER_UNIFORM_COMPLETED_COEFFICIENTS_20261030»

/-!
# Complete 2-adic arithmetic packets: the missing 4d partner

The original completed coefficient of 4d equals that of d when d is odd.
Thus an eligible original packet consists of d,2d,4d with coefficients
alpha,-2alpha,alpha. Pairing only d with 2d leaves a leading principal term;
including 4d cancels the constant uniform-residue mean.

Actual square-clock means are NOT uniform means: the quadratic-residue bias
and all three actual moving-admission terms are retained exactly below.
No unconditional bound on the complete original square-shell is assumed.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- A square product of two squarefree naturals forces equality. Consequently
no original STRICT unordered pair contributes at a square modulus. -/
theorem eulerCompletedProductCoeff_eq_zero_of_square
    (d : ℕ) (hs : IsSquare d) :
    eulerCompletedProductCoeff d = 0 := by
  unfold eulerCompletedProductCoeff eulerMovingProductCoeff
  apply Finset.sum_eq_zero
  intro b _hb
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hab : a * b = d
  · have hlt : a < b := by
      have := (Finset.mem_Icc.mp ha).2
      have := (Finset.mem_Icc.mp ha).1
      omega
    by_cases hma : μ a = 0
    · simp [hab, eulerMuQ, hma]
    by_cases hmb : μ b = 0
    · simp [hab, eulerMuQ, hmb]
    have hsa : Squarefree a := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hma
    have hsb : Squarefree b := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmb
    have hsab : IsSquare (a * b) := hab ▸ hs
    have hsba : IsSquare (b * a) := by simpa only [mul_comm] using hsab
    have heq : a = b := Nat.dvd_antisymm
      (hsa.dvd_of_isSquare_mul hsab) (hsb.dvd_of_isSquare_mul hsba)
    exact False.elim ((ne_of_lt hlt) heq)
  · simp only [ite_eq_right hab]

private theorem packet_four_mul_not_square
    (d : ℕ) (hs : ¬ IsSquare d) : ¬ IsSquare (4 * d) := by
  rintro ⟨k, hk⟩
  have hkmod : k % 2 = 0 := by
    have hh : (k * k) % 2 = 0 := by rw [← hk]; omega
    rw [Nat.mul_mod] at hh
    have hb : k % 2 < 2 := Nat.mod_lt _ (by decide)
    have hc : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hc with h | h
    · exact h
    · norm_num [h] at hh
  have hk2 : k = 2 * (k / 2) := by omega
  apply hs
  refine ⟨k / 2, ?_⟩
  nlinarith [hk]

/-- The genuine completed even-even partner has coefficient alpha_d,
uniformly across ALL odd moduli, including squareful exceptions. -/
theorem eulerCompletedProductCoeff_four
    (d : ℕ) (hd : Odd d) :
    eulerCompletedProductCoeff (4 * d) = eulerCompletedProductCoeff d := by
  by_cases hs : IsSquare d
  · have hs4 : IsSquare (4 * d) := by
      rcases hs with ⟨k, hk⟩
      refine ⟨2 * k, ?_⟩
      rw [hk]
      ring
    rw [eulerCompletedProductCoeff_eq_zero_of_square d hs,
      eulerCompletedProductCoeff_eq_zero_of_square (4 * d) hs4]
  · have hcop : Nat.Coprime 4 d := by
      simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using
        hd.coprime_two_left.pow_left 2
    have hfour : eulerPacketMobiusConvolution 4 = 1 := by decide +kernel
    have hm := eulerPacketMobiusConvolution_multiplicative.map_mul_of_coprime hcop
    rw [hfour, one_mul] at hm
    have h1 := eulerCompletedProductCoeff_twice_eq_convolution d hd.pos hs
    have h2 := eulerCompletedProductCoeff_twice_eq_convolution
      (4 * d) (by have := hd.pos; omega) (packet_four_mul_not_square d hs)
    linarith

/-- Complete fractional kernel BEFORE any absolute values or centering. -/
def eulerClosedPacketKernel (R d : ℕ) : ℚ :=
  eulerPacketRemainder R d -
  2 * eulerPacketRemainder R (2 * d) +
  eulerPacketRemainder R (4 * d)

/-- All three original product rows with their actual root-dependent weights. -/
def eulerPhysicalClosedPacket (R d : ℕ) : ℚ :=
  eulerPhysicalOddPacket R d +
  2 * eulerMovingProductCoeff R (4 * d) * eulerPacketRemainder R (4 * d)

/-- Full, signed activation correction for d, 2d AND 4d. -/
def eulerClosedPacketActivation (R d : ℕ) : ℚ :=
  eulerPacketActivationCorrection R d -
  2 * eulerUnadmittedProductCoeff R (4 * d) * eulerPacketRemainder R (4 * d)

/-- Uniform original closed packet: no missing composite partner or boundary. -/
theorem eulerPhysicalClosedPacket_uniform
    (R d : ℕ) (hd : Odd d) (hs : ¬ IsSquare d) :
    eulerPhysicalClosedPacket R d =
      2 * eulerCompletedProductCoeff d * eulerClosedPacketKernel R d +
      eulerClosedPacketActivation R d := by
  unfold eulerPhysicalClosedPacket
  rw [eulerPhysicalOddPacket_uniform R d hd hs]
  have h4 := eulerCompletedProductCoeff_four d hd
  unfold eulerClosedPacketKernel eulerClosedPacketActivation
    nativeEulerOddDoublingPacket oddDoublingPacket eulerPacketRemainder
    eulerUnadmittedProductCoeff
  rw [h4]
  ring

/-- At R>4d the actual three product rows are all fully admitted. -/
theorem eulerClosedPacketActivation_eq_zero
    (R d : ℕ) (hR : 4 * d < R) :
    eulerClosedPacketActivation R d = 0 := by
  unfold eulerClosedPacketActivation
  rw [eulerPacketActivationCorrection_eq_zero R d (by omega),
    eulerUnadmittedProductCoeff_eq_zero_of_lt R (4 * d) hR]
  ring

/-- No surrogate coefficients: this is the actual complete original packet. -/
theorem eulerPhysicalClosedPacket_eq_kernel
    (R d : ℕ) (hd : Odd d) (hs : ¬ IsSquare d) (hR : 4 * d < R) :
    eulerPhysicalClosedPacket R d =
      2 * eulerCompletedProductCoeff d * eulerClosedPacketKernel R d := by
  rw [eulerPhysicalClosedPacket_uniform R d hd hs,
    eulerClosedPacketActivation_eq_zero R d hR, add_zero]

/-- Mean of the fractional residue on ALL residues, not quadratic root residues. -/
def eulerUniformResidueMean (d : ℕ) : ℚ :=
  ((d : ℚ) - 1) / (2 * (d : ℚ))

/-- The genuine square-clock bias relative to the uniform-residue mean.
This term is retained; its quantitative Gauss bound needs an analytic proof. -/
def eulerSquareClockPrincipalBias (d : ℕ) : ℚ :=
  eulerPacketRootPrincipal d - eulerUniformResidueMean d

/-- The leading constant cancels in the complete 1,-2,1 packet. The small
rational remainder -1/(8d) is exact, not dropped as an approximation. -/
theorem eulerClosedUniformResidueMean (d : ℕ) (hd : 0 < d) :
    eulerUniformResidueMean d - 2 * eulerUniformResidueMean (2 * d) +
      eulerUniformResidueMean (4 * d) = -1 / (8 * (d : ℚ)) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  unfold eulerUniformResidueMean
  push_cast
  field_simp [hdq]
  ring

/-- The true principal has only quadratic-residue biases plus the explicit
1/d remainder. In contrast, the incomplete d/2d packet has a size-alpha mean. -/
theorem eulerClosedActualPrincipal_exact
    (d : ℕ) (hd : 0 < d) :
    2 * eulerCompletedProductCoeff d *
      (eulerPacketRootPrincipal d - 2 * eulerPacketRootPrincipal (2 * d) +
        eulerPacketRootPrincipal (4 * d)) =
      -eulerCompletedProductCoeff d / (4 * (d : ℚ)) +
      2 * eulerCompletedProductCoeff d *
        (eulerSquareClockPrincipalBias d -
          2 * eulerSquareClockPrincipalBias (2 * d) +
          eulerSquareClockPrincipalBias (4 * d)) := by
  have h := eulerClosedUniformResidueMean d hd
  unfold eulerSquareClockPrincipalBias
  linear_combination 2 * eulerCompletedProductCoeff d * h

/-- This identity retains every cross-packet interaction in a finite family.
No claim of independence or nonpositive cross covariance is made. -/
theorem eulerClosedFamily_energy_exact
    (S I : Finset ℕ) :
    (∑ R ∈ I, (∑ d ∈ S,
      2 * eulerCompletedProductCoeff d * eulerClosedPacketKernel R d) ^ 2) =
      ∑ d ∈ S, ∑ e ∈ S,
        (4 * eulerCompletedProductCoeff d * eulerCompletedProductCoeff e) *
          ∑ R ∈ I, eulerClosedPacketKernel R d * eulerClosedPacketKernel R e := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro R _hR
  ring

#print axioms eulerCompletedProductCoeff_eq_zero_of_square
#print axioms eulerCompletedProductCoeff_four
#print axioms eulerPhysicalClosedPacket_uniform
#print axioms eulerClosedUniformResidueMean
#print axioms eulerClosedActualPrincipal_exact
#print axioms eulerClosedFamily_energy_exact

end RHLean.Proof
