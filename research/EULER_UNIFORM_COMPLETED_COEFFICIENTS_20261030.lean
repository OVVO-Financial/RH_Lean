import Mathlib
import «research.EULER_PHYSICAL_COMPLETE_PACKET_20261030»

/-!
# Uniform ORIGINAL completed coefficients, not a free packet coefficient

For every positive nonsquare d, the original unordered coefficient is half
of the actual Dirichlet convolution mu*mu. Multiplicativity then proves
alpha(2d) = -2 alpha(d) for every ODD nonsquare d, including all legitimate
cubefree composite packets. This is not an assumption about the coefficients.
The inherited physical packet keeps both original activation corrections.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- The actual rational Mobius Dirichlet square. -/
def eulerPacketMobiusConvolution : ArithmeticFunction ℚ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℚ) *
    (ArithmeticFunction.moebius : ArithmeticFunction ℚ)

private def packetCoefficientKernel (d a b : ℕ) : ℚ :=
  if a * b = d then 1 else 0

private def packetFullCoefficient (d : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 d, eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 d, eulerMuQ a * packetCoefficientKernel d a b

private theorem packetSymmetricSquare (N : ℕ) (c : ℕ → ℚ)
    (F : ℕ → ℕ → ℚ) (hF : ∀ a b, F a b = F b a) :
    (∑ b ∈ Finset.Icc 1 N,
      c b * (∑ a ∈ Finset.Icc 1 N, c a * F a b)) =
      (∑ b ∈ Finset.Icc 1 N, c b ^ 2 * F b b) +
      2 * ∑ b ∈ Finset.Icc 1 N,
        c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hswap :
          (∑ b ∈ Finset.Icc 1 N, c b * (c (N + 1) * F (N + 1) b)) =
          c (N + 1) * (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        rw [hF (N + 1) b]
        ring
      have hQ :
          (∑ b ∈ Finset.Icc 1 (N + 1),
            c b * (∑ a ∈ Finset.Icc 1 (N + 1), c a * F a b)) =
          (∑ b ∈ Finset.Icc 1 N,
            c b * (∑ a ∈ Finset.Icc 1 N, c a * F a b)) +
          2 * c (N + 1) *
            (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) +
          c (N + 1) ^ 2 * F (N + 1) (N + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp_rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, hswap]
        ring
      have hD :
          (∑ b ∈ Finset.Icc 1 (N + 1), c b ^ 2 * F b b) =
          (∑ b ∈ Finset.Icc 1 N, c b ^ 2 * F b b) +
            c (N + 1) ^ 2 * F (N + 1) (N + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      have hB :
          (∑ b ∈ Finset.Icc 1 (N + 1),
            c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b)) =
          (∑ b ∈ Finset.Icc 1 N,
            c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b)) +
          c (N + 1) * (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp only [show N + 1 - 1 = N by omega]
      rw [hQ, hD, hB, ih]
      ring

private theorem packetAntidiagonal_eq_filter (d : ℕ) (hd : 0 < d) :
    d.divisorsAntidiagonal =
      ((Finset.Icc 1 d) ×ˢ (Finset.Icc 1 d)).filter
        (fun p : ℕ × ℕ => p.1 * p.2 = d) := by
  ext p
  simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨hab, _⟩
    have ha : 0 < p.1 := by nlinarith
    have hb : 0 < p.2 := by nlinarith
    have hal : p.1 ≤ d := by
      calc
        p.1 = p.1 * 1 := (mul_one _).symm
        _ ≤ p.1 * p.2 := Nat.mul_le_mul_left _ hb
        _ = d := hab
    have hbl : p.2 ≤ d := by
      calc
        p.2 = 1 * p.2 := (one_mul _).symm
        _ ≤ p.1 * p.2 := Nat.mul_le_mul_right _ ha
        _ = d := hab
    exact ⟨⟨⟨ha, hal⟩, ⟨hb, hbl⟩⟩, hab⟩
  · rintro ⟨_, hab⟩
    exact ⟨hab, ne_of_gt hd⟩

private theorem packetFullCoefficient_eq_convolution
    (d : ℕ) (hd : 0 < d) :
    packetFullCoefficient d = eulerPacketMobiusConvolution d := by
  unfold eulerPacketMobiusConvolution
  rw [ArithmeticFunction.mul_apply, packetAntidiagonal_eq_filter d hd,
    Finset.sum_filter, Finset.sum_product]
  unfold packetFullCoefficient
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [packetCoefficientKernel, eulerMuQ, ArithmeticFunction.intCoe_apply]
  by_cases hab : a * b = d
  · have hba : b * a = d := by simpa only [mul_comm] using hab
    rw [ite_eq_left hab, ite_eq_left hba]
    ring
  · have hba : b * a ≠ d := by simpa only [mul_comm] using hab
    rw [ite_eq_right hab, ite_eq_right hba]
    ring

/-- The factor-pair sum in #1055 equals half the original Mobius convolution
for every positive nonsquare modulus, not just the numerical example 15. -/
theorem eulerCompletedProductCoeff_twice_eq_convolution
    (d : ℕ) (hd : 0 < d) (hns : ¬ IsSquare d) :
    2 * eulerCompletedProductCoeff d = eulerPacketMobiusConvolution d := by
  have hsym : ∀ a b, packetCoefficientKernel d a b =
      packetCoefficientKernel d b a := by
    intro a b
    simp only [packetCoefficientKernel, mul_comm]
  have hfull := packetSymmetricSquare d eulerMuQ
    (packetCoefficientKernel d) hsym
  have hdiag : (∑ b ∈ Finset.Icc 1 d,
      eulerMuQ b ^ 2 * packetCoefficientKernel d b b) = 0 := by
    apply Finset.sum_eq_zero
    intro b _hb
    have hne : b * b ≠ d := by
      intro heq
      exact hns ⟨b, heq.symm⟩
    simp only [packetCoefficientKernel, ite_eq_right hne, mul_zero]
  rw [hdiag, zero_add] at hfull
  have hrewrite : packetFullCoefficient d =
      2 * eulerCompletedProductCoeff d := by
    simpa only [packetFullCoefficient, eulerCompletedProductCoeff,
      eulerMovingProductCoeff, Nat.add_sub_cancel, packetCoefficientKernel,
      Finset.mul_sum, mul_ite, mul_one, mul_zero] using hfull
  rw [← hrewrite, packetFullCoefficient_eq_convolution d hd]

/-- Squaring under Dirichlet convolution preserves multiplicativity of the
ACTUAL Mobius function. -/
theorem eulerPacketMobiusConvolution_multiplicative :
    eulerPacketMobiusConvolution.IsMultiplicative := by
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    ArithmeticFunction.isMultiplicative_moebius.intCast

private theorem packetConvolution_two :
    eulerPacketMobiusConvolution 2 = -2 := by
  decide +kernel

private theorem packetConvolution_four :
    eulerPacketMobiusConvolution 4 = 1 := by
  decide +kernel

/-- Odd d has an even multiple 2d that is never a square. -/
theorem eulerOdd_double_not_square {d : ℕ} (hd : Odd d) :
    ¬ IsSquare (2 * d) := by
  rintro ⟨k, hk⟩
  have hmod : (2 * d) % 4 = 2 := by
    rcases hd with ⟨j, hj⟩
    omega
  have hs : (k * k) % 4 = 2 := by rw [← hk, hmod]
  rw [Nat.mul_mod] at hs
  have hr : k % 4 < 4 := Nat.mod_lt _ (by decide)
  have hc : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hc with h | h | h | h <;> norm_num [h] at hs

/-- UNIFORM original odd-doubling pairing across all odd nonsquare moduli.
No freestanding alpha_(2d)=-2alpha_d premise is used. -/
theorem eulerCompletedProductCoeff_double
    (d : ℕ) (hd : Odd d) (hns : ¬ IsSquare d) :
    eulerCompletedProductCoeff (2 * d) =
      -2 * eulerCompletedProductCoeff d := by
  have hdpos : 0 < d := hd.pos
  have hleft := eulerCompletedProductCoeff_twice_eq_convolution
    (2 * d) (by omega) (eulerOdd_double_not_square hd)
  have hright := eulerCompletedProductCoeff_twice_eq_convolution d hdpos hns
  have hmul := eulerPacketMobiusConvolution_multiplicative.map_mul_of_coprime
    hd.coprime_two_left
  rw [packetConvolution_two] at hmul
  linarith

/-- The actual coefficient exception of #1055 vanishes for EVERY eligible
odd nonsquare product, including shared-prime cubefree composite products. -/
theorem eulerDoublingCoeffMismatch_eq_zero
    (d : ℕ) (hd : Odd d) (hns : ¬ IsSquare d) :
    eulerDoublingCoeffMismatch d = 0 := by
  unfold eulerDoublingCoeffMismatch
  rw [eulerCompletedProductCoeff_double d hd hns]
  ring

/-- Uniform physical pairing at ALL roots, with BOTH activation boundaries.
The right side is not declared a small quantity. -/
theorem eulerPhysicalOddPacket_uniform
    (R d : ℕ) (hd : Odd d) (hns : ¬ IsSquare d) :
    eulerPhysicalOddPacket R d =
      nativeEulerOddDoublingPacket (eulerCompletedProductCoeff d) d R +
        eulerPacketActivationCorrection R d := by
  rw [eulerPhysicalOddPacket_exact_decomposition,
    eulerDoublingCoeffMismatch_eq_zero d hd hns]
  ring

/-- After the ORIGINAL full admission threshold, the actual packet has
pointwise constant squared fluctuation. This is uniform, not finite testing. -/
theorem eulerPhysicalOddPacket_uniform_energy
    (R d : ℕ) (hd : Odd d) (hns : ¬ IsSquare d) (hR : 2 * d < R) :
    (eulerPhysicalOddPacket R d + eulerCompletedProductCoeff d) ^ 2 =
      eulerCompletedProductCoeff d ^ 2 := by
  rw [eulerPhysicalOddPacket_uniform R d hd hns,
    eulerPacketActivationCorrection_eq_zero R d hR, add_zero]
  exact nativeEulerOddDoublingPacket_centered_sq
    (eulerCompletedProductCoeff d) hd.pos

#print axioms eulerCompletedProductCoeff_twice_eq_convolution
#print axioms eulerCompletedProductCoeff_double
#print axioms eulerPhysicalOddPacket_uniform
#print axioms eulerPhysicalOddPacket_uniform_energy

end RHLean.Proof
