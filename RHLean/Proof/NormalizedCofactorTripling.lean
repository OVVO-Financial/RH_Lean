import RHLean.Proof.NormalizedCofactorExpansion

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

/-- Möbius changes sign when a new prime factor `3` is introduced. -/
theorem moebius_three_mul
    (c : ℕ) (h3 : ¬ 3 ∣ c) :
    (((μ (3 * c) : ℤ) : ℚ)) = -(((μ c : ℤ) : ℚ)) := by
  have hcop : Nat.Coprime 3 c :=
    Nat.prime_three.coprime_iff_not_dvd.mpr h3
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  rw [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  push_cast
  ring

/-- The dyadic multiplicity weight is halved when a new prime factor `3` is introduced. -/
theorem alphaWeightRat_three_mul
    (n : ℕ) (h3 : ¬ 3 ∣ n) :
    alphaWeightRat (3 * n) = (1 / 2 : ℚ) * alphaWeightRat n := by
  unfold alphaWeightRat
  rw [distinctPrimeCount_three_mul n h3, pow_succ]
  field_simp

end RHLean.Proof
