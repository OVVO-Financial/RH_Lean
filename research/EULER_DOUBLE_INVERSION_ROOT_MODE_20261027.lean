import Mathlib
import «research.EULER_COUPLED_HEAD_ABELED_20261027»

/-!
# Original Mobius double inversion: paying the coupled principal root mode

A second genuine Mobius inversion at L=R+1 shows that the paired
q=1 endpoint and historical smooth drift contain a root-payable
scalar mode. This is NOT a fixed-eta estimate for the full residual;
the complementary small-a quotient tail remains signed and unpaid.

The proof below uses the original integer Mobius coefficients, the
actual floor kernel, and a genuine finite cutoff B with 2(B+1)>L.
No arbitrary coefficient vectors or new axioms.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- Every missing endpoint b>B in a sufficiently wide cutoff lies in the
exact unit-floor range floor(L/b)=1, including all endpoint conventions. -/
theorem eulerDoubleInversion_upper_floor_one
    (L B b : ℕ) (hB : B < b) (hbL : b ≤ L)
    (hhalf : L < 2 * (B + 1)) :
    L / b = 1 := by
  have hbpos : 0 < b := by omega
  have hfloorlo : 1 ≤ L / b :=
    (Nat.le_div_iff_mul_le hbpos).2 (by simpa using hbL)
  have hfloortop : L / b < 2 :=
    (Nat.div_lt_iff_lt_mul hbpos).2 (by nlinarith)
  omega

/-- A second ORIGINAL Mobius floor inversion pays the truncated
wide-cutoff principal b-mode exactly with only the missing short tail. -/
theorem eulerDoubleInversion_truncated_floor
    (L B : ℕ) (hL : 1 ≤ L) (hBL : B ≤ L)
    (hhalf : L < 2 * (B + 1)) :
    (∑ b ∈ Finset.Icc 1 B,
      (μ b : ℤ) * (((L / b : ℕ)) : ℤ)) =
        1 - (mertensSummatoryInt L - mertensSummatoryInt B) := by
  have hfloor (b : ℕ) (hb : b ∈ Finset.Ioc B L) :
      L / b = 1 :=
    eulerDoubleInversion_upper_floor_one L B b
      (Finset.mem_Ioc.mp hb).1 (Finset.mem_Ioc.mp hb).2 hhalf
  have htail :
      (∑ b ∈ Finset.Ioc B L,
        (μ b : ℤ) * (((L / b : ℕ)) : ℤ)) =
      ∑ b ∈ Finset.Ioc B L, (μ b : ℤ) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [hfloor b hb]
    ring
  have hIoc (n : ℕ) :
      Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext b
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsplit := Finset.sum_Ioc_consecutive
    (f := fun b : ℕ => (μ b : ℤ) * (((L / b : ℕ)) : ℤ))
      (Nat.zero_le B) hBL
  rw [hIoc B, hIoc L, htail] at hsplit
  have hfull := nativeSumMoebiusMulFloor L hL
  have hMtail := eulerMobius_Ioc_eq_historicalMertens B L hBL
  omega

/-- Rational-cast principal root mode, ready to insert into the FULL
coupled Abel source while retaining the complementary small-a drift. -/
theorem eulerDoubleInversion_truncated_floor_rat
    (L B : ℕ) (hL : 1 ≤ L) (hBL : B ≤ L)
    (hhalf : L < 2 * (B + 1)) :
    (∑ b ∈ Finset.Icc 1 B,
      eulerMuQ b * (((L / b : ℕ)) : ℚ)) =
      1 - (eulerHistoricalMertensQ L - eulerHistoricalMertensQ B) := by
  have hZ := eulerDoubleInversion_truncated_floor L B hL hBL hhalf
  unfold eulerMuQ eulerHistoricalMertensQ
  exact_mod_cast hZ

#print axioms eulerDoubleInversion_upper_floor_one
#print axioms eulerDoubleInversion_truncated_floor
#print axioms eulerDoubleInversion_truncated_floor_rat

end RHLean.Proof
