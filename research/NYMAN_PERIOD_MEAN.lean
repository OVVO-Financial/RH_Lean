import «research.NYMAN_PERIOD_CELLS»

/-! The complete unweighted period energy is covariance plus squared bias.
The physical location-weighted infinite tail is not identified with this mean. -/
set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace RHLean.Analysis

/-- Mean of the original residual, not assumed zero for repaired coefficients. -/
def nymanPeriodBias (N : Nat) (c : Nat → Real) : Real :=
  1 - ∑ k ∈ Icc 2 N, (c k / k)*(((k : Real)-1)/2)

/-- Unnormalized complete-period energy, valid for all signed coefficient vectors. -/
theorem nyman_period_residual_energy (N P : Nat) (c : Nat → Real)
    (hP : ∀ k ∈ Icc 2 N, k ∣ P) :
    ∑ m : Fin P, (nymanResidual N c m.val)^2 =
      (P : Real)*((nymanPeriodBias N c)^2 + nymanCovariance N c) := by
  let S := Icc 2 N
  let d := fun k : Nat => c k / k
  let A := fun m : Nat => ∑ k ∈ S, d k * nymanCellFluct k m
  let b := nymanPeriodBias N c
  have hr (m : Nat) : nymanResidual N c m = b - A m := by
    have he : (∑ k ∈ S, c k * nymanResidue k m) = ∑ k ∈ S, d k*(m%k : Nat) := by
      apply sum_congr rfl; intro k _; simp only [d, nymanResidue, div_eq_mul_inv]; ring
    change 1 - (∑ k ∈ S, c k * nymanResidue k m) = _
    rw [he]; dsimp only [A, b, nymanPeriodBias, nymanCellFluct]
    simp only [mul_sub, sum_sub_distrib, S, d]; ring
  have h1 : (∑ m : Fin P, A m.val) = 0 := by
    dsimp only [A]; rw [sum_comm]
    apply sum_eq_zero; intro k hk
    rw [← mul_sum, nyman_period_cell_sum P k (hP k hk), mul_zero]
  have h2 : (∑ m : Fin P, (A m.val)^2) = (P : Real)*nymanCovariance N c := by
    calc
      _ = ∑ m : Fin P, ∑ k ∈ S, ∑ l ∈ S,
          (d k*d l)*(nymanCellFluct k m.val*nymanCellFluct l m.val) := by
        apply sum_congr rfl; intro m _
        simp only [A, pow_two, sum_mul, mul_sum]
        apply sum_congr rfl; intro k _; apply sum_congr rfl; intro l _; ring
      _ = ∑ k ∈ S, ∑ l ∈ S, (d k*d l)*
          (∑ m : Fin P, nymanCellFluct k m.val*nymanCellFluct l m.val) := by
        rw [sum_comm]; apply sum_congr rfl; intro k _
        rw [sum_comm]; simp only [mul_sum]
      _ = _ := by
        unfold nymanCovariance
        conv_rhs => rw [← mul_assoc]; simp only [mul_sum]
        apply sum_congr rfl; intro k hk; apply sum_congr rfl; intro l hl
        have hk0 : 0<k := lt_of_lt_of_le (by decide : 0<2) (mem_Icc.mp hk).1
        have hl0 : 0<l := lt_of_lt_of_le (by decide : 0<2) (mem_Icc.mp hl).1
        rw [nyman_period_cell_pair P k l hk0 hl0 (hP k hk) (hP l hl)]
        dsimp [d]; ring
  simp_rw [hr, show ∀ x : Real, (b-x)^2 = b^2-(2*b)*x+x^2 by intro x; ring]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, h1, h2]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero, sub_zero, b]
  ring

/-- The covariance alone is the mean square exactly in the centered case. -/
theorem nyman_period_mean_eq_covariance_iff (N P : Nat) (hpos : 0<P)
    (c : Nat → Real) (hP : ∀ k ∈ Icc 2 N, k ∣ P) :
    (∑ m : Fin P, (nymanResidual N c m.val)^2)/(P : Real) = nymanCovariance N c ↔
      nymanPeriodBias N c = 0 := by
  rw [nyman_period_residual_energy N P c hP]
  have hn : (P : Real) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [mul_div_cancel_left₀ _ hn]
  constructor <;> intro h
  · have hs : (nymanPeriodBias N c)^2 = 0 := by linarith
    exact pow_eq_zero hs
  · simp [h]

end RHLean.Analysis
