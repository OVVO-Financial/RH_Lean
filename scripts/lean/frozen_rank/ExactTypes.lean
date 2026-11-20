import «research.EULER_FROZEN_DIVISOR_RANK»

open RHLean.Proof RHLean.Analysis
open scoped BigOperators

example (R : ℕ) : eulerFloorBilinearQ R = ∑ b ∈ Finset.Icc 1 (R-1),
    ∑ a ∈ Finset.Icc 1 (R-1), eulerMuQ a * eulerMuQ b * eulerFloorQ R a b := by
  unfold eulerFloorBilinearQ
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

example {R : ℕ} (h : 0 < R) (S : Finset ℕ) (d : ∀ a ∈ S, a ∣ R) :
    Matrix.rank (show Matrix S S ℚ from fun a b => eulerMuQ a * eulerMuQ b * eulerFloorQ R a b) ≤ 2 :=
  eulerFrozen_rank_le_two h S d

example {R p : ℕ} (h : 0 < R) (hp : p.Prime) (S : Finset ℕ) (d : ∀ a ∈ S, a ∣ R)
    (a : 1 ∈ S) (b : p ∈ S) : (eulerFrozenMatrix R S).rank = 2 :=
  eulerFrozen_rank_eq_two h hp S d a b

example (R : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (a : ¬p ∣ R-1) (b : ¬q ∣ R-1) :
    eulerTwoRowProbe (eulerDoubleCenteredInteriorKernelQ R) p q =
      eulerTwoRowProbe (eulerFloorQ R) p q + eulerDoubleCenterScaleQ R *
        ((((R-1) % p : ℕ) : ℚ) - (((R-1) % q : ℕ) : ℚ)) ^ 2 := eulerTwoRow_interior R hp hq a b

example (F : ℕ → ℕ → ℚ) : eulerTwoRowProbe F 3 5 =
    9*F 3 3 - 15*F 3 5 - 15*F 5 3 + 25*F 5 5 := by
  norm_num [eulerTwoRowProbe, eulerMuQ, ArithmeticFunction.moebius_apply_prime Nat.prime_three,
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5)]

example (R : ℕ) (v : ℚ) : eulerTwoRowWitness R v ↔
    3 ∈ Finset.Icc 1 (R-1) ∧ 5 ∈ Finset.Icc 1 (R-1) ∧ (¬3 ∣ R) ∧ (¬5 ∣ R) ∧
    (¬3 ∣ R-1) ∧ (¬5 ∣ R-1) ∧ eulerTwoRowProbe (eulerContinuousQ R) 3 5 = 0 ∧
    eulerTwoRowProbe (eulerFloorQ R) 3 5 = v ∧
    eulerTwoRowProbe (eulerDoubleCenteredInteriorKernelQ R) 3 5 = v := Iff.rfl

example (n : ℕ) : eulerTwoRowWitness (225*n+17) (-7) ∧
    eulerTwoRowWitness (225*n+152) 3 ∧ eulerTwoRowWitness (225*n+227) 0 :=
  eulerTwoRow_sign_families n

#check @eulerFloorQ_of_root_divisors
#check @eulerFrozen_prime_minor
#check @eulerFrozen_rank_eq_two
#check @eulerTwoRow_floor_mod
#check @eulerTwoRow_interior
#check @eulerTwoRow_sign_families
