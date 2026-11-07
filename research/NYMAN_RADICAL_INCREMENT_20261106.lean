import «research.NYMAN_FLAT_TAPER_RETURN_20261104»

/-!
The source-exact FW3 increment identity from 20261106-census-3, independently
accepted by 20261106-referee-13. Radical classes classify increments, not
physical occurrences or weighted energies. The flat-source theorem retains
both cutoff tails and arbitrary correction jumps at every admitted cell.
No favorable correlation, norm estimate, or endpoint gain is asserted.
-/

set_option autoImplicit false

noncomputable section

open Finset UniqueFactorizationMonoid
open scoped BigOperators

namespace RHLean.Analysis

def nymanHighDivisorJump (H m : Nat) : Real :=
  -Finset.sum (m.divisors.filter (fun d => H < d)) (nymanLogKernel H)

def nymanScalarDefect (H : Nat) : Real :=
  1 - Finset.sum (Icc 1 H) (fun k => nymanLogKernel H k / (k : Real))

def nymanArithmeticResidual (H m : Nat) : Real :=
  (m : Real) - nymanPsi m - Real.log H -
    Finset.sum (Icc 1 H) (fun k => nymanLogKernel H k * nymanResidue k m)

def nymanCorrectionJump (N : Nat) (h : Nat -> Real) (m : Nat) : Real :=
  Finset.sum ((Icc 2 N).filter (fun k => k ∣ m)) h

theorem nymanHighDivisorJump_eq_original (H m : Nat) (hH : 1 <= H) :
    nymanHighDivisorJump H m =
      Finset.sum (m.divisors.filter (fun d => H < d)) (fun d =>
        (ArithmeticFunction.moebius d : Real) * Real.log ((d : Real) / H)) := by
  unfold nymanHighDivisorJump
  rw [<- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hHd := (Finset.mem_filter.mp hd).2
  have hHz : (H : Real) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  have hdz : (d : Real) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [Real.log_div hdz hHz]
  unfold nymanLogKernel
  ring

theorem nymanHighDivisorJump_radical (H m : Nat) (hm : 1 <= m) :
    nymanHighDivisorJump H m = nymanHighDivisorJump H (radical m) := by
  have hm0 : m ≠ 0 := by omega
  have hsub : (radical m).divisors.filter (fun d => H < d) ⊆
      m.divisors.filter (fun d => H < d) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hd, hHd⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(Nat.mem_divisors.mp hd).1.trans radical_dvd_self, hm0⟩, hHd⟩
  unfold nymanHighDivisorJump
  congr 1
  symm
  apply Finset.sum_subset hsub
  intro d hd hn
  have hsq : ¬ Squarefree d := by
    intro hs
    apply hn
    rcases Finset.mem_filter.mp hd with ⟨hd, hHd⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(dvd_radical_iff hs.isRadical hm0).mpr (Nat.mem_divisors.mp hd).1,
        radical_ne_zero⟩, hHd⟩
  simp [nymanLogKernel, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

theorem nymanHighDivisorJump_eq_zero_of_le (H m : Nat) (hm : m <= H) :
    nymanHighDivisorJump H m = 0 := by
  unfold nymanHighDivisorJump
  have he : m.divisors.filter (fun d => H < d) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hd, hHd⟩
    rcases Nat.mem_divisors.mp hd with ⟨hdm, hm0⟩
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm
    omega
  simp [he]

private theorem nymanLogTail_eq_cumulative (H m : Nat) :
    nymanLogTail H m = -Finset.sum (Icc 1 m) (nymanHighDivisorJump H) := by
  have hset : (Icc 1 m).filter (fun k => H < k) = Ioc H m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc
    nymanLogTail H m = Finset.sum (Icc 1 m) (fun k =>
        (if H < k then nymanLogKernel H k else 0) * ((m / k : Nat) : Real)) := by
      simp only [ite_mul, zero_mul, <- Finset.sum_filter, hset, nymanLogTail]
    _ = Finset.sum (Icc 1 m) (fun n => Finset.sum n.divisors
        (fun k => if H < k then nymanLogKernel H k else 0)) :=
      nyman_sum_mul_floor_eq_divisor_sum m _
    _ = -Finset.sum (Icc 1 m) (nymanHighDivisorJump H) := by
      change _ = -Finset.sum (Icc 1 m) (fun n =>
        -Finset.sum (n.divisors.filter (fun d => H < d)) (nymanLogKernel H))
      simp only [Finset.sum_neg_distrib, neg_neg, Finset.sum_filter]

theorem nymanLogTail_step (H m : Nat) (hm : 1 <= m) :
    nymanLogTail H m - nymanLogTail H (m - 1) = -nymanHighDivisorJump H m := by
  have hs := Finset.sum_Icc_succ_top (f := nymanHighDivisorJump H)
    (show 1 <= m - 1 + 1 by omega)
  simp only [Nat.sub_add_cancel hm] at hs
  rw [nymanLogTail_eq_cumulative, nymanLogTail_eq_cumulative, hs]
  ring

private theorem nyman_floor_step (k m : Nat) (hm : 1 <= m) :
    ((m / k : Nat) : Real) - (((m - 1) / k : Nat) : Real) =
      if k ∣ m then 1 else 0 := by
  have he := @Nat.succ_div (m - 1) k
  rw [Nat.sub_add_cancel hm] at he
  by_cases hd : k ∣ m
  · simp only [hd, ite_true] at he ⊢
    rw [he]
    push_cast
    ring
  · simp only [hd, ite_false, Nat.add_zero] at he ⊢
    rw [he]
    ring

theorem nymanCorrectionFloor_step (N m : Nat) (h : Nat -> Real) (hm : 1 <= m) :
    nymanCorrectionFloor N h m - nymanCorrectionFloor N h (m - 1) =
      nymanCorrectionJump N h m := by
  unfold nymanCorrectionFloor nymanCorrectionJump
  rw [<- Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  rw [<- mul_sub, nyman_floor_step k m hm]
  split_ifs <;> ring

theorem nyman_arithmetic_residual_eq_drift_tail (H m : Nat)
    (hH : 1 <= H) (hm : 1 <= m) :
    nymanArithmeticResidual H m = (m : Real) * nymanScalarDefect H -
      nymanLogTail H m := by
  have hs : Finset.sum (Icc 1 H) (fun k => nymanLogKernel H k * nymanResidue k m) =
      (m : Real) * Finset.sum (Icc 1 H) (fun k => nymanLogKernel H k / (k : Real)) -
        Finset.sum (Icc 1 H) (fun k => nymanLogKernel H k * ((m / k : Nat) : Real)) := by
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [nymanResidue_eq_div_sub_floor k m (Finset.mem_Icc.mp hk).1]
    ring
  unfold nymanArithmeticResidual nymanScalarDefect
  rw [hs, nyman_log_floor_with_tail H m hH hm]
  ring

theorem nyman_arithmetic_residual_step (H m : Nat) (hH : 1 <= H) (hm : 2 <= m) :
    nymanArithmeticResidual H m - nymanArithmeticResidual H (m - 1) =
      nymanScalarDefect H + nymanHighDivisorJump H (radical m) := by
  rw [nyman_arithmetic_residual_eq_drift_tail H m hH (by omega),
    nyman_arithmetic_residual_eq_drift_tail H (m - 1) hH (by omega)]
  have ht := nymanLogTail_step H m (by omega : 1 <= m)
  rw [nymanHighDivisorJump_radical H m (by omega)] at ht
  push_cast [Nat.cast_sub (by omega : 1 <= m)]
  linarith

theorem nyman_arithmetic_step_same_radical (H m n : Nat)
    (hH : 1 <= H) (hm : 2 <= m) (hn : 2 <= n) (hrad : radical m = radical n) :
    nymanArithmeticResidual H m - nymanArithmeticResidual H (m - 1) =
      nymanArithmeticResidual H n - nymanArithmeticResidual H (n - 1) := by
  rw [nyman_arithmetic_residual_step H m hH hm,
    nyman_arithmetic_residual_step H n hH hn, hrad]

theorem nyman_arithmetic_step_small_radical (H m : Nat)
    (hH : 1 <= H) (hm : 2 <= m) (hrad : radical m <= H) :
    nymanArithmeticResidual H m - nymanArithmeticResidual H (m - 1) =
      nymanScalarDefect H := by
  rw [nyman_arithmetic_residual_step H m hH hm,
    nymanHighDivisorJump_eq_zero_of_le H (radical m) hrad, add_zero]

/-- Complete original flat-source jump, including after-N and correction admission. -/
theorem nyman_flat_complete_step (N H m : Nat) (h : Nat -> Real)
    (hH : 1 <= H) (hHN : H < N) (hm : 2 <= m) :
    nymanFlatScale N H *
        (nymanResidual N (nymanFlatCoefficient N H h) m -
          nymanResidual N (nymanFlatCoefficient N H h) (m - 1)) =
      nymanFlatMoment N H - nymanCorrectionMoment N h +
        nymanHighDivisorJump H (radical m) -
        nymanHighDivisorJump N (radical m) + nymanCorrectionJump N h m := by
  rw [mul_sub, nyman_flat_complete_return N H m h hH hHN (by omega),
    nyman_flat_complete_return N H (m - 1) h hH hHN (by omega)]
  have hN := nymanLogTail_step N m (by omega : 1 <= m)
  have hH' := nymanLogTail_step H m (by omega : 1 <= m)
  have hc := nymanCorrectionFloor_step N m h (by omega : 1 <= m)
  rw [nymanHighDivisorJump_radical N m (by omega)] at hN
  rw [nymanHighDivisorJump_radical H m (by omega)] at hH'
  push_cast [Nat.cast_sub (by omega : 1 <= m)]
  linarith

/-- Before correction admission, the scalar defect is arbitrary, not assumed zero. -/
theorem nyman_flat_step_before_corrections (N H m : Nat) (h : Nat -> Real)
    (hH : 1 <= H) (hHN : H < N) (hm : 2 <= m) (hmN : m <= N)
    (hlow : ∀ k, k ∈ Icc 2 m -> h k = 0) :
    nymanFlatScale N H *
        (nymanResidual N (nymanFlatCoefficient N H h) m -
          nymanResidual N (nymanFlatCoefficient N H h) (m - 1)) =
      nymanFlatMoment N H - nymanCorrectionMoment N h +
        nymanHighDivisorJump H (radical m) := by
  have ht : nymanHighDivisorJump N (radical m) = 0 := by
    rw [<- nymanHighDivisorJump_radical N m (by omega)]
    exact nymanHighDivisorJump_eq_zero_of_le N m hmN
  have hc : nymanCorrectionJump N h m = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hk, hkm⟩
    exact hlow k (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      Nat.le_of_dvd (by omega) hkm⟩)
  rw [nyman_flat_complete_step N H m h hH hHN hm, ht, hc]
  ring

#check nymanHighDivisorJump_eq_original
#check nymanHighDivisorJump_radical
#check nymanHighDivisorJump_eq_zero_of_le
#check nymanLogTail_step
#check nymanCorrectionFloor_step
#check nyman_arithmetic_residual_eq_drift_tail
#check nyman_arithmetic_residual_step
#check nyman_arithmetic_step_same_radical
#check nyman_arithmetic_step_small_radical
#check nyman_flat_complete_step
#check nyman_flat_step_before_corrections
#print axioms nymanHighDivisorJump_eq_original
#print axioms nymanHighDivisorJump_radical
#print axioms nymanHighDivisorJump_eq_zero_of_le
#print axioms nymanLogTail_step
#print axioms nymanCorrectionFloor_step
#print axioms nyman_arithmetic_residual_eq_drift_tail
#print axioms nyman_arithmetic_residual_step
#print axioms nyman_arithmetic_step_same_radical
#print axioms nyman_arithmetic_step_small_radical
#print axioms nyman_flat_complete_step
#print axioms nyman_flat_step_before_corrections

end RHLean.Analysis
