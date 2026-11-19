import «research.NYMAN_THREE_PROFILE_COERCIVITY»

/-! Literal reciprocal and residue sums for the two RIDGE1 repair bands.
The first floor layer includes N+1; its first double at N+2 is not a new site. -/

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace RHLean.Analysis

def nymanRidgeS (a b : Nat) : Real := ∑ k ∈ Ioc a b, 1 / (k : Real)
def nymanRidgeG (a b m : Nat) : Real := ∑ k ∈ Ioc a b, nymanResidue k m
def nymanRidgeGap (K : Nat) : Real := nymanRidgeS (3*K) (4*K) - nymanRidgeS (5*K) (6*K)

/-- Pair k with k+2K. The uniform constant is attained at K=1. -/
theorem nyman_ridge_gap (K : Nat) (hK : 0 < K) : 1/12 ≤ nymanRidgeGap K := by
  have hR : (0 : Real) < K := by exact_mod_cast hK
  have shift : (∑ k ∈ Ioc (3*K) (4*K), 1 / ((k + 2*K : Nat) : Real)) =
      nymanRidgeS (5*K) (6*K) := by
    unfold nymanRidgeS
    apply Finset.sum_bij (fun k _ => k + 2*K)
    · intro k hk
      simp only [Finset.mem_Ioc] at hk ⊢
      omega
    · intro k _ j _ h
      omega
    · intro j hj
      refine ⟨j-2*K, ?_, ?_⟩
      · simp only [Finset.mem_Ioc] at hj ⊢
        omega
      · have := (Finset.mem_Ioc.mp hj).1
        omega
    · intro _ _
      rfl
  unfold nymanRidgeGap
  rw [← shift, nymanRidgeS, ← Finset.sum_sub_distrib]
  calc
    (1/12 : Real) = ∑ _k ∈ Ioc (3*K) (4*K), 1 / (12*(K:Real)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, show 4*K-3*K=K by omega]
      rw [← mul_div_assoc, div_eq_div_iff (by norm_num) (by positivity)]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hm := Finset.mem_Ioc.mp hk
      have hk0 : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
      have hu : (k : Real) ≤ 4*(K:Real) := by exact_mod_cast hm.2
      have hq : (0 : Real) < k + 2*(K:Real) := by positivity
      have hp := mul_le_mul hu (show (k:Real)+2*K ≤ 6*K by linarith) hq.le
        (show (0:Real) ≤ 4*K by positivity)
      push_cast
      rw [div_sub_div hk0.ne' hq.ne', div_le_div_iff₀ (by positivity) (mul_pos hk0 hq)]
      nlinarith only [hp]

theorem nyman_ridge_residue_floor (a b m : Nat) :
    nymanRidgeG a b m = m * nymanRidgeS a b - (nymanBandCount a b m : Real) := by
  unfold nymanRidgeG nymanRidgeS nymanBandCount
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [nymanResidue_eq_div_sub_floor k m (by have := (Finset.mem_Ioc.mp hk).1; omega)]
  ring

private theorem firstCount (a b m : Nat) (hm : m ≤ 2*a+1) :
    nymanBandCount a b m = min b m - a := by
  have sub : Ioc a (min b m) ⊆ Ioc a b := by
    intro k hk
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1,
      (Finset.mem_Ioc.mp hk).2.trans (min_le_left _ _)⟩
  calc
    nymanBandCount a b m = ∑ k ∈ Ioc a (min b m), m/k := by
      symm
      apply Finset.sum_subset sub
      intro k hk hn
      simp only [Finset.mem_Ioc, le_min_iff] at hk hn
      exact Nat.div_eq_of_lt (by omega)
    _ = ∑ _k ∈ Ioc a (min b m), (1:Nat) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_Ioc, le_min_iff] at hk
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    _ = _ := by simp

theorem nyman_ridge_first_layer (K m : Nat) (hm : m ≤ 6*K+1) :
    nymanBandCount (3*K) (4*K) m = min (4*K) m - 3*K ∧
    nymanBandCount (5*K) (6*K) m = min (6*K) m - 5*K :=
  ⟨firstCount _ _ _ (by omega), firstCount _ _ _ (by omega)⟩

theorem nyman_ridge_first_double (K : Nat) (hK : 0 < K) :
    nymanBandCount (3*K) (4*K) (6*K+2) = K+1 ∧
    nymanBandCount (5*K) (6*K) (6*K+2) = K := by
  have split : Ioc (3*K) (4*K) = insert (3*K+1) (Ioc (3*K+1) (4*K)) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hq : (6*K+2)/(3*K+1) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  constructor
  · change (∑ k ∈ Ioc (3*K) (4*K), (6*K+2)/k) = K+1
    rw [split, Finset.sum_insert (by simp), hq]
    change 2 + nymanBandCount (3*K+1) (4*K) (6*K+2) = K+1
    rw [firstCount _ _ _ (by omega), min_eq_left (by omega)]
    omega
  · rw [firstCount _ _ _ (by omega), min_eq_left (by omega)]
    omega

end RHLean.Analysis
