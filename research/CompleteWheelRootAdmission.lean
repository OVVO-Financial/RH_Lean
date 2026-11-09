import «research.CompleteSquareRootWheelFractionalBoundary»
import «research.VF_MID_PHI_OWNER_BRIDGE»

/-!
# Exact and uniformly bounded complete-wheel root admission

Formalizes the proper-component claims 20261109-wheel-1/RA2-RA3.
The full fractional source, including virtual divisors, is compensated before
counting survivors. At the next square endpoint, adjoining an odd prime root
has centered cost one plus its twin-prime indicator. Root two costs three.
The cumulative bound is uniform, but does not bound the physical-shell error.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Centered complete-wheel source at an arbitrary cutoff and real reference. -/
def finiteWheelCenteredAt (z N : ℕ) (L : ℝ) : ℝ :=
  finiteWheelFract z N - (N : ℝ) * vfMidPrefixWheelDensity z -
    (Nat.primeCounting z : ℝ) + 1 + L

private theorem compensated_eq_neg_count (z N : ℕ) :
    finiteWheelFract z N - (N : ℝ) * vfMidPrefixWheelDensity z =
      -(vfMidPrefixWheelCounting z N : ℝ) := by
  have h := congrArg (fun a : ℤ => (a : ℝ))
    (finiteWheel_divisorFloor_eq_survivorCount z N)
  push_cast at h
  rw [finiteWheelFract_sub_density_eq_neg_floor, h]

private theorem centered_eq_count (z N : ℕ) (L : ℝ) :
    finiteWheelCenteredAt z N L =
      -(vfMidPrefixWheelCounting z N : ℝ) -
        (Nat.primeCounting z : ℝ) + 1 + L := by
  unfold finiteWheelCenteredAt
  rw [compensated_eq_neg_count]

private theorem prime_count_step (r : ℕ) (hr : 2 ≤ r) :
    Nat.primeCounting r = Nat.primeCounting (r - 1) +
      if r.Prime then 1 else 0 := by
  have hpred : r - 1 + 1 = r := by omega
  simp [Nat.primeCounting, Nat.primeCounting', hpred, Nat.count_succ]

private theorem centered_prime_step {p : ℕ} (hp : p.Prime)
    (N : ℕ) (L : ℝ) :
    finiteWheelCenteredAt p N L - finiteWheelCenteredAt (p - 1) N L =
      (vfMidPrefixWheelCounting (p - 1) (N / p) : ℝ) - 1 := by
  have hc := congrArg (fun a : ℤ => (a : ℝ))
    (vfMidPrefixWheelCounting_cast_int_prime_step hp N)
  push_cast at hc
  have hpcount := prime_count_step p hp.two_le
  simp only [hp, ite_true] at hpcount
  have hpR : (Nat.primeCounting p : ℝ) =
      (Nat.primeCounting (p - 1) : ℝ) + 1 := by
    exact_mod_cast hpcount
  rw [centered_eq_count, centered_eq_count]
  linarith

private theorem centered_nonprime_step {r : ℕ} (hr : 2 ≤ r)
    (hp : ¬ r.Prime) (N : ℕ) (L : ℝ) :
    finiteWheelCenteredAt r N L = finiteWheelCenteredAt (r - 1) N L := by
  have hset : primesUpTo r = primesUpTo (r - 1) := by
    ext p
    simp only [mem_primesUpTo]
    constructor
    · rintro ⟨hprime, hle⟩
      refine ⟨hprime, ?_⟩
      by_contra hnot
      have heq : p = r := by omega
      exact hp (heq ▸ hprime)
    · rintro ⟨hprime, hle⟩
      exact ⟨hprime, by omega⟩
  have hc : vfMidPrefixWheelCounting r N =
      vfMidPrefixWheelCounting (r - 1) N := by
    unfold vfMidPrefixWheelCounting lowWheelHighSurvivor
    rw [hset]
  have hpc := prime_count_step r hr
  simp only [hp, ite_false, add_zero] at hpc
  rw [centered_eq_count, centered_eq_count, hc, hpc]

private theorem pred_count_self (r : ℕ) (hr : 2 ≤ r) :
    vfMidPrefixWheelCounting (r - 1) (r - 1) = 1 := by
  have hset : (Finset.Ioc 0 (r - 1)).filter
      (lowWheelHighSurvivor (r - 1)) = {1} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hn0, hnr⟩, hsurv⟩
      by_contra hn1
      have hp := Nat.minFac_prime hn1
      have hdiv := Nat.minFac_dvd n
      have hle := Nat.le_of_dvd hn0 hdiv
      exact hsurv n.minFac (mem_primesUpTo.mpr ⟨hp, hle.trans hnr⟩) hdiv
    · rintro rfl
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro p hp hdiv
      exact (prime_of_mem_primesUpTo hp).not_dvd_one hdiv
  unfold vfMidPrefixWheelCounting
  rw [hset]
  simp

private theorem small_survivor_iff {r n : ℕ} (hr : 3 ≤ r)
    (hn0 : 0 < n) (hn : n ≤ r + 2) :
    lowWheelHighSurvivor (r - 1) n ↔
      n = 1 ∨ (n.Prime ∧ r ≤ n) := by
  constructor
  · intro hsurv
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    have hprime : n.Prime := by
      by_contra hnot
      have hp := Nat.minFac_prime hn1
      have hdiv := Nat.minFac_dvd n
      have hsq := Nat.minFac_sq_le_self hn0 hnot
      have hlarge : r ≤ n.minFac := by
        by_contra hsmall
        exact hsurv n.minFac
          (mem_primesUpTo.mpr ⟨hp, by omega⟩) hdiv
      have hpow := Nat.pow_le_pow_left hlarge 2
      nlinarith
    have hlarge : r ≤ n := by
      by_contra hsmall
      exact hsurv n (mem_primesUpTo.mpr ⟨hprime, by omega⟩) (dvd_refl n)
    exact Or.inr ⟨hprime, hlarge⟩
  · rintro (rfl | ⟨hprime, hlarge⟩)
    · intro p hp hdiv
      exact (prime_of_mem_primesUpTo hp).not_dvd_one hdiv
    · intro p hp hdiv
      have heq := (Nat.prime_dvd_prime_iff_eq
        (prime_of_mem_primesUpTo hp) hprime).mp hdiv
      have hle := (mem_primesUpTo.mp hp).2
      omega

/-- Exact cofactor count, including one and the possible upper twin prime. -/
theorem finiteWheel_pred_count_prime_add_two {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) :
    vfMidPrefixWheelCounting (p - 1) (p + 2) =
      2 + if (p + 2).Prime then 1 else 0 := by
  have hnext : ¬ (p + 1).Prime := by
    intro h
    rcases hp.eq_two_or_odd with htwo | hodd
    · omega
    rcases h.eq_two_or_odd with htwo | hodd'
    · omega
    · omega
  have hmem (n : ℕ) :
      n ∈ (Finset.Ioc 0 (p + 2)).filter (lowWheelHighSurvivor (p - 1)) ↔
        n = 1 ∨ n = p ∨ (n = p + 2 ∧ (p + 2).Prime) := by
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hn0, hn⟩, hsurv⟩
      rcases (small_survivor_iff hp3 hn0 hn).mp hsurv with hn1 | ⟨hnp, hpn⟩
      · exact Or.inl hn1
      have hcases : n = p ∨ n = p + 1 ∨ n = p + 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact False.elim (hnext hnp)
      · exact Or.inr (Or.inr ⟨rfl, hnp⟩)
    · rintro (rfl | rfl | ⟨rfl, hprime⟩)
      · exact ⟨⟨by omega, by omega⟩,
          (small_survivor_iff hp3 (by omega) (by omega)).mpr (Or.inl rfl)⟩
      · exact ⟨⟨hp.pos, by omega⟩,
          (small_survivor_iff hp3 hp.pos (by omega)).mpr (Or.inr ⟨hp, le_rfl⟩)⟩
      · exact ⟨⟨by omega, le_rfl⟩,
          (small_survivor_iff hp3 (by omega) le_rfl).mpr
            (Or.inr ⟨hprime, by omega⟩)⟩
  have hset : (Finset.Ioc 0 (p + 2)).filter (lowWheelHighSurvivor (p - 1)) =
      insert 1 (insert p (if (p + 2).Prime then {p + 2} else ∅)) := by
    ext n
    rw [hmem]
    by_cases ht : (p + 2).Prime <;> simp [ht]
  unfold vfMidPrefixWheelCounting
  rw [hset]
  have hp1 : p ≠ 1 := by omega
  have hp21 : p + 2 ≠ 1 := by omega
  have h1p : 1 ≠ p := by omega
  have h1p2 : 1 ≠ p + 2 := by omega
  by_cases ht : (p + 2).Prime <;> simp [ht, hp1, hp21, h1p, h1p2]

private theorem next_endpoint_div (r : ℕ) (hr : 2 ≤ r) :
    squareRootEndpoint (r + 1) / r = r + 2 := by
  have heq : squareRootEndpoint (r + 1) = r * (r + 2) := by
    unfold squareRootEndpoint
    have hpoly : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
    omega
  simp [heq, Nat.ne_of_gt (by omega : 0 < r)]

private theorem old_endpoint_div (r : ℕ) (hr : 2 ≤ r) :
    squareRootEndpoint r / r = r - 1 := by
  have hr0 : 0 < r := by omega
  have hpred : r - 1 + 1 = r := by omega
  have hsq : 1 ≤ r ^ 2 := by nlinarith
  have hX : squareRootEndpoint r + 1 = r ^ 2 := Nat.sub_add_cancel hsq
  apply Nat.le_antisymm
  · have hlt : squareRootEndpoint r / r < r :=
      (Nat.div_lt_iff_lt_mul hr0).mpr (by nlinarith)
    omega
  · apply (Nat.le_div_iff_mul_le hr0).mpr
    nlinarith

/-- Root admission leaves the old square endpoint exactly unchanged. -/
theorem finiteWheel_centered_old_root_step (r : ℕ) (hr : 2 ≤ r) (L : ℝ) :
    finiteWheelCenteredAt r (squareRootEndpoint r) L =
      finiteWheelCenteredAt (r - 1) (squareRootEndpoint r) L := by
  by_cases hp : r.Prime
  · have h := centered_prime_step hp (squareRootEndpoint r) L
    rw [old_endpoint_div r hr, pred_count_self r hr] at h
    norm_num at h
    linarith
  · exact centered_nonprime_step hr hp _ L

/-- Exact next-endpoint centered cost; the first root is exceptional. -/
theorem finiteWheel_centered_next_root_step (r : ℕ) (hr : 2 ≤ r) (L : ℝ) :
    finiteWheelCenteredAt r (squareRootEndpoint (r + 1)) L -
        finiteWheelCenteredAt (r - 1) (squareRootEndpoint (r + 1)) L =
      if r = 2 then 3 else
        if r.Prime then 1 + (if (r + 2).Prime then 1 else 0) else 0 := by
  by_cases hr2 : r = 2
  · subst r
    rw [centered_prime_step Nat.prime_two, next_endpoint_div 2 (by omega)]
    norm_num [vfMidPrefixWheelCounting_one]
  · by_cases hp : r.Prime
    · rw [centered_prime_step hp, next_endpoint_div r hr,
        finiteWheel_pred_count_prime_add_two hp (by omega)]
      simp only [hr2, hp, ite_false, ite_true]
      split_ifs <;> norm_num
    · rw [centered_nonprime_step hr hp]
      simp [hr2, hp]

/-- The proper root-admission component of the original complete source. -/
def finiteWheelRootAdmission (r : ℕ) : ℝ :=
  finiteWheelCenteredAt r (squareRootEndpoint (r + 1)) 0 -
    finiteWheelCenteredAt (r - 1) (squareRootEndpoint (r + 1)) 0

/-- Uniform one-step bound, with no wheel-size or prime-distribution factor. -/
theorem finiteWheel_rootAdmission_bounds (r : ℕ) (hr : 2 ≤ r) :
    0 ≤ finiteWheelRootAdmission r ∧
      finiteWheelRootAdmission r ≤ 2 + if r = 2 then 1 else 0 := by
  unfold finiteWheelRootAdmission
  rw [finiteWheel_centered_next_root_step r hr 0]
  split_ifs <;> norm_num

/-- Uniform cumulative cost of this component, not of the full discrepancy. -/
theorem finiteWheel_rootAdmission_sum_bounds (A B : ℕ)
    (hA : 2 ≤ A) :
    0 ≤ ∑ r ∈ Finset.Ico A B, finiteWheelRootAdmission r ∧
      (∑ r ∈ Finset.Ico A B, finiteWheelRootAdmission r) ≤
        2 * (B - A : ℕ) + if A = 2 ∧ A < B then 1 else 0 := by
  constructor
  · exact Finset.sum_nonneg (fun r hr =>
      (finiteWheel_rootAdmission_bounds r
        (hA.trans (Finset.mem_Ico.mp hr).1)).1)
  · calc
      (∑ r ∈ Finset.Ico A B, finiteWheelRootAdmission r) ≤
          ∑ r ∈ Finset.Ico A B, ((2 : ℝ) + if r = 2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro r hr
        exact (finiteWheel_rootAdmission_bounds r
          (hA.trans (Finset.mem_Ico.mp hr).1)).2
      _ = 2 * (B - A : ℕ) + if 2 ∈ Finset.Ico A B then 1 else 0 := by
        simp [Finset.sum_add_distrib, Nat.card_Ico, mul_comm]
      _ = 2 * (B - A : ℕ) + if A = 2 ∧ A < B then 1 else 0 := by
        have hmem : 2 ∈ Finset.Ico A B ↔ A = 2 ∧ A < B := by
          simp only [Finset.mem_Ico]
          omega
        rw [hmem]

/-- Full scalar root step. The physical-shell term remains present and unpaid. -/
theorem finiteWheel_centered_root_return (r : ℕ) (L₀ L₁ : ℝ) :
    finiteWheelCenteredAt r (squareRootEndpoint (r + 1)) L₁ -
        finiteWheelCenteredAt (r - 1) (squareRootEndpoint r) L₀ =
      L₁ - L₀ -
        ((vfMidPrefixWheelCounting (r - 1) (squareRootEndpoint (r + 1)) : ℝ) -
          (vfMidPrefixWheelCounting (r - 1) (squareRootEndpoint r) : ℝ)) +
        finiteWheelRootAdmission r := by
  unfold finiteWheelRootAdmission
  simp only [centered_eq_count]
  ring

/-- The new intermediate coordinate agrees with the unchanged endpoint source. -/
theorem finiteWheel_centeredAt_square_source (r : ℕ) (L : ℝ) :
    finiteWheelCenteredAt (r - 1) (squareRootEndpoint r) L =
      finiteWheelFract (r - 1) (squareRootEndpoint r) -
        finiteWheelSquareDeterministic r L := by
  unfold finiteWheelCenteredAt finiteWheelSquareDeterministic
  ring

end RHLean.Analysis
