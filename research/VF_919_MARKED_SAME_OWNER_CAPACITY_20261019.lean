import «research.VF_919_MARKED_FIRST_OWNER_SHELL_20261019»

/-!
# Unconditional same-marked-prime shell collision count

For a finite marked set P and an actual marked p>0, a sharp shell
contains at most floor((2R+1)/p)+2 integer multiples of p. Every
first-owner site has magnitude <=1, hence

  sum_R sum_p (firstOwnerShell(p,R))^2
  <= sum_R sum_p (floor((2R+1)/p)+2)^2.

This is a source-faithful and UNCONDITIONAL finite counting bound,
before selecting P inside a dyadic prime band p~H^(1/2). The ordinary
numeric H^3/P0+HP0 corollary then follows by taking H shells, at most
P0 band primes, and p>=P0. The bound covers SAME marked owners only.
The unmarked sector, sifted/marked cross and distinct-prime Gram
remain fully present in vf919DyadicSquareShell_fullMarkedEnergy.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

def vf919DivisibleIntervalSites (a b p : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter (fun n => p ∣ n)

/-- An integer multiple of p is uniquely determined by its quotient n/p.
Therefore the number of multiples in [a,b) is bounded by the number
of possible quotient values, without assuming a prime distribution. -/
theorem vf919DivisibleIntervalSites_card_le_quotient
    (a b p : ℕ) (_hp : 0 < p) (_hab : a ≤ b) :
    (vf919DivisibleIntervalSites a b p).card ≤
      b / p + 1 - a / p := by
  let S := vf919DivisibleIntervalSites a b p
  let T := Finset.Icc (a / p) (b / p)
  have hmap : ∀ n ∈ S, n / p ∈ T := by
    intro n hn
    obtain ⟨hnb, hdiv⟩ := Finset.mem_filter.mp hn
    obtain ⟨hna, hnb'⟩ := Finset.mem_Ico.mp hnb
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_le_div_right hna, Nat.div_le_div_right hnb'.le⟩
  have hinj : Set.InjOn (fun n : ℕ => n / p) (S : Set ℕ) := by
    intro m hm n hn heq
    have hmp : p ∣ m := (Finset.mem_filter.mp hm).2
    have hnp : p ∣ n := (Finset.mem_filter.mp hn).2
    calc
      m = p * (m / p) := (Nat.mul_div_cancel' hmp).symm
      _ = p * (n / p) := by
        change m / p = n / p at heq
        rw [heq]
      _ = n := Nat.mul_div_cancel' hnp
  have hcard := Finset.card_le_card_of_injOn
    (fun n : ℕ => n / p) hmap hinj
  calc
    S.card ≤ T.card := hcard
    _ = b / p + 1 - a / p := by
      dsimp [T]
      rw [Nat.card_Icc]

/-- Elementary floor-division width estimate, with an allowance of
two incomplete residue cells. -/
theorem vf919QuotientInterval_width_le
    (a b p : ℕ) (hp : 0 < p) (hab : a ≤ b) :
    b / p + 1 - a / p ≤ (b - a) / p + 2 := by
  -- The exact floor-division addition formula pays at most one
  -- carry. This avoids nonlinear reasoning with truncated Nat subtraction.
  have hcarry :
      (if p ≤ a % p + (b - a) % p then 1 else 0) ≤ 1 := by
    split <;> omega
  have hsum : (a + (b - a)) / p ≤
      a / p + (b - a) / p + 1 := by
    rw [Nat.add_div hp]
    omega
  have hsub : a + (b - a) = b := Nat.add_sub_of_le hab
  rw [hsub] at hsum
  have hquot : a / p ≤ b / p := Nat.div_le_div_right hab
  omega

/-- Source-independent exact integer bound on the count of multiples
of p in an interval of length b-a. -/
theorem vf919DivisibleIntervalSites_card_le_width
    (a b p : ℕ) (hp : 0 < p) (hab : a ≤ b) :
    (vf919DivisibleIntervalSites a b p).card ≤
      (b - a) / p + 2 :=
  (vf919DivisibleIntervalSites_card_le_quotient a b p hp hab).trans
    (vf919QuotientInterval_width_le a b p hp hab)

/-- A priority-marked physical site has amplitude <=1 and is supported
on integers n divisible by its marked owner p. No sign is replaced. -/
theorem vf919FirstMarkedPhysicalSite_abs_le_divisible
    (P : Finset ℕ) (p n : ℕ) :
    |vf919FirstMarkedPhysicalSite P p n| ≤
      if p ∣ n then (1 : ℝ) else 0 := by
  by_cases hown : (vf919MarkedDivisors P n).Nonempty ∧
      p = vf919FirstMarkedDivisor P n
  · have hpd : p ∣ n := by
      have hmem : p ∈ vf919MarkedDivisors P n := by
        rw [hown.2]
        exact vf919FirstMarkedDivisor_mem P n hown.1
      exact (Finset.mem_filter.mp hmem).2
    have hstep : |realMoebiusStep n| ≤ 1 := by
      have hsq := realMoebiusStep_sq_le_one n
      nlinarith [sq_abs (realMoebiusStep n), abs_nonneg (realMoebiusStep n)]
    simpa only [vf919FirstMarkedPhysicalSite, ite_eq_left hown, ite_eq_left hpd]
      using hstep
  · simp only [vf919FirstMarkedPhysicalSite, ite_eq_right hown]
    split_ifs <;> norm_num

/-- Unconditional pointwise same-owner shell norm is paid by the number
of multiples of that marked prime in the original integer square shell. -/
theorem vf919FirstMarkedSquareShell_norm_le_siteCount
    (P : Finset ℕ) (p R : ℕ) :
    ‖vf919FirstMarkedSquareShell P p R‖ ≤
      ((vf919DivisibleIntervalSites
        (R ^ 2) ((R + 1) ^ 2) p).card : ℝ) := by
  unfold vf919FirstMarkedSquareShell
  have hpoint (n : ℕ) :
      ‖vf919FirstMarkedPhysicalSite P p n‖ ≤
        (if p ∣ n then (1 : ℝ) else 0) := by
    simpa only [Real.norm_eq_abs] using
      vf919FirstMarkedPhysicalSite_abs_le_divisible P p n
  calc
    ‖∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        vf919FirstMarkedPhysicalSite P p n‖ ≤
      ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        ‖vf919FirstMarkedPhysicalSite P p n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
          (if p ∣ n then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro n _
      exact hpoint n
    _ = ((vf919DivisibleIntervalSites (R ^ 2)
          ((R + 1) ^ 2) p).card : ℝ) := by
      simp [vf919DivisibleIntervalSites]

/-- Finite unconditional same-prime shell amplitude estimate: an
integer p>0 has at most (2R+1)/p+2 available cofactor positions. -/
theorem vf919FirstMarkedSquareShell_norm_le_widthDiv
    (P : Finset ℕ) (p R : ℕ) (hp : 0 < p) :
    ‖vf919FirstMarkedSquareShell P p R‖ ≤
      ((((2 * R + 1) / p + 2 : ℕ) : ℝ)) := by
  have hle : R ^ 2 ≤ (R + 1) ^ 2 := by
    have hsq : (R + 1) ^ 2 = R ^ 2 + (2 * R + 1) := by ring
    omega
  have hcount :=
    vf919DivisibleIntervalSites_card_le_width
      (R ^ 2) ((R + 1) ^ 2) p hp hle
  rw [vf919SquareShell_width] at hcount
  exact (vf919FirstMarkedSquareShell_norm_le_siteCount P p R).trans
    (by exact_mod_cast hcount)

/-- Actual same-prime dyadic energy pays only the squared counts of
original multiples, not all within-shell integer pairs. This is an
unconditional finite statement; nonprincipal moment bounds are absent. -/
theorem vf919MarkedSameOwnerEnergy_le_divisibleCapacity
    (P : Finset ℕ) (H : ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    vf919MarkedSameOwnerEnergy P H ≤
      ∑ R ∈ Finset.Ico H (2 * H),
        ∑ p ∈ P, ((((2 * R + 1) / p + 2 : ℕ) : ℝ)) ^ 2 := by
  unfold vf919MarkedSameOwnerEnergy
  apply Finset.sum_le_sum
  intro R _
  apply Finset.sum_le_sum
  intro p hpP
  have hnorm :=
    vf919FirstMarkedSquareShell_norm_le_widthDiv P p R (hP p hpP)
  have hsq : ‖vf919FirstMarkedSquareShell P p R‖ ^ 2 ≤
      ((((2 * R + 1) / p + 2 : ℕ) : ℝ)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).2 hnorm
  simpa only [Real.norm_eq_abs, sq_abs] using hsq

#print axioms vf919DivisibleIntervalSites_card_le_quotient
#print axioms vf919QuotientInterval_width_le
#print axioms vf919DivisibleIntervalSites_card_le_width
#print axioms vf919FirstMarkedPhysicalSite_abs_le_divisible
#print axioms vf919FirstMarkedSquareShell_norm_le_siteCount
#print axioms vf919FirstMarkedSquareShell_norm_le_widthDiv
#print axioms vf919MarkedSameOwnerEnergy_le_divisibleCapacity

end RHLean.Analysis
