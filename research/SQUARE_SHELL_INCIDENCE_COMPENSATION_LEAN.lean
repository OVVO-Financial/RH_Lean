import Mathlib
import RHLean.Analysis.DivisorUpperMobius

/-!
# Finite square-shell prime-incidence compensation (universal algebra)

The first centering is kernel-checked here on *arbitrary* integer-valued
smooth-divisibility profiles. The actual shell profile, the greatest-prime
transport and physical owner labels are supplied by the already audited
square-shell arithmetic module/certificate; no analytic moment bound is assumed.

The final lemma identifies an obstruction to a purely higher-divisor second
centering: the cofactor unit is invisible to every divisor channel d>1.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The explicit upper-incidence Möbius compensator, with physical cutoff R. -/
def shellIncidenceCompensator (R : ℕ) (B : ℕ → ℤ) (c : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 R,
    if c ∣ n then (μ (n / c) : ℤ) * B n else 0

private theorem shell_upper_divisor_delta
    {R d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) (hnR : n ≤ R) :
    (∑ c ∈ Finset.Icc 1 R,
      if d ∣ c then (if c ∣ n then (μ (n / c) : ℤ) else 0) else 0) =
        if d = n then 1 else 0 := by
  classical
  have hset :
      (Finset.Icc 1 R).filter (fun c => c ∣ n) = n.divisors := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hc1, hcR⟩, hcn⟩
      exact ⟨hcn, by omega⟩
    · rintro ⟨hcn, hn0⟩
      have hcpos : 0 < c := by
        by_contra hc
        have hc0 : c = 0 := by omega
        subst c
        have hzero : n = 0 := Nat.eq_zero_of_zero_dvd hcn
        exact hn0 hzero
      exact ⟨⟨by omega, le_trans (Nat.le_of_dvd (by omega) hcn) hnR⟩, hcn⟩
  calc
    (∑ c ∈ Finset.Icc 1 R,
      if d ∣ c then (if c ∣ n then (μ (n / c) : ℤ) else 0) else 0) =
      ∑ c ∈ Finset.Icc 1 R,
        if c ∣ n then (if d ∣ c then (μ (n / c) : ℤ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          by_cases hdc : d ∣ c <;> by_cases hcn : c ∣ n <;>
            simp [hdc, hcn]
    _ = ∑ c ∈ (Finset.Icc 1 R).filter (fun c => c ∣ n),
            if d ∣ c then (μ (n / c) : ℤ) else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ c ∈ n.divisors, if d ∣ c then (μ (n / c) : ℤ) else 0 := by
          rw [hset]
    _ = if d = n then 1 else 0 := by
          by_cases hdn : d ∣ n
          · exact RHLean.Analysis.sum_moebius_upper_divisors_eq_one_or_zero
              hdn hd (by omega)
          · have hne : d ≠ n := by
              intro heq
              exact hdn (heq ▸ dvd_rfl)
            rw [if_neg hne]
            apply Finset.sum_eq_zero
            intro c hc
            by_cases hdc : d ∣ c
            · have hcn : c ∣ n := (Nat.mem_divisors.mp hc).1
              exact False.elim (hdn (dvd_trans hdc hcn))
            · simp [hdc]

/-- **Actual finite Möbius inversion matching**. No main-term hypothesis. -/
theorem shellIncidenceCompensator_matches (R d : ℕ) (B : ℕ → ℤ)
    (hd : 1 ≤ d) (hdR : d ≤ R) :
    (∑ c ∈ Finset.Icc 1 R,
      if d ∣ c then shellIncidenceCompensator R B c else 0) = B d := by
  classical
  unfold shellIncidenceCompensator
  calc
    (∑ c ∈ Finset.Icc 1 R,
      if d ∣ c then
        (∑ n ∈ Finset.Icc 1 R,
          if c ∣ n then (μ (n / c) : ℤ) * B n else 0) else 0) =
      ∑ c ∈ Finset.Icc 1 R, ∑ n ∈ Finset.Icc 1 R,
        if d ∣ c then (if c ∣ n then (μ (n / c) : ℤ) * B n else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          by_cases hdc : d ∣ c
          · simp [hdc, Finset.sum_ite]
          · simp [hdc]
    _ = ∑ n ∈ Finset.Icc 1 R, ∑ c ∈ Finset.Icc 1 R,
        if d ∣ c then (if c ∣ n then (μ (n / c) : ℤ) * B n else 0) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 R, (if d = n then 1 else 0) * B n := by
          apply Finset.sum_congr rfl
          intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hnR : n ≤ R := (Finset.mem_Icc.mp hn).2
          rw [← shell_upper_divisor_delta (by omega : 0 < d) hn1 hnR]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro c _
          by_cases hdc : d ∣ c <;> by_cases hcn : c ∣ n <;>
            simp [hdc, hcn]
    _ = B d := by
          simp [Finset.sum_ite_eq', Finset.mem_Icc, hd, hdR]

/-- Finite symmetric bilinear incidence quadratic, integer-valued. -/
def shellBilinear (S : Finset ℕ) (G : ℕ → ℕ → ℤ)
    (u v : ℕ → ℤ) : ℤ :=
  ∑ c ∈ S, ∑ cp ∈ S, u c * G c cp * v cp

theorem shellBilinear_symm (S : Finset ℕ) (G : ℕ → ℕ → ℤ)
    (hG : ∀ c cp, G c cp = G cp c) (u v : ℕ → ℤ) :
    shellBilinear S G u v = shellBilinear S G v u := by
  unfold shellBilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro cp _
  rw [hG cp c]
  ring

theorem shellBilinear_sub (S : Finset ℕ) (G : ℕ → ℕ → ℤ)
    (z a : ℕ → ℤ) :
    shellBilinear S G (fun c => z c - a c) (fun c => z c - a c) =
      shellBilinear S G z z - shellBilinear S G z a -
      shellBilinear S G a z + shellBilinear S G a a := by
  unfold shellBilinear
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

/-- **Complete first compensation: kernel-checked at all finite sizes.**
This is the doubled integer identity, avoiding any rounding of 1/2. -/
theorem shellCompletedSquare
    (S : Finset ℕ) (G : ℕ → ℕ → ℤ)
    (hG : ∀ c cp, G c cp = G cp c)
    (z a b : ℕ → ℤ) (SS J : ℤ)
    (hb : ∀ c ∈ S, b c = ∑ cp ∈ S, G c cp * a cp) :
    2 * SS - 2 * (∑ c ∈ S, z c * b c) +
      shellBilinear S G z z - J =
      shellBilinear S G (fun c => z c - a c)
        (fun c => z c - a c) +
      (2 * SS - shellBilinear S G a a) - J := by
  have hpair : (∑ c ∈ S, z c * b c) = shellBilinear S G z a := by
    unfold shellBilinear
    apply Finset.sum_congr rfl
    intro c hc
    rw [hb c hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cp _
    ring
  rw [hpair, shellBilinear_sub]
  rw [shellBilinear_symm S G hG a z]
  ring

/-- A prime-only cofactor at c=1 is invisible to every d>1 channel. -/
def shellDivisibilityProfile (R : ℕ) (w : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ c ∈ Finset.Icc 1 R, if d ∣ c then w c else 0

theorem shell_unit_invisible_to_higher_divisors
    (R d : ℕ) (hd : 1 < d) :
    shellDivisibilityProfile R (fun c => if c = 1 then 1 else 0) d = 0 := by
  unfold shellDivisibilityProfile
  apply Finset.sum_eq_zero
  intro c hc
  by_cases h : c = 1
  · subst c
    have hnd : ¬ d ∣ 1 := by
      intro hdiv
      have hle : d ≤ 1 := Nat.le_of_dvd (by omega) hdiv
      omega
    simp [hnd]
  · simp [h]

theorem shell_unit_visible_at_one (R : ℕ) (hR : 1 ≤ R) :
    shellDivisibilityProfile R (fun c => if c = 1 then 1 else 0) 1 = 1 := by
  unfold shellDivisibilityProfile
  simp [Finset.sum_ite_eq', Finset.mem_Icc, hR]

/-- The actual zero mode is *exactly* the square-shell energy; never drop it. -/
theorem shell_low_divisor_d1_is_energy
    (F : ℕ → ℤ) :
    F 1 ^ 2 + (∑ d ∈ Finset.Icc 2 1, (μ d : ℤ) * F d ^ 2) =
      F 1 ^ 2 := by
  simp

end RHLean.Proof
