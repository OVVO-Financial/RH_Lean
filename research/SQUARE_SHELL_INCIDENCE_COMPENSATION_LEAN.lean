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
          · have hquot : n / d ≠ 0 := by
              intro hzero
              have hp : d * (n / d) = n := Nat.mul_div_cancel' hdn
              rw [hzero, mul_zero] at hp
              omega
            have hgeom :
                n.divisors.filter (fun c => d ∣ c) =
                  (n / d).divisors.image (fun k => d * k) := by
              ext c
              simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
              constructor
              · rintro ⟨⟨hcn, _hnzero⟩, hdc⟩
                refine ⟨c / d, ⟨?_, hquot⟩, Nat.mul_div_cancel' hdc⟩
                apply (Nat.dvd_div_iff_mul_dvd hdn).2
                simpa [Nat.mul_div_cancel' hdc] using! hcn
              · rintro ⟨k, ⟨hk, _⟩, rfl⟩
                exact ⟨⟨(Nat.dvd_div_iff_mul_dvd hdn).1 hk, by omega⟩,
                  dvd_mul_right d k⟩
            have hinj :
                Set.InjOn (fun k : ℕ => d * k)
                  ((n / d).divisors : Set ℕ) := by
              intro a _ha b _hb hab
              exact Nat.eq_of_mul_eq_mul_left hd hab
            calc
              (∑ c ∈ n.divisors,
                  if d ∣ c then (μ (n / c) : ℤ) else 0) =
                ∑ c ∈ n.divisors.filter (fun c => d ∣ c),
                  (μ (n / c) : ℤ) := by rw [Finset.sum_filter]
              _ = ∑ c ∈ (n / d).divisors.image (fun k => d * k),
                    (μ (n / c) : ℤ) := by rw [hgeom]
              _ = ∑ k ∈ (n / d).divisors, (μ (n / (d * k)) : ℤ) := by
                    rw [Finset.sum_image hinj]
              _ = ∑ k ∈ (n / d).divisors, (μ ((n / d) / k) : ℤ) := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    rw [Nat.div_div_eq_div_mul]
              _ = if n / d = 1 then 1 else 0 :=
                    RHLean.Analysis.sum_moebius_complementary_divisors_eq_one_or_zero
                      (n / d)
              _ = if d = n then 1 else 0 := by
                    by_cases hEq : d = n
                    · subst n
                      simp [Nat.div_self hd]
                    · have hneq : n / d ≠ 1 := by
                        intro heq
                        have hp : d * (n / d) = n := Nat.mul_div_cancel' hdn
                        rw [heq, mul_one] at hp
                        exact hEq hp
                      simp [hEq, hneq]
          · have hne : d ≠ n := by
              intro heq
              exact hdn (heq ▸ dvd_rfl)
            rw [ite_eq_right hne]
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
          simp [Finset.mem_Icc, hd, hdR]

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
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
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

/-- The genuine d=1 summand is isolated from ALL higher divisor summands.
This is not an empty range or a boundedness assertion. -/
theorem shellLowMoment_split_unit (R : ℕ) (F : ℕ → ℤ)
    (hR : 1 ≤ R) :
    (∑ d ∈ Finset.Icc 1 R, (μ d : ℤ) * F d ^ 2) =
      F 1 ^ 2 + ∑ d ∈ Finset.Icc 2 R, (μ d : ℤ) * F d ^ 2 := by
  classical
  have hmem : 1 ∈ Finset.Icc 1 R := Finset.mem_Icc.mpr ⟨by omega, hR⟩
  have hset : (Finset.Icc 1 R).erase 1 = Finset.Icc 2 R := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hsplit := Finset.sum_erase_add
    (s := Finset.Icc 1 R)
    (f := fun d => (μ d : ℤ) * F d ^ 2) hmem
  rw [hset] at hsplit
  simpa [add_comm] using! hsplit.symm


/-- If one prime q>r owns two seats in the strict square shell, their
cofactors differ by at most one. No probabilistic or PNT input. -/
theorem shellHighOwnerCofactorsAdjacent
    (r q c cp : ℕ) (hq : r < q)
    (hcL : r ^ 2 < q * c) (hcU : q * c ≤ r ^ 2 + 2 * r)
    (hpL : r ^ 2 < q * cp) (hpU : q * cp ≤ r ^ 2 + 2 * r) :
    c ≤ cp + 1 ∧ cp ≤ c + 1 := by
  constructor
  · by_contra hn
    have hgap : cp + 2 ≤ c := by omega
    have hmul : q * cp + 2 * q ≤ q * c := by
      calc
        q * cp + 2 * q = q * (cp + 2) := by ring
        _ ≤ q * c := Nat.mul_le_mul_left q hgap
    omega
  · by_contra hn
    have hgap : c + 2 ≤ cp := by omega
    have hmul : q * c + 2 * q ≤ q * cp := by
      calc
        q * c + 2 * q = q * (c + 2) := by ring
        _ ≤ q * cp := Nat.mul_le_mul_left q hgap
    omega

/-- No high-prime owner has three distinct cofactors in one square shell. -/
theorem shellHighOwnerCannotCarryThree
    (r q c₁ c₂ c₃ : ℕ) (hq : r < q)
    (h12 : c₁ < c₂) (h23 : c₂ < c₃)
    (h1L : r ^ 2 < q * c₁) (h1U : q * c₁ ≤ r ^ 2 + 2 * r)
    (h3L : r ^ 2 < q * c₃) (h3U : q * c₃ ≤ r ^ 2 + 2 * r) : False := by
  have h := shellHighOwnerCofactorsAdjacent r q c₃ c₁ hq h3L h3U h1L h1U
  omega

/-- Any disjoint collection of coefficient buckets, when it covers every
positive divisor k of d exactly once, collapses to the genuine d=1
Möbius delta. The dyadic gcd bands instantiate this with the bit-length
bucket map; this theorem does NOT estimate the remaining square energy. -/
theorem shellBucketBetaCollapse
    (d : ℕ) (bands : Finset ℕ) (bucket : ℕ → ℕ)
    (hcover : ∀ k ∈ d.divisors, bucket k ∈ bands) :
    (∑ D ∈ bands, ∑ k ∈ d.divisors,
      if bucket k = D then (μ (d / k) : ℤ) else 0) =
        if d = 1 then 1 else 0 := by
  calc
    (∑ D ∈ bands, ∑ k ∈ d.divisors,
      if bucket k = D then (μ (d / k) : ℤ) else 0) =
        ∑ k ∈ d.divisors, ∑ D ∈ bands,
          if bucket k = D then (μ (d / k) : ℤ) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ k ∈ d.divisors, (μ (d / k) : ℤ) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [hcover k hk]
    _ = if d = 1 then 1 else 0 :=
          RHLean.Analysis.sum_moebius_complementary_divisors_eq_one_or_zero d

end RHLean.Proof
