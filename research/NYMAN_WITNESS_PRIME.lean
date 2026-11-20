import «research.NYMAN_RIDGE_PROFILES»
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! PRIME-WITNESS: the two solved repair weights on the literal flat taper are nonzero. -/
set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace RHLean.Analysis

private theorem noOtherMultiple {p n : ℕ} (hn : 0 < n) (hlt : n < 2*p) (hne : n ≠ p) : ¬p ∣ n := by
  rintro ⟨d, hd⟩
  by_cases h0 : d = 0
  · simp [h0] at hd; omega
  by_cases h1 : d = 1
  · simp [h1] at hd; contradiction
  have hh := Nat.mul_le_mul_left p (show 2 ≤ d by omega)
  omega

private theorem integralSum {p : ℕ} [Fact p.Prime] (s : Finset ℕ)
    (h : ∀ k ∈ s, ¬p ∣ k) : 0 ≤ padicValRat p (∑ k ∈ s, 1/(k:ℚ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha]
    have h1 : 0 ≤ padicValRat p (1/(a:ℚ)) := by
      rw [one_div, padicValRat.inv, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd (h a (mem_insert_self a s))] <;> norm_num
    have h2 := ih (fun k hk => h k (mem_insert_of_mem hk))
    by_cases hz : 1/(a:ℚ) + (∑ k ∈ s, 1/(k:ℚ)) = 0
    · rw [hz, padicValRat.zero]
    · exact (le_min h1 h2).trans (padicValRat.min_le_padicValRat_add hz)

/-- An isolated prime denominator cannot give the arithmetic-mean equality K/p.
The extra condition for K=1 is needed only when the prime itself occurs. -/
theorem nyman_witness_reciprocal (p K : ℕ) (s : Finset ℕ) (hp : p.Prime)
    (hK : 0 < K) (hKp : K < p) (hs : ∀ k ∈ s, 0 < k ∧ k < 2*p)
    (hunit : p ∈ s → 2 ≤ K) : (∑ k ∈ s, 1/(k:ℚ)) ≠ (K:ℚ)/p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have bad (t : ℕ) (ht : 0 < t) (htp : t < p) : padicValRat p ((t:ℚ)/p) = -1 := by
    rw [padicValRat.div (by positivity) (by exact_mod_cast hp.ne_zero), padicValRat.self hp.one_lt,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt ht htp)] <;> norm_num
  intro he
  by_cases hm : p ∈ s
  · have h := integralSum (p := p) (s.erase p) (fun k hk =>
      noOtherMultiple (hs k (mem_erase.mp hk).2).1 (hs k (mem_erase.mp hk).2).2 (mem_erase.mp hk).1)
    have hadd := Finset.add_sum_erase s (fun k : ℕ => 1/(k:ℚ)) hm
    rw [he] at hadd
    have he' : (∑ k ∈ s.erase p, 1/(k:ℚ)) = ((K-1:ℕ):ℚ)/p := by
      rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one, sub_div]; linarith
    rw [he', bad _ (by have := hunit hm; omega) (by omega)] at h
    omega
  · have h := integralSum (p := p) s (fun k hk => noOtherMultiple (hs k hk).1 (hs k hk).2
      (fun heq => hm (heq ▸ hk)))
    rw [he, bad K hK hKp] at h
    omega

-- A positive rational whose logarithm is a common integer multiple certifies
-- a rational prime coordinate. No formal independence assumption is needed.
private def Tracks (p : ℕ) (x : ℝ) (u : ℚ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∃ r : ℚ, 0 < r ∧ Real.log (r:ℝ) = d*x ∧ (padicValRat p r:ℚ) = d*u

private theorem trAdd {p : ℕ} [Fact p.Prime] {x y : ℝ} {u v : ℚ}
    (hx : Tracks p x u) (hy : Tracks p y v) : Tracks p (x+y) (u+v) := by
  obtain ⟨d, hd, r, hr, hx, hu⟩ := hx
  obtain ⟨e, he, t, ht, hy, hv⟩ := hy
  refine ⟨d*e, Nat.mul_pos hd he, r^e*t^d, by positivity, ?_, ?_⟩
  · push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, hx, hy]; ring
  · rw [padicValRat.mul (pow_ne_zero _ hr.ne') (pow_ne_zero _ ht.ne'),
      padicValRat.pow, padicValRat.pow]
    push_cast
    rw [hu, hv]; ring

private theorem trScale {p : ℕ} [Fact p.Prime] {x : ℝ} {u : ℚ} (c : ℚ)
    (h : Tracks p x u) : Tracks p ((c:ℝ)*x) (c*u) := by
  obtain ⟨d, hd, r, hr, hx, hu⟩ := h
  have hq : c * (c.den:ℚ) = c.num := (eq_div_iff (by exact_mod_cast c.den_nz)).mp c.num_div_den.symm
  have hR : (c:ℝ) * (c.den:ℝ) = c.num := by exact_mod_cast hq
  refine ⟨d*c.den, Nat.mul_pos hd c.den_pos, r^c.num, zpow_pos hr _, ?_, ?_⟩
  · push_cast
    rw [Real.log_zpow, hx, ← hR]; ring
  · rw [padicValRat.zpow]
    push_cast
    rw [hu, ← hq]; ring

private theorem trSub {p : ℕ} [Fact p.Prime] {x y : ℝ} {u v : ℚ}
    (hx : Tracks p x u) (hy : Tracks p y v) : Tracks p (x-y) (u-v) := by
  simpa [sub_eq_add_neg] using trAdd hx (trScale (-1) hy)

private theorem trSum {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℝ) (g : ℕ → ℚ)
    (h : ∀ k ∈ s, Tracks p (f k) (g k)) : Tracks p (∑ k ∈ s, f k) (∑ k ∈ s, g k) := by
  induction s using Finset.induction_on with
  | empty => simpa using (show Tracks p 0 0 from ⟨1, by decide, 1, by decide, by simp, by simp⟩)
  | @insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact trAdd (h a (mem_insert_self a s)) (ih (fun k hk => h k (mem_insert_of_mem hk)))

private theorem trDetect {p : ℕ} {x : ℝ} {u : ℚ} (h : Tracks p x u) (hz : x = 0) : u = 0 := by
  obtain ⟨d, hd, r, hr, hx, hu⟩ := h
  have he := Real.exp_log (show (0:ℝ) < r by exact_mod_cast hr)
  rw [hx, hz, mul_zero, Real.exp_zero] at he
  have hr1 : r = 1 := by exact_mod_cast he.symm
  rw [hr1, padicValRat.one, Int.cast_zero] at hu
  exact (mul_eq_zero.mp hu.symm).resolve_left (by positivity)

private theorem trLog {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hlt : n < 2*p) :
    Tracks p (Real.log n) (if n=p then 1 else 0) := by
  refine ⟨1, by decide, n, by exact_mod_cast hn, by simp, ?_⟩
  by_cases h : n=p
  · subst n; rw [padicValRat.self hp.one_lt]; simp
  · rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (noOtherMultiple hn hlt h)]; simp [h]

private theorem sourceCoordinates (K H p : ℕ) (hp : p.Prime) (hlo : 3*K < p) (hhi : p < 6*K)
    (hH : 0 < H) (hHp : H < p) :
    Tracks p (nymanFlatMoment (6*K) H) (1/(p:ℚ)) ∧ Tracks p (nymanRidgeV K H) 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hn := trLog hp (n := 6*K) (by omega) (by omega)
  have hh := trLog hp hH (by omega)
  simp only [show 6*K ≠ p by omega, ite_false] at hn
  simp only [hHp.ne, ite_false] at hh
  have kernel (k : ℕ) (hk : k ∈ Icc 1 (6*K)) :
      Tracks p (nymanFlatKernel (6*K) H k) (if k=p then 1 else 0) := by
    obtain ⟨hk0, hkN⟩ := mem_Icc.mp hk
    have hm0 : 0 < max H k := lt_of_lt_of_le hH (le_max_left ..)
    have hm2 : max H k < 2*p := max_lt (by omega) (by omega)
    have ht := trScale (ArithmeticFunction.moebius k : ℚ) (trSub hn (trLog hp hm0 hm2))
    rw [nymanFlatKernel_eq_original _ _ _ (by omega) hH hk0,
      Real.log_div (by exact_mod_cast (show 6*K ≠ 0 by omega)) (by exact_mod_cast hm0.ne')]
    by_cases he : k = p
    · subst k; simpa [max_eq_right hHp.le, ArithmeticFunction.moebius_apply_prime hp] using ht
    · have hmp : max H k ≠ p := by
        rcases le_total H k with h|h
        · simpa only [max_eq_right h] using he
        · simpa only [max_eq_left h] using hHp.ne
      simpa [he, hmp] using ht
  have hm : p ∈ Icc 1 (6*K) := mem_Icc.mpr ⟨hp.pos, hhi.le⟩
  constructor
  · unfold nymanFlatMoment
    have ht := trSum (p := p) (Icc 1 (6*K)) _ (fun k => (if k=p then 1 else 0)/(k:ℚ))
      (fun k hk => show Tracks p (nymanFlatKernel (6*K) H k / k) _ from by
        simpa [div_eq_mul_inv, mul_comm] using trScale (1/(k:ℚ)) (kernel k hk))
    have he : (∑ k ∈ Icc 1 (6*K), (if k=p then 1 else 0)/(k:ℚ)) = 1/(p:ℚ) := by
      rw [sum_eq_single_of_mem p hm (fun k _ hne => by simp [hne])]; simp
    rwa [he] at ht
  · have hs := trSum (Icc 1 (6*K)) _ _ kernel
    have he : (∑ k ∈ Icc 1 (6*K), (if k=p then (1:ℚ) else 0)) = 1 := by simp [hm]
    rw [he] at hs
    simpa [nymanRidgeV, nymanFlatScale] using trAdd (trScale 2 (trSub hn hh)) hs

private theorem massNe (K H p a b : ℕ) (hp : p.Prime) (hK : 0 < K) (hlo : 3*K < p)
    (hhi : p < 6*K) (hH : 0 < H) (hHp : H < p) (hb : b ≤ 6*K)
    (hunit : p ∈ Ioc a b → 2 ≤ K) :
    nymanFlatMoment (6*K) H - nymanRidgeS a b * nymanRidgeV K H / K ≠ 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let s : ℚ := ∑ k ∈ Ioc a b, 1/(k:ℚ)
  have hs : (s:ℝ) = nymanRidgeS a b := by simp [s, nymanRidgeS]
  have hn : s ≠ (K:ℚ)/p := nyman_witness_reciprocal p K _ hp hK (by omega)
    (fun k hk => by obtain ⟨_, _⟩ := mem_Ioc.mp hk; constructor <;> omega) hunit
  obtain ⟨hu,hv⟩ := sourceCoordinates K H p hp hlo hhi hH hHp
  have ht := trSub hu (trScale (s/K) hv)
  have hr : ((s/(K:ℚ):ℚ):ℝ)*nymanRidgeV K H = nymanRidgeS a b * nymanRidgeV K H / K := by
    push_cast; rw [hs]; ring
  rw [hr] at ht
  intro he
  have hc : 1/(p:ℚ)-s/(K:ℚ) = 0 := by simpa using trDetect ht he
  apply hn
  have hpn : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hKn : (K:ℚ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp [hpn,hKn] at hc ⊢ <;> linarith

/-- The witness need only lie above H, not immediately above the lower half. -/
theorem nyman_witness_amplitudes_of_prime (K H p : ℕ) (hp : p.Prime)
    (hlo : 3*K < p) (hhi : p < 6*K) (hH : 0 < H) (hHp : H < p) :
    nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) ≠ 0 ∧
    nymanRidgeRight K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) ≠ 0 := by
  have hK : 0 < K := by omega
  have hd := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/12) (nyman_ridge_gap K hK)).ne'
  constructor
  · apply div_ne_zero _ hd
    apply massNe K H p (5*K) (6*K) hp hK hlo hhi hH hHp le_rfl
    intro h; have := mem_Ioc.mp h; omega
  · apply div_ne_zero _ hd
    apply sub_ne_zero.mpr
    apply Ne.symm
    apply sub_ne_zero.mp
    apply massNe K H p (3*K) (4*K) hp hK hlo hhi hH hHp (by omega)
    intro h; have := mem_Ioc.mp h
    by_contra hh
    have he : p=4 := by omega
    rw [he] at hp; norm_num at hp

theorem nyman_witness_amplitudes (K H : ℕ) (hK : 0<K) (hH : 0<H) (hHK : H ≤ 3*K) :
    nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) ≠ 0 ∧
    nymanRidgeRight K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) ≠ 0 := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.bertrand (3*K) (by omega)
  have hn : p ≠ 6*K := by
    intro he; rw [he] at hp
    have h := (Nat.dvd_prime hp).mp (show 2 ∣ 6*K from ⟨3*K, by omega⟩); omega
  exact nyman_witness_amplitudes_of_prime K H p hp hlo (by omega) hH (by omega)

end RHLean.Analysis
