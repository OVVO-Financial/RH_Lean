import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Prime-exponent fibres of the square clock

Factorization gives the low and high parts on the original integers. The
norm estimate uses the total exponent of the high part. The strict clock
inequality is in squared integer form, so it also handles the endpoints.
-/

namespace RHLean.Analysis.AlpogeThin.PrimeExponent

open scoped BigOperators

/-- Retain the complete multiplicity at every prime in the specified part. -/
def part (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ :=
  (n.factorization.filter P).prod (fun p a => p ^ a)

theorem part_mul_complement (P : ℕ → Prop) [DecidablePred P] {n : ℕ} (hn : n ≠ 0) :
    part P n * part (fun p => ¬ P p) n = n := by
  unfold part
  rw [← Finsupp.prod_add_index' (fun p : ℕ => pow_zero p) (fun p i j => pow_add p i j),
    Finsupp.filter_add_filter_not, Nat.prod_factorization_pow_eq_self hn]

theorem factorization_part (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    (part P n).factorization = n.factorization.filter P := by
  apply Nat.factorization_prod_pow_eq_self_of_le_factorization (n := n)
  intro p
  rw [Finsupp.filter_apply]
  split <;> first | exact le_rfl | exact Nat.zero_le _

theorem high_prime (z n p : ℕ) (hp : p ∈ (part (fun q => ¬ q ≤ z) n).primeFactors) :
    z < p := by
  by_contra! h
  have hv : (part (fun q => ¬ q ≤ z) n).factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp hp
  rw [factorization_part, Finsupp.filter_apply] at hv
  simp [h] at hv

def omegaTotal (h : ℕ) : ℕ := ∑ p ∈ h.primeFactors, h.factorization p

/-- Every factor in the high part pays at least one factor of the cutoff. -/
theorem cutoff_pow_omega_le {z h : ℕ} (hh : h ≠ 0)
    (hrough : ∀ p ∈ h.primeFactors, z < p) : z ^ omegaTotal h ≤ h := by
  calc
    z ^ omegaTotal h = ∏ p ∈ h.primeFactors, z ^ h.factorization p :=
      (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ p ∈ h.primeFactors, p ^ h.factorization p := by
      exact Finset.prod_le_prod fun p hp => Nat.pow_le_pow_left (hrough p hp).le _
    _ = h := Nat.prod_factorization_pow_eq_self hh

/-- This is the bound for the unweighted column mass of either signed or
unsigned binomial translation. It holds on the full truncated prefix. -/
theorem mass_le_rpow {z h N : ℕ} (hz : 1 < z) (hh : h ≠ 0) (hN : h ≤ N)
    (hrough : ∀ p ∈ h.primeFactors, z < p) :
    (2 : ℝ) ^ omegaTotal h ≤ (N : ℝ) ^ (Real.log 2 / Real.log z) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hh).trans_le hN
  have hzpos : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hzlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have h2log : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hp : (z : ℝ) ^ omegaTotal h ≤ N := by
    exact_mod_cast (cutoff_pow_omega_le hh hrough).trans hN
  have hlog := Real.log_le_log (pow_pos hzpos _) hp
  rw [Real.log_pow] at hlog
  rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hNpos _),
    Real.log_pow, Real.log_rpow hNpos, div_mul_eq_mul_div, le_div_iff₀ hzlog]
  calc
    _ = Real.log 2 * ((omegaTotal h : ℝ) * Real.log z) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog h2log

/-- A proper high divisor is more than one cutoff behind its originating
site, strictly even at a perfect-square endpoint. -/
theorem proper_ancestor {z l h d : ℕ} (hl : 0 < l) (hh : 0 < h) (hd : d ∣ h)
    (hne : d ≠ h) (hrough : ∀ p ∈ h.primeFactors, z < p) :
    z * (l * d) < l * h := by
  obtain ⟨q, hq⟩ := hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero fun hd0 => by simp [hd0] at hq; omega
  have hqpos : 0 < q := Nat.pos_of_ne_zero fun hq0 => by simp [hq0] at hq; omega
  have hq1 : q ≠ 1 := by intro h; apply hne; simpa [h] using hq.symm
  have hprime := Nat.minFac_prime hq1
  have hdiv : q.minFac ∣ h := dvd_trans (Nat.minFac_dvd q) ⟨d, by simpa [Nat.mul_comm] using hq⟩
  have hzq := (hrough _ (hprime.mem_primeFactors hdiv hh.ne')).trans_le
    (Nat.le_of_dvd hqpos (Nat.minFac_dvd q))
  calc
    z * (l * d) < q * (l * d) := Nat.mul_lt_mul_of_pos_right hzq (Nat.mul_pos hl hdpos)
    _ = l * h := by rw [hq]; ring

theorem ancestor_clock {z l h d R : ℕ} (hl : 0 < l) (hh : 0 < h) (hd : d ∣ h)
    (hne : d ≠ h) (hrough : ∀ p ∈ h.primeFactors, z < p)
    (hblock : l * h < (R + 1) ^ 2) :
    z * (Nat.sqrt (l * d)) ^ 2 < (R + 1) ^ 2 :=
  (Nat.mul_le_mul_left z (Nat.sqrt_le' _)).trans_lt
    ((proper_ancestor hl hh hd hne hrough).trans hblock)

end RHLean.Analysis.AlpogeThin.PrimeExponent
