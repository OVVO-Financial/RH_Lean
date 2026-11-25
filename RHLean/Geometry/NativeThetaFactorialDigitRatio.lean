import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Consecutive coarse factorial units

For a block of length `P`, crossing the residue `ρ` determines which
of the two consecutive blocks supplies each nonzero residue. The exact
rational recurrence exposes a factor of `p` in each slope when `P = p^g`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RHLean.Geometry.NativeTheta.ExponentDigits

/-- The rational factorial quotient at residue `ρ` and coarse index `b`. -/
def factorialDigitUnit (P ρ b : ℕ) : ℚ :=
  ((ρ + P * b).factorial : ℚ) /
    ((ρ.factorial : ℚ) * (P.factorial : ℚ) ^ b * (b.factorial : ℚ))

private theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

private theorem shifted_interval_prod (a lo hi : ℕ) (h : lo ≤ hi) :
    (∏ u ∈ Finset.Ioc lo hi, ((a : ℚ) + u)) =
      ((a + hi).factorial : ℚ) / ((a + lo).factorial : ℚ) := by
  induction hi, h using Nat.le_induction with
  | base => simp [factorial_cast_ne_zero]
  | succ hi h ih =>
    rw [Finset.prod_Ioc_succ_top h, ih, show a + (hi + 1) = (a + hi) + 1 by omega,
      Nat.factorial_succ (a + hi)]
    push_cast
    ring

/-- Every residue occurs once in the quotient of two consecutive block factorials. -/
theorem factorialDigitUnit_succ_ratio (P ρ b : ℕ) (hρ : ρ < P) :
    factorialDigitUnit P ρ (b + 1) / factorialDigitUnit P ρ b =
      ∏ u ∈ Finset.Ico 1 P,
        (1 + (P : ℚ) / u * ((b : ℚ) + if u ≤ ρ then 1 else 0)) := by
  let f (u : ℕ) : ℚ := 1 + (P : ℚ) / u * ((b : ℚ) + if u ≤ ρ then 1 else 0)
  let n (u : ℕ) : ℚ :=
    if u ≤ ρ then ((P * (b + 1) : ℕ) : ℚ) + u else ((P * b : ℕ) : ℚ) + u
  have hlow : (∏ u ∈ Finset.Ioc 0 ρ, n u) =
      ∏ u ∈ Finset.Ioc 0 ρ, (((P * (b + 1) : ℕ) : ℚ) + u) := by
    exact Finset.prod_congr rfl fun u hu => if_pos (Finset.mem_Ioc.mp hu).2
  have hhigh : (∏ u ∈ Finset.Ioc ρ P, n u) =
      ∏ u ∈ Finset.Ioc ρ P, (((P * b : ℕ) : ℚ) + u) := by
    exact Finset.prod_congr rfl fun u hu => if_neg (not_le.mpr (Finset.mem_Ioc.mp hu).1)
  have hnum : (∏ u ∈ Finset.Ioc 0 P, n u) =
      ((P * (b + 1) + ρ).factorial : ℚ) / ((P * b + ρ).factorial : ℚ) := by
    rw [← Finset.prod_Ioc_consecutive n (Nat.zero_le ρ) hρ.le, hlow, hhigh,
      shifted_interval_prod _ _ _ (Nat.zero_le ρ), shifted_interval_prod _ _ _ hρ.le,
      Nat.add_zero, ← Nat.mul_succ P b]
    field_simp [factorial_cast_ne_zero] <;> ring
  have hden : (∏ u ∈ Finset.Ioc 0 P, (u : ℚ)) = (P.factorial : ℚ) := by
    simpa using shifted_interval_prod 0 0 P (Nat.zero_le P)
  have hfull : (∏ u ∈ Finset.Ioc 0 P, f u) =
      ((P * (b + 1) + ρ).factorial : ℚ) / ((P * b + ρ).factorial : ℚ) /
        (P.factorial : ℚ) := by
    calc
      _ = ∏ u ∈ Finset.Ioc 0 P, n u / (u : ℚ) := by
        apply Finset.prod_congr rfl
        intro u hu
        have hu' : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.mem_Ioc.mp hu).1.ne'
        by_cases hh : u ≤ ρ <;> simp only [f, n, hh, if_true, if_false] <;>
          push_cast <;> field_simp [hu'] <;> ring
      _ = _ := by rw [Finset.prod_div_distrib, hnum, hden]
  have hset : Finset.Ioc 0 P = insert P (Finset.Ico 1 P) := by
    ext u
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hP0 : (P : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : P ≠ 0)
  have hfP : f P = (b : ℚ) + 1 := by simp [f, not_le.mpr hρ, hP0, add_comm]
  rw [hset, Finset.prod_insert (by simp), hfP] at hfull
  change factorialDigitUnit P ρ (b + 1) / factorialDigitUnit P ρ b = ∏ u ∈ Finset.Ico 1 P, f u
  calc
    _ = (((P * (b + 1) + ρ).factorial : ℚ) / ((P * b + ρ).factorial : ℚ) /
           (P.factorial : ℚ)) / ((b : ℚ) + 1) := by
      unfold factorialDigitUnit
      rw [Nat.add_comm ρ (P * (b + 1)), Nat.add_comm ρ (P * b),
        Nat.factorial_succ b, pow_succ (P.factorial : ℚ) b]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hb : (b : ℚ) + 1 ≠ 0 := by positivity
      have hpow := pow_ne_zero b (factorial_cast_ne_zero P)
      field_simp [factorial_cast_ne_zero, hb, hpow] <;> ring
    _ = _ := (div_eq_iff (by positivity : (b : ℚ) + 1 ≠ 0)).2
      (hfull.symm.trans (mul_comm _ _))

/-- After one factor of `p` is removed from the slope, its reduced denominator
is prime to `p`. This gives an explicit rational coefficient in ℤ localized at `p`. -/
theorem factorialDigitUnit_slope_local (p g u : ℕ) [Fact p.Prime]
    (hu : 0 < u) (huP : u < p ^ g) :
    let c : ℚ := (p : ℚ) ^ g / ((p : ℚ) * u)
    0 ≤ padicValRat p c ∧ ¬ p ∣ c.den := by
  let c : ℚ := (p : ℚ) ^ g / ((p : ℚ) * u)
  change 0 ≤ padicValRat p c ∧ ¬ p ∣ c.den
  have hvu : padicValNat p u < g := by
    by_contra! h
    have hd : p ^ g ∣ u := (padicValNat_dvd_iff_le hu.ne').2 h
    exact (not_le.mpr huP) (Nat.le_of_dvd hu hd)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu.ne'
  have hv : 0 ≤ padicValRat p c := by
    dsimp only [c]
    rw [padicValRat.div (pow_ne_zero _ hp0) (mul_ne_zero hp0 hu0),
      padicValRat.mul hp0 hu0, padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt,
      padicValRat.of_nat, mul_one]
    omega
  refine ⟨hv, ?_⟩
  intro hd
  have hdpos : 0 < padicValNat p c.den :=
    Nat.pos_of_ne_zero ((dvd_iff_padicValNat_ne_zero c.den_nz).mp hd)
  rcases c.num_or_den_zero_padicVal (Fact.out : p.Prime) with hn | hn
  · rw [padicValRat_def, hn] at hv
    omega
  · omega

end RHLean.Geometry.NativeTheta.ExponentDigits
