import RHLean.Arithmetic.PrimeCombComplementSmoothInversion
import RHLean.Arithmetic.MobiusFiniteDifferenceIdentification
import RHLean.Analysis.NativePNTChebyshev

/-!
# Full wheel recovery does not force prime divisibility of the source coefficients

The coefficient of `log q` in the genuine von Mangoldt source is one at
every positive power of the prime `q`, and zero elsewhere. Its first
nonzero site is `q`. Every nonidentity floor shift evaluates a strictly
earlier site there. Consequently the existing finite prime-wheel difference
and every iterate of it preserve this coefficient as exactly one.

The same source has an exact integral recovery by the existing smooth-number
inverse. Thus the issue tested here is not loss of arithmetic information:
full recovery does not itself earn even one factor of a prime in this
integer coefficient lattice. This does not assign a p-adic valuation to
the real number `log q`, and does not rule out a different geometric lift.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators Classical

namespace RHLean.Arithmetic

/-- The integer coefficient of `log q` on its actual prime-power fibre. -/
def nativePrimePowerCoefficient (q n : ℕ) : ℤ :=
  if ∃ k : ℕ, 0 < k ∧ n = q ^ k then 1 else 0

theorem nativePrimePowerCoefficient_pow (q k : ℕ) (hk : 0 < k) :
    nativePrimePowerCoefficient q (q ^ k) = 1 := by
  unfold nativePrimePowerCoefficient
  exact ite_eq_left ⟨k, hk, rfl⟩

theorem nativePrimePowerCoefficient_self (q : ℕ) :
    nativePrimePowerCoefficient q q = 1 := by
  simpa using nativePrimePowerCoefficient_pow q 1 (by omega)

/-- Exact attachment to the original von Mangoldt prime-power values. -/
theorem nativePrimePowerCoefficient_vonMangoldt
    {q k : ℕ} (hq : q.Prime) (hk : 0 < k) :
    Λ (q ^ k) = (nativePrimePowerCoefficient q (q ^ k) : ℝ) * Real.log q := by
  rw [nativePrimePowerCoefficient_pow q k hk,
    ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hq]
  simp

theorem nativePrimePowerCoefficient_below {q n : ℕ} (hn : n < q) :
    nativePrimePowerCoefficient q n = 0 := by
  unfold nativePrimePowerCoefficient
  apply ite_eq_right
  rintro ⟨k, hk, rfl⟩
  exact (not_lt_of_ge (Nat.le_self_pow hk.ne' q)) hn

private theorem finiteDifference_firstSupport
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (f : ℕ → ℤ) (q : ℕ) (hq : 0 < q)
    (hzero : ∀ n < q, f n = 0) :
    (∀ n < q, finiteDifferenceOperator S f n = 0) ∧
      finiteDifferenceOperator S f q = f q := by
  constructor
  · intro n hn
    unfold finiteDifferenceOperator
    apply Finset.sum_eq_zero
    intro d _hd
    unfold shift
    rw [hzero (n / d) ((Nat.div_le_self n d).trans_lt hn), mul_zero]
  · unfold finiteDifferenceOperator
    rw [Finset.sum_eq_single 1]
    · simp [shift]
    · intro d hd hd1
      have hdpos := Nat.pos_of_mem_divisors hd
      have hd2 : 1 < d := by omega
      unfold shift
      rw [hzero (q / d) (Nat.div_lt_self hq hd2), mul_zero]
    · intro h1
      exact (h1 (Nat.one_mem_divisors.mpr (primorial_ne_zero S hS))).elim

/-- Arbitrarily many complete wheel-difference passes retain the literal
unit coefficient at the first prime site. The source is fixed beforehand. -/
theorem nativePrimePowerCoefficient_wheel_iterate
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (q : ℕ) (hq : q.Prime) (m : ℕ) :
    (∀ n < q, ((finiteDifferenceOperator S)^[m]
      (nativePrimePowerCoefficient q)) n = 0) ∧
      ((finiteDifferenceOperator S)^[m] (nativePrimePowerCoefficient q)) q = 1 := by
  induction m with
  | zero =>
      exact ⟨fun n hn => nativePrimePowerCoefficient_below hn,
        nativePrimePowerCoefficient_self q⟩
  | succ m ih =>
      have h := finiteDifference_firstSupport S hS
        ((finiteDifferenceOperator S)^[m] (nativePrimePowerCoefficient q)) q hq.pos ih.1
      simpa only [Function.iterate_succ_apply'] using
        And.intro h.1 (h.2.trans ih.2)

/-- Even a single prime factor in the coefficient lattice is not earned
by this operation, regardless of the number of iterations. -/
theorem nativePrimePowerCoefficient_wheel_iterate_not_dvd
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (m : ℕ) :
    ¬ (p : ℤ) ∣
      ((finiteDifferenceOperator S)^[m] (nativePrimePowerCoefficient q)) q := by
  rw [(nativePrimePowerCoefficient_wheel_iterate S hS q hq m).2]
  intro hdiv
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hdiv)

/-- The complete coefficient fibre nevertheless has an exact integral
inverse through actual smooth-number floor shifts. No denominator is used. -/
theorem nativePrimePowerCoefficient_smooth_recovery
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (q : ℕ) (hq : q.Prime) (n : ℕ) :
    nativePrimePowerCoefficient q n =
      ∑ d ∈ primeSetSmoothIcc S n,
        finiteDifferenceOperator S (nativePrimePowerCoefficient q) (n / d) := by
  have hzero : nativePrimePowerCoefficient q 0 = 0 :=
    nativePrimePowerCoefficient_below hq.pos
  have h := finiteDifferenceOperator_eq_sum_complementSmooth ∅ S
    (by simp) hS (by simp) (nativePrimePowerCoefficient q) hzero n
  simpa using h

end RHLean.Arithmetic

#print axioms RHLean.Arithmetic.nativePrimePowerCoefficient_vonMangoldt
#print axioms RHLean.Arithmetic.nativePrimePowerCoefficient_wheel_iterate
#print axioms RHLean.Arithmetic.nativePrimePowerCoefficient_wheel_iterate_not_dvd
#print axioms RHLean.Arithmetic.nativePrimePowerCoefficient_smooth_recovery
