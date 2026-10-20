import Mathlib

/-!
# Every integer in the 317 / 1027 Mobius prefixes, exactly

This uses the GENUINE Mathlib integer Mobius at each natural site. Each
recursive step records:
   (M_n, K_n, C_n)
 = (sum_{1<=i<=n} mu(i),
    sum_{1<=i<=n} mu(i)^2,
    sum_{1<=i<j<=n} mu(i)mu(j)).

The pair-covariance recurrence is literally
  C_(n+1) = C_n + mu(n+1)*M_n,
so no signed pair or squarefree zero disappears.

The two complete finite prefixes are acceptance tests. The global
7/8 theorem has an all-n and epsilon-dependent uniform-constant
quantifier, and does NOT follow just from these computations.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Genuine integer Mobius, not a synthetic 0 or +1 or -1 stream. -/
def vf919ExactSiteMu (n : ℕ) : ℤ :=
  ArithmeticFunction.moebius n

/-- Exact signed pair ledger one integer at a time. -/
def vf919ExactSiteLedgerStep (t : ℤ × ℤ × ℤ) (a : ℤ) :
    ℤ × ℤ × ℤ :=
  (t.1 + a, t.2.1 + a ^ 2, t.2.2 + t.1 * a)

/-- The state after physically admitting every integer site 1,...,n. -/
def vf919ExactSiteLedger : ℕ → ℤ × ℤ × ℤ
  | 0 => (0, 0, 0)
  | n + 1 =>
      vf919ExactSiteLedgerStep
        (vf919ExactSiteLedger n) (vf919ExactSiteMu (n + 1))

/-- The zero-target energy is an invariant of each single-site update. -/
theorem vf919ExactSiteLedgerStep_greenKubo
    (t : ℤ × ℤ × ℤ) (a : ℤ)
    (h : t.1 ^ 2 = t.2.1 + 2 * t.2.2) :
    (vf919ExactSiteLedgerStep t a).1 ^ 2 =
      (vf919ExactSiteLedgerStep t a).2.1 +
        2 * (vf919ExactSiteLedgerStep t a).2.2 := by
  simp only [vf919ExactSiteLedgerStep]
  nlinarith [h]

/-- Every prefix has the exact diagonal + twice signed pair covariance. -/
theorem vf919ExactSiteLedger_greenKubo (n : ℕ) :
    (vf919ExactSiteLedger n).1 ^ 2 =
      (vf919ExactSiteLedger n).2.1 +
        2 * (vf919ExactSiteLedger n).2.2 := by
  induction n with
  | zero => norm_num [vf919ExactSiteLedger]
  | succ n ih =>
      change (vf919ExactSiteLedgerStep
        (vf919ExactSiteLedger n) (vf919ExactSiteMu (n + 1))).1 ^ 2 =
          (vf919ExactSiteLedgerStep
            (vf919ExactSiteLedger n) (vf919ExactSiteMu (n + 1))).2.1 +
          2 * (vf919ExactSiteLedgerStep
            (vf919ExactSiteLedger n) (vf919ExactSiteMu (n + 1))).2.2
      exact vf919ExactSiteLedgerStep_greenKubo _ _ ih

/-- The ledger is the original Mobius prefix, not just an abstract
    process satisfying a covariance identity. -/
theorem vf919ExactSiteLedger_mass_eq_actualMuPrefix (n : ℕ) :
    (vf919ExactSiteLedger n).1 =
      ∑ i ∈ Finset.range n, vf919ExactSiteMu (i + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (vf919ExactSiteLedger n).1 +
          vf919ExactSiteMu (n + 1) =
        ∑ i ∈ Finset.range (n + 1), vf919ExactSiteMu (i + 1)
      rw [Finset.sum_range_succ, ih]

/-- Exact finite full prefix certificate. Every 1<=n<=317 contributes its
    *actual* Mobius sign and its complete pairs with all earlier integers.
    Here M=-4, diagonal=194, signed pair=-89. -/
set_option maxRecDepth 16384 in
theorem vf919ExactSiteLedger_317 :
    vf919ExactSiteLedger 317 = ((-4 : ℤ), 194, -89) := by
  native_decide

/-- Same, without selecting only the high-prime/Eisenstein sector:
    every 1<=n<=1027 is admitted. M=-3, diagonal=625, signed pair=-308. -/
set_option maxRecDepth 16384 in
theorem vf919ExactSiteLedger_1027 :
    vf919ExactSiteLedger 1027 = ((-3 : ℤ), 625, -308) := by
  native_decide

/-- Finite exact 7/8 exponent certificate at both complete prefixes:
    M(x)^8 <= x^7 is the integer-only form of |M(x)|<=x^(7/8).
    The constant 1 is specific to these finite checks, not universal. -/
theorem vf919ExactSiteLedger_317_1027_sevenEighths :
    (vf919ExactSiteLedger 317).1 ^ 8 ≤ (317 : ℤ) ^ 7 ∧
      (vf919ExactSiteLedger 1027).1 ^ 8 ≤ (1027 : ℤ) ^ 7 := by
  constructor
  · rw [vf919ExactSiteLedger_317]
    norm_num
  · rw [vf919ExactSiteLedger_1027]
    norm_num

/-- The actual covariance payment, not just the amplitude value. -/
theorem vf919ExactSiteLedger_317_1027_covariance_payment :
    (vf919ExactSiteLedger 317).2.1 +
      2 * (vf919ExactSiteLedger 317).2.2 = 16 ∧
    (vf919ExactSiteLedger 1027).2.1 +
      2 * (vf919ExactSiteLedger 1027).2.2 = 9 := by
  constructor
  · rw [vf919ExactSiteLedger_317]
    norm_num
  · rw [vf919ExactSiteLedger_1027]
    norm_num

#print axioms vf919ExactSiteLedger_greenKubo
#print axioms vf919ExactSiteLedger_mass_eq_actualMuPrefix
#print axioms vf919ExactSiteLedger_317
#print axioms vf919ExactSiteLedger_1027
#print axioms vf919ExactSiteLedger_317_1027_sevenEighths
#print axioms vf919ExactSiteLedger_317_1027_covariance_payment

end RHLean.Analysis
