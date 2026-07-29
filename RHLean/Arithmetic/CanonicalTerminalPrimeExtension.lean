import Mathlib
import RHLean.Arithmetic.CanonicalEndpointCore
import RHLean.Analysis.LogWeightedPrimeExtension

/-!
# Canonical terminal-prime extensions

This module isolates the unique largest-prime / lowest-cofactor representation
used by the square-block population program.  It proves uniqueness of the
canonical parent and terminal prime and the exact Möbius flip-or-zero law.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Arithmetic

open RHLean.Analysis

/-- A canonical terminal-prime extension of `n` consists of its lowest
complementary factor `parent` and its greatest prime divisor `terminal`. -/
structure CanonicalTerminalPrimeExtension (n : ℕ) where
  parent : ℕ
  terminal : ℕ
  terminal_prime : terminal.Prime
  product_eq : parent * terminal = n
  terminal_greatest : IsGreatestPrimeDivisor n terminal

namespace CanonicalTerminalPrimeExtension

variable {n : ℕ}

/-- The terminal prime divides the endpoint. -/
theorem terminal_dvd (d : CanonicalTerminalPrimeExtension n) :
    d.terminal ∣ n :=
  d.terminal_greatest.2.1

/-- Any two canonical terminal-prime extensions have the same terminal prime. -/
theorem terminal_unique
    (d e : CanonicalTerminalPrimeExtension n) :
    d.terminal = e.terminal := by
  apply Nat.le_antisymm
  · exact e.terminal_greatest.2.2 d.terminal d.terminal_prime d.terminal_dvd
  · exact d.terminal_greatest.2.2 e.terminal e.terminal_prime e.terminal_dvd

/-- Once the terminal prime is fixed, the complementary parent is forced. -/
theorem parent_unique
    (d e : CanonicalTerminalPrimeExtension n) :
    d.parent = e.parent := by
  have hterminal : d.terminal = e.terminal := terminal_unique d e
  have hprod : d.parent * e.terminal = e.parent * e.terminal := by
    calc
      d.parent * e.terminal = d.parent * d.terminal := by rw [hterminal]
      _ = n := d.product_eq
      _ = e.parent * e.terminal := e.product_eq.symm
  exact Nat.mul_right_cancel e.terminal_prime.pos hprod

/-- Canonical parent and terminal components are unique. -/
theorem components_unique
    (d e : CanonicalTerminalPrimeExtension n) :
    d.parent = e.parent ∧ d.terminal = e.terminal :=
  ⟨parent_unique d e, terminal_unique d e⟩

/-- A canonical extension is fresh when the terminal prime does not divide the
parent. -/
def Fresh (d : CanonicalTerminalPrimeExtension n) : Prop :=
  ¬ d.terminal ∣ d.parent

/-- A canonical extension is square-producing when the terminal prime already
divides the parent. -/
def Collision (d : CanonicalTerminalPrimeExtension n) : Prop :=
  d.terminal ∣ d.parent

instance instDecidableFresh (d : CanonicalTerminalPrimeExtension n) :
    Decidable d.Fresh := by
  unfold Fresh
  infer_instance

instance instDecidableCollision (d : CanonicalTerminalPrimeExtension n) :
    Decidable d.Collision := by
  unfold Collision
  infer_instance

/-- Fresh and square-producing canonical extensions are complementary. -/
theorem fresh_or_collision (d : CanonicalTerminalPrimeExtension n) :
    d.Fresh ∨ d.Collision := by
  unfold Fresh Collision
  exact Classical.em (d.terminal ∣ d.parent)

/-- A fresh canonical terminal-prime extension flips the Möbius sign. -/
theorem moebiusReal_eq_neg_parent_of_fresh
    (d : CanonicalTerminalPrimeExtension n) (hfresh : d.Fresh) :
    moebiusReal n = -moebiusReal d.parent := by
  have hflip := moebiusReal_prime_mul d.terminal_prime hfresh
  calc
    moebiusReal n = moebiusReal (d.terminal * d.parent) := by
      rw [Nat.mul_comm, d.product_eq]
    _ = -moebiusReal d.parent := hflip

/-- A square-producing canonical extension has Möbius value zero. -/
theorem moebiusReal_eq_zero_of_collision
    (d : CanonicalTerminalPrimeExtension n) (hcollision : d.Collision) :
    moebiusReal n = 0 := by
  have hsq : d.terminal * d.terminal ∣ n := by
    rw [← d.product_eq]
    exact Nat.mul_dvd_mul_right d.terminal hcollision
  have hnot : ¬ Squarefree n := by
    intro hs
    exact d.terminal_prime.not_isUnit (hs d.terminal hsq)
  have hmu : μ n = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot
  simp [moebiusReal, hmu]

/-- Exact canonical flip-or-zero law. -/
theorem moebiusReal_eq_canonical_step
    (d : CanonicalTerminalPrimeExtension n) :
    moebiusReal n = if d.Fresh then -moebiusReal d.parent else 0 := by
  by_cases hfresh : d.Fresh
  · simp [hfresh, moebiusReal_eq_neg_parent_of_fresh d hfresh]
  · have hcollision : d.Collision := by
      unfold Fresh Collision at *
      simpa using hfresh
    simp [hfresh, moebiusReal_eq_zero_of_collision d hcollision]

end CanonicalTerminalPrimeExtension

/-- A fresh canonical ancestry records the number of sign flips from `1` to an
endpoint. -/
inductive CanonicalFreshAncestry : ℕ → ℕ → Prop
  | root : CanonicalFreshAncestry 1 0
  | step {n k : ℕ}
      (d : CanonicalTerminalPrimeExtension n)
      (hfresh : d.Fresh)
      (hparent : CanonicalFreshAncestry d.parent k) :
      CanonicalFreshAncestry n (k + 1)

/-- Along a fresh canonical ancestry, the Möbius sign is exactly `(-1)^k`. -/
theorem moebiusReal_eq_negOne_pow_of_canonicalFreshAncestry
    {n k : ℕ} (h : CanonicalFreshAncestry n k) :
    moebiusReal n = (-1 : ℝ) ^ k := by
  induction h with
  | root => simp [moebiusReal]
  | @step n k d hfresh hparent ih =>
      rw [CanonicalTerminalPrimeExtension.moebiusReal_eq_neg_parent_of_fresh d hfresh, ih]
      rw [pow_succ]
      ring

/-- Existence of the canonical largest-prime / lowest-cofactor decomposition.
This is kept as an explicit finite arithmetic target until the pinned mathlib
largest-prime-factor API is connected. -/
def CanonicalTerminalPrimeExtensionExistenceStatement : Prop :=
  ∀ n : ℕ, 1 < n → Nonempty (CanonicalTerminalPrimeExtension n)

end RHLean.Arithmetic
