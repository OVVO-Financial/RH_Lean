import Mathlib
import «research.SQUARE_SHELL_TRAPEZOID_FINITE_COFACTOR_20261018»

/-!
# Translated square-shell prime-owner orientation is a fixed factor triangle

If 2 <= r, T <= r-2 and 0 <= k <= 2T, then for any positive
product p*c in the genuine translated half-open shell
(r^2-T+k,(r+1)^2-T+k], the moving condition

  r < p and c <= r

is EQUIVALENT to the factor-order condition

  c < p.

Neither a prime-density estimate nor unique factorization is needed for the
geometric lemma. Specializing p to actual primes gives a stationary triangle
in the (p,c) plane. Choosing T comparable to H makes the remaining high-
cofactor band T<c<=r into a balanced Type II range p,c=O(H) instead of the
asymmetric p<=O(H^(4/3)) band when T=H^(2/3).

This is a source-coordinate identity, not a signed bilinear bound.
-/

noncomputable section

namespace RHLean.Analysis

/-- The lower translated wall lies *strictly above* r*(r-1). This excludes
factor pairs p<=r, c<p even at the most negative admissible translation. -/
theorem shellTrapezoidLower_gt_root_predecessor
    (r T k : ℕ) (hr : 2 ≤ r) (hT : T ≤ r - 2) :
    r * (r - 1) < shellTrapezoidLower r T k := by
  have hpred : r - 1 + 1 = r := by omega
  have hfactor : r * (r - 1) + r = r ^ 2 := by
    calc
      r * (r - 1) + r = r * ((r - 1) + 1) := by ring
      _ = r * r := by rw [hpred]
      _ = r ^ 2 := by ring
  unfold shellTrapezoidLower
  omega

/-- The upper translated wall lies strictly below (r+1)*(r+2).
This excludes p>c>=r+1 even at the most positive translation. -/
theorem shellTrapezoidUpper_lt_next_factor_product
    (r T k : ℕ) (hr : 2 ≤ r) (hT : T ≤ r - 2)
    (hk : k ≤ 2 * T) :
    shellTrapezoidUpper r T k < (r + 1) * (r + 2) := by
  have hfactor : (r + 1) * (r + 2) = (r + 1) ^ 2 + (r + 1) := by ring
  have hsqexpand : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
  have hsquare : T ≤ (r + 1) ^ 2 := by omega
  have hmargin : T < r + 1 := by omega
  unfold shellTrapezoidUpper
  omega

/-- **Exact fixed-triangle owner criterion for every translated half-open
shell**: no moving root cutoff survives on an admitted product. -/
theorem shellTrapezoidAdmitted_owner_iff_factorOrder
    (r T k p c : ℕ) (hr : 2 ≤ r) (hT : T ≤ r - 2)
    (hk : k ≤ 2 * T)
    (hadmit : shellTrapezoidProductAdmitted r T k p c) :
    (r < p ∧ c ≤ r) ↔ c < p := by
  constructor
  · rintro ⟨hrp, hcr⟩
    omega
  · intro hcp
    have hlower := shellTrapezoidLower_gt_root_predecessor r T k hr hT
    have hupper := shellTrapezoidUpper_lt_next_factor_product r T k hr hT hk
    have hrp : r < p := by
      by_contra hnot
      have hp : p ≤ r := by omega
      have hc : c ≤ r - 1 := by omega
      have hprod : p * c ≤ r * (r - 1) := by
        calc
          p * c ≤ r * c := Nat.mul_le_mul_right c hp
          _ ≤ r * (r - 1) := Nat.mul_le_mul_left r hc
      exact absurd hadmit.1 (by omega)
    have hcr : c ≤ r := by
      by_contra hnot
      have hc : r + 1 ≤ c := by omega
      have hp : r + 2 ≤ p := by omega
      have hprod : (r + 1) * (r + 2) ≤ p * c := by
        calc
          (r + 1) * (r + 2) = (r + 2) * (r + 1) := by ring
          _ ≤ p * (r + 1) := Nat.mul_le_mul_right (r + 1) hp
          _ ≤ p * c := Nat.mul_le_mul_left p hc
      exact absurd hadmit.2 (by omega)
    exact ⟨hrp, hcr⟩

/-- Actual signed high-owner factor on one physical translated shell.
The underlying Mobius cofactor sign is never replaced by a density. -/
noncomputable def shellTrapezoidMovingOwnerAtom
    (r T k p c : ℕ) : ℝ := by
  classical
  exact if r < p ∧ c ≤ r ∧ shellTrapezoidProductAdmitted r T k p c
        then shellTrapezoidMu c else 0

/-- The same signed atom with no moving r-relative prime condition. -/
noncomputable def shellTrapezoidFixedTriangleAtom
    (r T k p c : ℕ) : ℝ := by
  classical
  exact if c < p ∧ shellTrapezoidProductAdmitted r T k p c
        then shellTrapezoidMu c else 0

/-- Exact equality of the moving-root and fixed-factor high-prime sources.
No prime number theorem, Dirichlet polynomial or signed estimate is used. -/
theorem shellTrapezoidMovingOwner_eq_fixedTriangle
    (r T k p c : ℕ) (hr : 2 ≤ r) (hT : T ≤ r - 2)
    (hk : k ≤ 2 * T) :
    shellTrapezoidMovingOwnerAtom r T k p c =
      shellTrapezoidFixedTriangleAtom r T k p c := by
  classical
  unfold shellTrapezoidMovingOwnerAtom shellTrapezoidFixedTriangleAtom
  by_cases hadmit : shellTrapezoidProductAdmitted r T k p c
  · have hiff := shellTrapezoidAdmitted_owner_iff_factorOrder
      r T k p c hr hT hk hadmit
    by_cases hfactor : c < p
    · have howner : r < p ∧ c ≤ r := hiff.mpr hfactor
      simp [hadmit, hfactor, howner]
    · have howner : ¬(r < p ∧ c ≤ r) := by
        intro hh
        exact hfactor (hiff.mp hh)
      simp [hadmit, hfactor, howner]
  · simp [hadmit]

#print axioms shellTrapezoidLower_gt_root_predecessor
#print axioms shellTrapezoidUpper_lt_next_factor_product
#print axioms shellTrapezoidAdmitted_owner_iff_factorOrder
#print axioms shellTrapezoidMovingOwner_eq_fixedTriangle

end RHLean.Analysis
