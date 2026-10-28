import Mathlib
import «research.EULER_THREE_SITE_STRATIFIED_SAMPLING_20261028»

/-!
# Actual deterministic block-index sampling has exact first-moment discrepancy

The randomness surrogate is the moving integer square boundary, NOT a
randomization of the Mobius coefficients. For every fixed divisor d>0,
the difference between its count in [R^2,(R+1)^2) and the expected block
length divided by d has an exact modular boundary telescope.

This is a genuine, uniform, all-interval FIRST-MOMENT equidistribution
statement for each individual divisor channel (discrepancy <1 after
normalizing by d). It is NOT the missing JOINT signed second-moment
estimate across d,e and all prime-owner/site strata.

In particular, a complete joint period for coprime d,e is unnecessary
for this one-channel telescope. The products of two discrepancy streams
still require genuinely new arithmetic estimates.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

/-- Unnormalized square-block sampling discrepancy for fixed divisor d,
in exact integer coordinates. The floor quotient difference counts d-multiples,
and the endpoint difference is the length of the physical half-open block. -/
def eulerSquareBlockDivisorSampleError (R d : ℕ) : ℤ :=
  (d : ℤ) *
      (((squareRootEndpoint (R + 1) / d : ℕ) : ℤ) -
        ((squareRootEndpoint R / d : ℕ) : ℤ)) -
    (((squareRootEndpoint (R + 1) : ℕ) : ℤ) -
      ((squareRootEndpoint R : ℕ) : ℤ))

/-- The square block's entire divisor-sampling error lives at its two
fractional, i.e. modular, boundaries. Valid even for d=0. -/
theorem eulerSquareBlockDivisorSampleError_eq_mod_boundary
    (R d : ℕ) :
    eulerSquareBlockDivisorSampleError R d =
      (((squareRootEndpoint R % d : ℕ) : ℤ) -
        ((squareRootEndpoint (R + 1) % d : ℕ) : ℤ)) := by
  have hA :
      (((squareRootEndpoint R % d : ℕ) : ℤ) +
        (d : ℤ) * (((squareRootEndpoint R / d : ℕ) : ℤ))) =
          ((squareRootEndpoint R : ℕ) : ℤ) := by
    exact_mod_cast Nat.mod_add_div (squareRootEndpoint R) d
  have hB :
      (((squareRootEndpoint (R + 1) % d : ℕ) : ℤ) +
        (d : ℤ) * (((squareRootEndpoint (R + 1) / d : ℕ) : ℤ))) =
          ((squareRootEndpoint (R + 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.mod_add_div (squareRootEndpoint (R + 1)) d
  unfold eulerSquareBlockDivisorSampleError
  linear_combination hB - hA

/-- Exact deterministic equidistribution for every consecutive sampling
window: all interior square-boundary errors cancel, leaving only two
endpoint remainders. No probability or prime distribution theorem. -/
theorem eulerSquareBlockDivisorSampleError_telescope
    (A B d : ℕ) (hAB : A ≤ B) :
    (∑ R ∈ Finset.Ico A B, eulerSquareBlockDivisorSampleError R d) =
      (((squareRootEndpoint A % d : ℕ) : ℤ) -
        ((squareRootEndpoint B % d : ℕ) : ℤ)) := by
  let f : ℕ → ℤ := fun R => (((squareRootEndpoint R % d : ℕ) : ℤ))
  calc
    _ = ∑ R ∈ Finset.Ico A B, (f R - f (R + 1)) := by
      apply Finset.sum_congr rfl
      intro R _hR
      exact eulerSquareBlockDivisorSampleError_eq_mod_boundary R d
    _ = -(∑ R ∈ Finset.Ico A B, (f (R + 1) - f R)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro R _hR
      ring
    _ = -(f B - f A) := by
      rw [Finset.sum_Ico_sub f hAB]
    _ = _ := by
      dsimp [f]
      ring

/-- Strong all-window sampled FIRST-MOMENT bound: after normalizing by d,
the accumulated divisor sampling bias is <1. It is not a Mobius
correlation or a concentration theorem for the full signed sequence. -/
theorem eulerSquareBlockDivisorSampleError_abs_lt
    (A B d : ℕ) (hAB : A ≤ B) (hd : 0 < d) :
    |∑ R ∈ Finset.Ico A B, eulerSquareBlockDivisorSampleError R d| <
      (d : ℤ) := by
  rw [eulerSquareBlockDivisorSampleError_telescope A B d hAB]
  have hloA : (0 : ℤ) ≤ ((squareRootEndpoint A % d : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (squareRootEndpoint A % d))
  have hloB : (0 : ℤ) ≤ ((squareRootEndpoint B % d : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (squareRootEndpoint B % d))
  have hhiA : (((squareRootEndpoint A % d : ℕ) : ℤ)) < (d : ℤ) := by
    exact_mod_cast Nat.mod_lt (squareRootEndpoint A) hd
  have hhiB : (((squareRootEndpoint B % d : ℕ) : ℤ)) < (d : ℤ) := by
    exact_mod_cast Nat.mod_lt (squareRootEndpoint B) hd
  exact abs_lt.mpr (by constructor <;> omega)

#print axioms eulerSquareBlockDivisorSampleError_eq_mod_boundary
#print axioms eulerSquareBlockDivisorSampleError_telescope
#print axioms eulerSquareBlockDivisorSampleError_abs_lt

end RHLean.Proof
