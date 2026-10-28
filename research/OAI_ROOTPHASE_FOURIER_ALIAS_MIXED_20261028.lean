import Mathlib

/-!
# Original root-phase Fourier aliasing: genuine Mobius mixed-mode warning

The exact square-block Fourier mask is
  exp(2*pi*i*theta*floor(sqrt n)).
Fourier expansion of the periodic fractional-root factor produces
harmonic modes with *coherent signed cross-mode terms*. Merely retaining
diagonal O(k^-2) weights is invalid without a separate orthogonality
theorem. This file certifies a genuine, extremely small Mobius witness:

  5, 6 belong to the same physical shell [2^2,3^2)
  mu(5)=-1, mu(6)=+1.

Consequently their exact floor-root-phase contribution is ZERO for
every theta, whereas their smooth-root-phase contributions need not
vanish when the phases differ.

It also proves the generic two-mode diagonal-only identity is FALSE.
No OAI global-to-local moment bound, harmonic orthogonality, or RH
exponent improvement is asserted. The analytic Fourier coefficient
and Mellin-phase derivations are spelled out in the adjacent note.

The completely reassembled Mobius source has zero weight at every
perfect-square Fourier jump n=m^2 for m>=2; this is already formally
proved in the ongoing PR #1048, so not duplicated here.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- A real physical square block containing both witness integers. -/
theorem oaiRootAlias_five_six_same_squareBlock :
    2 ^ 2 ≤ (5 : ℕ) ∧ 5 < 3 ^ 2 ∧
      2 ^ 2 ≤ (6 : ℕ) ∧ 6 < 3 ^ 2 := by
  norm_num

/-- Genuine Mobius signs, not randomized surrogate signs. -/
theorem oaiRootAlias_mobius_five : μ 5 = (-1 : ℤ) :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

/-- The two distinct prime factors of six yield the opposite sign. -/
theorem oaiRootAlias_mobius_six : μ 6 = (1 : ℤ) := by
  have hcop : Nat.Coprime 2 3 := by norm_num
  have hmult :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have h2 : μ 2 = (-1 : ℤ) :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h3 : μ 3 = (-1 : ℤ) :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [show (6 : ℕ) = 2 * 3 by norm_num, h2, h3] at hmult ⊢

/-- The two original integer Mobius coefficients cancel. -/
theorem oaiRootAlias_mobius_five_add_six :
    μ 5 + μ 6 = (0 : ℤ) := by
  rw [oaiRootAlias_mobius_five, oaiRootAlias_mobius_six]
  norm_num

/-- Every physical ROOT-index phase uses the same multiplier on
these two members of the [4,9) square block, so cancellation is exact. -/
theorem oaiRootAlias_twoSitePhysicalPhase_zero (z : ℂ) :
    ((μ 5 : ℤ) : ℂ) * z + ((μ 6 : ℤ) : ℂ) * z = 0 := by
  rw [oaiRootAlias_mobius_five, oaiRootAlias_mobius_six]
  push_cast
  ring

/-- A single SMOOTH root-phase harmonic sees different multipliers
at n=5 and n=6, so its source need not vanish. -/
def oaiRootAlias_twoSiteSmoothMode (z5 z6 : ℂ) : ℂ :=
  ((μ 5 : ℤ) : ℂ) * z5 + ((μ 6 : ℤ) : ℂ) * z6

theorem oaiRootAlias_twoSiteSmoothMode_eq
    (z5 z6 : ℂ) :
    oaiRootAlias_twoSiteSmoothMode z5 z6 = z6 - z5 := by
  unfold oaiRootAlias_twoSiteSmoothMode
  rw [oaiRootAlias_mobius_five, oaiRootAlias_mobius_six]
  push_cast
  ring

theorem oaiRootAlias_twoSiteSmoothMode_nonzero
    (z5 z6 : ℂ) (h : z5 ≠ z6) :
    oaiRootAlias_twoSiteSmoothMode z5 z6 ≠ 0 := by
  rw [oaiRootAlias_twoSiteSmoothMode_eq]
  exact sub_ne_zero.mpr h.symm

/-- A diagonal-only sum of harmonic energies cannot equal the
energy of the coherent sum for arbitrary source modes. -/
theorem oaiRootAlias_not_diagonal_orthogonality :
    ¬ (∀ a b : ℂ, ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  intro h
  have hbad := h (1 : ℂ) (-1)
  norm_num at hbad

/-- At least one signed cross term is NECESSARY, even for the
two-mode cancellation 1+(-1)=0, while both diagonal energies are 1. -/
theorem oaiRootAlias_twoMode_crossCancellation :
    ‖(1 : ℂ) + (-1)‖ ^ 2 = 0 ∧
      ‖(1 : ℂ)‖ ^ 2 + ‖(-1 : ℂ)‖ ^ 2 = 2 := by
  norm_num

#print axioms oaiRootAlias_five_six_same_squareBlock
#print axioms oaiRootAlias_mobius_five
#print axioms oaiRootAlias_mobius_six
#print axioms oaiRootAlias_mobius_five_add_six
#print axioms oaiRootAlias_twoSitePhysicalPhase_zero
#print axioms oaiRootAlias_twoSiteSmoothMode_eq
#print axioms oaiRootAlias_twoSiteSmoothMode_nonzero
#print axioms oaiRootAlias_not_diagonal_orthogonality
#print axioms oaiRootAlias_twoMode_crossCancellation

end RHLean.Analysis
