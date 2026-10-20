import «research.VF_919_SEVEN_EIGHTHS_DYADIC_SHELL_COVARIANCE_20261019»

/-!
# Exact arbitrary-integer endpoint transfer for dyadic square-shell Mertens

For K = floor(sqrt X), the already-defined shell prefix
realMertensLength (K^2) equals M(K^2-1) whenever X>=1.
The remainder M(X)-M(K^2-1) consists of at most 2K+1 physical sites.

This is unconditional and uses the repository's own bounded-increment
Mertens theorem; no conjectured covariance, PNT, complex detector, or
prime-density assumption is used.

A dyadic 5/2 shell-energy estimate is still required separately to
bound the completed-square prefix uniformly.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Exactly the missing last partial shell, from the completed square
prefix immediately preceding K^2 through an arbitrary endpoint X. -/
theorem vf919LastIncompleteSquareShell_norm_le_width (X : ℕ) :
    ‖mertensSummatory X -
        mertensSummatory ((Nat.sqrt X) ^ 2 - 1)‖ ≤
      (((2 * Nat.sqrt X + 1 : ℕ) : ℝ)) := by
  let K := Nat.sqrt X
  have hlow : K ^ 2 ≤ X := by
    simpa only [K] using Nat.sqrt_le' X
  have htop : X < (K + 1) ^ 2 := by
    simpa only [K] using Nat.lt_succ_sqrt' X
  have hle : K ^ 2 - 1 ≤ X :=
    (Nat.sub_le _ _).trans hlow
  have hlen : X - (K ^ 2 - 1) ≤ 2 * K + 1 := by
    have hexpand : (K + 1) ^ 2 = K ^ 2 + 2 * K + 1 := by ring
    omega
  calc
    ‖mertensSummatory X - mertensSummatory (K ^ 2 - 1)‖ ≤
      ((X - (K ^ 2 - 1) : ℕ) : ℝ) :=
        norm_mertensSummatory_sub_le (K ^ 2 - 1) X hle
    _ ≤ ((2 * K + 1 : ℕ) : ℝ) := by exact_mod_cast hlen

/-- The complex completed-square Mertens prefix is exactly the
existing real shell-prefix representation; the natural subtraction
is justified by K>=1 (rather than silently wrapping Nat subtraction). -/
theorem vf919SquarePrefix_realComplex_exact (K : ℕ) (hK : 1 ≤ K) :
    ((realMertensLength (K ^ 2) : ℝ) : ℂ) =
      mertensSummatory (K ^ 2 - 1) := by
  have hpow : 1 ≤ K ^ 2 := by nlinarith
  have hsub : (K ^ 2 - 1) + 1 = K ^ 2 :=
    Nat.sub_add_cancel hpow
  have hcast :=
    realMertensLength_cast_eq_mertensSummatory (K ^ 2 - 1)
  rw [hsub] at hcast
  exact hcast

/-- For X>=1 the full exact endpoint wrapper takes the native dyadic
square-prefix sum plus at most 2K+1 arbitrary-interval error sites.
No distributional estimate on the partial shell is needed. -/
theorem vf919MertensNorm_le_squarePrefix_add_lastShell
    (X : ℕ) (hX : 1 ≤ X) :
    ‖mertensSummatory X‖ ≤
      ‖realMertensLength ((Nat.sqrt X) ^ 2)‖ +
        (((2 * Nat.sqrt X + 1 : ℕ) : ℝ)) := by
  let K := Nat.sqrt X
  have htop : X < (K + 1) ^ 2 := by
    simpa only [K] using Nat.lt_succ_sqrt' X
  have hK : 1 ≤ K := by
    by_contra hh
    have hz : K = 0 := by omega
    rw [hz] at htop
    norm_num at htop
    omega
  have hcast := vf919SquarePrefix_realComplex_exact K hK
  have hres := vf919LastIncompleteSquareShell_norm_le_width X
  calc
    ‖mertensSummatory X‖ =
      ‖(mertensSummatory X - mertensSummatory (K ^ 2 - 1)) +
        mertensSummatory (K ^ 2 - 1)‖ := by rw [sub_add_cancel]
    _ ≤ ‖mertensSummatory X - mertensSummatory (K ^ 2 - 1)‖ +
          ‖mertensSummatory (K ^ 2 - 1)‖ := norm_add_le _ _
    _ ≤ ((2 * K + 1 : ℕ) : ℝ) +
          ‖mertensSummatory (K ^ 2 - 1)‖ := by
      exact add_le_add hres le_rfl
    _ = ‖realMertensLength (K ^ 2)‖ +
          ((2 * K + 1 : ℕ) : ℝ) := by
      rw [← hcast, Complex.norm_real]
      ring

#print axioms vf919LastIncompleteSquareShell_norm_le_width
#print axioms vf919SquarePrefix_realComplex_exact
#print axioms vf919MertensNorm_le_squarePrefix_add_lastShell

end RHLean.Analysis
