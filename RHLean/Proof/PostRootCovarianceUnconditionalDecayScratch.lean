import RHLean.Proof.PostRootCovarianceGlobalExponentTransfer
import RHLean.Analysis.DyadicTransportCanonicalForm
import RHLean.Analysis.StrongMertensLogNineBalance

/-!
# Unconditional decay pulled back onto the post-root remainder carrier

The fixed-power equivalence in `PostRootCovarianceGlobalExponentTransfer` does
not exhaust the unconditional information already proved elsewhere in the
repository.  Two exact facts survive transport back to the current carrier:

* adjoining `2` cancels the lower odd prefix exactly, so every physical Mertens
  value is an odd dyadic-annulus sum;
* the repository already proves the unconditional strong Mertens estimate
  `M(N) = O(N * exp(-c (log N)^(1/10)))`.

The Bessel inequality therefore gives an unconditional *subquadratic* upper
envelope for the signed post-root remainder, with the full subexponential rate
visible.  This is not a fixed power saving, but it is strictly stronger than
any constant improvement of the quadratic bound.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The real prefix used by the covariance tower is exactly the native real
Mertens summatory function at the preceding endpoint. -/
theorem realMertensLength_succ_eq_nativeMertensSummatory (N : ℕ) :
    realMertensLength (N + 1) = nativeMertensSummatory N := by
  unfold realMertensLength nativeMertensSummatory
  have hset :
      Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp
    omega
  rw [hset]
  simp [realMoebiusStep]

/-- **Adjoining two cancels the lower odd prefix.**  In the real covariance
coordinate, the whole Mertens prefix is exactly the odd dyadic annulus
`B/2 < c <= B`. -/
theorem realMertensLength_succ_eq_oddDyadicAnnulus (B : ℕ) :
    realMertensLength (B + 1) =
      ∑ c ∈ dyadicCofactorBoundary B, realMoebiusStep c := by
  have h := mertensSummatory_eq_dyadicCofactorBoundaryMass B
  have hre := congrArg Complex.re h
  simpa [RHLean.Analysis.mertensSummatory, dyadicCofactorBoundaryMass,
    canonicalMoebiusWeight, realMertensLength, realMoebiusStep] using hre

/-- **Unconditional subquadratic remainder envelope.**  The repository's
finished strong Mertens theorem transfers through the Bessel inequality with
its full rate: for fixed positive `c`,

`E(W) <= 1/2 * (C W exp(-c (log W)^(1/10)))^2`.

Thus the current carrier has unconditional decay beyond every fixed quadratic
constant, even though this does not yet constitute a fixed power saving. -/
theorem postRootCovarianceRemainder_le_strongMertensSubexp :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ W : ℕ, 3 ≤ W →
        postRootCovarianceRemainder W ≤
          (C * (W : ℝ) *
            Real.exp (-c * (Real.log (W : ℝ)) ^ ((1 : ℝ) / 10))) ^ 2 / 2 := by
  rcases strongNativeMertensSubexp with ⟨c, C, hc, hC, hM⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro W hW
  let R : ℝ :=
    C * (W : ℝ) *
      Real.exp (-c * (Real.log (W : ℝ)) ^ ((1 : ℝ) / 10))
  have hbound : |nativeMertensSummatory W| ≤ R := by
    simpa [R] using hM W hW
  have hnn : 0 ≤ |nativeMertensSummatory W| := abs_nonneg _
  have hsqMul := mul_self_le_mul_self hnn hbound
  have hsq : nativeMertensSummatory W ^ 2 ≤ R ^ 2 := by
    calc
      nativeMertensSummatory W ^ 2 = |nativeMertensSummatory W| ^ 2 :=
        (sq_abs _).symm
      _ ≤ R ^ 2 := by
        simpa [pow_two] using hsqMul
  have hhalf := postRootCovarianceRemainder_le_half_mertensSquare W
  rw [realMertensLength_succ_eq_nativeMertensSummatory W] at hhalf
  have hfinal := hhalf.trans
    (div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2))
  simpa [R] using hfinal

end RHLean.Proof
