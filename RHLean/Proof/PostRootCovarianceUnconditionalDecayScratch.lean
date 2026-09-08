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

The first fact already improves the elementary quadratic constant by a full
factor of nine over the coarse squarefree-count estimate in the exponent
transfer file.  The second gives an unconditional *subquadratic* upper envelope
for the signed post-root remainder, with the full subexponential rate visible.
Neither statement is a fixed power saving, but both are genuine quantitative
improvements on the current carrier.
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

/-! ## The elementary gain hidden by the coarse squarefree sieve -/

/-- The odd dyadic annulus contains at most one quarter of the physical prefix.
The map `c ↦ c / 2` is injective on odd integers and sends the boundary into the
integer interval

`[(B+2)/4, (B-1)/2]`.

Counting that interval gives the sharp uniform upper bound `(B+3)/4`. -/
theorem card_dyadicCofactorBoundary_le_quarter (B : ℕ) :
    (dyadicCofactorBoundary B).card ≤ (B + 3) / 4 := by
  classical
  by_cases hB0 : B = 0
  · subst B
    norm_num [dyadicCofactorBoundary, oddCofactorPrefix]
  · have hmaps : ∀ c ∈ dyadicCofactorBoundary B,
        c / 2 ∈ Finset.Icc ((B + 2) / 4) ((B - 1) / 2) := by
      intro c hc
      rcases mem_dyadicCofactorBoundary.mp hc with
        ⟨_hc1, hcB, hcodd, hdouble⟩
      rcases hcodd with ⟨k, hk⟩
      have hcdiv : c / 2 = k := by omega
      rw [hcdiv]
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hinj : Set.InjOn (fun c : ℕ => c / 2)
        (dyadicCofactorBoundary B : Set ℕ) := by
      intro a ha b hb hab
      rcases mem_dyadicCofactorBoundary.mp (Finset.mem_coe.mp ha) with
        ⟨_ha1, _haB, haodd, _hadouble⟩
      rcases mem_dyadicCofactorBoundary.mp (Finset.mem_coe.mp hb) with
        ⟨_hb1, _hbB, hbodd, _hbdouble⟩
      rcases haodd with ⟨ka, hka⟩
      rcases hbodd with ⟨kb, hkb⟩
      have hada : a / 2 = ka := by omega
      have hbdb : b / 2 = kb := by omega
      rw [hada, hbdb] at hab
      omega
    have hcard :=
      Finset.card_le_card_of_injOn (fun c : ℕ => c / 2) hmaps hinj
    rw [Nat.card_Icc] at hcard
    omega

private theorem abs_realMoebiusStep_le_one_dyadic (n : ℕ) :
    |realMoebiusStep n| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h]

/-- The exact signed dyadic identity plus trivial pointwise Möbius support gives
an unconditional quarter-prefix bound.  Unlike the previous `3/4` bound, this
uses the sign flip from adjoining `2`, not only squarefree support. -/
theorem abs_realMertensLength_succ_le_dyadicQuarter (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (((B + 3) / 4 : ℕ) : ℝ) := by
  rw [realMertensLength_succ_eq_oddDyadicAnnulus]
  calc
    |∑ c ∈ dyadicCofactorBoundary B, realMoebiusStep c| ≤
        ∑ c ∈ dyadicCofactorBoundary B, |realMoebiusStep c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ dyadicCofactorBoundary B, (1 : ℝ) := by
      exact Finset.sum_le_sum fun c _hc => abs_realMoebiusStep_le_one_dyadic c
    _ = ((dyadicCofactorBoundary B).card : ℝ) := by simp
    _ ≤ (((B + 3) / 4 : ℕ) : ℝ) := by
      exact_mod_cast card_dyadicCofactorBoundary_le_quarter B

/-- Squaring the exact quarter-prefix estimate in the Bessel inequality gives

`E(W) <= (floor((W+3)/4))^2 / 2`.

Asymptotically this is `W^2 / 32`, improving the previous squarefree-sieve
coefficient `9/32` by a factor of nine before any analytic decay is used. -/
theorem postRootCovarianceRemainder_le_dyadicQuarterSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((((W + 3) / 4 : ℕ) : ℝ) ^ 2) / 2 := by
  have hM := abs_realMertensLength_succ_le_dyadicQuarter W
  have hsqMul := mul_self_le_mul_self (abs_nonneg _) hM
  have hsq :
      realMertensLength (W + 1) ^ 2 ≤
        (((W + 3) / 4 : ℕ) ^ 2 := by
    calc
      realMertensLength (W + 1) ^ 2 =
          |realMertensLength (W + 1)| ^ 2 := (sq_abs _).symm
      _ ≤ (((W + 3) / 4 : ℕ) : ℝ) ^ 2 := by
        simpa [pow_two] using hsqMul
  exact (postRootCovarianceRemainder_le_half_mertensSquare W).trans
    (div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2))

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
