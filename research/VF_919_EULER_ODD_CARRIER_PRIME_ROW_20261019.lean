import RHLean.Analysis.DyadicTransportCanonicalForm
import «research.VF_919_EULER_FIXED_WHEEL_SIX_CHANNEL_20261019»

/-!
# Odd-carrier reduction and exact prime-row compensation

The original VF active historical sector-six incidence test uses odd squarefree
sites. This is sufficient for a global Mertens estimate: every even squarefree
site is twice an odd squarefree site with the opposite Möbius sign.

The repository already proves Möbius doubling and exact dyadic cofactor-prefix
compression; no artificial enlarged even-site incidence matrix is required.

Exact prime-row compensation:
  PP + AP + HP = -Q(Q+1)/2 - Q*S_odd.
No quantitative signed covariance estimate is assumed or proved here.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
attribute [local instance] Classical.propDecidable

/-- Odd Möbius summatory function with the actual canonical complex weights
and the inclusive physical endpoint X. -/
def vf919EulerOddMertens (X : ℕ) : ℂ :=
  ∑ n ∈ RHLean.Proof.oddCofactorPrefix X,
    RHLean.Proof.canonicalMoebiusWeight n

/-- Full Mertens is the odd prefix minus the half-scale odd prefix.
This reuses the repository's proved exact Möbius-doubling compression. -/
theorem vf919EulerMertens_eq_odd_sub_half (X : ℕ) :
    mertensSummatory X =
      vf919EulerOddMertens X - vf919EulerOddMertens (X / 2) := by
  rw [← RHLean.Proof.cofactorMobiusPrefixMass_eq_mertensSummatory X]
  unfold RHLean.Proof.cofactorMobiusPrefixMass vf919EulerOddMertens
  rw [RHLean.Proof.sum_Icc_eq_odd_add_even,
    RHLean.Proof.sum_evenCofactorPrefix_eq_neg_odd_half]
  ring

/-- The real-valued form of the exact odd-carrier reduction. -/
def vf919EulerOddRealMertens (X : ℕ) : ℝ :=
  (vf919EulerOddMertens X).re

theorem vf919EulerMertens_real_eq_odd_sub_half (X : ℕ) :
    (mertensSummatory X).re =
      vf919EulerOddRealMertens X - vf919EulerOddRealMertens (X / 2) := by
  have h := congrArg Complex.re (vf919EulerMertens_eq_odd_sub_half X)
  simpa [vf919EulerOddRealMertens] using! h

/-- Any true odd-prefix envelope transfers to full Mertens at two scales.
This is conditional on the explicit odd bound hOdd. -/
theorem vf919EulerMertens_norm_le_odd_budgets
    (X : ℕ) (B : ℕ → ℝ)
    (hOdd : ∀ Y : ℕ, ‖vf919EulerOddMertens Y‖ ≤ B Y) :
    ‖mertensSummatory X‖ ≤ B X + B (X / 2) := by
  rw [vf919EulerMertens_eq_odd_sub_half]
  exact (norm_sub_le _ _).trans (add_le_add (hOdd X) (hOdd (X / 2)))

/-! ## True odd-carrier square-shell source classes -/

def vf919EulerOddBlockS (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X,
    if Odd n then realMoebiusStep n else 0

def vf919EulerOddBlockA (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X,
    if Odd n then vf919EulerFixedSmoothWeight R n else 0

def vf919EulerOddBlockH (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X,
    if Odd n then vf919EulerFixedHighCompositeWeight R n else 0

def vf919EulerOddBlockQ (R X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) X,
    if Odd n then vf919EulerPrimeIndicator n else 0

/-- Every odd physical site is charged once by A, H, or -Q. -/
theorem vf919EulerOddBlock_source_partition (R X : ℕ) :
    vf919EulerOddBlockS R X =
      vf919EulerOddBlockA R X +
        vf919EulerOddBlockH R X - vf919EulerOddBlockQ R X := by
  unfold vf919EulerOddBlockS vf919EulerOddBlockA
    vf919EulerOddBlockH vf919EulerOddBlockQ
  calc
    (∑ n ∈ Finset.Ico (R ^ 2) X,
        if Odd n then realMoebiusStep n else 0) =
      ∑ n ∈ Finset.Ico (R ^ 2) X,
        ((if Odd n then vf919EulerFixedSmoothWeight R n else 0) +
          (if Odd n then vf919EulerFixedHighCompositeWeight R n else 0) -
          (if Odd n then vf919EulerPrimeIndicator n else 0)) := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases hn : Odd n
        · simp only [ite_eq_left hn]
          exact vf919EulerFixedWheel_site_partition R n
        · simp only [ite_eq_right hn]
          ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-! ## Exact algebraic payment for the prime-involving rows -/

/-- PP is Q choose 2; AP and HP are signed prime-composite products. -/
def vf919EulerPrimeRows (A H Q : ℝ) : ℝ :=
  (Q ^ 2 - Q) / 2 - A * Q - H * Q

/-- Keep PP, AP, and HP together before taking absolute values. -/
theorem vf919EulerPrimeRows_exact (A H Q : ℝ) :
    vf919EulerPrimeRows A H Q =
      -(Q * (Q + 1)) / 2 - Q * (A + H - Q) := by
  unfold vf919EulerPrimeRows
  ring

/-- The exact prime-row identity for the genuine masked odd shell. -/
theorem vf919EulerOddPrimeRows_exact (R X : ℕ) :
    vf919EulerPrimeRows
        (vf919EulerOddBlockA R X)
        (vf919EulerOddBlockH R X)
        (vf919EulerOddBlockQ R X) =
      -(vf919EulerOddBlockQ R X *
          (vf919EulerOddBlockQ R X + 1)) / 2 -
        vf919EulerOddBlockQ R X * vf919EulerOddBlockS R X := by
  rw [vf919EulerOddBlock_source_partition]
  exact vf919EulerPrimeRows_exact _ _ _

/-- The three remaining source rows AA, HH, AH. -/
def vf919EulerCompositeRows (A H KA KH : ℝ) : ℝ :=
  (A ^ 2 - KA) / 2 + (H ^ 2 - KH) / 2 + A * H

/-- Exact six-to-two row regrouping. It does not prove a smaller
magnitude for either of the two signed bills. -/
theorem vf919EulerSixCov_eq_composite_add_primeRows
    (A H Q KA KH : ℝ) :
    vf919EulerFixedSixCov A H Q KA KH =
      vf919EulerCompositeRows A H KA KH +
        vf919EulerPrimeRows A H Q := by
  unfold vf919EulerFixedSixCov vf919EulerCompositeRows
    vf919EulerPrimeRows
  ring

#print axioms vf919EulerMertens_eq_odd_sub_half
#print axioms vf919EulerMertens_real_eq_odd_sub_half
#print axioms vf919EulerMertens_norm_le_odd_budgets
#print axioms vf919EulerOddBlock_source_partition
#print axioms vf919EulerPrimeRows_exact
#print axioms vf919EulerOddPrimeRows_exact
#print axioms vf919EulerSixCov_eq_composite_add_primeRows

end RHLean.Analysis
