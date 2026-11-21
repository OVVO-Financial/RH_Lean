import Mathlib
import RHLean.Analysis.NativePNTErrorMass
import RHLean.Analysis.NativePNTSignedSecondSelberg

/-!
# Exact Type-II census of Alpoge's native K2(2p) child-error channel

The source-specific family with physical carriers 2*p gives
  S_R = sum_p 2 log(2) log(p) E(floor((R^2-1)/(2*p))).

Here we prove a complete finite Fubini identity:
  sum_p w_p E(t_p)
    = sum_(1<=n<=N) (Lambda(n)-1) sum_(p:n<=t_p) w_p,
provided t_p<=N. Thus the child family is one positive-weight
arithmetic census of the SAME prime population, not independent signs.

The physical condition n<=t_p is exactly 2*p*n<=R^2-1 for p>0.
These facts locate the actual signed interaction that a Type II or
automorphic/geometry estimate must improve.

There is NO bound on the complete original signed complement here,
no statistical independence hypothesis and no RH theorem.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators
namespace RHLean.Analysis

/-- Exact signed prime/composite census tested by arbitrary reciprocal
quotients t_p. Its weight is a FINITE, source-defined arithmetic object. -/
def alpogeBilinearChildCensus
    (P : Finset ℕ) (t : ℕ → ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, if n ≤ t p then w p else 0

/-- Full finite Fubini of weighted Chebyshev errors. All Lambda values,
including higher prime powers, are retained and centered against 1.
No cancellation is imposed; the identity holds for ANY finite family. -/
theorem alpogeWeightedError_eq_lambdaCenteredBilinear
    (N : ℕ) (P : Finset ℕ) (t : ℕ → ℕ) (w : ℕ → ℝ)
    (ht : ∀ p ∈ P, t p ≤ N) :
    (∑ p ∈ P, w p * nativePNTError (t p)) =
      ∑ n ∈ Finset.Icc 1 N,
        (Λ n - 1) * alpogeBilinearChildCensus P t w n := by
  classical
  have hinner (p : ℕ) (hp : p ∈ P) :
      nativePNTError (t p) =
        ∑ n ∈ Finset.Icc 1 N,
          if n ≤ t p then (Λ n - 1) else 0 := by
    have hcard :
        (∑ n ∈ Finset.Icc 1 (t p), (1 : ℝ)) = (t p : ℝ) := by
      simp
    have hfilter :
        (Finset.Icc 1 N).filter (fun n => n ≤ t p) =
          Finset.Icc 1 (t p) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    unfold nativePNTError nativePsi
    calc
      (∑ n ∈ Finset.Icc 1 (t p), Λ n) - (t p : ℝ) =
          ∑ n ∈ Finset.Icc 1 (t p), (Λ n - 1) := by
            rw [← hcard, Finset.sum_sub_distrib]
      _ = ∑ n ∈ Finset.Icc 1 N,
            if n ≤ t p then (Λ n - 1) else 0 := by
            rw [← hfilter, Finset.sum_filter]
  calc
    (∑ p ∈ P, w p * nativePNTError (t p)) =
        ∑ p ∈ P,
          ∑ n ∈ Finset.Icc 1 N,
            if n ≤ t p then w p * (Λ n - 1) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hinner p hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      split_ifs <;> ring
    _ = ∑ n ∈ Finset.Icc 1 N,
          ∑ p ∈ P,
            if n ≤ t p then w p * (Λ n - 1) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 N,
        (Λ n - 1) * alpogeBilinearChildCensus P t w n := by
      apply Finset.sum_congr rfl
      intro n _hn
      unfold alpogeBilinearChildCensus
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      split_ifs <;> ring

/-- True physical reciprocal quotient of the selected 2*p K2 term. -/
def alpogeBilinearChild (R p : ℕ) : ℕ :=
  (R ^ 2 - 1) / (2 * p)

/-- Exactly the coefficient inherited from K2(2p), p an odd prime. -/
def alpogeBilinearWeight (p : ℕ) : ℝ :=
  2 * Real.log (2 : ℝ) * Real.log (p : ℝ)

/-- One physical selected signed second-Selberg error slice. -/
def alpogeBilinearSelectedSource (R : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P,
    alpogeBilinearWeight p * nativePNTError (alpogeBilinearChild R p)

/-- A genuinely arithmetic incidence weight: positive log-prime
contributions from every physical integer pair 2*p*n<=R^2-1. -/
def alpogeBilinearPrimeIncidence
    (R : ℕ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ P,
    if 2 * p * n ≤ R ^ 2 - 1 then alpogeBilinearWeight p else 0

/-- For any strictly positive prime owner p, the ordinary floor test
is EXACTLY the unrounded physical pair inequality. -/
theorem alpogeBilinearFloor_iff_carrier
    (R p n : ℕ) (hp : 0 < p) :
    n ≤ alpogeBilinearChild R p ↔ 2 * p * n ≤ R ^ 2 - 1 := by
  unfold alpogeBilinearChild
  have hden : 0 < 2 * p := by omega
  rw [Nat.le_div_iff_mul_le hden]
  simp only [Nat.mul_comm]

/-- Exact source-specific source/Fubini translation, with NO dropped
prime power, no expectation and no square-root cancellation assumption. -/
theorem alpogeBilinearSelectedSource_eq_primeCensus
    (R : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    alpogeBilinearSelectedSource R P =
      ∑ n ∈ Finset.Icc 1 (R ^ 2 - 1),
        (Λ n - 1) * alpogeBilinearPrimeIncidence R P n := by
  have ht : ∀ p ∈ P, alpogeBilinearChild R p ≤ R ^ 2 - 1 := by
    intro p _hp
    exact Nat.div_le_self _ _
  have h := alpogeWeightedError_eq_lambdaCenteredBilinear
    (R ^ 2 - 1) P (alpogeBilinearChild R) alpogeBilinearWeight ht
  unfold alpogeBilinearSelectedSource at *
  rw [h]
  apply Finset.sum_congr rfl
  intro n _hn
  congr 1
  unfold alpogeBilinearPrimeIncidence alpogeBilinearChildCensus
  apply Finset.sum_congr rfl
  intro p hp
  rw [alpogeBilinearFloor_iff_carrier R p n (hP p hp)]

/-- Purely algebraic coherence counterexample: distinct labels do not
supply square-root cancellation. A constant-sign vector has square
of total response equal to m times its diagonal energy, m=|P|.
This is a test of what can be inferred from injectivity ALONE, not a
claim about the true arithmetic E(t_p). -/
theorem alpogeCoherentUnitFamily_exact
    (P : Finset ℕ) :
    (∑ _p ∈ P, (1 : ℝ)) ^ 2 =
      (P.card : ℝ) * (∑ _p ∈ P, ((1 : ℝ) ^ 2)) := by
  simp
  ring

end RHLean.Analysis
