import Mathlib
import «research.STABLE_FAR_PERRON_REAL_GRAM_COSINE»

/-!
# Finite derivative-weighted real Gram and cosine bridge

All statements here are finite algebraic identities.  No analytic
continuation, zero-freeness, or asymptotic estimate is used.

The existing returned-fibre Perron kernel is used without discarding its
off-diagonal, logarithmic-phase correlations.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- The cosine kernel already certified by the returned-fibre Perron module.
The natural zero index is harmless because its Möbius coefficient is zero. -/
def K_τ (n m : ℕ) (tau : ℝ) : ℝ :=
  RHLean.Proof.stableFarCriticalQ2RealGramKernel tau n m

theorem K_τ_eq_log_cosine (n m : ℕ) (tau : ℝ)
    (hn : 0 < n) (hm : 0 < m) :
    K_τ n m tau =
      ((1 / (n : ℝ)) * (1 / (m : ℝ))) *
        Real.cos (2 * tau *
          (Real.log (n : ℝ) - Real.log (m : ℝ))) := by
  unfold K_τ
  rw [RHLean.Proof.stableFarCriticalQ2RealGramKernel_eq_logCosine tau hn hm]
  rw [show 2 * tau * (Real.log (m : ℝ) - Real.log (n : ℝ)) =
      -(2 * tau * (Real.log (n : ℝ) - Real.log (m : ℝ))) by ring,
    Real.cos_neg]

/-- A finite symmetric logarithmic weight can be redistributed equally
between its two original source indices. -/
theorem finite_symmetrized_weighted_product
    (S : Finset ℕ) (x w : ℕ → ℝ) (a : ℝ) :
    a * (∑ n ∈ S, x n) ^ 2 +
      (∑ n ∈ S, w n * x n) * (∑ n ∈ S, x n) =
      ∑ n ∈ S, ∑ m ∈ S,
        (a + (w n + w m) / 2) * x n * x m := by
  classical
  have hA :
      (∑ n ∈ S, ∑ m ∈ S, a * x n * x m) =
        a * (∑ n ∈ S, x n) ^ 2 := by
    calc
      _ = (∑ n ∈ S, a * x n) * (∑ m ∈ S, x m) := by
        rw [Finset.sum_mul_sum]
      _ = a * (∑ n ∈ S, x n) ^ 2 := by
        rw [← Finset.mul_sum]
        ring
  have hWn :
      (∑ n ∈ S, ∑ m ∈ S, w n * x n * x m) =
        (∑ n ∈ S, w n * x n) * (∑ m ∈ S, x m) := by
    rw [Finset.sum_mul_sum]
  have hWm :
      (∑ n ∈ S, ∑ m ∈ S, w m * x n * x m) =
        (∑ n ∈ S, w n * x n) * (∑ m ∈ S, x m) := by
    calc
      _ = (∑ n ∈ S, x n) * (∑ m ∈ S, w m * x m) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        apply Finset.sum_congr rfl
        intro m _hm
        ring
      _ = (∑ n ∈ S, w n * x n) * (∑ m ∈ S, x m) := by ring
  have hsplit :
      (∑ n ∈ S, ∑ m ∈ S,
        (a + (w n + w m) / 2) * x n * x m) =
      (∑ n ∈ S, ∑ m ∈ S, a * x n * x m) +
        (1 / 2 : ℝ) * (∑ n ∈ S, ∑ m ∈ S, w n * x n * x m) +
        (1 / 2 : ℝ) * (∑ n ∈ S, ∑ m ∈ S, w m * x n * x m) := by
    calc
      _ = ∑ n ∈ S, ∑ m ∈ S,
            (a * x n * x m) +
            (1 / 2 : ℝ) * (w n * x n * x m) +
            (1 / 2 : ℝ) * (w m * x n * x m) := by
        apply Finset.sum_congr rfl
        intro n _hn
        apply Finset.sum_congr rfl
        intro m _hm
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  rw [hsplit, hA, hWn, hWm]
  ring

/-- The complete two-channel real Gram retains both coordinate energies
and every cross term before any sign estimate. -/
theorem finite_real_directional_gram
    (S : Finset ℕ) (x y w : ℕ → ℝ) (a : ℝ) :
    a * ((∑ n ∈ S, x n) ^ 2 + (∑ n ∈ S, y n) ^ 2) +
      (∑ n ∈ S, w n * x n) * (∑ n ∈ S, x n) +
      (∑ n ∈ S, w n * y n) * (∑ n ∈ S, y n) =
      ∑ n ∈ S, ∑ m ∈ S,
        (a + (w n + w m) / 2) *
          (x n * x m + y n * y m) := by
  classical
  have hx := finite_symmetrized_weighted_product S x w a
  have hy := finite_symmetrized_weighted_product S y w a
  calc
    _ = (a * (∑ n ∈ S, x n) ^ 2 +
           (∑ n ∈ S, w n * x n) * (∑ n ∈ S, x n)) +
        (a * (∑ n ∈ S, y n) ^ 2 +
           (∑ n ∈ S, w n * y n) * (∑ n ∈ S, y n)) := by ring
    _ = (∑ n ∈ S, ∑ m ∈ S,
            (a + (w n + w m) / 2) * x n * x m) +
        (∑ n ∈ S, ∑ m ∈ S,
            (a + (w n + w m) / 2) * y n * y m) := by
      rw [hx, hy]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro m _hm
      ring

/-- Radial coefficient of the actual squarefree Möbius population.
The form n^(1-sigma)/n is chosen to expose the existing Perron kernel. -/
def finiteMobiusRadial (sigma : ℝ) (n : ℕ) : ℝ :=
  ((μ n : ℤ) : ℝ) * ((n : ℝ) ^ (1 - sigma)) / (n : ℝ)

def finiteMobiusCos (sigma tau : ℝ) (n : ℕ) : ℝ :=
  finiteMobiusRadial sigma n *
    Real.cos (2 * tau * Real.log (n : ℝ))

def finiteMobiusSin (sigma tau : ℝ) (n : ℕ) : ℝ :=
  finiteMobiusRadial sigma n *
    Real.sin (2 * tau * Real.log (n : ℝ))

/-- The Perron cosine kernel equals the full real dot product of the
actual finite Möbius log-phase contributions. -/
theorem finiteMobiusCos_sin_pair_eq_kernel
    (sigma tau : ℝ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    finiteMobiusCos sigma tau n * finiteMobiusCos sigma tau m +
      finiteMobiusSin sigma tau n * finiteMobiusSin sigma tau m =
      (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) *
        ((n : ℝ) ^ (1 - sigma)) * ((m : ℝ) ^ (1 - sigma)) *
        K_τ n m tau := by
  rw [K_τ_eq_log_cosine n m tau hn hm]
  unfold finiteMobiusCos finiteMobiusSin finiteMobiusRadial
  rw [Real.cos_sub]
  ring

/-- Equation (13): exact realified finite-source cosine expansion, with
the radial/log-derivative budget represented by its two real components.
Identification with the analytic derivative of C_X is a separate lemma. -/
theorem finite_directional_budget_cosine_realified
    (X : ℕ) (sigma tau a : ℝ) :
    a * ((∑ n ∈ Finset.Icc 1 X, finiteMobiusCos sigma tau n) ^ 2 +
         (∑ n ∈ Finset.Icc 1 X, finiteMobiusSin sigma tau n) ^ 2) +
      (∑ n ∈ Finset.Icc 1 X,
        Real.log (n : ℝ) * finiteMobiusCos sigma tau n) *
        (∑ n ∈ Finset.Icc 1 X, finiteMobiusCos sigma tau n) +
      (∑ n ∈ Finset.Icc 1 X,
        Real.log (n : ℝ) * finiteMobiusSin sigma tau n) *
        (∑ n ∈ Finset.Icc 1 X, finiteMobiusSin sigma tau n) =
      ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
        (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) *
          ((n : ℝ) ^ (1 - sigma)) * ((m : ℝ) ^ (1 - sigma)) *
          (a + (Real.log (n : ℝ) + Real.log (m : ℝ)) / 2) *
          K_τ n m tau := by
  classical
  rw [finite_real_directional_gram
    (Finset.Icc 1 X) (finiteMobiusCos sigma tau)
    (finiteMobiusSin sigma tau)
    (fun n => Real.log (n : ℝ)) a]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hnpos : 0 < n := by
    have h := (Finset.mem_Icc.mp hn).1
    omega
  have hmpos : 0 < m := by
    have h := (Finset.mem_Icc.mp hm).1
    omega
  rw [finiteMobiusCos_sin_pair_eq_kernel sigma tau hnpos hmpos]
  ring

-- Certifies the fully real finite-source phase/covariance core of Eq. (13).
-- No positive-semidefiniteness or RH sign claim is made.

end RHLean.Analysis
