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
  calc
    a * (∑ n ∈ S, x n) ^ 2 +
        (∑ n ∈ S, w n * x n) * (∑ n ∈ S, x n) =
      (∑ n ∈ S, ∑ m ∈ S, a * x n * x m) +
        (1 / 2 : ℝ) * (∑ n ∈ S, ∑ m ∈ S, w n * x n * x m) +
        (1 / 2 : ℝ) * (∑ n ∈ S, ∑ m ∈ S, w m * x n * x m) := by
          rw [hA, hWn, hWm]
          ring
    _ = ∑ n ∈ S, ∑ m ∈ S,
        (a + (w n + w m) / 2) * x n * x m := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n _hn
          apply Finset.sum_congr rfl
          intro m _hm
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
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [← Finset.sum_add_distrib]
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
  rw [show 2 * tau * (Real.log (n : ℝ) - Real.log (m : ℝ)) =
      2 * tau * Real.log (n : ℝ) - 2 * tau * Real.log (m : ℝ) by ring,
    Real.cos_sub]
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


/-! ## The exact finite complex derivative budget -/

/-- The real completed-zeta prefactor weight. This definition is a function,
not an analytic hypothesis; the finite arithmetic theorem below is algebraic
in its value and uses no properties of digamma. -/
noncomputable def α (s : ℂ) : ℝ :=
  (s⁻¹ + (s - 1)⁻¹ - ((Real.log Real.pi : ℝ) : ℂ) / 2 +
    Complex.digamma (s / 2) / 2).re

/-- Exact finite Möbius Dirichlet term, including the zero index. -/
noncomputable def finiteMobiusComplexTerm (n : ℕ) (s : ℂ) : ℂ :=
  (((μ n : ℤ) : ℂ)) / (n : ℂ) ^ s

/-- Original finite complex Möbius Dirichlet polynomial. -/
noncomputable def C_X (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (X + 1), finiteMobiusComplexTerm n s

/-- Original finite directional budget, with the ordinary complex derivative. -/
noncomputable def ℬ_X (X : ℕ) (s : ℂ) : ℝ :=
  α s * Complex.normSq (C_X X s) -
    ((deriv (C_X X) s) * star (C_X X s)).re

private theorem finiteMobiusComplexTerm_hasDerivAt
    (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z => finiteMobiusComplexTerm n z)
      (-((Real.log (n : ℝ) : ℂ) * finiteMobiusComplexTerm n s)) s := by
  by_cases hn : n = 0
  · subst n
    simp [finiteMobiusComplexTerm, hasDerivAt_const]
  · have h := LSeries.hasDerivAt_term
        (fun k : ℕ => (((μ k : ℤ) : ℂ))) n s
    simpa [finiteMobiusComplexTerm, LSeries.term_of_ne_zero hn,
      LSeries.logMul, Complex.natCast_log,
      mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h

/-- Differentiating the literal finite complex sum introduces no
convergence or continuation assumption. -/
theorem deriv_C_X (X : ℕ) (s : ℂ) :
    deriv (C_X X) s =
      -(∑ n ∈ Finset.range (X + 1),
          (Real.log (n : ℝ) : ℂ) * finiteMobiusComplexTerm n s) := by
  have h : HasDerivAt
      (fun z : ℂ => ∑ n ∈ Finset.range (X + 1),
        finiteMobiusComplexTerm n z)
      (∑ n ∈ Finset.range (X + 1),
        -((Real.log (n : ℝ) : ℂ) * finiteMobiusComplexTerm n s)) s :=
    HasDerivAt.fun_sum (fun n _ => finiteMobiusComplexTerm_hasDerivAt n s)
  change deriv (fun z : ℂ => ∑ n ∈ Finset.range (X + 1),
    finiteMobiusComplexTerm n z) s = _
  simpa only [Finset.sum_neg_distrib] using h.deriv

/-- Realification of the *complete* signed complex finite Gram. -/
private theorem finite_complex_directional_gram
    (S : Finset ℕ) (f : ℕ → ℂ) (w : ℕ → ℝ) (a : ℝ) :
    a * Complex.normSq (∑ n ∈ S, f n) +
      ((∑ n ∈ S, (w n : ℂ) * f n) *
        star (∑ n ∈ S, f n)).re =
      ∑ n ∈ S, ∑ m ∈ S,
        (a + (w n + w m) / 2) *
          (f n * star (f m)).re := by
  have h := finite_real_directional_gram S
    (fun n => (f n).re) (fun n => (f n).im) w a
  calc
    _ = a * ((∑ n ∈ S, (f n).re) ^ 2 +
              (∑ n ∈ S, (f n).im) ^ 2) +
        (∑ n ∈ S, w n * (f n).re) * (∑ n ∈ S, (f n).re) +
        (∑ n ∈ S, w n * (f n).im) * (∑ n ∈ S, (f n).im) := by
        simp only [Complex.star_def, Complex.normSq_apply, Complex.mul_re,
          Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.re_sum,
          Complex.im_sum, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, add_zero]
        ring
    _ = ∑ n ∈ S, ∑ m ∈ S,
        (a + (w n + w m) / 2) *
          ((f n).re * (f m).re + (f n).im * (f m).im) := h
    _ = _ := by
        apply Finset.sum_congr rfl
        intro n _hn
        apply Finset.sum_congr rfl
        intro m _hm
        simp only [Complex.star_def, Complex.mul_re,
          Complex.conj_re, Complex.conj_im]
        ring

/-- Complex powers at a positive integer carry precisely the real cosine
and negative sine log-frequency channels already used in the Perron kernel. -/
private theorem finiteMobiusComplexTerm_phase
    (n : ℕ) (sigma tau : ℝ) (hn : 0 < n) :
    finiteMobiusComplexTerm n ((sigma : ℂ) + 2 * tau * Complex.I) =
      (finiteMobiusCos sigma tau n : ℂ) -
        (finiteMobiusSin sigma tau n : ℂ) * Complex.I := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let L : ℝ := Real.log (n : ℝ)
  let theta : ℝ := 2 * tau * L
  have hlog : Complex.log (n : ℂ) = (L : ℂ) := by
    simp [L]
  have hreal : Real.exp (-sigma * L) = (n : ℝ) ^ (-sigma) := by
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  have hpow :
      (n : ℂ) ^ (-((sigma : ℂ) + 2 * tau * Complex.I)) =
        (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
          ((Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hnC,
      Complex.exp_eq_exp_re_mul_sin_add_cos]
    have hRe :
        (Complex.log (n : ℂ) *
          (-((sigma : ℂ) + 2 * tau * Complex.I))).re = -sigma * L := by
      rw [hlog]
      simp [Complex.mul_re, Complex.mul_im] <;> ring
    have hIm :
        (Complex.log (n : ℂ) *
          (-((sigma : ℂ) + 2 * tau * Complex.I))).im = -theta := by
      rw [hlog]
      simp [Complex.mul_re, Complex.mul_im, theta] <;> ring
    rw [hRe, hIm]
    rw [← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, hreal]
    push_cast only [Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  have hradial :
      finiteMobiusRadial sigma n =
        (((μ n : ℤ) : ℝ)) * ((n : ℝ) ^ (-sigma)) := by
    unfold finiteMobiusRadial
    rw [Real.rpow_sub hnR 1 sigma, Real.rpow_one,
      Real.rpow_neg hnR.le sigma]
    have hnR0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hpow0 : (n : ℝ) ^ sigma ≠ 0 := by positivity
    field_simp
  unfold finiteMobiusComplexTerm
  rw [div_eq_mul_inv, ← Complex.cpow_neg, hpow]
  simp only [finiteMobiusCos, finiteMobiusSin, hradial,
    Complex.ofReal_mul]
  dsimp [L, theta]
  ring

private theorem finiteMobiusComplexTerm_phase_pair
    {n m : ℕ} (s : ℂ) (tau : ℝ)
    (h : s = (s.re : ℂ) + 2 * tau * Complex.I)
    (hn : 0 < n) (hm : 0 < m) :
    (finiteMobiusComplexTerm n s *
      star (finiteMobiusComplexTerm m s)).re =
      (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) *
        ((n : ℝ) ^ (1 - s.re)) * ((m : ℝ) ^ (1 - s.re)) *
        K_τ n m tau := by
  have hnphase :
      finiteMobiusComplexTerm n s =
        (finiteMobiusCos s.re tau n : ℂ) -
          (finiteMobiusSin s.re tau n : ℂ) * Complex.I := by
    conv_lhs => rw [h]
    exact finiteMobiusComplexTerm_phase n s.re tau hn
  have hmphase :
      finiteMobiusComplexTerm m s =
        (finiteMobiusCos s.re tau m : ℂ) -
          (finiteMobiusSin s.re tau m : ℂ) * Complex.I := by
    conv_lhs => rw [h]
    exact finiteMobiusComplexTerm_phase m s.re tau hm
  calc
    _ = finiteMobiusCos s.re tau n * finiteMobiusCos s.re tau m +
        finiteMobiusSin s.re tau n * finiteMobiusSin s.re tau m := by
          rw [hnphase, hmphase]
          simp [Complex.mul_re, Complex.mul_im]
    _ = _ := finiteMobiusCos_sin_pair_eq_kernel s.re tau hn hm

/-- Equation (13): the exact complex derivative budget, including zero-index
handling and all physical off-diagonal Möbius correlations. -/
theorem finite_directional_budget_cosine
    (X : ℕ) (s : ℂ) (tau : ℝ)
    (h : s = (s.re : ℂ) + 2 * tau * Complex.I) :
    ℬ_X X s =
      ∑ n ∈ Finset.range (X + 1), ∑ m ∈ Finset.range (X + 1),
        (((μ n : ℤ) : ℝ) * ((μ m : ℤ) : ℝ)) *
          ((n : ℝ) ^ (1 - s.re)) * ((m : ℝ) ^ (1 - s.re)) *
          (α s + (Real.log (n : ℝ) + Real.log (m : ℝ)) / 2) *
          K_τ n m tau := by
  classical
  have hg := finite_complex_directional_gram
    (Finset.range (X + 1))
    (fun n => finiteMobiusComplexTerm n s)
    (fun n => Real.log (n : ℝ)) (α s)
  have hB :
      ℬ_X X s =
        ∑ n ∈ Finset.range (X + 1), ∑ m ∈ Finset.range (X + 1),
          (α s + (Real.log (n : ℝ) + Real.log (m : ℝ)) / 2) *
            (finiteMobiusComplexTerm n s *
              star (finiteMobiusComplexTerm m s)).re := by
    unfold ℬ_X
    rw [deriv_C_X X s]
    simpa only [C_X, neg_mul, Complex.neg_re, sub_neg_eq_add] using hg
  rw [hB]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hn : n = 0
  · subst n
    simp [finiteMobiusComplexTerm]
  by_cases hm : m = 0
  · subst m
    simp [finiteMobiusComplexTerm]
  have hp := finiteMobiusComplexTerm_phase_pair s tau h
    (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hm)
  rw [hp]
  ring

-- Certifies Eq. (13) of the directional-Gram arithmetic note.

#print axioms finite_directional_budget_cosine

end RHLean.Analysis
