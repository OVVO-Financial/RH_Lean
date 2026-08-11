from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNTError_abs_log_sq_le_affine_compensated' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-! ## Affine envelopes and the compensated squared recurrence -/

/-- An affine global envelope for the Chebyshev error.  The additive constant
is allowed to depend on the coefficient; this is exactly what is needed when
the cubic improvement is iterated and then read at infinity. -/
def nativePNTHasAffineEnvelope (alpha : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
    |nativePNTError N| ≤ alpha * (N : ℝ) + D

/-- The elementary Chebyshev bound supplies the starting affine coefficient
`6`. -/
theorem nativePNTHasAffineEnvelope_six :
    nativePNTHasAffineEnvelope 6 := by
  refine ⟨0, le_rfl, ?_⟩
  intro N
  have herr := nativePNTError_abs_le_const_mul N
  have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  have hC : Real.log 4 + 3 ≤ (6 : ℝ) := by
    norm_num at hlog4 ⊢
    linarith
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hC hN0
  simpa using herr.trans hmul

/-- An affine endpoint envelope automatically controls every reciprocal fibre
in the real `N/n` normalization used by the compensation identity. -/
theorem nativePNTAffineEnvelope_on_fiber
    (alpha D : ℝ) (halpha : 0 ≤ alpha)
    (henv : ∀ q : ℕ, |nativePNTError q| ≤ alpha * (q : ℝ) + D)
    (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    |nativePNTError (N / n)| ≤
      alpha * ((N : ℝ) / (n : ℝ)) + D := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hfloor : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    exact_mod_cast Nat.div_mul_le_self N n
  have hscale := mul_le_mul_of_nonneg_left hfloor halpha
  exact (henv (N / n)).trans (add_le_add_right hscale D)

/-- **Compensated squared Selberg recurrence.**  This is the quantitative
interface between an affine error envelope and the good-fibre packing.  The
leading reciprocal `Lambda_2` coefficient is exactly `1`; all lower-order
terms are displayed explicitly. -/
theorem nativePNTError_abs_log_sq_le_affine_compensated
    (N : ℕ) (hN : 3 ≤ N)
    (alpha beta D : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta ≤ alpha)
    (hD : 0 ≤ D)
    (henv : ∀ q : ℕ,
      |nativePNTError q| ≤ alpha * (q : ℝ) + D) :
    |nativePNTError N| * (Real.log N) ^ 2 ≤
      alpha * (N : ℝ) *
          ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
        (alpha - beta) * (N : ℝ) *
          nativeLambdaTwoGoodRecipMass N beta +
        D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) +
        3000 * (N : ℝ) * Real.log N := by
  have hall : ∀ n ∈ Finset.Icc 1 N,
      |nativePNTError (N / n)| ≤
        alpha * ((N : ℝ) / (n : ℝ)) + D := by
    intro n hn
    exact nativePNTAffineEnvelope_on_fiber alpha D halpha henv N n hn
  have hsq := nativePNTError_abs_log_sq_le_lambdaTwo N hN
  have hcomp := nativeLambdaTwoErrorMass_compensation
    N alpha beta D halpha hbeta hba hD hall
  have hrec := nativeLambdaTwoRecipMass_upper N hN
  have hrho := nativeLambdaTwoSummatory_upper_all N
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hrecMul :
      alpha * (N : ℝ) * nativeLambdaTwoRecipMass N ≤
        alpha * (N : ℝ) *
          ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) := by
    exact mul_le_mul_of_nonneg_left hrec (mul_nonneg halpha hN0)
  have hrhoMul :
      D * nativeLambdaTwoSummatory N ≤
        D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) :=
    mul_le_mul_of_nonneg_left hrho hD
  have hmass :
      nativeLambdaTwoErrorMass N ≤
        alpha * (N : ℝ) *
            ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta +
          D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) := by
    exact hcomp.trans
      (add_le_add
        (sub_le_sub_right hrecMul
          ((alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta))
        hrhoMul)
  calc
    |nativePNTError N| * (Real.log N) ^ 2 ≤
        nativeLambdaTwoErrorMass N +
          3000 * (N : ℝ) * Real.log N := hsq
    _ ≤
        (alpha * (N : ℝ) *
            ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta +
          D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600)) +
          3000 * (N : ℝ) * Real.log N :=
      add_le_add_right hmass _
    _ = _ := by ring
'''
s = s.replace(marker, block + marker)
p.write_text(s)
