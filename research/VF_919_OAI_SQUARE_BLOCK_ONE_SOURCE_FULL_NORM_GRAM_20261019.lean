import «research.VF_919_OAI_SQUARE_BLOCK_EXCLUDED_NORM_BOUNDARIES_20261019»

/-!
# One principal Hecke norm coefficient, one ACTUAL square-shell weight

The whole original square block is reassembled as a SINGLE norm sum
  S_R = sum_{m <= (R+1)^2-1} a_F^(6)(m) *
    (Q36(floor(((R+1)^2-1)/m)) - Q36(floor((R^2-1)/m))).

The lower weight vanishes AUTOMATICALLY for m>R^2-1, since Q36(0)=0.
There is no fictitious norm cut-off, no missing endpoint and no
high/low upper/lower energy separation before the signed cross term.

The complete original Green-Kubo energy is the FULL double norm
coefficient Gram, including all cross-m and same-m phases. It can
subsequently be lifted to actual Hecke ideals only by proving the
norm-fiber ideal-Mobius identification and matching the original OAI
cubic theta/Poisson physical source, not by attaching random phases.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Periodic excluded-character floor weight vanishes at quotient zero. -/
theorem vf919OAISharpQuotient36_zero :
    vf919SharpQuotientKernel36 0 = 0 := by
  simp [vf919SharpQuotientKernel36, vf919IntegerCharacterPrefix]

/-- This is the ACTUAL sharp square interval's norm-fiber weight, not
    two independently bounded prefix coefficients. -/
def vf919OAIExactSquareNormWeight (R m : ℕ) : ℂ :=
  (vf919SharpQuotientKernel36 (vf919OAIhighSquareEndpoint R / m) : ℂ) -
    (vf919SharpQuotientKernel36 (vf919OAIlowSquareEndpoint R / m) : ℂ)

/-- The complete principal Hecke norm contribution at each m, including
    the restored 1,3,4,12 Euler factors and split-prime multiplicity. -/
def vf919OAIExactSquareNormTerm (R m : ℕ) : ℂ :=
  vf919ExcludedNormCoefficients m * vf919OAIExactSquareNormWeight R m

/-- A SINGLE weighted Hecke norm sum, equal to the original square block. -/
def vf919OAIExactSquareNormSource (R : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
    vf919OAIExactSquareNormTerm R m

/-- No spurious low-cutoff contribution for a norm m beyond R^2-1. -/
theorem vf919OAI_exact_lowerNormWeight_zero
    (R m : ℕ) (h : vf919OAIlowSquareEndpoint R < m) :
    vf919SharpQuotientKernel36 (vf919OAIlowSquareEndpoint R / m) = 0 := by
  rw [Nat.div_eq_of_lt h, vf919OAISharpQuotient36_zero]

/-- Source-faithful Fubini: combine two complete square endpoints into
    ONE coefficient per original norm m. All low/upper cross-terms remain
    available BEFORE squaring. -/
theorem vf919OAIExactSquareNormSource_eq_originalSquareShell
    (R : ℕ) (hR : 4 ≤ R) :
    vf919OAIExactSquareNormSource R = (vf919SquareShellSum R : ℂ) := by
  have hle :
      vf919OAIlowSquareEndpoint R ≤ vf919OAIhighSquareEndpoint R := by
    unfold vf919OAIlowSquareEndpoint vf919OAIhighSquareEndpoint
    nlinarith
  have hsubset :
      Finset.Icc 1 (vf919OAIlowSquareEndpoint R) ⊆
        Finset.Icc 1 (vf919OAIhighSquareEndpoint R) := by
    intro m hm
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hle⟩
  have hpad :
      (∑ m ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
        vf919ExcludedNormCoefficients m *
          (vf919SharpQuotientKernel36
            (vf919OAIlowSquareEndpoint R / m) : ℂ)) =
      (∑ m ∈ Finset.Icc 1 (vf919OAIlowSquareEndpoint R),
        vf919ExcludedNormCoefficients m *
          (vf919SharpQuotientKernel36
            (vf919OAIlowSquareEndpoint R / m) : ℂ)) := by
    symm
    apply Finset.sum_subset hsubset
    intro m hm hi
    have hbound : vf919OAIlowSquareEndpoint R < m := by
      have hlo : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      by_contra hh
      apply hi
      exact Finset.mem_Icc.mpr ⟨hlo, Nat.le_of_not_gt hh⟩
    rw [vf919OAI_exact_lowerNormWeight_zero R m hbound]
    simp
  calc
    vf919OAIExactSquareNormSource R =
        vf919OAIExcludedNormSharpPrefix (vf919OAIhighSquareEndpoint R) -
          ∑ m ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
            vf919ExcludedNormCoefficients m *
              (vf919SharpQuotientKernel36
                (vf919OAIlowSquareEndpoint R / m) : ℂ) := by
      unfold vf919OAIExactSquareNormSource vf919OAIExactSquareNormTerm
        vf919OAIExactSquareNormWeight vf919OAIExcludedNormSharpPrefix
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    _ = vf919OAIExcludedNormSharpPrefix (vf919OAIhighSquareEndpoint R) -
          vf919OAIExcludedNormSharpPrefix (vf919OAIlowSquareEndpoint R) := by
      rw [hpad]
      rfl
    _ = (vf919SquareShellSum R : ℂ) :=
      (vf919SquareShellSum_eq_OAI_excludedNorm_high_sub_low R hR).symm

/-- The ORIGINAL signed block covariance (not merely the lower bound)
    is the complete double Hecke norm moment at its genuine sharp
    interval weights; no ideal row or cross-m pair has been discarded. -/
def vf919OAIExactSquareNormFullGram (R : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
    ∑ n ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
      vf919OAIExactSquareNormTerm R m *
        vf919OAIExactSquareNormTerm R n

theorem vf919OAIExactSquareNormFullGram_eq_source_sq (R : ℕ) :
    vf919OAIExactSquareNormFullGram R =
      (vf919OAIExactSquareNormSource R) ^ 2 := by
  unfold vf919OAIExactSquareNormFullGram
  calc
    (∑ m ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
      ∑ n ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
        vf919OAIExactSquareNormTerm R m *
          vf919OAIExactSquareNormTerm R n) =
      ∑ m ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
        vf919OAIExactSquareNormTerm R m *
          (∑ n ∈ Finset.Icc 1 (vf919OAIhighSquareEndpoint R),
            vf919OAIExactSquareNormTerm R n) := by
              apply Finset.sum_congr rfl
              intro m _hm
              rw [Finset.mul_sum]
    _ = (vf919OAIExactSquareNormSource R) ^ 2 := by
      rw [← Finset.sum_mul]
      simp [vf919OAIExactSquareNormSource, pow_two]

/-- SAME original square-block covariance + squarefree diagonal, but
    entirely as a full complex Hecke norm-gram BEFORE any absolute value.
    The original signed four-index pair and the exact 36-periodic norm
    representation are now one single theorem. -/
theorem vf919SquareShell_original_signed_covariance_eq_fullNormGram
    (R : ℕ) (hR : 4 ≤ R) :
    (vf919SquareShellDiagonal R : ℂ) +
        2 * vf919SquareShellFourIndexHeckeCovariance R =
      vf919OAIExactSquareNormFullGram R := by
  have henergy := vf919SquareShell_signedGreenKubo R
  have hcov := vf919SquareShell_actual_signed_covariance_eq_fourIndexHecke R
  have hsource := vf919OAIExactSquareNormSource_eq_originalSquareShell R hR
  have hGram := vf919OAIExactSquareNormFullGram_eq_source_sq R
  have hcomplex := congrArg (fun x : ℝ => (x : ℂ)) henergy
  push_cast at hcomplex
  rw [hcov] at hcomplex
  rw [← hsource, ← hGram] at hcomplex
  exact hcomplex.symm

#print axioms vf919OAISharpQuotient36_zero
#print axioms vf919OAIExactSquareNormSource_eq_originalSquareShell
#print axioms vf919OAIExactSquareNormFullGram_eq_source_sq
#print axioms vf919SquareShell_original_signed_covariance_eq_fullNormGram

end RHLean.Analysis
