import Mathlib
import «research.VF_CANONICAL_SQRT_TWO»

/-!
# Canonical sqrt2 VF preserves EXACTLY the classical von-Koch scale

Existing VF_mid <-> prime-Li_2 proof was already a real Lean equivalence.
Here the sole sqrt(2) phase is transported in both directions with ONE
fixed harmless coefficient; it does not change the arithmetic difficulty.

Riemann Hypothesis is NOT claimed: the terminal classical von-Koch theorem
remains an explicit ClassicalVonKochRHCriterion argument, and the
actual-prime canonical tracking estimate remains open.
-/

noncomputable section
namespace RHLean.Analysis

def VFCanonicalRealVonKochStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfCanonicalPrimeError x| ≤ C * Real.sqrt x * Real.log x

def VFCanonicalSquareVonKochStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 2 ≤ R →
      |vfCanonicalSquareDefect R| ≤
        C * (R : ℝ) * Real.log (R : ℝ)

/-- The real-cutoff von-Koch weight is at least one on x>=4. -/
theorem vfCanonicalRealVonKochWeight_ge_one
    {x : ℝ} (hx : 4 ≤ x) :
    1 ≤ Real.sqrt x * Real.log x := by
  have h := two_log_four_le_sqrt_mul_log hx
  have hlog := one_lt_log_four
  linarith

/-- The square-index von-Koch weight is at least one for R>=2. -/
theorem vfCanonicalSquareVonKochWeight_ge_one
    {R : ℕ} (hR : 2 ≤ R) :
    1 ≤ (R : ℝ) * Real.log (R : ℝ) := by
  have hR4 : 4 ≤ R ^ 2 := by nlinarith
  have hx : (4 : ℝ) ≤ (R : ℝ) ^ 2 := by exact_mod_cast hR4
  have h := two_log_four_le_sqrt_mul_log hx
  have hroot : Real.sqrt ((R : ℝ) ^ 2) = (R : ℝ) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hlog : Real.log ((R : ℝ) ^ 2) =
      2 * Real.log (R : ℝ) := by
    rw [Real.log_pow]
    ring
  rw [hroot, hlog] at h
  have hloggt := one_lt_log_four
  nlinarith

private theorem abs_sub_fixed_phase_on_weight
    (a c C w : ℝ) (hc : 0 ≤ c) (hw : 1 ≤ w)
    (ha : |a| ≤ C * w) :
    |a - c| ≤ (C + c) * w := by
  have hcW : c ≤ c * w := by
    simpa using! mul_le_mul_of_nonneg_left hw hc
  calc
    |a - c| ≤ |a| + |c| := abs_sub _ _
    _ ≤ C * w + c := by
      rw [abs_of_nonneg hc]
      linarith
    _ ≤ (C + c) * w := by nlinarith

private theorem abs_add_fixed_phase_on_weight
    (a c C w : ℝ) (hc : 0 ≤ c) (hw : 1 ≤ w)
    (ha : |a| ≤ C * w) :
    |a + c| ≤ (C + c) * w := by
  have hcW : c ≤ c * w := by
    simpa using! mul_le_mul_of_nonneg_left hw hc
  calc
    |a + c| ≤ |a| + |c| := abs_add_le _ _
    _ ≤ C * w + c := by
      rw [abs_of_nonneg hc]
      linarith
    _ ≤ (C + c) * w := by nlinarith

/-- The canonical all-real sqrt2 tracking criterion is exactly the older
unshifted VF tracking criterion, with a different absolute constant. -/
theorem vfCanonicalRealVonKoch_iff_legacy :
    VFCanonicalRealVonKochStatement ↔ VFMidVonKochBoundedStatement := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C + vfCanonicalPhase,
      add_nonneg hC vfCanonicalPhase_nonneg, ?_⟩
    intro x hx
    have h : vfMidPrimeError x =
        vfCanonicalPrimeError x + vfCanonicalPhase := by
      rw [vfCanonicalPrimeError_eq_legacy_sub_phase]
      ring
    rw [h]
    have hbound' :
        |vfCanonicalPrimeError x| ≤
          C * (Real.sqrt x * Real.log x) := by
      simpa only [mul_assoc] using! hbound x hx
    have hphase :=
      abs_add_fixed_phase_on_weight
        (vfCanonicalPrimeError x) vfCanonicalPhase C
        (Real.sqrt x * Real.log x)
        vfCanonicalPhase_nonneg
        (vfCanonicalRealVonKochWeight_ge_one hx) hbound'
    simpa only [mul_assoc] using! hphase
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C + vfCanonicalPhase,
      add_nonneg hC vfCanonicalPhase_nonneg, ?_⟩
    intro x hx
    rw [vfCanonicalPrimeError_eq_legacy_sub_phase]
    have hbound' :
        |vfMidPrimeError x| ≤
          C * (Real.sqrt x * Real.log x) := by
      simpa only [mul_assoc] using! hbound x hx
    have hphase :=
      abs_sub_fixed_phase_on_weight
        (vfMidPrimeError x) vfCanonicalPhase C
        (Real.sqrt x * Real.log x)
        vfCanonicalPhase_nonneg
        (vfCanonicalRealVonKochWeight_ge_one hx) hbound'
    simpa only [mul_assoc] using! hphase

/-- The square-only canonical tracking criterion is exactly the original
square-endpoint von-Koch statement; NO per-band pointwise criterion added. -/
theorem vfCanonicalSquareVonKoch_iff_legacy :
    VFCanonicalSquareVonKochStatement ↔
      VFMidSquareEndpointVonKochBoundedStatement := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C + vfCanonicalPhase,
      add_nonneg hC vfCanonicalPhase_nonneg, ?_⟩
    intro R hR
    have h :
        vfMidPrimeError ((R : ℝ)^2) =
          vfCanonicalSquareDefect R + vfCanonicalPhase := by
      rw [← vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR]
      rw [vfCanonicalSquareDefect_eq_legacy_sub_phase]
      ring
    rw [h]
    have hbound' :
        |vfCanonicalSquareDefect R| ≤
          C * ((R : ℝ) * Real.log (R : ℝ)) := by
      simpa only [mul_assoc] using! hbound R hR
    have hphase :=
      abs_add_fixed_phase_on_weight
        (vfCanonicalSquareDefect R) vfCanonicalPhase C
        ((R : ℝ) * Real.log (R : ℝ))
        vfCanonicalPhase_nonneg
        (vfCanonicalSquareVonKochWeight_ge_one hR) hbound'
    simpa only [mul_assoc] using! hphase
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C + vfCanonicalPhase,
      add_nonneg hC vfCanonicalPhase_nonneg, ?_⟩
    intro R hR
    have hold :
        |vfMidDirectSquareEndpointError R| ≤
          C * (R : ℝ) * Real.log (R : ℝ) := by
      rw [vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR]
      exact hbound R hR
    rw [vfCanonicalSquareDefect_eq_legacy_sub_phase]
    have hold' :
        |vfMidDirectSquareEndpointError R| ≤
          C * ((R : ℝ) * Real.log (R : ℝ)) := by
      simpa only [mul_assoc] using! hold
    have hphase :=
      abs_sub_fixed_phase_on_weight
        (vfMidDirectSquareEndpointError R) vfCanonicalPhase C
        ((R : ℝ) * Real.log (R : ℝ))
        vfCanonicalPhase_nonneg
        (vfCanonicalSquareVonKochWeight_ge_one hR) hold'
    simpa only [mul_assoc] using! hphase

/-- Both REAL and SQUARE versions preserve classical Li_2 tracking. -/
theorem vfCanonicalRealVonKoch_iff_primeLiVonKoch :
    VFCanonicalRealVonKochStatement ↔ PrimeLiVonKochBoundedStatement :=
  vfCanonicalRealVonKoch_iff_legacy.trans
    vfMidVonKochBounded_iff_primeLiVonKochBounded

theorem vfCanonicalSquareVonKoch_iff_primeLiVonKoch :
    VFCanonicalSquareVonKochStatement ↔ PrimeLiVonKochBoundedStatement :=
  vfCanonicalSquareVonKoch_iff_legacy.trans
    vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded

theorem vfCanonicalSquareVonKoch_iff_realVonKoch :
    VFCanonicalSquareVonKochStatement ↔ VFCanonicalRealVonKochStatement :=
  vfCanonicalSquareVonKoch_iff_primeLiVonKoch.trans
    vfCanonicalRealVonKoch_iff_primeLiVonKoch.symm

/-- Final consumer is CONDITIONAL on an actual-prime arithmetic bound
and the standard classical von-Koch equivalence, still supplied explicitly. -/
theorem riemannHypothesis_of_vfCanonicalSquare
    (criterion : ClassicalVonKochRHCriterion)
    (h : VFCanonicalSquareVonKochStatement) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (vfCanonicalSquareVonKoch_iff_primeLiVonKoch.mp h)

end RHLean.Analysis
