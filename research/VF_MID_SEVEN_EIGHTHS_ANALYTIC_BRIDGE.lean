import Mathlib
import «research.VF_MID_LI_UNIFORM_QUADRATURE»

/-!
# The seven-eighths zero-free result as a SEPARATE analytic input

As of October 9, 2026, openai/math RELEASES A NEWLY CLAIMED,
Lean-formalized 7/8 zeta nonvanishing theorem (Lean 4.34.1).
An independent third-party repository reports recompilation of
its 2,924-module zeta proof closure. This is NEW, not a classical
previously settled result, and expert review is not complete.

RH_Lean's native kernel is Lean 4.24.0. Its current proof DOES
NOT import or re-verify the upstream theorem. The nonvanishing
statement here is an EXPLICIT PROP, not an unproved axiom.
The crucial quantitative ZERO-FREE -> prime-count error
explicit-formula implication is also a SEPARATE, UNPROVED PROP.
Upstream Nonvanishing.lean does not supply that quantitative
pi(x)-Li(x) transfer merely by stating zero-freeness.

The target for stronger RH-scale cancellation is not a scalar
7/8 wall but a new uniform moving-A signed bilinear estimate
with the ORIGINAL full Sector Six cross-family Gram.
See VF_MID_919_OPEN_UNIFORM_ANALYTIC_TARGET.md.

This module proves the conditional, fully kernel-checked, exact
VF midpoint consequence of the named prime-counting input, preserving
the repository's existing uniformly O(1) square-endpoint quadrature.

NO 'sorry', 'axiom', unrestricted theorem asserting RH, or circular
use of an owner-sector condition is introduced.
-/

noncomputable section

namespace RHLean.Analysis

/-- Statement of the newly released external 7/8 zeta nonvanishing
claim, whose exact theorem appears in openai/math (Lean 4.34.1).
This RH_Lean Lean 4.24 declaration is ONLY A PROPOSITION.
A #check of this definition does not verify or import the
upstream theorem; no local proof is claimed. -/
def VFMidSevenEighthsZetaZeroFree : Prop :=
  ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0

/-- The classical EXPLICIT-FORMULA transfer at our square endpoints.
This is the precisely named external analytic obligation not yet
available from the OpenAI zero-free theorem alone in Mathlib 4.24.

At x=R², x^(7/8) log x has scale R^(7/4) log R.
The factor 2 from log(R²) is absorbed by the constant C. -/
def VFMidSevenEighthsPrimeLiEndpointBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 2 ≤ R →
      |vfMidPrimeLiError ((R : ℝ) ^ 2)| ≤
        C * ((R : ℝ) ^ (7 / 4 : ℝ) * Real.log (R : ℝ))

/-- This is NOT asserted unconditionally. The missing implication
is the analytic explicit formula / zero-sum argument, not a
sieve reassembly and not a definitionally disguised sector-six gate. -/
def VFMidSevenEighthsExplicitFormulaBridge : Prop :=
  VFMidSevenEighthsZetaZeroFree →
    VFMidSevenEighthsPrimeLiEndpointBounded

/-- The genuine midpoint prime-count discrepancy obeys a 7/8
squared-coordinate bound if the named external prime-Li estimate
is supplied. This conclusion concerns the ACTUAL pi staircase. -/
def VFMidSevenEighthsVFEndpointBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 2 ≤ R →
      |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
        C * ((R : ℝ) ^ (7 / 4 : ℝ) * Real.log (R : ℝ))

/-- Since R>=2, the real power-log weight is >=log 2.
The O(1) midpoint-Li quadrature error can be absorbed ONCE
without enlarging the growth exponent. -/
theorem vfMidSevenEighthsWeight_ge_logTwo
    {R : ℕ} (hR : 2 ≤ R) :
    Real.log (2 : ℝ) ≤
      (R : ℝ) ^ (7 / 4 : ℝ) * Real.log (R : ℝ) := by
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hone : (1 : ℝ) ≤ (R : ℝ) := by linarith
  have hpow : (1 : ℝ) ≤ (R : ℝ) ^ (7 / 4 : ℝ) :=
    Real.one_le_rpow hone (by norm_num)
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlog :
      Real.log (2 : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by norm_num) hRreal
  have hlogR : 0 ≤ Real.log (R : ℝ) :=
    le_trans hlog2.le hlog
  calc
    Real.log (2 : ℝ) ≤ Real.log (R : ℝ) := hlog
    _ = 1 * Real.log (R : ℝ) := by ring
    _ ≤ (R : ℝ) ^ (7 / 4 : ℝ) * Real.log (R : ℝ) :=
      mul_le_mul_of_nonneg_right hpow hlogR

/-- The O(1) midpoint quadrature gives a direct ACTUAL-prime
7/8 VF endpoint theorem from an actual-prime/Li 7/8 input.

The proof uses the genuine Mathlib primeCounting staircase, not
a floor-Li fantasy function, a surrogate owner census, or RH. -/
theorem vfMidSevenEighthsVFEndpointBounded_of_primeLi
    (hinput : VFMidSevenEighthsPrimeLiEndpointBounded) :
    VFMidSevenEighthsVFEndpointBounded := by
  obtain ⟨C, hC, hsource⟩ := hinput
  let Q : ℝ := vfMidLiSquareEndpointUniformConstant
  have hQ : 0 ≤ Q :=
    vfMidLiSquareEndpointUniformConstant_nonneg
  have hlog2 : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hQdiv : 0 ≤ Q / Real.log (2 : ℝ) :=
    div_nonneg hQ hlog2.le
  refine ⟨C + Q / Real.log (2 : ℝ), add_nonneg hC hQdiv, ?_⟩
  intro R hR
  let x : ℝ := (R : ℝ) ^ 2
  let w : ℝ := (R : ℝ) ^ (7 / 4 : ℝ) * Real.log (R : ℝ)
  have hident :
      vfMidPrimeError x = vfMidPrimeLiError x - vfMidLiError x := by
    rw [vfMidPrimeLiError_eq_primeError_add_liError]
    ring
  have htriangle :
      |vfMidPrimeError x| ≤
        |vfMidPrimeLiError x| + |vfMidLiError x| := by
    rw [hident]
    simpa only [sub_zero, zero_sub, abs_neg] using
      (abs_sub_le (vfMidPrimeLiError x) 0 (vfMidLiError x))
  have hsourceR : |vfMidPrimeLiError x| ≤ C * w := by
    simpa [x, w] using hsource R hR
  have hquad : |vfMidLiError x| ≤ Q := by
    simpa [x, Q] using
      (abs_vfMidLiError_sq_le_uniform (R := R) hR)
  have hw : Real.log (2 : ℝ) ≤ w := by
    simpa [w] using vfMidSevenEighthsWeight_ge_logTwo hR
  have hboundQ : Q ≤ (Q / Real.log (2 : ℝ)) * w := by
    have hmul :=
      mul_le_mul_of_nonneg_left hw hQdiv
    have hcancel :
        (Q / Real.log (2 : ℝ)) * Real.log (2 : ℝ) = Q :=
      div_mul_cancel₀ Q hlog2.ne'
    linarith
  change |vfMidPrimeError x| ≤ (C + Q / Real.log (2 : ℝ)) * w
  calc
    |vfMidPrimeError x| ≤
        |vfMidPrimeLiError x| + |vfMidLiError x| := htriangle
    _ ≤ C * w + Q := add_le_add hsourceR hquad
    _ ≤ C * w + (Q / Real.log (2 : ℝ)) * w :=
      add_le_add_left hboundQ _
    _ = (C + Q / Real.log (2 : ℝ)) * w := by ring

/-- A published zero-free theorem PLUS the explicitly identified
analytic explicit-formula bridge yields the 7/8 VF tracking wall.
Neither premise is silently converted into an actual RH statement. -/
theorem vfMidSevenEighthsVFEndpointBounded_of_zeroFree
    (hzero : VFMidSevenEighthsZetaZeroFree)
    (hexplicit : VFMidSevenEighthsExplicitFormulaBridge) :
    VFMidSevenEighthsVFEndpointBounded :=
  vfMidSevenEighthsVFEndpointBounded_of_primeLi (hexplicit hzero)

/-- A normed, root-scale wall constructed from the 7/8 midpoint theorem;
in contrast to C*R*log R it is NOT an RH-equivalent von-Koch wall. -/
def vfMidSevenEighthsWall (C : ℝ) (R : ℕ) : ℝ :=
  C * ((R : ℝ) ^ (7 / 4 : ℝ) * Real.log (R : ℝ))

theorem vfMidSevenEighthsWall_track_of_primeLi
    (hinput : VFMidSevenEighthsPrimeLiEndpointBounded) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
          vfMidSevenEighthsWall C R := by
  simpa [VFMidSevenEighthsVFEndpointBounded, vfMidSevenEighthsWall] using
    (vfMidSevenEighthsVFEndpointBounded_of_primeLi hinput)

end RHLean.Analysis
