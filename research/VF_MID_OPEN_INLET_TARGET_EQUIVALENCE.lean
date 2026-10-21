import Mathlib
import «research.VF_MID_DYADIC_SUMMATION_TRANSFER»
import «research.VF_CANONICAL_SQRT_TWO_VON_KOCH»
import «research.VF_MID_OWNER_ADMISSIBLE_ESCAPE_CLASS»

/-!
# No-narrowing certificate for two named direct-VF inlets

`main` names several "single remaining" arithmetic statements for the direct
VF route.  This module proves that two of them are *exactly equivalent* to the
square-endpoint von-Koch target, so neither is a narrower seam than the
target itself:

* `VFMidDyadicSignedLateCorrectionStatement` (the dyadic signed late
  correction at the parity prefix `z = 2`);
* `VFMidActualPrimeOwnerEscapeAdmissibleStatement` (structural owner-escape
  admissibility of the actual prime defect);
* and, as a by-product, the native tracking form
  `VFMidDyadicVFTrackingBoundedStatement`.

The forward implications were already compiled on `main`.  The new content is
the reverse implications:

* At `z = 2` the centered late correction is *literally* the negative
  square-endpoint VF error increment (the parity prefix has no rounding).
  Hence a square-endpoint bound with constant `C` gives the dyadic late
  correction bound with constant `5 C`.
* Under the square-endpoint bound with constant `K` there is no bad scale at
  all (the scales `R = 0, 1` have zero defect and zero radial scale), so the
  descent clause of admissibility holds vacuously.

Consequently each statement is also equivalent to the public canonical
`VFCanonicalSquareVonKochStatement`.

Mathematical status: this is a logical audit.  It proves no prime-counting
estimate, introduces no hypothesis, and does not assert RH.  Its purpose is to
prevent these statements from being reported as narrower than the target.

Research claim IDs: CL-20261014-1 and CL-20261014-2 (Claude direct session,
2026-10-14).
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Small-scale facts used by the admissibility audit -/

/-- There is no prime at most one. -/
private theorem vfMidOpenInlet_primeCounting_one :
    Nat.primeCounting 1 = 0 := by
  unfold Nat.primeCounting Nat.primeCounting'
  simp [Nat.count_succ, Nat.count_zero, Nat.not_prime_zero, Nat.not_prime_one]

/-- The actual endpoint defect vanishes at the degenerate scales `R = 0, 1`:
both the prime count and the midpoint VF path are zero there. -/
private theorem vfMidOpenInlet_endpointDefect_eq_zero_of_le_one
    {R : ℕ} (hR : R ≤ 1) :
    vfMidActualPrimeEndpointDefect R = 0 := by
  have hRreal : (R : ℝ) ≤ 1 := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hsq : (R : ℝ) * (R : ℝ) ≤ 1 * 1 :=
    mul_le_mul hRreal hRreal hR0 (by norm_num)
  have hsq_lt : (R : ℝ) ^ 2 < 4 := by nlinarith [hsq]
  have hvf : vfMid ((R : ℝ) ^ 2) = 0 := by
    unfold vfMid
    rw [ite_eq_left hsq_lt]
  have hfloor : ⌊(R : ℝ) ^ 2⌋₊ = R ^ 2 := by
    rw [show (R : ℝ) ^ 2 = ((R ^ 2 : ℕ) : ℝ) by norm_num]
    exact Nat.floor_natCast (R ^ 2)
  have hsqle : R ^ 2 ≤ 1 := by
    have h := Nat.pow_le_pow_left hR 2
    simpa using! h
  have hpi : Nat.primeCounting (R ^ 2) = 0 := by
    have hmono : Nat.primeCounting (R ^ 2) ≤ Nat.primeCounting 1 :=
      Nat.monotone_primeCounting hsqle
    rw [vfMidOpenInlet_primeCounting_one] at hmono
    omega
  unfold vfMidActualPrimeEndpointDefect vfMidPrimeError vfMidPrimeCount
  rw [hvf, hfloor, hpi]
  simp

/-- The repository radial scale `R log R` vanishes at `R = 0, 1`. -/
private theorem vfMidOpenInlet_radialScale_eq_zero_of_le_one
    {R : ℕ} (hR : R ≤ 1) :
    vfMidSyntheticRadialScale R = 0 := by
  unfold vfMidSyntheticRadialScale
  interval_cases R <;> simp

/-! ## The dyadic late correction at the parity prefix -/

/-- **Exact identity.**  At the parity prefix `z = 2` the centered late
correction carries no prefix rounding at all: it is the negative
square-endpoint VF error increment. -/
theorem vfMidDyadicLateCorrection_two_eq_neg_primeError_increment
    {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) :
    vfMidDyadicLateRemoval 2 A B - vfMidDyadicLateReference 2 A B =
      -(vfMidPrimeError ((B : ℝ) ^ 2) - vfMidPrimeError ((A : ℝ) ^ 2)) := by
  rw [vfMidPrimeError_sq_sub_sq_eq_dyadicPrimeVFError hA hB]
  unfold vfMidDyadicLateRemoval vfMidDyadicLateReference
  rw [vfMidDyadicPrefixSupply_two_eq_half_interior,
    vfMidPrefixWheelDensity_two_eq_half]
  ring

/-- A square-endpoint von-Koch bound with constant `C` controls every dyadic
increment `A < B <= 2A` with constant `5 C`.  Elementary: triangle inequality,
`B <= 2A`, and `log 2 <= log A`. -/
theorem abs_vfMidPrimeError_sq_sub_sq_le_of_squareEndpointBound
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ R : ℕ, 2 ≤ R →
      |vfMidPrimeError ((R : ℝ) ^ 2)| ≤ C * (R : ℝ) * Real.log R)
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    |vfMidPrimeError ((B : ℝ) ^ 2) - vfMidPrimeError ((A : ℝ) ^ 2)| ≤
      5 * C * (A : ℝ) * Real.log A := by
  have hB : 2 ≤ B := hA.trans hAB
  have hEA := hC A hA
  have hEB := hC B hB
  have htri :
      |vfMidPrimeError ((B : ℝ) ^ 2) - vfMidPrimeError ((A : ℝ) ^ 2)| ≤
        |vfMidPrimeError ((B : ℝ) ^ 2)| + |vfMidPrimeError ((A : ℝ) ^ 2)| := by
    have h := abs_add_le (vfMidPrimeError ((B : ℝ) ^ 2))
      (-(vfMidPrimeError ((A : ℝ) ^ 2)))
    simpa only [sub_eq_add_neg, abs_neg] using! h
  have hAreal : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hBreal : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBA' : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hBA
  have hApos : (0 : ℝ) < (A : ℝ) := by linarith [hAreal]
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith [hBreal]
  have hlogB0 : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by linarith [hBreal])
  have hlog2A : Real.log (2 * (A : ℝ)) = Real.log 2 + Real.log (A : ℝ) :=
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hApos.ne'
  have hlog2 : Real.log 2 ≤ Real.log (A : ℝ) :=
    Real.log_le_log (by norm_num) hAreal
  have hlogB : Real.log (B : ℝ) ≤ 2 * Real.log (A : ℝ) := by
    have h1 : Real.log (B : ℝ) ≤ Real.log (2 * (A : ℝ)) :=
      Real.log_le_log hBpos hBA'
    linarith [h1, hlog2A, hlog2]
  have hscale :
      (B : ℝ) * Real.log (B : ℝ) ≤ 4 * ((A : ℝ) * Real.log (A : ℝ)) := by
    calc
      (B : ℝ) * Real.log (B : ℝ) ≤
          (2 * (A : ℝ)) * (2 * Real.log (A : ℝ)) :=
        mul_le_mul hBA' hlogB hlogB0 (by linarith [hApos])
      _ = 4 * ((A : ℝ) * Real.log (A : ℝ)) := by ring
  have hCB :
      C * (B : ℝ) * Real.log (B : ℝ) ≤
        4 * (C * (A : ℝ) * Real.log (A : ℝ)) := by
    calc
      C * (B : ℝ) * Real.log (B : ℝ) =
          C * ((B : ℝ) * Real.log (B : ℝ)) := by ring
      _ ≤ C * (4 * ((A : ℝ) * Real.log (A : ℝ))) :=
        mul_le_mul_of_nonneg_left hscale hC0
      _ = 4 * (C * (A : ℝ) * Real.log (A : ℝ)) := by ring
  calc
    |vfMidPrimeError ((B : ℝ) ^ 2) - vfMidPrimeError ((A : ℝ) ^ 2)| ≤
        |vfMidPrimeError ((B : ℝ) ^ 2)| + |vfMidPrimeError ((A : ℝ) ^ 2)| :=
      htri
    _ ≤ C * (B : ℝ) * Real.log B + C * (A : ℝ) * Real.log A :=
      add_le_add hEB hEA
    _ ≤ 4 * (C * (A : ℝ) * Real.log A) + C * (A : ℝ) * Real.log A :=
      add_le_add_left hCB _
    _ = 5 * C * (A : ℝ) * Real.log A := by ring

/-- **Reverse implication (new).**  The square-endpoint von-Koch statement
implies the dyadic signed late-correction statement. -/
theorem vfMidDyadicSignedLateCorrection_of_squareEndpointVonKoch
    (h : VFMidSquareEndpointVonKochBoundedStatement) :
    VFMidDyadicSignedLateCorrectionStatement := by
  rcases h with ⟨C, hC0, hC⟩
  refine ⟨5 * C, mul_nonneg (by norm_num) hC0, ?_⟩
  intro A B hA hAB hBA
  rw [vfMidDyadicLateCorrection_two_eq_neg_primeError_increment hA
      (hA.trans hAB.le), abs_neg]
  exact abs_vfMidPrimeError_sq_sub_sq_le_of_squareEndpointBound
    hC0 hC hA hAB.le hBA

/-- The dyadic signed late correction is EXACTLY the legacy square-endpoint
von-Koch target; it is not a narrower seam. -/
theorem vfMidDyadicSignedLateCorrection_iff_squareEndpointVonKoch :
    VFMidDyadicSignedLateCorrectionStatement ↔
      VFMidSquareEndpointVonKochBoundedStatement :=
  ⟨vfMidSquareEndpointVonKochBounded_of_signedLateCorrection,
    vfMidDyadicSignedLateCorrection_of_squareEndpointVonKoch⟩

/-- Canonical form: the dyadic signed late correction is exactly the public
canonical sqrt-two von-Koch statement. -/
theorem vfMidDyadicSignedLateCorrection_iff_canonicalSquareVonKoch :
    VFMidDyadicSignedLateCorrectionStatement ↔
      VFCanonicalSquareVonKochStatement :=
  vfMidDyadicSignedLateCorrection_iff_squareEndpointVonKoch.trans
    vfCanonicalSquareVonKoch_iff_legacy.symm

/-- Reverse implication for the native owner tracking form. -/
theorem vfMidDyadicVFTrackingBounded_of_squareEndpointVonKoch
    (h : VFMidSquareEndpointVonKochBoundedStatement) :
    VFMidDyadicVFTrackingBoundedStatement := by
  rcases h with ⟨C, hC0, hC⟩
  refine ⟨5 * C, mul_nonneg (by norm_num) hC0, ?_⟩
  intro A B hA hAB hBA
  rw [vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment hA
      (hA.trans hAB.le) hAB.le, abs_neg]
  exact abs_vfMidPrimeError_sq_sub_sq_le_of_squareEndpointBound
    hC0 hC hA hAB.le hBA

/-- The native VF tracking bound is exactly the legacy square-endpoint
von-Koch target. -/
theorem vfMidDyadicVFTrackingBounded_iff_squareEndpointVonKoch :
    VFMidDyadicVFTrackingBoundedStatement ↔
      VFMidSquareEndpointVonKochBoundedStatement :=
  ⟨fun h => vfMidSquareEndpointVonKochBounded_of_signedLateCorrection
      (vfMidDyadicSignedLateCorrection_of_vfTracking h),
    vfMidDyadicVFTrackingBounded_of_squareEndpointVonKoch⟩

/-! ## Owner-escape admissibility of the actual prime defect -/

/-- **Reverse implication (new).**  Under the square-endpoint von-Koch bound
with constant `K` no scale is bad at `K` (the degenerate scales have zero
defect and zero radial scale), so finite base control holds and the descent
clause is vacuous. -/
theorem vfMidActualPrimeOwnerEscapeAdmissible_of_squareEndpointVonKoch
    (h : VFMidSquareEndpointVonKochBoundedStatement) :
    VFMidActualPrimeOwnerEscapeAdmissibleStatement := by
  obtain ⟨K, hK0, hK⟩ := vfMidActualRadialBounded_iff_squareEndpoint.mpr h
  have hnotbad :
      ∀ R : ℕ, ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect K R := by
    intro R hbad
    unfold VFMidSyntheticBadAt at hbad
    by_cases hR : 2 ≤ R
    · have hbound :
          |vfMidActualPrimeEndpointDefect R| ≤
            K * vfMidSyntheticRadialScale R :=
        hK R hR
      linarith [hbound, hbad]
    · have hR1 : R ≤ 1 := by omega
      rw [vfMidOpenInlet_endpointDefect_eq_zero_of_le_one hR1, abs_zero,
        vfMidOpenInlet_radialScale_eq_zero_of_le_one hR1, mul_zero] at hbad
      exact lt_irrefl (0 : ℝ) hbad
  unfold VFMidActualPrimeOwnerEscapeAdmissibleStatement VFMidOwnerEscapeAdmissible
  refine ⟨K, hK0, ?_, ?_⟩
  · intro R _hR
    exact hnotbad R
  · intro R _hR hbad
    exact (hnotbad R hbad).elim

/-- Actual-prime owner-escape admissibility is EXACTLY the legacy
square-endpoint von-Koch target; it is not a narrower seam. -/
theorem vfMidActualPrimeOwnerEscapeAdmissible_iff_squareEndpointVonKoch :
    VFMidActualPrimeOwnerEscapeAdmissibleStatement ↔
      VFMidSquareEndpointVonKochBoundedStatement :=
  ⟨vfMidSquareEndpointVonKochBounded_of_actualPrimeOwnerEscapeAdmissible,
    vfMidActualPrimeOwnerEscapeAdmissible_of_squareEndpointVonKoch⟩

/-- Canonical form of the admissibility audit. -/
theorem vfMidActualPrimeOwnerEscapeAdmissible_iff_canonicalSquareVonKoch :
    VFMidActualPrimeOwnerEscapeAdmissibleStatement ↔
      VFCanonicalSquareVonKochStatement :=
  vfMidActualPrimeOwnerEscapeAdmissible_iff_squareEndpointVonKoch.trans
    vfCanonicalSquareVonKoch_iff_legacy.symm

/-- **No-narrowing certificate.**  Each of the three statements is exactly the
public canonical target. -/
theorem vfMidOpenInlets_noNarrowing_canonical :
    (VFMidDyadicSignedLateCorrectionStatement ↔
        VFCanonicalSquareVonKochStatement) ∧
      (VFMidDyadicVFTrackingBoundedStatement ↔
        VFCanonicalSquareVonKochStatement) ∧
      (VFMidActualPrimeOwnerEscapeAdmissibleStatement ↔
        VFCanonicalSquareVonKochStatement) :=
  ⟨vfMidDyadicSignedLateCorrection_iff_canonicalSquareVonKoch,
    vfMidDyadicVFTrackingBounded_iff_squareEndpointVonKoch.trans
      vfCanonicalSquareVonKoch_iff_legacy.symm,
    vfMidActualPrimeOwnerEscapeAdmissible_iff_canonicalSquareVonKoch⟩

/-! ## Axiom audit (compile-time)

Each `#guard_msgs` fails the warning-fatal build unless the theorem depends on
exactly the standard axioms `propext`, `Classical.choice`, `Quot.sound`. -/

/-- info: 'RHLean.Analysis.vfMidDyadicLateCorrection_two_eq_neg_primeError_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidDyadicLateCorrection_two_eq_neg_primeError_increment

/-- info: 'RHLean.Analysis.abs_vfMidPrimeError_sq_sub_sq_le_of_squareEndpointBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_vfMidPrimeError_sq_sub_sq_le_of_squareEndpointBound

/-- info: 'RHLean.Analysis.vfMidDyadicSignedLateCorrection_of_squareEndpointVonKoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidDyadicSignedLateCorrection_of_squareEndpointVonKoch

/-- info: 'RHLean.Analysis.vfMidDyadicSignedLateCorrection_iff_squareEndpointVonKoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidDyadicSignedLateCorrection_iff_squareEndpointVonKoch

/-- info: 'RHLean.Analysis.vfMidDyadicSignedLateCorrection_iff_canonicalSquareVonKoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidDyadicSignedLateCorrection_iff_canonicalSquareVonKoch

/-- info: 'RHLean.Analysis.vfMidDyadicVFTrackingBounded_of_squareEndpointVonKoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidDyadicVFTrackingBounded_of_squareEndpointVonKoch

/-- info: 'RHLean.Analysis.vfMidDyadicVFTrackingBounded_iff_squareEndpointVonKoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidDyadicVFTrackingBounded_iff_squareEndpointVonKoch

/-- info: 'RHLean.Analysis.vfMidActualPrimeOwnerEscapeAdmissible_of_squareEndpointVonKoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidActualPrimeOwnerEscapeAdmissible_of_squareEndpointVonKoch

/-- info: 'RHLean.Analysis.vfMidActualPrimeOwnerEscapeAdmissible_iff_squareEndpointVonKoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidActualPrimeOwnerEscapeAdmissible_iff_squareEndpointVonKoch

/-- info: 'RHLean.Analysis.vfMidActualPrimeOwnerEscapeAdmissible_iff_canonicalSquareVonKoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidActualPrimeOwnerEscapeAdmissible_iff_canonicalSquareVonKoch

/-- info: 'RHLean.Analysis.vfMidOpenInlets_noNarrowing_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vfMidOpenInlets_noNarrowing_canonical

end RHLean.Analysis
