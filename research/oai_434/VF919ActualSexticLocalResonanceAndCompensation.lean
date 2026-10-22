import OAI.NumberTheory.DirichletL.Moments.Canonical
import OAI.NumberTheory.DirichletL.Detector.Local
import «research.VF_919_OAI_EFFECTIVE_SEXTIC_VALUATION_CLASSIFICATION_20261022»

/-!
# ORIGINAL OAI local sextic character and exact compensation: no fictitious saving

Actual pinned upstream imports:
  CenteredMomentCanonical.actualSextic_order_six
  ProbeLocal.normalized_cancellation
These are original OAI theorems, NOT assumptions or rewritten toy values.

A genuine good Eisenstein prime ideal has an order-SIX character; its
powers at exponents 0,1,2 are distinct. Together with the native
bounded-valuation lemma and the CRT decomposition, this identifies
the finite local resonance classes.

It DOES NOT prove: that every ORIGINAL completed GaussianSubset coefficient
admits an effective ideal of cap 2, that all original row labels are
complete for CRT separation, or that its principal/rescaled fiber
errors obey a uniform analytic bound. Each remains an explicit gate.

The actual physical local compensation formula has TWO residual bills,
not just -chi^2*(Norm P)^(-2s). We prove the honest norm bound on BOTH.
The principal residue cancellation is a separate algebraic conditional
equality pending original Mellin residue-source identification.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge

namespace SevenEighths
local notation "O" => ActualEisensteinCubic.O

/-- On a genuine good Eisenstein prime ideal, ORIGINAL actualSextic
    distinguishes all three permitted effective valuations 0,1,2.
    No rational-prime norm alias or invented character is involved. -/
theorem oai_actualSextic_bounded_local_resonance_iff_eq
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
    (actualSextic P hg) ^ a = (actualSextic P hg) ^ b ↔ a = b := by
  constructor
  · intro heq
    have horder : orderOf (actualSextic P hg) = 6 :=
      CenteredMomentCanonical.actualSextic_order_six P hg hchar
    have hA : a < orderOf (actualSextic P hg) := by
      rw [horder]
      omega
    have hB : b < orderOf (actualSextic P hg) := by
      rw [horder]
      omega
    exact (pow_injOn_Iio_orderOf (x := actualSextic P hg)) hA hB heq
  · intro h
    rw [h]

/-- The ORIGINAL physical local cancellation has TWO remainder terms.
    Their norms must be paid together: neither may be silently dropped
    or replaced by a bare quadratic Euler estimate. -/
theorem oai_actual_local_compensation_two_bills_le
    (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    ‖ProbeLocal.compensatedReplacement V W D Pstar B q +
        ProbeLocal.localCorrection V W D Pstar * vInv‖ ≤
      ‖(1 - V) * (1 - W) / (1 - D)‖ *
        (‖vInv - q‖ * ‖V / (1 - V) - D‖ +
          ‖B + vInv - q‖ * ‖Pstar + D‖) := by
  rw [ProbeLocal.normalized_cancellation
    V W D Pstar B q vInv hV hW hD hBD hvW]
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖(vInv - q) * (V / (1 - V) - D) +
       (B + vInv - q) * (Pstar + D)‖ ≤
      ‖(vInv - q) * (V / (1 - V) - D)‖ +
        ‖(B + vInv - q) * (Pstar + D)‖ := norm_add_le _ _
    _ = _ := by simp only [norm_mul]

/-- Algebraic principal-residue cancellation, conditional on the
    ORIGINAL Mellin contour residue actually equalling normer*signal.
    No bound on the nonresidue tail follows from this identity alone. -/
theorem oai_principal_residue_normalized_cancel
    (raw residue tail signal normer : ℂ)
    (hnormer : normer ≠ 0)
    (hraw : raw = residue + tail)
    (hResidue : residue = normer * signal) :
    raw / normer - signal = tail / normer := by
  rw [hraw, hResidue]
  field_simp
  ring

/-- The exact energy left after subtracting the calibrated principal
    signal; this is only small if the genuine contour tail is small. -/
theorem oai_principal_residue_normalized_energy
    (raw residue tail signal normer : ℂ)
    (hnormer : normer ≠ 0)
    (hraw : raw = residue + tail)
    (hResidue : residue = normer * signal) :
    ‖raw / normer - signal‖ ^ 2 = ‖tail‖ ^ 2 / ‖normer‖ ^ 2 := by
  rw [oai_principal_residue_normalized_cancel raw residue tail signal normer
    hnormer hraw hResidue, norm_div]
  ring

end SevenEighths

#print axioms SevenEighths.oai_actualSextic_bounded_local_resonance_iff_eq
#print axioms SevenEighths.oai_actual_local_compensation_two_bills_le
#print axioms SevenEighths.oai_principal_residue_normalized_cancel
#print axioms SevenEighths.oai_principal_residue_normalized_energy

end OAI
