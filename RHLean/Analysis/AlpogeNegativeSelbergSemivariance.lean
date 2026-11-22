import Mathlib
import RHLean.Analysis.AlpogeNNSMatchedSelbergKernel
import RHLean.Proof.FinitePartialMoments

/-!
# Alpoge's square-clock negative semivariance in the complete signed Selberg source

This file never truncates the physical von Mangoldt source or replaces the
second Selberg kernel by a positive majorant. The matched source is exactly the
genuine Chebyshev error multiplied by log(N)^2, and its zero-target LPM2 is
therefore an *exact* normalized negative-part square of that complete source.

The finite envelope-to-LPM2 theorem is proved below. The supplier
`NativeSquareDyadicChebyshevBound` is NOT proved here: its unconditional
mathematical justification is RH (Alpoge) plus the classical RH-to-Chebyshev
explicit formula, neither of which is an imported theorem in the pinned
RH_Lean root library. An RH-strength theorem must not be declared unconditional
inside Lean until that imported proof dependency is discharged.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The ORIGINAL, fully matched signed second-Selberg source. -/
def alpogeFullMatchedSecondSelberg (N : ℕ) : ℝ :=
  nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
    nativePNTLambdaFloorLogSignedErrorMass N -
    nativePNTLambdaFloorLogSignedDefectMass N +
    alpogeNNSMatchedMass N (Finset.Icc 1 N)

/-- No negative principal band credit is counted twice: the entire
second-Selberg recurrence is the original Chebyshev error. -/
theorem alpogeFullMatchedSecondSelberg_eq_nativeError (N : ℕ) :
    alpogeFullMatchedSecondSelberg N =
      nativePNTError N * (Real.log (N : ℝ)) ^ 2 := by
  exact (alpogeNNSNativeError_eq_matched_primePowerSource N).symm

/-- Negative-part scaling with a nonnegative weight. -/
theorem alpogeNegativePart_mul_nonneg (a b : ℝ) (hb : 0 ≤ b) :
    negativePart (a * b) = negativePart a * b := by
  unfold negativePart
  by_cases ha : 0 ≤ -a
  · have hab : 0 ≤ -(a * b) := by nlinarith [mul_nonneg ha hb]
    rw [max_eq_left ha, max_eq_left hab]
    ring
  · have ha' : -a ≤ 0 := le_of_not_ge ha
    have ha0 : 0 ≤ a := by linarith
    have hab : -(a * b) ≤ 0 := by nlinarith [mul_nonneg ha0 hb]
    rw [max_eq_right ha', max_eq_right hab]
    ring

theorem alpogeFullMatchedSecondSelberg_negativePart (N : ℕ) :
    negativePart (alpogeFullMatchedSecondSelberg N) =
      negativePart (nativePNTError N) * (Real.log (N : ℝ)) ^ 2 := by
  rw [alpogeFullMatchedSecondSelberg_eq_nativeError]
  exact alpogeNegativePart_mul_nonneg _ _ (sq_nonneg _)

/-- Native, physical, zero-target lower partial second moment. -/
def alpogeNativeSquareNegativeLPM2 (H : ℕ) : ℝ :=
  lowerPartialMomentNat 2 (Finset.Ico H (2 * H))
    (fun R => nativePNTError (R ^ 2 - 1))

/-- The same negative energy evaluated on the COMPLETE signed matched source.
Crucially the max is formed after all pieces have been recombined. -/
def alpogeFullMatchedSquareNegativeLPM2 (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    negativePart (alpogeFullMatchedSecondSelberg (R ^ 2 - 1)) ^ 2 /
      (Real.log (((R ^ 2 - 1 : ℕ) : ℝ))) ^ 4

/-- Exact inverse-log normalization; there are no omitted prime powers,
higher quotients, floor defects or off-band products. -/
theorem alpogeFullMatchedSquareNegativeLPM2_eq_native
    (H : ℕ) (hH : 2 ≤ H) :
    alpogeFullMatchedSquareNegativeLPM2 H = alpogeNativeSquareNegativeLPM2 H := by
  unfold alpogeFullMatchedSquareNegativeLPM2
    alpogeNativeSquareNegativeLPM2 lowerPartialMomentNat
  apply Finset.sum_congr rfl
  intro R hR
  have hR2 : 2 ≤ R := by
    have hlow := (Finset.mem_Ico.mp hR).1
    omega
  have hX : 1 < R ^ 2 - 1 := by
    have hfour : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hXreal : (1 : ℝ) < ((R ^ 2 - 1 : ℕ) : ℝ) := by
    exact_mod_cast hX
  have hlog : Real.log (((R ^ 2 - 1 : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.log_pos hXreal)
  rw [alpogeFullMatchedSecondSelberg_negativePart]
  calc
    (negativePart (nativePNTError (R ^ 2 - 1)) *
          Real.log (((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2) ^ 2 /
        Real.log (((R ^ 2 - 1 : ℕ) : ℝ)) ^ 4 =
      negativePart (nativePNTError (R ^ 2 - 1)) ^ 2 *
        Real.log (((R ^ 2 - 1 : ℕ) : ℝ)) ^ 4 /
        Real.log (((R ^ 2 - 1 : ℕ) : ℝ)) ^ 4 := by ring
    _ = negativePart (nativePNTError (R ^ 2 - 1)) ^ 2 := by
      field_simp

/-- A finite, completely unconditional dyadic LPM2 bound by the maximum
absolute Chebyshev error on the same square endpoints. -/
theorem alpogeNativeSquareNegativeLPM2_le_uniform
    (H : ℕ) (hH : 1 ≤ H) (M : ℝ) (hM : 0 ≤ M)
    (hpoint : ∀ R ∈ Finset.Ico H (2 * H),
      |nativePNTError (R ^ 2 - 1)| ≤ M) :
    alpogeNativeSquareNegativeLPM2 H ≤ (H : ℝ) * M ^ 2 := by
  unfold alpogeNativeSquareNegativeLPM2 lowerPartialMomentNat
  calc
    (∑ R ∈ Finset.Ico H (2 * H),
      negativePart (nativePNTError (R ^ 2 - 1)) ^ 2) ≤
        ∑ _R ∈ Finset.Ico H (2 * H), M ^ 2 := by
      apply Finset.sum_le_sum
      intro R hR
      have hneg : 0 ≤ negativePart (nativePNTError (R ^ 2 - 1)) := by
        unfold negativePart
        exact le_max_right _ _
      have hab : negativePart (nativePNTError (R ^ 2 - 1)) ≤
          |nativePNTError (R ^ 2 - 1)| := by
        have heq := positivePart_add_negativePart
          (nativePNTError (R ^ 2 - 1))
        have hpos : 0 ≤ positivePart (nativePNTError (R ^ 2 - 1)) := by
          unfold positivePart
          exact le_max_right _ _
        linarith
      have hbound := le_trans hab (hpoint R hR)
      nlinarith
    _ = (H : ℝ) * M ^ 2 := by
      rw [Finset.sum_const, Nat.card_Ico]
      have hlen : 2 * H - H = H := by omega
      rw [hlen]
      simp only [nsmul_eq_mul]

/-- The analytic supplier is a LOCAL square-clock statement, not an axiom:
the external RH theorem plus a RH-to-psi explicit formula imply it.
The `H` in this bound is the square-root index, not the prime cutoff. -/
def NativeSquareDyadicChebyshevBound : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ H : ℕ, 2 ≤ H →
        ∀ R ∈ Finset.Ico H (2 * H),
          |nativePNTError (R ^ 2 - 1)| ≤
            C * (H : ℝ) ^ (1 + δ)

/-- Full RH-scale LPM2 consequence of the *explicitly supplied*
pointwise square-clock estimate. No proof of this supplier is invented. -/
theorem alpogeNativeSquareNegativeLPM2_of_dyadicChebyshev
    (h : NativeSquareDyadicChebyshevBound) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ H : ℕ, 2 ≤ H →
          alpogeNativeSquareNegativeLPM2 H ≤
            C * (H : ℝ) ^ (3 + ε) := by
  intro ε hε
  have hδ : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨C, hC, hpoint⟩ := h (ε / 2) hδ
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro H hH
  have hHpos : (0 : ℝ) < H := by exact_mod_cast
    (show 0 < H by omega)
  have hHnonneg : (0 : ℝ) ≤ H := hHpos.le
  have hM : 0 ≤ C * (H : ℝ) ^ (1 + ε / 2) :=
    mul_nonneg hC (Real.rpow_nonneg hHnonneg _)
  have hbase := alpogeNativeSquareNegativeLPM2_le_uniform H (by omega)
    (C * (H : ℝ) ^ (1 + ε / 2)) hM
    (hpoint H hH)
  have hpow2 :
      ((H : ℝ) ^ (1 + ε / 2)) ^ 2 = (H : ℝ) ^ (2 + ε) := by
    calc
      _ = ((H : ℝ) ^ (1 + ε / 2)) ^ (2 : ℝ) := by
        rw [Real.rpow_two]
      _ = (H : ℝ) ^ ((1 + ε / 2) * 2) :=
        (Real.rpow_mul hHnonneg (1 + ε / 2) 2).symm
      _ = (H : ℝ) ^ (2 + ε) := by
        congr 1
        ring
  have hpow : (H : ℝ) * (C * (H : ℝ) ^ (1 + ε / 2)) ^ 2 =
      C ^ 2 * (H : ℝ) ^ (3 + ε) := by
    calc
      _ = C ^ 2 * ((H : ℝ) * ((H : ℝ) ^ (1 + ε / 2)) ^ 2) := by ring
      _ = C ^ 2 * ((H : ℝ) ^ (1 : ℝ) * (H : ℝ) ^ (2 + ε)) := by
        rw [hpow2, Real.rpow_one]
      _ = C ^ 2 * (H : ℝ) ^ (3 + ε) := by
        rw [← Real.rpow_add hHpos, show (1 : ℝ) + (2 + ε) = 3 + ε by ring]
  calc
    alpogeNativeSquareNegativeLPM2 H ≤
        (H : ℝ) * (C * (H : ℝ) ^ (1 + ε / 2)) ^ 2 := hbase
    _ = C ^ 2 * (H : ℝ) ^ (3 + ε) := hpow

end RHLean.Analysis
