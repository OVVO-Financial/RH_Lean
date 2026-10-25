import Mathlib
import «research.CORR4_OAI_BUFFERED_INDUCTION_CORE_20261025»
import «research.GLOBAL_RETURNED_CORE_STOKES_COMMON_SPECTRUM_LEDGER»

/-!
# Deterministic q² daughter frame and the complete CORR-4 power biconditional

Every source term is the real Mertens amplitude at the ORIGINAL cutoff
Y_q=floor((R²-1)/q²). No nearest-square rounding and no Gaussian phases.

The new daughter-frame lemma is PURELY DETERMINISTIC. It assumes a
prefix-bound and transports that bound to the true low-q² daughters.
The final theorem consumes the INDEPENDENT signed full owner-Gram
power bill as its explicit hypothesis. No new Mertens exponent or
RH theorem is asserted unconditionally.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

private theorem corr4_daughter_source_norm_square (R q : ℕ) :
    rawQ2ChildEnergyReal R q =
      ‖mertensSummatory (rawQ2ChildCutoff R q)‖ ^ 2 := by
  rw [← norm_sq_lowOwnerRawMertensAmplitude R q]
  unfold lowOwnerRawMertensAmplitude
  rw [mertensSummatoryInt_cast]

/-- True q² daughter frame, no rounded cutoff, conditional only on a
    previously established bound at all integer cutoffs up to R²-1. -/
theorem corr4_low_daughter_energy_of_prefix_power
    (R : ℕ) (hR : 56 ≤ R) (β H : ℝ)
    (hβ : (1 / 2 : ℝ) ≤ β) (hH : 0 ≤ H)
    (hPrefix : ∀ n : ℕ, 1 ≤ n → n ≤ squareRootEndpoint R →
      ‖mertensSummatory n‖ ≤ H * Real.rpow (n : ℝ) β) :
    canonicalRoughLowQ2DaughterEnergy R ≤
      (211 / 900 : ℝ) * H ^ 2 * Real.rpow (R : ℝ) (4 * β) := by
  have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have hβ0 : 0 ≤ β := by linarith
  have hRtwo :
      (Real.rpow (R : ℝ) (2 * β)) ^ 2 =
        Real.rpow (R : ℝ) (4 * β) := by
    calc
      (Real.rpow (R : ℝ) (2 * β)) ^ 2 =
          Real.rpow (Real.rpow (R : ℝ) (2 * β)) (2 : ℝ) :=
            (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (R : ℝ) ((2 * β) * 2) :=
        (Real.rpow_mul hRnonneg (2 * β) 2).symm
      _ = Real.rpow (R : ℝ) (4 * β) := by congr 1; ring
  have hsub :
      canonicalRoughLowQ2Owners R ⊆ (primesUpTo (R - 1)).erase 2 :=
    Finset.sdiff_subset
  have hBudget :
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 : ℝ) / (q : ℝ) ^ 2) ≤ (211 / 900 : ℝ) := by
    calc
      _ ≤ ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        (1 : ℝ) / (q : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro q _hq _hnot
          positivity
      _ ≤ (211 / 900 : ℝ) :=
        oddPrimeOwnerReciprocalSquareBudgetReal_le_twoTermBasel (R - 1)
  have hTerm (q : ℕ) (hq : q ∈ canonicalRoughLowQ2Owners R) :
      rawQ2ChildEnergyReal R q ≤
        (H ^ 2 * Real.rpow (R : ℝ) (4 * β)) / (q : ℝ) ^ 2 := by
    have hqp : q.Prime :=
      (mem_primesUpTo.mp (Finset.mem_erase.mp (hsub hq)).2).1
    have hqNat : 2 ≤ q := hqp.two_le
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqp.pos
    have hqSq : (0 : ℝ) < (q : ℝ) ^ 2 := sq_pos_of_pos hqpos
    let Y : ℕ := rawQ2ChildCutoff R q
    have hYpos : 0 < Y :=
      rawQ2ChildCutoff_pos_of_mem_lowQ2Owners (by omega) hq
    have hYle : Y ≤ squareRootEndpoint R := by
      dsimp [Y, rawQ2ChildCutoff]
      exact Nat.div_le_self _ _
    have hM := hPrefix Y (by omega) hYle
    have hYX : Y * (q * q) ≤ squareRootEndpoint R := by
      dsimp [Y, rawQ2ChildCutoff]
      exact Nat.div_mul_le_self _ _
    have hR2 : squareRootEndpoint R ≤ R ^ 2 := by
      unfold squareRootEndpoint
      exact Nat.sub_le _ _
    have hX : Y * (q * q) ≤ R ^ 2 := hYX.trans hR2
    have hXreal :
        (Y : ℝ) * (q : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
      exact_mod_cast hX
    have hqOne : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
      have hqTwo : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqNat
      nlinarith
    have hqPow :
        (q : ℝ) ≤ Real.rpow ((q : ℝ) ^ 2) β := by
      have hh :=
        Real.rpow_le_rpow_of_exponent_le hqOne hβ
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (le_of_lt hqpos)] at hh
      exact hh
    have hRaise :
        Real.rpow (Y : ℝ) β *
            Real.rpow ((q : ℝ) ^ 2) β ≤
          Real.rpow ((R : ℝ) ^ 2) β := by
      have hh := Real.rpow_le_rpow
        (mul_nonneg (Nat.cast_nonneg Y) (sq_nonneg _)) hXreal hβ0
      rw [Real.mul_rpow (Nat.cast_nonneg Y) (sq_nonneg _)] at hh
      exact hh
    have hRpower :
        Real.rpow ((R : ℝ) ^ 2) β =
          Real.rpow (R : ℝ) (2 * β) := by
      calc
        Real.rpow ((R : ℝ) ^ 2) β =
            Real.rpow (Real.rpow (R : ℝ) (2 : ℝ)) β := by
              rw [Real.rpow_natCast]
        _ = Real.rpow (R : ℝ) (2 * β) :=
          (Real.rpow_mul hRnonneg 2 β).symm
    have hYPower :
        Real.rpow (Y : ℝ) β * (q : ℝ) ≤
          Real.rpow (R : ℝ) (2 * β) := by
      have hh := mul_le_mul_of_nonneg_left hqPow
        (Real.rpow_nonneg (Nat.cast_nonneg Y) β)
      rw [hRpower] at hRaise
      linarith
    have hByScale :
        ‖mertensSummatory Y‖ * (q : ℝ) ≤
          H * Real.rpow (R : ℝ) (2 * β) := by
      calc
        _ ≤ (H * Real.rpow (Y : ℝ) β) * (q : ℝ) :=
          mul_le_mul_of_nonneg_right hM hqpos.le
        _ = H * (Real.rpow (Y : ℝ) β * (q : ℝ)) := by ring
        _ ≤ H * Real.rpow (R : ℝ) (2 * β) :=
          mul_le_mul_of_nonneg_left hYPower hH
    have hLnonneg :
        0 ≤ ‖mertensSummatory Y‖ * (q : ℝ) :=
      mul_nonneg (norm_nonneg _) hqpos.le
    have hUnonneg :
        0 ≤ H * Real.rpow (R : ℝ) (2 * β) :=
      mul_nonneg hH (Real.rpow_nonneg hRnonneg _)
    have hSquare :
        (‖mertensSummatory Y‖ * (q : ℝ)) ^ 2 ≤
          (H * Real.rpow (R : ℝ) (2 * β)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hByScale)
        (add_nonneg hUnonneg hLnonneg)]
    have hScaled :
        ‖mertensSummatory Y‖ ^ 2 * (q : ℝ) ^ 2 ≤
          H ^ 2 * Real.rpow (R : ℝ) (4 * β) := by
      nlinarith [hSquare, hRtwo]
    rw [corr4_daughter_source_norm_square R q]
    apply (le_div_iff₀ hqSq).2
    simpa [Y] using hScaled
  have hPnonneg :
      0 ≤ H ^ 2 * Real.rpow (R : ℝ) (4 * β) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hRnonneg _)
  calc
    canonicalRoughLowQ2DaughterEnergy R =
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          rawQ2ChildEnergyReal R q := rfl
    _ ≤ ∑ q ∈ canonicalRoughLowQ2Owners R,
        (H ^ 2 * Real.rpow (R : ℝ) (4 * β)) / (q : ℝ) ^ 2 :=
      Finset.sum_le_sum hTerm
    _ = (H ^ 2 * Real.rpow (R : ℝ) (4 * β)) *
          (∑ q ∈ canonicalRoughLowQ2Owners R,
            (1 : ℝ) / (q : ℝ) ^ 2) := by
      simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]
    _ ≤ (H ^ 2 * Real.rpow (R : ℝ) (4 * β)) *
          (211 / 900 : ℝ) :=
      mul_le_mul_of_nonneg_left hBudget hPnonneg
    _ = (211 / 900 : ℝ) * H ^ 2 *
          Real.rpow (R : ℝ) (4 * β) := by ring

/-- Nothing arithmetic remains in the first 56²-1 integers: every Mobius step
    is bounded by 1 and n^beta >= sqrt(n) whenever beta>=1/2. -/
theorem corr4_power_buffered_base (β H : ℝ)
    (hβ : (1 / 2 : ℝ) ≤ β) (hH : 1000 ≤ H) :
    ∀ n : ℕ, 1 ≤ n → n ≤ squareRootEndpoint 56 →
      ‖mertensSummatory n‖ ≤ H * Real.rpow (n : ℝ) β := by
  intro n hn hnR
  have hN : n ≤ 56 ^ 2 := by
    norm_num [squareRootEndpoint] at hnR ⊢
    omega
  have hNreal : (n : ℝ) ≤ (56 : ℝ) ^ 2 := by
    exact_mod_cast hN
  have hSq :
      (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hSqrt0 := Real.sqrt_nonneg (n : ℝ)
  have hSqrtBound : Real.sqrt (n : ℝ) ≤ 56 := by
    nlinarith
  have hNBound : (n : ℝ) ≤ 56 * Real.sqrt (n : ℝ) := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hSqrtBound) hSqrt0]
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hPow := Real.rpow_le_rpow_of_exponent_le hN1 hβ
  rw [← Real.sqrt_eq_rpow] at hPow
  calc
    ‖mertensSummatory n‖ ≤ (n : ℝ) :=
      RHLean.Analysis.MertensExponent.mertens_norm_le n
    _ ≤ 56 * Real.sqrt (n : ℝ) := hNBound
    _ ≤ 56 * Real.rpow (n : ℝ) β :=
      mul_le_mul_of_nonneg_left hPow (by norm_num)
    _ ≤ H * Real.rpow (n : ℝ) β :=
      mul_le_mul_of_nonneg_right (by linarith : (56 : ℝ) ≤ H)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Numerical subcritical buffer with one uniform amplitude constant:
    for every nonnegative coefficient A, H=1000*(A+1) more than pays
    the 101 root term and (101/75)*A source error. -/
theorem corr4_power_buffer_for_H (A : ℝ) (hA : 0 ≤ A) :
    ((101 / 100 : ℝ) * (886 / 225) * (211 / 900)) *
        (1000 * (A + 1)) ^ 2 +
        (101 / 75 : ℝ) * A + 101 ≤
      (49 / 50 : ℝ) ^ 2 * (1000 * (A + 1)) ^ 2 := by
  nlinarith [sq_nonneg A]

/-- The COMPLETE general-exponent biconditional. Crucially this is a
    CONDITIONAL EQUIVALENCE between two genuine arithmetic statements,
    not an unconditional hypothesis discharge or a proof of RH. -/
theorem corr4PowerFirstOwnerGram_iff_mertensPowerBound
    (β : ℝ) (hβ : (1 / 2 : ℝ) ≤ β) :
    (∃ A : ℝ, 0 ≤ A ∧ Corr4PowerFirstOwnerGram A β) ↔
      RHLean.Analysis.MertensExponent.MertensPowerBound β := by
  constructor
  · rintro ⟨A, hA, hGram⟩
    let H : ℝ := 1000 * (A + 1)
    have hH : 1000 ≤ H := by dsimp [H]; linarith
    have hB : Corr4PowerPhysicalRemainder A β :=
      (corr4PowerFirstOwnerGram_iff_powerPhysicalRemainder A β).mp hGram
    have hFrame :
        ∀ R : ℕ, 56 ≤ R →
          (∀ n : ℕ, 1 ≤ n → n ≤ squareRootEndpoint R →
            ‖mertensSummatory n‖ ≤ H * Real.rpow (n : ℝ) β) →
          canonicalRoughLowQ2DaughterEnergy R ≤
            (211 / 900 : ℝ) * H ^ 2 *
              Real.rpow (R : ℝ) (4 * β) := by
      intro R hR hPrefix
      exact corr4_low_daughter_energy_of_prefix_power R hR β H hβ
        (by dsimp [H]; linarith) hPrefix
    have hAll :=
      corr4_buffered_all_integer_of_prefix_daughter_frame
        A β H hβ hH (by simpa [H] using corr4_power_buffer_for_H A hA)
        hB (corr4_power_buffered_base β H hβ hH) hFrame
    exact ⟨H, by linarith, hAll⟩
  · intro hM
    exact corr4PowerFirstOwnerGram_of_mertensPowerBound
      (by linarith : 0 ≤ β) hM

#print axioms corr4_low_daughter_energy_of_prefix_power
#print axioms corr4_power_buffered_base
#print axioms corr4_power_buffer_for_H
#print axioms corr4PowerFirstOwnerGram_iff_mertensPowerBound

end RHLean.Proof
