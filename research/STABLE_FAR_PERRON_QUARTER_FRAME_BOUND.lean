import Mathlib
import «research.STABLE_FAR_CRITICAL_Q2_ENERGY_MULTIPLIER»
import RHLean.Proof.SquareRootLowPrimeSharpFrameBudget

/-!
# Exact quarter-frame bound for the critical q² Perron synthesis

The critical-line q² multiplier already has exact modulus `1/q`. Therefore a
finite synthesis over owners satisfies a weighted Cauchy--Schwarz bound with
coefficient equal to the reciprocal-square mass of the owner schedule.

For the actual odd-prime owner schedule, the repository already proves

  sum_{q odd prime <= N} 1/q^2 <= 1/4.

Combining the two facts gives an unconditional frequencywise frame bound

  || sum_q m_q(tau) a_q ||^2 <= (1/4) sum_q ||a_q||^2.

This theorem is deliberately directional. It controls synthesis from arbitrary
owner amplitudes into one Perron mode. It does not identify the physical parent
census with such a synthesis of endpoint Mertens daughters, and hence is not a
LOW-4 theorem by itself.

The final witness records why this direction warning matters: at zero frequency
the two owner amplitudes `3` and `-5` synthesize to zero through the owners
`3` and `5`, while their input energy is nonzero. Thus no unrestricted inverse
frame bound can be obtained by merely reversing the Perron synthesis.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Critical q² synthesis over an arbitrary finite owner set. -/
def stableFarCriticalQ2Synthesis
    (tau : ℝ) (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ q ∈ S, stableFarCriticalQ2LogMultiplier tau q * a q

/-- Weighted Cauchy--Schwarz with the exact critical q² multiplier norm.
Every owner is required to be positive only so that `||m_q|| = 1/q` can be
used literally. -/
theorem stableFarCriticalQ2Synthesis_energy_le_reciprocalSquareBudget
    (tau : ℝ) (S : Finset ℕ) (a : ℕ → ℂ)
    (hpos : ∀ q ∈ S, 0 < q) :
    ‖stableFarCriticalQ2Synthesis tau S a‖ ^ 2 ≤
      (∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ 2) *
        ∑ q ∈ S, ‖a q‖ ^ 2 := by
  have htri :
      ‖stableFarCriticalQ2Synthesis tau S a‖ ≤
        ∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * ‖a q‖ := by
    unfold stableFarCriticalQ2Synthesis
    calc
      ‖∑ q ∈ S, stableFarCriticalQ2LogMultiplier tau q * a q‖ ≤
          ∑ q ∈ S, ‖stableFarCriticalQ2LogMultiplier tau q * a q‖ :=
        norm_sum_le _ _
      _ = ∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * ‖a q‖ := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [norm_mul, norm_stableFarCriticalQ2LogMultiplier tau (hpos q hq)]
  have hleft : 0 ≤ ‖stableFarCriticalQ2Synthesis tau S a‖ := norm_nonneg _
  have hright : 0 ≤ ∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * ‖a q‖ := by
    apply Finset.sum_nonneg
    intro q hq
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hpos q hq
    positivity
  have hsq :
      ‖stableFarCriticalQ2Synthesis tau S a‖ ^ 2 ≤
        (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * ‖a q‖) ^ 2 := by
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (R := ℝ) S (fun q => (1 : ℝ) / (q : ℝ)) (fun q => ‖a q‖)
  calc
    ‖stableFarCriticalQ2Synthesis tau S a‖ ^ 2 ≤
        (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * ‖a q‖) ^ 2 := hsq
    _ ≤ (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) *
          ∑ q ∈ S, ‖a q‖ ^ 2 := hcs
    _ = (∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ 2) *
          ∑ q ∈ S, ‖a q‖ ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro q hq
            ring

/-- Real form of the already-compiled odd-prime reciprocal-square budget. -/
theorem oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter (N : ℕ) :
    (∑ q ∈ (primesUpTo N).erase 2, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 / 4 := by
  have hQ := oddPrimeOwnerReciprocalSquareBudget_le_quarter N
  have hcast :
      (((∑ q ∈ (primesUpTo N).erase 2,
          (1 : ℚ) / (q : ℚ) ^ 2) : ℚ) : ℝ) ≤
        (((1 / 4 : ℚ)) : ℝ) := by
    exact_mod_cast hQ
  push_cast at hcast
  norm_num at hcast ⊢
  simpa [Nat.cast_pow] using hcast

/-- **Quarter-frame theorem.** At every log frequency, the complete odd-prime
critical q² synthesis has squared operator norm at most `1/4`. -/
theorem stableFarCriticalQ2OddPrimeSynthesis_energy_le_quarter
    (tau : ℝ) (N : ℕ) (a : ℕ → ℂ) :
    ‖stableFarCriticalQ2Synthesis tau ((primesUpTo N).erase 2) a‖ ^ 2 ≤
      (1 / 4 : ℝ) *
        ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 := by
  have hpos : ∀ q ∈ (primesUpTo N).erase 2, 0 < q := by
    intro q hq
    exact (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1.pos
  have hframe :=
    stableFarCriticalQ2Synthesis_energy_le_reciprocalSquareBudget
      tau ((primesUpTo N).erase 2) a hpos
  have hbudget := oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter N
  have henergy :
      0 ≤ ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 := by positivity
  calc
    ‖stableFarCriticalQ2Synthesis tau ((primesUpTo N).erase 2) a‖ ^ 2 ≤
        (∑ q ∈ (primesUpTo N).erase 2, (1 : ℝ) / (q : ℝ) ^ 2) *
          ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 := hframe
    _ ≤ (1 / 4 : ℝ) *
          ∑ q ∈ (primesUpTo N).erase 2, ‖a q‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hbudget henergy

/-- At zero frequency, owners `3` and `5` already give a nontrivial kernel of
the unrestricted synthesis map. This prevents reversing the quarter-frame
bound without additional arithmetic restrictions on the amplitude family. -/
theorem stableFarCriticalQ2Synthesis_zeroFrequency_twoOwner_kernel :
    stableFarCriticalQ2LogMultiplier 0 3 * (3 : ℂ) +
      stableFarCriticalQ2LogMultiplier 0 5 * (-5 : ℂ) = 0 := by
  rw [stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase 0 (by norm_num : 0 < 3),
    stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase 0 (by norm_num : 0 < 5)]
  simp

/-- The preceding kernel witness has strictly positive input energy. -/
theorem stableFarCriticalQ2Synthesis_zeroFrequency_twoOwner_kernel_energy :
    ‖(3 : ℂ)‖ ^ 2 + ‖(-5 : ℂ)‖ ^ 2 = 34 := by
  norm_num

/-! ## Raw daughter normalization

The physical log-frequency Mertens column uses the unit-modulus phase, not
the critical half-density multiplier. Its exact forward input to the critical
synthesis is therefore `q * M(Y_q)`. This is a forward identity, with no
inversion of the many-to-one synthesis operator.
-/

/-- Restoring the raw owner amplitude cancels the critical half-density. -/
theorem stableFarCriticalQ2LogMultiplier_mul_owner_amplitude
    (tau : ℝ) {q : ℕ} (hq : 0 < q) (a : ℂ) :
    stableFarCriticalQ2LogMultiplier tau q * ((q : ℂ) * a) =
      stableFarQ2LogFrequencyMultiplier tau q * a := by
  rw [stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase tau hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hqC] <;> ring

/-- Exact forward synthesis of a raw phase-weighted family. -/
theorem stableFarCriticalQ2Synthesis_owner_scaled_eq_phase_sum
    (tau : ℝ) (S : Finset ℕ) (a : ℕ → ℂ)
    (hpos : ∀ q ∈ S, 0 < q) :
    stableFarCriticalQ2Synthesis tau S (fun q => (q : ℂ) * a q) =
      ∑ q ∈ S, stableFarQ2LogFrequencyMultiplier tau q * a q := by
  unfold stableFarCriticalQ2Synthesis
  apply Finset.sum_congr rfl
  intro q hq
  exact stableFarCriticalQ2LogMultiplier_mul_owner_amplitude tau (hpos q hq) (a q)

/-- The existing physical Mertens frequency family requires owner-scaled
inputs to the critical synthesis. At frequency zero it recovers the raw
Mertens column, not the reciprocal-weighted column. -/
theorem farFourOddMertensLogFrequencyColumn_eq_criticalSynthesis_owner_scaled
    (R : ℕ) (tau : ℝ) :
    farFourOddMertensLogFrequencyColumn R tau =
      stableFarCriticalQ2Synthesis tau ((primesUpTo (R - 1)).erase 2)
        (fun q => (q : ℂ) *
          ((mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ)) := by
  symm
  apply stableFarCriticalQ2Synthesis_owner_scaled_eq_phase_sum
  intro q hq
  exact (mem_primesUpTo.mp (Finset.mem_erase.mp hq).2).1.pos

/-- The quarter-frame theorem applied to the raw physical frequency family
has the exact compensating `q^2` input-energy weight. -/
theorem farFourOddMertensLogFrequencyColumn_energy_le_quarter_owner_weighted
    (R : ℕ) (tau : ℝ) :
    ‖farFourOddMertensLogFrequencyColumn R tau‖ ^ 2 ≤
      (1 / 4 : ℝ) * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        (q : ℝ) ^ 2 *
          ‖((mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ)‖ ^ 2 := by
  rw [farFourOddMertensLogFrequencyColumn_eq_criticalSynthesis_owner_scaled]
  have h := stableFarCriticalQ2OddPrimeSynthesis_energy_le_quarter
    tau (R - 1) (fun q => (q : ℂ) *
      ((mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ))
  simpa only [norm_mul, Complex.norm_natCast, mul_pow] using h

/-- Even at zero frequency a single nonzero raw input is changed by inserting
the critical multiplier. A boundary or input renormalization is necessary. -/
theorem stableFarCriticalQ2LogMultiplier_zero_three_ne_raw :
    stableFarCriticalQ2LogMultiplier 0 3 * (1 : ℂ) ≠
      stableFarQ2LogFrequencyMultiplier 0 3 * (1 : ℂ) := by
  rw [stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase 0 (by norm_num : 0 < 3)]
  norm_num

end RHLean.Proof
