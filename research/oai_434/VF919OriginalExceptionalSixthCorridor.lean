import OAI.NumberTheory.DirichletL.Detector.GramClassification
import OAI.NumberTheory.DirichletL.Detector.SixthFrequency
import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
import OAI.NumberTheory.DirichletL.Detector.CalibrationFourier

/-!
# The ORIGINAL exceptional sixth-power corridor is phase-coherent

Source: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.

The exceptional frequencies responsible for the original low-Gaussian
P^(1/6) cost INCLUDE ALL nonzero sixth powers. On this same corridor
the ACTUAL calibrated physical coefficient is invariant under
multiplication of the frequency by a sixth power coprime to the
complete conductor.

Thus primitive sixth-order Gauss sums, alone, cannot give
cross-frequency cancellation on the difficult sixth-power family.
This file does not claim cancellation of the weighted exceptional
Gram/Mobius sum or improvement of any global exponent.
-/

namespace OAI
noncomputable section
namespace SevenEighths.ProbeGramCommon

open ActualEisensteinCubic
open SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
open CenteredExceptionalCount
open UniqueFactorizationMonoid
open CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Every nonzero sixth power is in the *original* exceptional
    frequency set for every calibrated conductor and every common
    Gram divisor ideal. This is an unconditional ideal-factorization
    statement; there are no extra phase hypotheses. -/
theorem original_exceptional_of_sixth_power
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (C : SupportedIdeal) (v : O) (hv : v ≠ 0) :
    ExceptionalFrequency S hS C ⟨v ^ 6, pow_ne_zero 6 hv⟩ := by
  intro p hp
  change CenteredExceptionalCount.valuation (Ideal.span {v ^ 6}) p % 6 = 0
  rw [← Ideal.span_singleton_pow, CenteredExceptionalCount.valuation_pow]
  omega

/-- Extend the original bare sixth-frequency invariance to the
    ACTUAL calibrated congruence coefficient, retaining the complete
    CRT character and its zero-on-nonunits mask. Both coprimality
    assumptions are essential for the sixth-power multiplier. -/
theorem original_actual_calibrated_sixth_frequency_invariant
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (A s : O)
    (hA : Supported (Ideal.span {A}))
    (hs : Supported (Ideal.span {s}))
    (v H : O)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A * s))
    (hvg : IsCoprime (calibrationForSet S hS).generator v)
    (hvas : IsCoprime v (A * s)) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s
        (supportedElement_ne_zero A hA) (v ^ 6 * H) =
      actualCongruenceCoefficient (calibrationForSet S hS) A s
        (supportedElement_ne_zero A hA) H := by
  have hcal :
      (calibrationForSet S hS).residueMonoid (v ^ 6 * H) =
        (calibrationForSet S hS).residueMonoid H := by
    rw [map_mul, map_pow, calibrationForSet_residue_sixth S hS v hvg, one_mul]
  have hb := bareCongruenceCoefficient_sixth_frequency A s hA hs v H hvas
  have hleft := actualCongruenceCoefficient_calibration_factor S hS A s
    (supportedElement_ne_zero A hA) hs hcop (v ^ 6 * H)
  have hright := actualCongruenceCoefficient_calibration_factor S hS A s
    (supportedElement_ne_zero A hA) hs hcop H
  dsimp only at hleft hright
  rw [hcal, hb] at hleft
  exact hleft.trans hright.symm

/-- Put the frequency classification and actual calibrated
    phase coherence in ONE genuine source theorem. -/
theorem original_actual_exceptional_sixth_corridor
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (C : SupportedIdeal)
    (A s : O) (hA : Supported (Ideal.span {A}))
    (hs : Supported (Ideal.span {s}))
    (v H : O) (hv : v ≠ 0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A * s))
    (hvg : IsCoprime (calibrationForSet S hS).generator v)
    (hvas : IsCoprime v (A * s)) :
    ExceptionalFrequency S hS C ⟨v ^ 6, pow_ne_zero 6 hv⟩ ∧
      actualCongruenceCoefficient (calibrationForSet S hS) A s
          (supportedElement_ne_zero A hA) (v ^ 6 * H) =
        actualCongruenceCoefficient (calibrationForSet S hS) A s
          (supportedElement_ne_zero A hA) H := by
  exact ⟨original_exceptional_of_sixth_power S hS C v hv,
    original_actual_calibrated_sixth_frequency_invariant
      S hS A s hA hs v H hcop hvg hvas⟩

/-- The single active nonzero-frequency P^(1/6) term, after taking
    a square root, has exponent 3/16. Replacing it with P^(1/6-xi)
    would improve that exponent by xi/16, UNTIL the diagonal term
    at 17/96 takes over. This ledger is arithmetic, not a claim that
    such a signed saving exists. -/
theorem original_exceptional_gram_power_ledger (xi : ℝ) :
    (17 / 48 + (1 / 8) * (1 / 6 - xi)) / 2 =
      3 / 16 - xi / 16 := by
  ring

theorem original_gram_zero_to_exceptional_gap :
    (3 / 16 : ℝ) - 17 / 96 = 1 / 96 := by
  norm_num

/-- The exact exceptional frequency parameter P=Y'^2/Q' does not
    depend on the selected-slot product L when X'=X/L and Y'=Y/L. -/
theorem original_compensated_exceptional_parameter_invariant
    (q X Y L : ℝ) (hq : q ≠ 0) (hX : X ≠ 0)
    (hY : Y ≠ 0) (hL : L ≠ 0) :
    ((Y / L) ^ 2) / (q * (X / L) * (Y / L)) = Y / (q * X) := by
  field_simp


/-- The sixth-free seed of an ACTUAL exceptional Gaussian
    frequency has NO prime factor outside the fixed Gram conductor.
    Unlike the mere sixth-power inclusion, this treats EVERY
    exceptional frequency, including all conductor-supported
    nontrivial sixth-free seeds. -/
theorem original_exceptional_sixth_seed_support
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (C : SupportedIdeal) (k : GramFrequency)
    (hk : ExceptionalFrequency S hS C k) :
    ∀ p ∉ IdealMobiusDivisorSum.primeSupport
        (exceptionalModulus S hS C),
      CenteredExceptionalCount.valuation
        (CenteredExceptionalCount.sixthRemainder (Ideal.span {k.val})) p = 0 := by
  intro p hp
  rw [CenteredExceptionalCount.sixthRemainder_valuation]
  exact hk p hp

/-- The entire exceptional frequency ideal is a sixth-power ideal
    times a sixth-free seed supported on the fixed conductor.
    This is an exact classification and does NOT imply signed
    cancellation when the sixth-power lattice is summed. -/
theorem original_exceptional_sixth_normal_form
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (C : SupportedIdeal) (k : GramFrequency)
    (hk : ExceptionalFrequency S hS C k) :
    ∃ R V : Ideal O, R ≠ 0 ∧ V ≠ 0 ∧
      Ideal.span {k.val} = R * V ^ 6 ∧
      ∀ p ∉ IdealMobiusDivisorSum.primeSupport
          (exceptionalModulus S hS C),
        CenteredExceptionalCount.valuation R p = 0 := by
  let I : Ideal O := Ideal.span {k.val}
  have hI : I ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr k.property
  refine ⟨CenteredExceptionalCount.sixthRemainder I,
    CenteredExceptionalCount.sixthQuotient I,
    CenteredExceptionalCount.sixthRemainder_ne_zero I,
    CenteredExceptionalCount.sixthQuotient_ne_zero I, ?_, ?_⟩
  · exact (CenteredExceptionalCount.sixth_normal_form I hI).symm
  · exact original_exceptional_sixth_seed_support S hS C k hk

/-- Stronger finite seed control: every original exceptional
    sixth-free remainder DIVIDES the fifth power of its original
    fixed Gram modulus. This is the exact finite-divisor
    parameter needed to isolate all coherent sixth-power towers. -/
theorem original_exceptional_seed_dvd_fixed_fifth
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (C : SupportedIdeal) (k : GramFrequency)
    (hk : ExceptionalFrequency S hS C k) :
    CenteredExceptionalCount.sixthRemainder (Ideal.span {k.val}) ∣
      (exceptionalModulus S hS C) ^ 5 := by
  let G := exceptionalModulus S hS C
  have hR := CenteredExceptionalCount.sixthRemainder_ne_zero (Ideal.span {k.val})
  have hG := exceptionalModulus_nonzero S hS C
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hR
    (pow_ne_zero 5 hG)).mpr
  apply Multiset.le_iff_count.mpr
  intro p
  change CenteredExceptionalCount.valuation
    (CenteredExceptionalCount.sixthRemainder (Ideal.span {k.val})) p ≤
      CenteredExceptionalCount.valuation (G ^ 5) p
  rw [CenteredExceptionalCount.sixthRemainder_valuation,
    CenteredExceptionalCount.valuation_pow]
  by_cases hp : p ∈ IdealMobiusDivisorSum.primeSupport G
  · have hpos : 0 < CenteredExceptionalCount.valuation G p :=
      Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    omega
  · have hz := hk p hp
    omega


/-- A bad-prime fifth-power frequency may cancel the entire original
    low-column sextic character. This source-exact identity preserves
    the full calibrated residual character and its nonunit mask.
    In a fixed calibration ray that residual character can be constant,
    so nonprincipality of a column on its own does not imply that
    every exceptional sixth-power seed has zero finite mean. -/
theorem original_low_column_fifth_seed_restores_calibration
    (C : CalibrationData) (n : O)
    (hn : Supported (Ideal.span {n}))
    (hcop : IsCoprime n C.generator) :
    (C.residueMonoid n)⁻¹ *
        idealRowHom C.generator (Ideal.span {n}) *
          idealRowHom (C.generator ^ 5) (Ideal.span {n}) =
      (C.residueMonoid n)⁻¹ := by
  have h6 := idealRowHom_sixth_mask C.generator (Ideal.span {n}) hn
  rw [idealRowHom_argument_pow C.generator 6 _ hn,
    ite_eq_left ((Ideal.isCoprime_span_singleton_iff n C.generator).mpr hcop)] at h6
  rw [idealRowHom_argument_pow C.generator 5 _ hn]
  calc
    _ = (C.residueMonoid n)⁻¹ *
        (idealRowHom C.generator (Ideal.span {n})) ^ 6 := by ring
    _ = (C.residueMonoid n)⁻¹ := by rw [h6, mul_one]

#print axioms original_exceptional_of_sixth_power
#print axioms original_actual_calibrated_sixth_frequency_invariant
#print axioms original_actual_exceptional_sixth_corridor
#print axioms original_exceptional_gram_power_ledger
#print axioms original_gram_zero_to_exceptional_gap
#print axioms original_compensated_exceptional_parameter_invariant
#print axioms original_exceptional_sixth_seed_support
#print axioms original_exceptional_sixth_normal_form
#print axioms original_exceptional_seed_dvd_fixed_fifth
#print axioms original_low_column_fifth_seed_restores_calibration

end SevenEighths.ProbeGramCommon
end
end OAI
