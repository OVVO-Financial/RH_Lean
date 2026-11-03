import OAI.NumberTheory.DirichletL.Detector.GramTruncation
import «research.VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021»
import «research.oai_434.VF919OriginalExceptionalSixthCorridor»

/-!
# Original OAI exceptional-frequency source: exact signed outer Gram and NNS

Original sourceCanonicalSum, with literal sourceMobiusWeight, Hecke phases,
calibration, radial Fourier kernels, divisor pools, common C columns and
all individual nonzero frequencies. No early source absolute-value bound.

The original exceptional ideal estimate uses normalized_double_sum_bound,
losing signed Mobius and complex phases. This file retains them before
the bound P^(1/6) is used. No exponent improvement is asserted here.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT RHLean.Analysis RHLean.Proof
local notation "Id" => Ideal ActualEisensteinCubic.O

/-- At the ACTUAL original low-Gaussian column, the bad fifth-power
frequency cancels the full sextic local phase of the column. This is not
an assumed generic NNS alignment: both factors are literal source
objects, and every original bad-prime and primary/ray admission is kept.

The remaining factor is the original calibration residue character. -/
theorem original_primary_fifth_seed_clears_column
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (hbad : fixedBadPrimes ⊆ S)
    (σ : RayRing) (n : ActualEisensteinCubic.O)
    (hn : Supported (Ideal.span {n}))
    (hprimary : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ n - 1)
    (hray : physicalRay n = σ)
    (hcop : IsCoprime (calibrationForSet S hS).generator n) :
    primaryCoefficient S hS σ n *
        idealRowHom ((calibrationForSet S hS).generator ^ 5)
          (Ideal.span {n}) =
      (calibrationForSet S hS).tau⁻¹ *
        ((calibrationForSet S hS).residueMonoid n)⁻¹ := by
  let C := calibrationForSet S hS
  have hbadgenerator := calibration_generator_bad S hS hbad
  have hrow := gramPeriodicMonoid_primary C C.generator
    (calibrationLowData S hS) hbadgenerator.1 hbadgenerator.2
    n hn hprimary hcop
  have hrestore := original_low_column_fifth_seed_restores_calibration
    C n hn hcop.symm
  change (if ConcretePrimeRowBridge.goodLambda ^ 2 ∣ n - 1 then
      (if physicalRay n = σ then
        C.tau⁻¹ * gramPeriodicMonoid C C.generator
          (calibrationLowData S hS) n else 0)
      else 0) * idealRowHom (C.generator ^ 5) (Ideal.span {n}) =
      C.tau⁻¹ * (C.residueMonoid n)⁻¹
  simp [hprimary, hray, hrow]
  calc
    C.tau⁻¹ *
        ((C.residueMonoid n)⁻¹ *
          idealRowHom C.generator (Ideal.span {n})) *
        idealRowHom (C.generator ^ 5) (Ideal.span {n}) =
      C.tau⁻¹ *
        ((C.residueMonoid n)⁻¹ *
          idealRowHom C.generator (Ideal.span {n}) *
          idealRowHom (C.generator ^ 5) (Ideal.span {n})) := by ring
    _ = _ := by rw [hrestore]

/-- Every coprime sixth-power multiple of the bad fifth seed is
equally coherent at the ACTUAL calibrated primary low column.
The genuine sixth-power character mask is proved by the original
source, not postulated for abstract NNS atoms. -/
theorem original_primary_fifth_sixth_tower_clears_column
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (hbad : fixedBadPrimes ⊆ S)
    (σ : RayRing) (n v : ActualEisensteinCubic.O)
    (hn : Supported (Ideal.span {n}))
    (hprimary : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ n - 1)
    (hray : physicalRay n = σ)
    (hcop : IsCoprime (calibrationForSet S hS).generator n)
    (hv : IsCoprime n v) :
    primaryCoefficient S hS σ n *
        idealRowHom (((calibrationForSet S hS).generator ^ 5) * v ^ 6)
          (Ideal.span {n}) =
      (calibrationForSet S hS).tau⁻¹ *
        ((calibrationForSet S hS).residueMonoid n)⁻¹ := by
  rw [idealRowHom_argument_mul,
    supported_sixth_value n v hn hv, mul_one]
  exact original_primary_fifth_seed_clears_column
    S hS hbad σ n hn hprimary hray hcop

/-- One original common-ideal row, with all ideal divisor coefficients,
Hecke phases and nonzero frequencies retained. -/
noncomputable def originalSignedCommonOuterRow
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (σ : RayRing) (F : Finset SupportedIdeal)
    (E : SupportedIdeal → Finset GramFrequency)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0 < Y)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) (C : SupportedIdeal) : ℂ :=
  ((Q / Y^3 : ℝ) : ℂ) *
    ∑ D ∈ sourceDivisorUnion F W hW Y hY,
      sourceMobiusWeight W hW Y hY C D *
        ∑ k ∈ E C,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}) : ℝ) /
              ((Y^2/Q) / gramIdealNorm C))
            (Y / (gramIdealNorm C * gramIdealNorm D))

/-- Exactly the full original signed source, before triangle. -/
theorem original_source_eq_signed_common_rows
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (σ : RayRing) (F : Finset SupportedIdeal)
    (E : SupportedIdeal → Finset GramFrequency)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0 < Y)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceCanonicalSum S hS σ F E W hW Y Q hY U v =
      ∑ C ∈ F, originalSignedCommonOuterRow S hS σ F E W hW Y Q hY U v C := by
  unfold sourceCanonicalSum originalSignedCommonOuterRow
  rw [Finset.mul_sum]

/-- Complete original signed Hermitian Gram. All diagonal and offdiagonal
pairs of common ideals are present, with their entire divisor/frequency
subrows and original Möbius signs. -/
theorem original_source_signed_hermitian_gram
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (σ : RayRing) (F : Finset SupportedIdeal)
    (E : SupportedIdeal → Finset GramFrequency)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0 < Y)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    ‖sourceCanonicalSum S hS σ F E W hW Y Q hY U v‖^2 =
      ∑ C ∈ F, ∑ C' ∈ F,
        (originalSignedCommonOuterRow S hS σ F E W hW Y Q hY U v C *
          star (originalSignedCommonOuterRow S hS σ F E W hW Y Q hY U v C')).re := by
  rw [original_source_eq_signed_common_rows]
  have hn (z : ℂ) : ‖z‖^2 = (z * star z).re := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re]
  rw [hn, star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [Complex.re_sum]

/-- Complete ORIGINAL source in native two-real NNS Co minus Div,
with no synthetic coefficients, no dropped physical rows and no energy
majorization. This is before the exceptional P^(1/6) estimate. -/
theorem original_source_signed_nns_codiv
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (σ : RayRing) (F : Finset SupportedIdeal)
    (E : SupportedIdeal → Finset GramFrequency)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0 < Y)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    let a := originalSignedCommonOuterRow S hS σ F E W hW Y Q hY U v
    ‖sourceCanonicalSum S hS σ F E W hW Y Q hY U v‖^2 =
      ((zeroTargetCoPartialGram F
          (fun C => (stableFarComplexToRealPair (a C)).1) +
        zeroTargetCoPartialGram F
          (fun C => (stableFarComplexToRealPair (a C)).2)) -
       (zeroTargetDivergentGram F
          (fun C => (stableFarComplexToRealPair (a C)).1) +
        zeroTargetDivergentGram F
          (fun C => (stableFarComplexToRealPair (a C)).2))) / 2 := by
  dsimp only
  rw [original_source_eq_signed_common_rows]
  exact vf919FiniteSource_normSq_eq_NNS F
    (originalSignedCommonOuterRow S hS σ F E W hW Y Q hY U v)

/-- Specialization to the literal SIXTH-POWER exceptional-frequency branch
that incurs the binding P^(1/6) loss. -/
theorem original_exceptional_source_signed_nns
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (σ : RayRing) (F : Finset SupportedIdeal)
    (E : Finset GramFrequency)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0 < Y)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    let a := originalSignedCommonOuterRow S hS σ F
      (exceptionalFrequencies S hS E) W hW Y Q hY U v
    ‖sourceCanonicalSum S hS σ F
       (exceptionalFrequencies S hS E) W hW Y Q hY U v‖^2 =
      ((zeroTargetCoPartialGram F
          (fun C => (stableFarComplexToRealPair (a C)).1) +
        zeroTargetCoPartialGram F
          (fun C => (stableFarComplexToRealPair (a C)).2)) -
       (zeroTargetDivergentGram F
          (fun C => (stableFarComplexToRealPair (a C)).1) +
        zeroTargetDivergentGram F
          (fun C => (stableFarComplexToRealPair (a C)).2))) / 2 := by
  exact original_source_signed_nns_codiv S hS σ F
    (exceptionalFrequencies S hS E) W hW Y Q hY U v

/-- No source rewriting: the exact original nonzero truncation itself. -/
theorem original_truncation_signed_nns
    (S : Finset Id) (hS : ∀ p ∈ S, p.IsMaximal)
    (hbad : fixedBadPrimes ⊆ S)
    (σ : RayRing) (F : Finset SupportedIdeal)
    (E : Finset GramFrequency)
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0 < Y) (hQ : 0 < Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    let a := originalSignedCommonOuterRow S hS σ F
      (fun _ => E) W hW Y Q hY U v
    ‖sourceTruncation S hS σ F E W hW Y Q hY U v‖^2 =
      ((zeroTargetCoPartialGram F
          (fun C => (stableFarComplexToRealPair (a C)).1) +
        zeroTargetCoPartialGram F
          (fun C => (stableFarComplexToRealPair (a C)).2)) -
       (zeroTargetDivergentGram F
          (fun C => (stableFarComplexToRealPair (a C)).1) +
        zeroTargetDivergentGram F
          (fun C => (stableFarComplexToRealPair (a C)).2))) / 2 := by
  dsimp only
  rw [sourceTruncation_eq_canonical S hS hbad σ F E W hW Y Q hY hQ U v]
  exact original_source_signed_nns_codiv S hS σ F
    (fun _ => E) W hW Y Q hY U v

#print axioms original_primary_fifth_seed_clears_column
#print axioms original_primary_fifth_sixth_tower_clears_column
#print axioms original_source_signed_hermitian_gram
#print axioms original_source_signed_nns_codiv
#print axioms original_exceptional_source_signed_nns
#print axioms original_truncation_signed_nns

end SevenEighths.ProbeGramCommon
end
end OAI
