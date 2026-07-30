import Mathlib
import RHLean.Analysis.PrimeWheelDirichletResponse
import RHLean.Analysis.PrimeWheelJointSpectrum

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Squared Euclidean energy of one complex spectral coefficient. -/
def primeWheelSpectralEnergy (z : ℂ) : ℝ :=
  RCLike.normSq z

/-- Real raw/core alignment, equal to `Re (alpha * conj gamma)`. -/
def primeWheelSpectralAlignment (alpha gamma : ℂ) : ℝ :=
  (alpha * conj gamma).re

/-- Exact raw-minus-twice-core square.  The negative cross term means that
small corrected energy requires positive raw/core alignment. -/
theorem primeWheelSpectralEnergy_sub_two
    (alpha gamma : ℂ) :
    primeWheelSpectralEnergy (alpha - 2 * gamma) =
      primeWheelSpectralEnergy alpha +
        4 * primeWheelSpectralEnergy gamma -
          4 * primeWheelSpectralAlignment alpha gamma := by
  unfold primeWheelSpectralEnergy primeWheelSpectralAlignment
  simp [RCLike.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Energy is unchanged by multiplication by a unit-energy phase. -/
theorem primeWheelSpectralEnergy_mul_of_energy_eq_one
    (u z : ℂ) (hu : primeWheelSpectralEnergy u = 1) :
    primeWheelSpectralEnergy (u * z) = primeWheelSpectralEnergy z := by
  unfold primeWheelSpectralEnergy at hu ⊢
  rw [RCLike.normSq_mul, hu, one_mul]

/-- The pinned arithmetic phase has norm one. -/
theorem primeWheelPinnedPhase_norm
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    ‖primeWheelPinnedPhase W r‖ = 1 := by
  unfold primeWheelPinnedPhase
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Hence the pinned arithmetic phase has coefficient energy one. -/
theorem primeWheelPinnedPhase_energy
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    primeWheelSpectralEnergy (primeWheelPinnedPhase W r) = 1 := by
  unfold primeWheelSpectralEnergy
  rw [RCLike.normSq_eq_def', primeWheelPinnedPhase_norm]
  norm_num

/-- Raw-minus-twice-core coefficient carrying the common pinned phase. -/
def primeWheelPinnedRawCoreCoefficient
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) : ℂ :=
  primeWheelPinnedPhase W r *
    (W.rawBlockSpectrum r - 2 * W.smoothCoreBlockSpectrum r)

/-- The common pinned phase disappears completely from coefficientwise energy. -/
theorem pinnedRawCoreCoefficient_energy_eq
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    primeWheelSpectralEnergy (primeWheelPinnedRawCoreCoefficient W r) =
      primeWheelSpectralEnergy
        (W.rawBlockSpectrum r - 2 * W.smoothCoreBlockSpectrum r) := by
  unfold primeWheelPinnedRawCoreCoefficient
  exact primeWheelSpectralEnergy_mul_of_energy_eq_one _ _
    (primeWheelPinnedPhase_energy W r)

/-- Exact coefficientwise raw/core square after the pinned phase has cancelled. -/
theorem pinnedRawCoreCoefficient_energy_expansion
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    primeWheelSpectralEnergy (primeWheelPinnedRawCoreCoefficient W r) =
      primeWheelSpectralEnergy (W.rawBlockSpectrum r) +
        4 * primeWheelSpectralEnergy (W.smoothCoreBlockSpectrum r) -
          4 * primeWheelSpectralAlignment
            (W.rawBlockSpectrum r) (W.smoothCoreBlockSpectrum r) := by
  rw [pinnedRawCoreCoefficient_energy_eq]
  exact primeWheelSpectralEnergy_sub_two _ _

/-- Raw energy in an arbitrary finite frequency packet. -/
def primeWheelRawBandEnergy {ι : Type*}
    (B : Finset ι) (alpha : ι → ℂ) : ℝ :=
  ∑ r in B, primeWheelSpectralEnergy (alpha r)

/-- Smooth-core energy in an arbitrary finite frequency packet. -/
def primeWheelCoreBandEnergy {ι : Type*}
    (B : Finset ι) (gamma : ι → ℂ) : ℝ :=
  ∑ r in B, primeWheelSpectralEnergy (gamma r)

/-- Real raw/core correlation in an arbitrary finite frequency packet. -/
def primeWheelRawCoreBandCorrelation {ι : Type*}
    (B : Finset ι) (alpha gamma : ι → ℂ) : ℝ :=
  ∑ r in B, primeWheelSpectralAlignment (alpha r) (gamma r)

/-- Corrected raw-minus-twice-core energy in a finite frequency packet. -/
def primeWheelCorrectedBandEnergy {ι : Type*}
    (B : Finset ι) (alpha gamma : ι → ℂ) : ℝ :=
  ∑ r in B, primeWheelSpectralEnergy (alpha r - 2 * gamma r)

/-- Exact bandwise energy identity `J = A + 4 C - 4 X`. -/
theorem primeWheelCorrectedBandEnergy_eq
    {ι : Type*} (B : Finset ι) (alpha gamma : ι → ℂ) :
    primeWheelCorrectedBandEnergy B alpha gamma =
      primeWheelRawBandEnergy B alpha +
        4 * primeWheelCoreBandEnergy B gamma -
          4 * primeWheelRawCoreBandCorrelation B alpha gamma := by
  unfold primeWheelCorrectedBandEnergy primeWheelRawBandEnergy
    primeWheelCoreBandEnergy primeWheelRawCoreBandCorrelation
  calc
    (∑ r in B, primeWheelSpectralEnergy (alpha r - 2 * gamma r)) =
        ∑ r in B,
          (primeWheelSpectralEnergy (alpha r) +
            4 * primeWheelSpectralEnergy (gamma r) -
              4 * primeWheelSpectralAlignment (alpha r) (gamma r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact primeWheelSpectralEnergy_sub_two _ _
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]

/-- Raw packet energy is nonnegative. -/
theorem primeWheelRawBandEnergy_nonneg
    {ι : Type*} (B : Finset ι) (alpha : ι → ℂ) :
    0 ≤ primeWheelRawBandEnergy B alpha := by
  unfold primeWheelRawBandEnergy primeWheelSpectralEnergy
  exact Finset.sum_nonneg fun r hr => RCLike.normSq_nonneg _

/-- Core packet energy is nonnegative. -/
theorem primeWheelCoreBandEnergy_nonneg
    {ι : Type*} (B : Finset ι) (gamma : ι → ℂ) :
    0 ≤ primeWheelCoreBandEnergy B gamma := by
  unfold primeWheelCoreBandEnergy primeWheelSpectralEnergy
  exact Finset.sum_nonneg fun r hr => RCLike.normSq_nonneg _

/-- Failure of quarter-energy matching in one packet. -/
def primeWheelBandEnergyMismatch {ι : Type*}
    (B : Finset ι) (alpha gamma : ι → ℂ) : ℝ :=
  (Real.sqrt (primeWheelRawBandEnergy B alpha) -
      2 * Real.sqrt (primeWheelCoreBandEnergy B gamma)) ^ 2

/-- Failure of maximal positive raw/core coherence in one packet. -/
def primeWheelBandCoherenceDefect {ι : Type*}
    (B : Finset ι) (alpha gamma : ι → ℂ) : ℝ :=
  4 *
    (Real.sqrt (primeWheelRawBandEnergy B alpha) *
        Real.sqrt (primeWheelCoreBandEnergy B gamma) -
      primeWheelRawCoreBandCorrelation B alpha gamma)

/-- Exact two-defect decomposition of the corrected band energy. -/
theorem primeWheelCorrectedBandEnergy_eq_mismatch_add_coherenceDefect
    {ι : Type*} (B : Finset ι) (alpha gamma : ι → ℂ) :
    primeWheelCorrectedBandEnergy B alpha gamma =
      primeWheelBandEnergyMismatch B alpha gamma +
        primeWheelBandCoherenceDefect B alpha gamma := by
  rw [primeWheelCorrectedBandEnergy_eq]
  unfold primeWheelBandEnergyMismatch primeWheelBandCoherenceDefect
  have hA := primeWheelRawBandEnergy_nonneg B alpha
  have hC := primeWheelCoreBandEnergy_nonneg B gamma
  rw [← Real.sq_sqrt hA, ← Real.sq_sqrt hC]
  ring

/-- The energy-matching defect is always nonnegative. -/
theorem primeWheelBandEnergyMismatch_nonneg
    {ι : Type*} (B : Finset ι) (alpha gamma : ι → ℂ) :
    0 ≤ primeWheelBandEnergyMismatch B alpha gamma := by
  unfold primeWheelBandEnergyMismatch
  positivity

/-- Cauchy--Schwarz control of the correlation makes the coherence defect
nonnegative.  The finite Cauchy--Schwarz estimate can be supplied separately. -/
theorem primeWheelBandCoherenceDefect_nonneg_of_correlation_le
    {ι : Type*} (B : Finset ι) (alpha gamma : ι → ℂ)
    (hCS : primeWheelRawCoreBandCorrelation B alpha gamma ≤
      Real.sqrt (primeWheelRawBandEnergy B alpha) *
        Real.sqrt (primeWheelCoreBandEnergy B gamma)) :
    0 ≤ primeWheelBandCoherenceDefect B alpha gamma := by
  unfold primeWheelBandCoherenceDefect
  positivity

/-- A separate bound for each defect gives the desired corrected packet bound. -/
theorem primeWheelCorrectedBandEnergy_le_of_defect_bounds
    {ι : Type*} (B : Finset ι) (alpha gamma : ι → ℂ)
    (DeltaEnergy DeltaCoherence : ℝ)
    (hEnergy : primeWheelBandEnergyMismatch B alpha gamma ≤ DeltaEnergy)
    (hCoherence : primeWheelBandCoherenceDefect B alpha gamma ≤ DeltaCoherence) :
    primeWheelCorrectedBandEnergy B alpha gamma ≤
      DeltaEnergy + DeltaCoherence := by
  rw [primeWheelCorrectedBandEnergy_eq_mismatch_add_coherenceDefect]
  linarith

/-- The phase pair that survives in a full frequency-frequency Gram entry. -/
def primeWheelPinnedPhasePair
    (W : PrimeWheelFiniteSystem) (r s : ZMod W.modulus) : ℂ :=
  primeWheelPinnedPhase W r * conj (primeWheelPinnedPhase W s)

/-- On the diagonal the phase pair is one; only off-diagonal entries can retain
information about the pinned origin. -/
theorem primeWheelPinnedPhasePair_self
    (W : PrimeWheelFiniteSystem) (r : ZMod W.modulus) :
    primeWheelPinnedPhasePair W r r = 1 := by
  unfold primeWheelPinnedPhasePair primeWheelPinnedPhase
  rw [ZMod.stdAddChar_apply]
  rw [← Circle.coe_inv_eq_conj]
  simp

/-- One explicitly raw/core, phase-sensitive Dirichlet atom. -/
def primeWheelPinnedRawCoreDirichletAtom
    (W : PrimeWheelFiniteSystem) (N : ℕ) (r : ZMod W.modulus) : ℂ :=
  ((W.modulus : ℂ)⁻¹) *
    primeWheelPinnedRawCoreCoefficient W r *
      primeWheelDirichletKernel W N r

/-- The exact Dirichlet prefix is the sum of the raw/core atoms. -/
theorem primeWheelDirichletPrefix_eq_sum_pinnedRawCoreAtoms
    (W : PrimeWheelFiniteSystem) (N : ℕ) :
    primeWheelDirichletPrefix W N =
      ∑ r : ZMod W.modulus,
        primeWheelPinnedRawCoreDirichletAtom W N r := by
  unfold primeWheelDirichletPrefix primeWheelPinnedCoefficient
    primeWheelPinnedRawCoreDirichletAtom primeWheelPinnedRawCoreCoefficient
  apply Finset.sum_congr rfl
  intro r hr
  rw [W.jointSpectrum_eq_raw_sub_two_smooth]
  ring

/-- Complete phase-sensitive frequency-frequency Gram entry. -/
def primeWheelPinnedRawCoreGramEntry
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r s : ZMod W.modulus) : ℂ :=
  primeWheelPinnedRawCoreDirichletAtom W N r *
    conj (primeWheelPinnedRawCoreDirichletAtom W N s)

/-- Exact expansion exposing the surviving off-diagonal pinned phase pair. -/
theorem primeWheelPinnedRawCoreGramEntry_eq_phasePair
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r s : ZMod W.modulus) :
    primeWheelPinnedRawCoreGramEntry W N r s =
      (((W.modulus : ℂ)⁻¹) * conj ((W.modulus : ℂ)⁻¹)) *
        primeWheelPinnedPhasePair W r s *
        ((W.rawBlockSpectrum r - 2 * W.smoothCoreBlockSpectrum r) *
          conj (W.rawBlockSpectrum s - 2 * W.smoothCoreBlockSpectrum s)) *
        (primeWheelDirichletKernel W N r *
          conj (primeWheelDirichletKernel W N s)) := by
  unfold primeWheelPinnedRawCoreGramEntry
    primeWheelPinnedRawCoreDirichletAtom
    primeWheelPinnedRawCoreCoefficient primeWheelPinnedPhasePair
  simp only [map_mul]
  ring

/-- Full signed raw/core Gram energy; all off-diagonal phase-sensitive terms
are retained. -/
def primeWheelPinnedRawCoreGramEnergy
    (W : PrimeWheelFiniteSystem) (N : ℕ) : ℂ :=
  ∑ r : ZMod W.modulus,
    ∑ s : ZMod W.modulus, primeWheelPinnedRawCoreGramEntry W N r s

/-- The complete raw/core Gram is exactly the square of the full Dirichlet sum. -/
theorem primeWheelPinnedRawCoreGramEnergy_eq_mul_conj
    (W : PrimeWheelFiniteSystem) (N : ℕ) :
    primeWheelPinnedRawCoreGramEnergy W N =
      primeWheelDirichletPrefix W N * conj (primeWheelDirichletPrefix W N) := by
  rw [primeWheelDirichletPrefix_eq_sum_pinnedRawCoreAtoms, map_sum]
  unfold primeWheelPinnedRawCoreGramEnergy primeWheelPinnedRawCoreGramEntry
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]

end RHLean.Analysis
