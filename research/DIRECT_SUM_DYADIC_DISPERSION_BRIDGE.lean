import Mathlib
import RHLean.Analysis.PrimeSieveDyadicCoherentAbel
import RHLean.Proof.FarSurvivorRenewal_is_LowerMertens
import RHLean.Proof.TerminalMertensReduction

/-!
# Direct-sum dyadic dispersion bridge

This file records only the deterministic reduction suggested by Diagnostics D--G.
It does **not** prove a dispersion estimate.

The high channel is the existing reciprocal-quotient dyadic PNT-error channel.
The low channel is the freshness-restricted physical prime-error channel on
`2 <= n <= R`.  They are kept in a formal direct sum at the energy level, while
the scalar coherent and wavelet outputs are added before squaring.

There is one important honesty constraint.  An `X^epsilon` dispersion estimate
by itself does not imply the fixed-coefficient FAR-4 inequality.  One still needs
an absorption statement relating the direct-sum coefficient energies and the
exact reconstruction remainder to the existing `4 * Q_R + C R^2 K` budget.
That missing step is therefore named explicitly below rather than hidden in the
dispersion predicate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## High reciprocal channel -/

/-- Existing high-channel coherent scalar at the complete square endpoint. -/
def directSumHighCoherent (R : ℕ) : ℂ :=
  primeSieveDyadicCoherentPNTError R (squareRootEndpoint R)

/-- Existing high-channel mean-zero wavelet scalar at the complete square endpoint. -/
def directSumHighWavelet (R : ℕ) : ℂ :=
  primeSieveDyadicWaveletPNTError R (squareRootEndpoint R)

/-- Existing high-channel boundary-free Abel-potential energy. -/
def directSumHighWaveletEnergy (R : ℕ) : ℝ :=
  primeSieveDyadicAbelPotentialEnergy R (squareRootEndpoint R)

/-- Diagonal `L2` energy of the coherent high-channel dyadic summands. -/
def directSumHighCoherentEnergy (R : ℕ) : ℝ :=
  ∑ d ∈ primeSieveQuotientSupport R (squareRootEndpoint R),
    ‖primeSieveDyadicBlockMean R (squareRootEndpoint R)
        (primeSieveDyadicIndex d) * mertensSummatory d‖ ^ 2

/-! ## Low freshness channel -/

/-- Singleton prime-error atom, using the repository's exact Li increment. -/
def directSumLowPrimeErrorAtom (n : ℕ) : ℂ :=
  primeSievePrimeIndicator n - primeSievePNTDensity n

/-- Exact freshness-restricted shell seen by a low prime coordinate `n <= R`. -/
def directSumLowFreshnessShell (R n : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
    if canonicalLargestPrimeFactor c < n ∧
        R ≤ c * n ∧ c * n ≤ squareRootEndpoint R then
      canonicalMoebiusWeight c
    else
      0

/-- Low-channel PNT-error scalar before dyadic centering. -/
def directSumLowPNTError (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 R,
    directSumLowPrimeErrorAtom n * directSumLowFreshnessShell R n

/-- Physical dyadic block on the low prime coordinate. -/
def directSumLowDyadicBlock (R j : ℕ) : Finset ℕ :=
  (Finset.Icc 2 R).filter fun n => primeSieveDyadicIndex n = j

/-- Occupied low-channel dyadic labels. -/
def directSumLowDyadicBlockIndices (R : ℕ) : Finset ℕ :=
  (Finset.Icc 2 R).image primeSieveDyadicIndex

/-- Literal mean prime-error atom on one occupied low dyadic block. -/
def directSumLowDyadicBlockMean (R j : ℕ) : ℂ :=
  (((directSumLowDyadicBlock R j).card : ℂ)⁻¹) *
    ∑ n ∈ directSumLowDyadicBlock R j, directSumLowPrimeErrorAtom n

/-- Mean-zero low-channel prime-error atom. -/
def directSumLowWaveletAtom (R n : ℕ) : ℂ :=
  directSumLowPrimeErrorAtom n -
    directSumLowDyadicBlockMean R (primeSieveDyadicIndex n)

/-- Coherent low-channel scalar. -/
def directSumLowCoherent (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 R,
    directSumLowDyadicBlockMean R (primeSieveDyadicIndex n) *
      directSumLowFreshnessShell R n

/-- Mean-zero low-channel wavelet scalar. -/
def directSumLowWavelet (R : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 R,
    directSumLowWaveletAtom R n * directSumLowFreshnessShell R n

/-- Exact low-channel coherent/wavelet split.  This is finite algebra only. -/
theorem directSumLowPNTError_eq_coherent_add_wavelet (R : ℕ) :
    directSumLowPNTError R =
      directSumLowCoherent R + directSumLowWavelet R := by
  unfold directSumLowPNTError directSumLowCoherent directSumLowWavelet
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold directSumLowWaveletAtom directSumLowPrimeErrorAtom
  ring

/-- Negative prefix potential of one low-channel dyadic wavelet block. -/
def directSumLowBlockAbelPotential (R j n : ℕ) : ℂ :=
  -∑ t ∈ directSumLowDyadicBlock R j,
    if t < n then directSumLowWaveletAtom R t else 0

/-- Direct-sum low-channel Abel-potential energy. -/
def directSumLowWaveletEnergy (R : ℕ) : ℝ :=
  ∑ j ∈ directSumLowDyadicBlockIndices R,
    ∑ n ∈ directSumLowDyadicBlock R j,
      ‖directSumLowBlockAbelPotential R j n‖ ^ 2

/-- Diagonal `L2` energy of the coherent low-channel summands. -/
def directSumLowCoherentEnergy (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 R,
    ‖directSumLowDyadicBlockMean R (primeSieveDyadicIndex n) *
        directSumLowFreshnessShell R n‖ ^ 2

/-! ## Coupled scalar / direct-sum energy package -/

/-- Scalar wavelets are added before any norm is taken. -/
def directSumDyadicWavelet (R : ℕ) : ℂ :=
  directSumHighWavelet R + directSumLowWavelet R

/-- Scalar coherent channels are added before any norm is taken. -/
def directSumDyadicCoherent (R : ℕ) : ℂ :=
  directSumHighCoherent R + directSumLowCoherent R

/-- Honest direct-sum wavelet energy: no artificial cross inner product is inserted. -/
def directSumDyadicWaveletEnergy (R : ℕ) : ℝ :=
  directSumHighWaveletEnergy R + directSumLowWaveletEnergy R

/-- Honest direct-sum coherent energy. -/
def directSumDyadicCoherentEnergy (R : ℕ) : ℝ :=
  directSumHighCoherentEnergy R + directSumLowCoherentEnergy R

/-- Exact high+low PNT-error decomposition at the scalar level. -/
theorem directSumPNTError_eq_coherent_add_wavelet (R : ℕ) :
    primeSievePNTError R (squareRootEndpoint R) + directSumLowPNTError R =
      directSumDyadicCoherent R + directSumDyadicWavelet R := by
  rw [primeSievePNTError_eq_dyadicCoherent_add_wavelet,
    directSumLowPNTError_eq_coherent_add_wavelet]
  unfold directSumDyadicCoherent directSumDyadicWavelet
    directSumHighCoherent directSumHighWavelet
  ring

/-- Exact remainder needed to reconstruct the compiled FAR residual from the
coupled direct-sum scalar channels.  Naming it makes the deterministic gap
explicit instead of silently treating PNT centering as the whole FAR carrier. -/
def directSumDyadicFarRemainder (R : ℕ) : ℂ :=
  lowWheelFrozenTopFarResidual R -
    (directSumDyadicWavelet R + directSumDyadicCoherent R)

/-- Exact scalar reconstruction, by definition of the named remainder. -/
theorem directSumDyadicFar_reconstruction (R : ℕ) :
    lowWheelFrozenTopFarResidual R =
      directSumDyadicWavelet R + directSumDyadicCoherent R +
        directSumDyadicFarRemainder R := by
  unfold directSumDyadicFarRemainder
  ring

/-- The empirical Type-II target.  It is intentionally only a proposition:
no dispersion estimate is asserted or proved in this file. -/
def DirectSumDyadicDispersionBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 56 ≤ R →
        ‖directSumDyadicWavelet R‖ ^ 2 ≤
            C * Real.rpow (squareRootEndpoint R : ℝ) ε *
              directSumDyadicWaveletEnergy R ∧
          ‖directSumDyadicCoherent R‖ ^ 2 ≤
            C * Real.rpow (squareRootEndpoint R : ℝ) ε *
              directSumDyadicCoherentEnergy R

/-- Missing fixed-scale absorption needed to turn `X^epsilon` dispersion into
FAR-4.  This is kept separate from dispersion because the current kernel has no
theorem bounding these direct-sum energies by the literal q^2 daughter budget
with the required fixed factor four. -/
def DirectSumDyadicFarFourBudgetStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 ≤ D →
    ∃ CF : ℝ, 0 ≤ CF ∧
      ∀ R : ℕ, ∀ K : ℝ,
        56 ≤ R →
        LowerMertensCriticalEnvelope R K →
        3 * (D * Real.rpow (squareRootEndpoint R : ℝ) ε *
              (directSumDyadicWaveletEnergy R +
                directSumDyadicCoherentEnergy R) +
            ‖directSumDyadicFarRemainder R‖ ^ 2) ≤
          4 * farFourOddQ2DaughterEnergy R +
            CF * (R : ℝ) ^ 2 * K

private theorem norm_three_sum_sq_le_three_sum_sq (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤
      3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have hab : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have habc : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le (a + b) c
  have htri : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    linarith
  have hsum0 : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by positivity
  have hsq :
      ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum0).2 htri
  have hcauchy :
      (‖a‖ + ‖b‖ + ‖c‖) ^ 2 ≤
        3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖),
      sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖c‖ - ‖a‖)]
  exact hsq.trans hcauchy

/-- **Deterministic FAR-4 bridge.**

The direct-sum dispersion hypothesis supplies the two scalar estimates.  The
separate budget hypothesis is exactly the still-missing absorption of their
coefficient energies (plus the exact reconstruction remainder) into the
compiled factor-four q^2 daughter budget.  No instance of either analytic
hypothesis is constructed here. -/
theorem farFour_of_directSumDispersion
    (hD : DirectSumDyadicDispersionBoundedStatement)
    (hB : DirectSumDyadicFarFourBudgetStatement) :
    FrozenTopFarFourEnergyStatement := by
  have hε : (0 : ℝ) < 1 := by norm_num
  obtain ⟨D, hD0, hDb⟩ := hD 1 hε
  obtain ⟨CF, hCF, hBb⟩ := hB 1 hε D hD0
  refine ⟨CF, hCF, ?_⟩
  intro R K hR hK
  have hdisp := hDb R hR
  have hbudget := hBb R K hR hK
  rw [directSumDyadicFar_reconstruction R]
  have hthree :=
    norm_three_sum_sq_le_three_sum_sq
      (directSumDyadicWavelet R)
      (directSumDyadicCoherent R)
      (directSumDyadicFarRemainder R)
  have hpair :
      ‖directSumDyadicWavelet R‖ ^ 2 +
          ‖directSumDyadicCoherent R‖ ^ 2 ≤
        D * Real.rpow (squareRootEndpoint R : ℝ) 1 *
          (directSumDyadicWaveletEnergy R +
            directSumDyadicCoherentEnergy R) := by
    nlinarith [hdisp.1, hdisp.2]
  calc
    ‖directSumDyadicWavelet R + directSumDyadicCoherent R +
        directSumDyadicFarRemainder R‖ ^ 2 ≤
      3 * (‖directSumDyadicWavelet R‖ ^ 2 +
        ‖directSumDyadicCoherent R‖ ^ 2 +
        ‖directSumDyadicFarRemainder R‖ ^ 2) := hthree
    _ ≤ 3 * (D * Real.rpow (squareRootEndpoint R : ℝ) 1 *
          (directSumDyadicWaveletEnergy R +
            directSumDyadicCoherentEnergy R) +
        ‖directSumDyadicFarRemainder R‖ ^ 2) := by
      nlinarith
    _ ≤ 4 * farFourOddQ2DaughterEnergy R +
        CF * (R : ℝ) ^ 2 * K := hbudget

end RHLean.Proof
