import Mathlib
import «research.STABLE_FAR_PERRON_REALIFICATION»
import «research.VF_MID_919_OAI_PARTIAL_MOMENT_TAILS»

/-!
# Real NNS version of OAI's actual refined marked fourth-moment rows

OAI actual source: Detector/DetectorPlainMarkedFineField.lean:
  sum_{u in F.rows} ‖P_j(u) * P_k(u) * F.physicalProduct selected u‖^2
    <= C * (1+height)^J * (Z^d)^(1+D.t), for j+k<=2,
    selected slots satisfying 2*F.m+6*(3/4+2*Delta)*sum widths<=1.

The carrier remains exactly F.rows and the original selected masked physical
product. This file is an unconditional algebraic REAL NNS representation of
that very row integrand, not a new bound on the Hecke family.

The j=k=0 row is a genuine fourth moment of P_0, weighted by
‖physicalProduct‖^2. All weights are unnormalized; no independent samples
or probabilistic covariance axioms are introduced.

The original OAI proof also has the precise pre-relaxation exponent
1+D.t/2 (state.width=1+D.t/4, stageError=D.t/4), rather than its
published 1+D.t; this exact exponent calculation is recorded below.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis
open RHLean.Proof

/-- Phi preserves the whole Hecke character phase, unlike Re(z^2). -/
def vf919MarkedRealEnergy (z : ℂ) : ℝ :=
  let v := stableFarComplexToRealPair z
  (v.1 ^ 2 + v.2 ^ 2) / 2

theorem vf919MarkedRealEnergy_eq_normSq (z : ℂ) :
    vf919MarkedRealEnergy z = ‖z‖ ^ 2 := by
  simpa [vf919MarkedRealEnergy, stableFarRealPairNormalizedEnergy,
    stableFarRealPairEnergy] using
    stableFarRealPairNormalizedEnergy_complexToRealPair z

/-- The actual two-polynomial, selected-product plain marked integrand.
`physical` can be the LITERAL `F.physicalProduct selected u` from OAI,
and `Pj`, `Pk` its literal derivative-profile polynomials. -/
def vf919ActualMarkedIntegrand
    {ι : Type*} (Pj Pk physical : ι → ℂ) (u : ι) : ℝ :=
  ‖Pj u * Pk u * physical u‖ ^ 2

/-- Exactly three real NNS energies, no magnitude-first split of the
marked source and no modification of the original slot mask. -/
theorem vf919ActualMarkedIntegrand_eq_realEnergies
    {ι : Type*} (Pj Pk physical : ι → ℂ) (u : ι) :
    vf919ActualMarkedIntegrand Pj Pk physical u =
      vf919MarkedRealEnergy (Pj u) *
        vf919MarkedRealEnergy (Pk u) *
        vf919MarkedRealEnergy (physical u) := by
  simp only [vf919ActualMarkedIntegrand, vf919MarkedRealEnergy_eq_normSq,
    norm_mul]
  ring

/-- Full actual row index set is unchanged. F.rows is substituted for `rows`
without equality-of-sample-size or independence assumptions. -/
theorem vf919ActualMarkedMoment_eq_realEnergies
    {ι : Type*} (rows : Finset ι) (Pj Pk physical : ι → ℂ) :
    (∑ u ∈ rows, vf919ActualMarkedIntegrand Pj Pk physical u) =
      ∑ u ∈ rows,
        vf919MarkedRealEnergy (Pj u) *
          vf919MarkedRealEnergy (Pk u) *
          vf919MarkedRealEnergy (physical u) := by
  apply Finset.sum_congr rfl
  intro u _
  exact vf919ActualMarkedIntegrand_eq_realEnergies Pj Pk physical u

/-- Unnormalized degree-four NNS UPM/LPM at target zero. -/
def vf919NNSPartialFourth (x : ℝ) : ℝ :=
  (partialUpper x 0) ^ 4 + (partialLower x 0) ^ 4

theorem vf919NNSPartialFourth_eq_pow (x : ℝ) :
    vf919NNSPartialFourth x = x ^ 4 := by
  unfold vf919NNSPartialFourth
  by_cases hx : 0 ≤ x
  · simp [partialUpper, partialLower, hx, not_lt_of_ge hx]
  · have hlt : x < 0 := lt_of_not_ge hx
    simp [partialUpper, partialLower, hx, hlt]; ring

/-- Four unnormalized NNS directional 2-by-2 quadrants. -/
def vf919NNSQuadrant22 (x y : ℝ) : ℝ :=
  (partialUpper x 0) ^ 2 * (partialUpper y 0) ^ 2 +
  (partialUpper x 0) ^ 2 * (partialLower y 0) ^ 2 +
  (partialLower x 0) ^ 2 * (partialUpper y 0) ^ 2 +
  (partialLower x 0) ^ 2 * (partialLower y 0) ^ 2

theorem vf919NNSQuadrant22_eq (x y : ℝ) :
    vf919NNSQuadrant22 x y = x ^ 2 * y ^ 2 := by
  have hx := vf919RowPartialSquare_reassembly x 0
  have hy := vf919RowPartialSquare_reassembly y 0
  unfold vf919NNSQuadrant22
  calc
    _ = ((partialUpper x 0)^2 + (partialLower x 0)^2) *
        ((partialUpper y 0)^2 + (partialLower y 0)^2) := by ring
    _ = x^2 * y^2 := by rw [hx, hy]; simp only [sub_zero]

/-- Full row quartic, retaining ALL four mixed physical quadrants. -/
def vf919MarkedFourthNNS (z : ℂ) : ℝ :=
  let v := stableFarComplexToRealPair z
  (vf919NNSPartialFourth v.1 +
     2 * vf919NNSQuadrant22 v.1 v.2 +
     vf919NNSPartialFourth v.2) / 4

theorem vf919MarkedFourthNNS_eq_normFourth (z : ℂ) :
    vf919MarkedFourthNNS z = ‖z‖ ^ 4 := by
  have he := vf919MarkedRealEnergy_eq_normSq z
  unfold vf919MarkedFourthNNS
  dsimp only
  rw [vf919NNSPartialFourth_eq_pow,
      vf919NNSQuadrant22_eq, vf919NNSPartialFourth_eq_pow]
  unfold vf919MarkedRealEnergy at he
  dsimp only at he
  calc
    _ = (((stableFarComplexToRealPair z).1 ^ 2 +
        (stableFarComplexToRealPair z).2 ^ 2) / 2) ^ 2 := by ring
    _ = (‖z‖ ^ 2) ^ 2 := by rw [he]
    _ = ‖z‖ ^ 4 := by ring

/-- The j=k=0 case of the ACTUAL marked input is a genuine quartic
partial-moment identity, weighted by its unchanged physicalProduct.
No division by the number of rows or by the total mass. -/
theorem vf919ActualMarkedFourth_eq_unnormalizedNNS
    {ι : Type*} (rows : Finset ι) (P physical : ι → ℂ) :
    (∑ u ∈ rows, ‖P u * P u * physical u‖ ^ 2) =
      ∑ u ∈ rows, ‖physical u‖ ^ 2 * vf919MarkedFourthNNS (P u) := by
  apply Finset.sum_congr rfl
  intro u _
  rw [vf919MarkedFourthNNS_eq_normFourth]
  simp only [norm_mul]
  ring

/-- An existing OAI marked-moment estimate transfers WITHOUT LOSS to its
unnormalized real-NNS form, for the exact same rows and source mask. -/
theorem vf919ActualMarkedBound_to_realNNS
    {ι : Type*} (rows : Finset ι) (Pj Pk physical : ι → ℂ)
    (budget : ℝ)
    (hOAI : (∑ u ∈ rows, ‖Pj u * Pk u * physical u‖ ^ 2) ≤ budget) :
    (∑ u ∈ rows,
      vf919MarkedRealEnergy (Pj u) *
        vf919MarkedRealEnergy (Pk u) *
        vf919MarkedRealEnergy (physical u)) ≤ budget := by
  rw [←vf919ActualMarkedMoment_eq_realEnergies rows Pj Pk physical]
  exact hOAI

/-- Source-level width algebra in the actual OAI refined marked proof.
The published final output costs 1+t but the intermediate marked state
pays exactly width + stageError = 1+t/2. -/
theorem vf919MarkedActualWidthExponent (t : ℝ) :
    (1 + t / 4) + t / 4 = 1 + t / 2 := by ring

/-- A theorem of the PRE-RELAXATION analytic input, not an assumed new
large-sieve estimate. For any actual complex row family it records exactly
the improvement available IF its proved hrow term has the retained width. -/
theorem vf919ActualMarkedSharperOfRawWidth
    {ι : Type*} (rows : Finset ι) (Pj Pk physical : ι → ℂ)
    (C U t : ℝ)
    (hraw : (∑ u ∈ rows, ‖Pj u * Pk u * physical u‖ ^ 2) ≤
      C * U ^ ((1 + t / 4) + t / 4)) :
    (∑ u ∈ rows,
      vf919MarkedRealEnergy (Pj u) *
        vf919MarkedRealEnergy (Pk u) *
        vf919MarkedRealEnergy (physical u)) ≤
          C * U ^ (1 + t / 2) := by
  calc
    _ = (∑ u ∈ rows, ‖Pj u * Pk u * physical u‖ ^ 2) := by
      simpa only [vf919ActualMarkedIntegrand] using
        (vf919ActualMarkedMoment_eq_realEnergies rows Pj Pk physical).symm
    _ ≤ C * U ^ (1 + t / 2) := by
      simpa only [vf919MarkedActualWidthExponent] using hraw

end RHLean.Analysis

#print axioms RHLean.Analysis.vf919ActualMarkedMoment_eq_realEnergies
#print axioms RHLean.Analysis.vf919ActualMarkedFourth_eq_unnormalizedNNS
#print axioms RHLean.Analysis.vf919ActualMarkedSharperOfRawWidth
