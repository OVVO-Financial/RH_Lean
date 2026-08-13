import Mathlib
import RHLean.Analysis.PrimeSievePNTGoodMassChargeAttack

/-!
# Base-eight shallow packet attack

PR #330 made the deep packet tail unconditional at the base-eight cutoff.  The
remaining packet-side input is the successor-shallow estimate.  This module
opens that shallow energy without separating `pi` and `Li`.

For every midpoint node `[a,b)` with split `m`, the existing signed sibling
identity writes the packet as the weighted reciprocal-discrepancy contrast

`(m-a) * sum_[m,b) Delta_d - (b-m) * sum_[a,m) Delta_d`.

The recursive square function below uses exactly those contrasts.  The first
result of the attack is an exact identification with the existing recursive
packet tree, hence with the base-eight successor-shallow energy.  The shallow
energy is then flattened into the finite sum of its exact packet levels.  The
final block-uniform square-function statement is therefore not a new
assumption: it is precisely the remaining shallow analytic frontier in
arithmetic coordinates.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Weighted left-versus-right reciprocal discrepancy on one midpoint node.
This is the arithmetic numerator of the signed sibling residual and keeps
`pi - Li` intact as one signed object. -/
def primeSieveReciprocalSiblingContrast
    (y x a m b : ℕ) : ℂ :=
  (((m - a : ℕ) : ℂ) *
      (∑ d ∈ Finset.Ico m b,
        primeSieveReciprocalPrimeDiscrepancy y x d)) -
    (((b - m : ℕ) : ℂ) *
      (∑ d ∈ Finset.Ico a m,
        primeSieveReciprocalPrimeDiscrepancy y x d))

/-- Exact node identity: on reciprocal support, the width-normalized signed
sibling packet is the normalized weighted discrepancy contrast. -/
theorem primeSieveSignedSiblingPacketResidual_eq_reciprocalSiblingContrast
    {y x a m b : ℕ}
    (ha : 1 ≤ a) (ham : a ≤ m) (hmb : m ≤ b)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveSignedSiblingPacketResidual y x a m b =
      (((b - a : ℕ) : ℂ)⁻¹) *
        primeSieveReciprocalSiblingContrast y x a m b := by
  unfold primeSieveSignedSiblingPacketResidual
    primeSieveReciprocalSiblingContrast
  rw [primeSieveSignedSiblingPacket_eq_weighted_intervalDiscrepancies
    ha ham hmb hb]

/-- Recursive low-frequency square function on one reciprocal interval.  It is
written directly in terms of weighted sums of the unsplit reciprocal prime
minus Li discrepancy. -/
def primeSieveReciprocalLowFrequencyIntervalEnergy
    (y x : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, _a, _b => 0
  | depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        ((b - a : ℕ) : ℝ) *
            ‖(((b - a : ℕ) : ℂ)⁻¹ *
              primeSieveReciprocalSiblingContrast y x a m b)‖ ^ 2 +
          primeSieveReciprocalLowFrequencyIntervalEnergy y x depth a m +
          primeSieveReciprocalLowFrequencyIntervalEnergy y x depth m b
      else 0

/-- On every interval contained in reciprocal support, the existing midpoint
packet tree is exactly the reciprocal-discrepancy low-frequency square
function. -/
theorem primeSieveDyadicPacketIntervalTreeEnergy_eq_reciprocalLowFrequencyIntervalEnergy
    (y x depth a b : ℕ)
    (ha : 1 ≤ a)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveDyadicPacketIntervalTreeEnergy y x depth a b =
      primeSieveReciprocalLowFrequencyIntervalEnergy y x depth a b := by
  induction depth generalizing a b with
  | zero =>
      simp [primeSieveReciprocalLowFrequencyIntervalEnergy,
        primeSieveDyadicPacketIntervalTreeEnergy_zero]
  | succ depth ih =>
      rw [show Nat.succ depth = depth + 1 by omega,
        primeSieveDyadicPacketIntervalTreeEnergy_succ]
      by_cases hsplit : a + 1 < b
      · let m := dyadicPacketMidpoint a b
        have hm : a < m ∧ m < b := by
          simpa [m] using dyadicPacketMidpoint_facts hsplit
        have hm1 : 1 ≤ m := ha.trans hm.1.le
        have hmB : m ≤ x / (y + 1) + 1 := hm.2.le.trans hb
        have hres :
            primeSieveSignedSiblingPacketResidual y x a m b =
              (((b - a : ℕ) : ℂ)⁻¹) *
                primeSieveReciprocalSiblingContrast y x a m b :=
          primeSieveSignedSiblingPacketResidual_eq_reciprocalSiblingContrast
            ha hm.1.le hm.2.le hb
        simp [primeSieveReciprocalLowFrequencyIntervalEnergy, hsplit, m,
          hres, ih a m ha hmB, ih m b hm1 hb]
      · simp [primeSieveReciprocalLowFrequencyIntervalEnergy, hsplit]

/-- The global reciprocal low-frequency square function through depth `J` on
every occupied dyadic block. -/
def primeSieveReciprocalLowFrequencySquareFunction
    (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveReciprocalLowFrequencyIntervalEnergy y x (min J j)
      (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)

/-- Exact global identification with the existing shallow packet energy. -/
theorem primeSieveReciprocalLowFrequencySquareFunction_eq_shallowEnergy
    (y x J : ℕ) :
    primeSieveReciprocalLowFrequencySquareFunction y x J =
      primeSieveDyadicPacketShallowEnergy y x J := by
  unfold primeSieveReciprocalLowFrequencySquareFunction
    primeSieveDyadicPacketShallowEnergy primeSieveDyadicPacketTreeBlockEnergy
  apply Finset.sum_congr rfl
  intro j hj
  have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
    simpa [primeSieveDyadicBlockLeft] using (Nat.one_le_pow' j 1)
  have hright :
      primeSieveDyadicBlockRight y x j + 1 ≤ x / (y + 1) + 1 := by
    have h := min_le_left (x / (y + 1)) (2 ^ (j + 1) - 1)
    simpa [primeSieveDyadicBlockRight] using Nat.add_le_add_right h 1
  exact (primeSieveDyadicPacketIntervalTreeEnergy_eq_reciprocalLowFrequencyIntervalEnergy
    y x (min J j) (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1) hleft1 hright).symm

/-- The shallow tree is the finite sum of the exact packet levels below the
cutoff.  This removes the recursive wrapper from the remaining analytic target. -/
theorem primeSieveDyadicPacketShallowEnergy_eq_sum_levelEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J =
      ∑ r ∈ Finset.range J, primeSieveDyadicPacketLevelEnergy y x r := by
  induction J with
  | zero =>
      unfold primeSieveDyadicPacketShallowEnergy
        primeSieveDyadicPacketTreeBlockEnergy
      simp
  | succ J ih =>
      rw [show Nat.succ J = J + 1 by omega,
        primeSieveDyadicPacketShallowEnergy_succ_eq, ih,
        Finset.sum_range_succ]

/-- Fully expanded finite-level form: each shallow level is the exact signed
midpoint energy on every occupied block still alive at that level. -/
theorem primeSieveDyadicPacketShallowEnergy_eq_sum_intervalLevelEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J =
      ∑ r ∈ Finset.range J,
        ∑ j ∈ primeSieveDyadicBlockIndices y x,
          if r < j then
            primeSieveDyadicPacketIntervalLevelEnergy y x r
              (primeSieveDyadicBlockLeft j)
              (primeSieveDyadicBlockRight y x j + 1)
          else 0 := by
  rw [primeSieveDyadicPacketShallowEnergy_eq_sum_levelEnergy]
  apply Finset.sum_congr rfl
  intro r _hr
  exact primeSieveDyadicPacketLevelEnergy_eq_sum_intervalLevelEnergy y x r

/-- Base-eight successor shallow square function selected by #330. -/
def primeSieveBaseEightShallowSquareFunction (k x : ℕ) : ℝ :=
  primeSieveReciprocalLowFrequencySquareFunction
    (primorialPNTPrimeSieveCutoff k) x
    (dyadicPacketBaseEightCutoff k x + 1)

/-- The base-eight square function is literally the successor-shallow packet
energy left open by #330. -/
theorem primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy
    (k x : ℕ) :
    primeSieveBaseEightShallowSquareFunction k x =
      primeSieveDyadicPacketShallowEnergy
        (primorialPNTPrimeSieveCutoff k) x
        (dyadicPacketBaseEightCutoff k x + 1) := by
  simpa [primeSieveBaseEightShallowSquareFunction] using
    primeSieveReciprocalLowFrequencySquareFunction_eq_shallowEnergy
      (primorialPNTPrimeSieveCutoff k) x
      (dyadicPacketBaseEightCutoff k x + 1)

/-- At the base-eight successor cutoff, the remaining square function is the
finite sum of levels `0 <= r <= log_8(x+1)`. -/
theorem primeSieveBaseEightShallowSquareFunction_eq_sum_levelEnergy
    (k x : ℕ) :
    primeSieveBaseEightShallowSquareFunction k x =
      ∑ r ∈ Finset.range (dyadicPacketBaseEightCutoff k x + 1),
        primeSieveDyadicPacketLevelEnergy
          (primorialPNTPrimeSieveCutoff k) x r := by
  rw [primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy,
    primeSieveDyadicPacketShallowEnergy_eq_sum_levelEnergy]

/-- The exact low-frequency arithmetic statement exposed by #331.  It asks for
a critical block-uniform bound on the reciprocal-discrepancy Haar square
function at the base-eight successor cutoff. -/
def DyadicPrimeReciprocalLowFrequencySquareFunctionBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveBaseEightShallowSquareFunction k x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The new arithmetic square-function statement is exactly equivalent to the
remaining successor-shallow packet hypothesis in the #330 terminal package. -/
theorem dyadicPrimeReciprocalLowFrequencySquareFunctionBlockBounded_iff_baseEightShallow :
    DyadicPrimeReciprocalLowFrequencySquareFunctionBlockBoundedStatement ↔
      DyadicPacketShallowEnergyBlockBoundedStatement
        (dyadicPacketSuccCutoff dyadicPacketBaseEightCutoff) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hCb⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    have hs := hCb k x hk hlow hup
    rw [primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy] at hs
    simpa [dyadicPacketSuccCutoff] using hs
  · intro h ε hε
    obtain ⟨C, hC, hCb⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    have hs := hCb k x hk hlow hup
    rw [primeSieveBaseEightShallowSquareFunction_eq_shallowEnergy]
    simpa [dyadicPacketSuccCutoff] using hs

/-- RH can now be stated with the packet-side shallow input entirely in the
reciprocal-discrepancy square-function coordinate exposed above. -/
theorem riemannHypothesis_of_baseEightReciprocalLowFrequencyPackage
    (hC : DyadicCoherentChannelRHScale)
    (hS : DyadicPrimeReciprocalLowFrequencySquareFunctionBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_baseEightPacketAnalyticPackage hC
  · exact
      dyadicPrimeReciprocalLowFrequencySquareFunctionBlockBounded_iff_baseEightShallow.mp hS
  · exact hD

end RHLean.Analysis
