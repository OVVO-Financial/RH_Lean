import Mathlib
import «research.VF_MID_PHYSICAL_FORCING_MOBIUS_DECODER»
import «research.VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT»

/-!
# Global Mobius-to-actual-VF physical owner weld, without proxy replacement

This file identifies the ORIGINAL odd-seat VF charge, original historical
anchor, original absolute NNS denominator, and Co/Div excess with the global
Mobius prime-indicator decoder. There is NO cubic/depth-two restriction.

The exact corrected signed source is

  z_R(n) = w_R - (mu(n)^2 - mu(n) - 2*D_-(n))/2,

where D_- is the indicator of a *composite* with mu(n)=-1.

On a high-prime owner n=q*c, the original site value is w_R-1_{c=1},
even though mu(q*c)=-mu(c). This is the actual mismatch that must be
retained when bringing prime-owner histories to the original #915 gate.

Every theorem below is an identity, not a bound on the open #915 gate.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

def vf915GlobalMuSq (n : ℕ) : ℝ := (((μ n) ^ 2 : ℤ) : ℝ)
def vf915GlobalMu (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ)
def vf915GlobalNegativeComposite (n : ℕ) : ℝ :=
  ((vfMidNegativeMobiusCompositeIndicator n : ℤ) : ℝ)

/-- The actual VF prime/composite site in the global Mobius coordinates. -/
def vf915GlobalDecodedPhysicalCharge (R n : ℕ) : ℝ :=
  vfMidOddFractionalPrimeSeatWeight R -
    (vf915GlobalMuSq n - vf915GlobalMu n -
      2 * vf915GlobalNegativeComposite n) / 2

/-- EVERY integer site, including squareful sites and arbitrary prime depth. -/
theorem vf915GlobalDecodedPhysicalCharge_eq_original (R n : ℕ) :
    vf915GlobalDecodedPhysicalCharge R n =
      vfMidOddSignedSeatCharge R n := by
  have hz := two_mul_vfMidActualPrimeIndicatorInt_eq_squarefree_sub_mobius_sub_defect n
  have hzReal :
      (2 : ℝ) * ((vfMidActualPrimeIndicatorInt n : ℤ) : ℝ) =
        vf915GlobalMuSq n - vf915GlobalMu n -
          2 * vf915GlobalNegativeComposite n := by
    unfold vf915GlobalMuSq vf915GlobalMu vf915GlobalNegativeComposite
    exact_mod_cast hz
  have hindicator :
      ((vfMidActualPrimeIndicatorInt n : ℤ) : ℝ) =
        vfMidActualPrimeSeatMass n := by
    unfold vfMidActualPrimeIndicatorInt vfMidActualPrimeSeatMass
    by_cases hp : n.Prime <;> simp [hp]
  unfold vf915GlobalDecodedPhysicalCharge vfMidOddSignedSeatCharge
  rw [← hindicator]
  linear_combination hzReal / 2

/-- A prime q with positive cofactor c yields a prime precisely at c=1.
This statement does not assert any Mobius parity rule for the original
physical seat charge. -/
theorem vf915HighPrime_mul_is_prime_iff
    {q c : ℕ} (hq : q.Prime) (hc : 0 < c) :
    (q * c).Prime ↔ c = 1 := by
  constructor
  · intro hprime
    have hd : q ∣ q * c := ⟨c, rfl⟩
    have heq : q = q * c :=
      (Nat.prime_dvd_prime_iff_eq hq hprime).mp hd
    have hqpos : 1 < q := hq.one_lt
    nlinarith
  · intro h1
    subst c
    simpa using hq

/-- Actual original weight on a complete high-prime owner occurrence.
Only the c=1 child is a negative prime seat. All c>1 children contribute
the same positive VF weight, independently of their Mobius sign. -/
theorem vf915GlobalDecoded_highPrimeCofactor
    (R : ℕ) {q c : ℕ} (hq : q.Prime) (hc : 0 < c) :
    vf915GlobalDecodedPhysicalCharge R (q * c) =
      vfMidOddFractionalPrimeSeatWeight R -
        (if c = 1 then (1 : ℝ) else 0) := by
  rw [vf915GlobalDecodedPhysicalCharge_eq_original]
  unfold vfMidOddSignedSeatCharge vfMidActualPrimeSeatMass
  rw [vf915HighPrime_mul_is_prime_iff hq hc]

/-- Exact sign change in the Mobius cofactor source, distinct from
the original VF physical charge. -/
theorem vf915HighPrime_mobiusFlip
    {q c : ℕ} (hq : q.Prime) (hc : 0 < c) (hlt : c < q) :
    μ (q * c) = -μ c := by
  apply moebius_mul_fresh_prime_eq_neg hq
  intro hd
  have hle : q ≤ c := Nat.le_of_dvd hc hd
  omega

/-- The precise compensation missing from the naive "mu reverses, so
VF charge reverses" argument. It retains both the physical w_R and the
prime-root delta, so the owner transfer is exact BEFORE norming. -/
def vf915HighPrimePhysicalCorrection (R c : ℕ) : ℝ :=
  vfMidOddFractionalPrimeSeatWeight R + vf915GlobalMu c -
    (if c = 1 then (1 : ℝ) else 0)

theorem vf915GlobalDecoded_highPrime_eq_mu_plus_correction
    (R : ℕ) {q c : ℕ} (hq : q.Prime)
    (hc : 0 < c) (hlt : c < q) :
    vf915GlobalDecodedPhysicalCharge R (q * c) =
      vf915GlobalMu (q * c) +
        vf915HighPrimePhysicalCorrection R c := by
  rw [vf915GlobalDecoded_highPrimeCofactor R hq hc]
  have hflip := vf915HighPrime_mobiusFlip hq hc hlt
  unfold vf915GlobalMu vf915HighPrimePhysicalCorrection
  rw [hflip]
  push_cast
  ring

/-- Full-key, arbitrary original-weight, occurrence-preserving Fubini inlet.
The index type can include age, clip, owner, revealed prime, original raw
parent and occurrence ID. No stripped-parent deduplication occurs. -/
theorem vf915GlobalDecoded_fullKeyWeightedOwnerWeld
    {ι : Type*} [DecidableEq ι]
    (R : ℕ) (s : Finset ι)
    (owner cofactor : ι → ℕ) (originalWeight : ι → ℝ)
    (hvalid : ∀ i ∈ s,
      (owner i).Prime ∧ 0 < cofactor i ∧ cofactor i < owner i) :
    (∑ i ∈ s, originalWeight i *
      vf915GlobalDecodedPhysicalCharge R (owner i * cofactor i)) =
    ∑ i ∈ s, originalWeight i *
      (vf915GlobalMu (owner i * cofactor i) +
        vf915HighPrimePhysicalCorrection R (cofactor i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  rcases hvalid i hi with ⟨hp, hc, hlt⟩
  rw [vf915GlobalDecoded_highPrime_eq_mu_plus_correction R hp hc hlt]

/-- Original signed physical block mass, expressed only through the
global decoder; no smooth model, cube restriction, or density heuristic. -/
theorem vf915GlobalDecoded_signedBlockMass
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ vfMidOddCandidateSeats R,
      vf915GlobalDecodedPhysicalCharge R n) =
    vfMidBandMass R - (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  simp only [vf915GlobalDecodedPhysicalCharge_eq_original]
  unfold vfMidOddSignedSeatCharge
  rw [Finset.sum_sub_distrib,
      vfMidOddFractionalPrimeSeatWeight_sum R hR,
      vfMidActualPrimeSeatMass_sum_oddCandidates R hR]

/-- The decoded signed block and the compressed ACTUAL historical anchor
reconstruct the next physical VF endpoint without a new historical norm. -/
theorem vf915GlobalDecoded_nextEndpoint
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidActualPrimeEndpointDefect (R + 1) =
      vfMidActualPrimeEndpointDefect R -
        (∑ n ∈ vfMidOddCandidateSeats R,
          vf915GlobalDecodedPhysicalCharge R n) := by
  rw [vfMidActualPrimeEndpointDefect_succ_eq_add_blockSupply hR,
      vf915GlobalDecoded_signedBlockMass R hR]
  ring

/-- Exactly the ORIGINAL anchored #915 absolute denominator; the decompressed
absolute historical population has NOT been added. -/
theorem vf915GlobalDecoded_originalNNSMass (R : ℕ) :
    vfMidFirstBadZeroTargetTotalMass R =
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vf915GlobalDecodedPhysicalCharge R n|) ^ 2 := by
  rw [vfMidFirstBadZeroTargetTotalMass_eq]
  simp only [vf915GlobalDecodedPhysicalCharge_eq_original]

/-- The entire ORIGINAL anchored Co/Div excess rewritten as the global
Mobius-decoded population, including the exact original absolute denominator
and the uncompressed historical anchor exactly once. -/
theorem vf915GlobalDecoded_originalAnchoredExcess (R : ℕ) :
    vfMidFirstBadAnchoredCoDivExcess R =
      2 * ((∑ n ∈ vfMidOddCandidateSeats R,
        vf915GlobalDecodedPhysicalCharge R n) -
        vfMidActualPrimeEndpointDefect R) ^ 2 -
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vf915GlobalDecodedPhysicalCharge R n|) ^ 2 := by
  calc
    vfMidFirstBadAnchoredCoDivExcess R =
      vfMidFirstBadAnchoredUpperPartialMass R ^ 2 +
      vfMidFirstBadAnchoredLowerPartialMass R ^ 2 -
      6 * vfMidFirstBadAnchoredUpperPartialMass R *
        vfMidFirstBadAnchoredLowerPartialMass R :=
          vfMidFirstBadAnchoredCoDivExcess_eq_upperLowerBalance R
    _ = 2 * (vfMidFirstBadAnchoredUpperPartialMass R -
        vfMidFirstBadAnchoredLowerPartialMass R) ^ 2 -
      (vfMidFirstBadAnchoredUpperPartialMass R +
        vfMidFirstBadAnchoredLowerPartialMass R) ^ 2 := by ring
    _ = 2 * ((∑ n ∈ vfMidOddCandidateSeats R,
        vfMidOddSignedSeatCharge R n) -
        vfMidActualPrimeEndpointDefect R) ^ 2 -
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n|) ^ 2 := by
        rw [vfMidFirstBadAnchoredUpper_sub_lower_eq_signedSource R,
            vfMidFirstBadAnchoredUpper_add_lower_eq_absMass R]
    _ = _ := by
      simp only [vf915GlobalDecodedPhysicalCharge_eq_original]

/-- Algebraic half gate in the EXACT original physical currency.
An independent proof of this inequality under actual first-badness is
still equivalent to closing the original #915 gate, not a new free bound. -/
theorem vf915GlobalDecoded_halfGate_iff_original
    (R : ℕ) :
    (2 * ((∑ n ∈ vfMidOddCandidateSeats R,
        vf915GlobalDecodedPhysicalCharge R n) -
        vfMidActualPrimeEndpointDefect R) ^ 2 ≤
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vf915GlobalDecodedPhysicalCharge R n|) ^ 2) ↔
      vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  rw [vf915GlobalDecoded_originalAnchoredExcess]
  constructor <;> intro h <;> linarith

end RHLean.Analysis

#print axioms RHLean.Analysis.vf915GlobalDecodedPhysicalCharge_eq_original
#print axioms RHLean.Analysis.vf915GlobalDecoded_fullKeyWeightedOwnerWeld
#print axioms RHLean.Analysis.vf915GlobalDecoded_originalAnchoredExcess
