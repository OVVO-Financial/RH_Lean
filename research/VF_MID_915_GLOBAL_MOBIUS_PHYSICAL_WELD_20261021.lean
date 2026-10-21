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
    by_contra hne
    have hc2 : 2 ≤ c := by omega
    have hmul : q * 2 ≤ q * c := Nat.mul_le_mul_left q hc2
    omega
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

/-- Fresh-prime factor reversal is valid for BOTH canonical orientations,
not merely largest-prime high-owner cells. -/
theorem vf915FreshPrime_mobiusFlip
    {p c : ℕ} (hp : p.Prime) (hpc : ¬ p ∣ c) :
    μ (p * c) = -μ c :=
  moebius_mul_fresh_prime_eq_neg hp hpc

/-- Exact global odd-depth composite correction over a fresh-prime child:
the missing third/fifth/... factor-depth states exactly cancel the naive
Mobius prime detector except for the genuine prime root c=1. -/
theorem vf915GlobalNegativeComposite_freshPrime_normalForm
    {p c : ℕ} (hp : p.Prime) (hc : 0 < c)
    (hpc : ¬ p ∣ c) :
    2 * vf915GlobalNegativeComposite (p * c) =
      vf915GlobalMuSq c + vf915GlobalMu c -
        2 * (if c = 1 then (1 : ℝ) else 0) := by
  have hsite := vf915GlobalDecoded_highPrimeCofactor 0 hp hc
  have hflip := vf915FreshPrime_mobiusFlip hp hpc
  have hmu : vf915GlobalMu (p * c) = -vf915GlobalMu c := by
    unfold vf915GlobalMu
    rw [hflip]
    push_cast
    ring
  have hsq : vf915GlobalMuSq (p * c) = vf915GlobalMuSq c := by
    unfold vf915GlobalMuSq
    rw [hflip]
    ring
  unfold vf915GlobalDecodedPhysicalCharge at hsite
  rw [hmu, hsq] at hsite
  linarith

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
  unfold vf915HighPrimePhysicalCorrection vf915GlobalMu
  rw [hflip]
  push_cast
  ring

/-- The same exact physical correction for EVERY fresh-prime factor,
including small-owner daughters q<c. -/
theorem vf915GlobalDecoded_freshPrime_eq_mu_plus_correction
    (R : ℕ) {p c : ℕ} (hp : p.Prime)
    (hc : 0 < c) (hpc : ¬ p ∣ c) :
    vf915GlobalDecodedPhysicalCharge R (p * c) =
      vf915GlobalMu (p * c) +
        vf915HighPrimePhysicalCorrection R c := by
  rw [vf915GlobalDecoded_highPrimeCofactor R hp hc]
  unfold vf915HighPrimePhysicalCorrection vf915GlobalMu
  rw [vf915FreshPrime_mobiusFlip hp hpc]
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
      (owner i).Prime ∧ 0 < cofactor i ∧ ¬ owner i ∣ cofactor i) :
    (∑ i ∈ s, originalWeight i *
      vf915GlobalDecodedPhysicalCharge R (owner i * cofactor i)) =
    ∑ i ∈ s, originalWeight i *
      (vf915GlobalMu (owner i * cofactor i) +
        vf915HighPrimePhysicalCorrection R (cofactor i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  rcases hvalid i hi with ⟨hp, hc, hpc⟩
  rw [vf915GlobalDecoded_freshPrime_eq_mu_plus_correction R hp hc hpc]

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

/-- The full ALL-depth physical correction to the signed Mobius field.
It is NOT assumed small. In particular it cancels the naive fresh-prime
sign reversal on every composite physical VF seat. -/
def vf915GlobalPhysicalRemainder (R n : ℕ) : ℝ :=
  vfMidOddFractionalPrimeSeatWeight R -
    vf915GlobalMuSq n / 2 - vf915GlobalMu n / 2 +
      vf915GlobalNegativeComposite n

theorem vf915GlobalDecoded_eq_mu_add_remainder (R n : ℕ) :
    vf915GlobalDecodedPhysicalCharge R n =
      vf915GlobalMu n + vf915GlobalPhysicalRemainder R n := by
  unfold vf915GlobalDecodedPhysicalCharge vf915GlobalPhysicalRemainder
  ring

/-- EVERY pair of original VF physical sites, including arbitrary
squareful and odd-factor-depth sources, evaluated at their OWN original
age and multiplied by their OWN retained source coefficient.

The full physical Gram is the Mobius/Mobius term PLUS both mixed terms
PLUS the correction/correction term. Only the FULL sum represents the
original masked physical observable. -/
theorem vf915GlobalDecoded_fullyLabelledPairGramWeld
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (leftAge rightAge leftSite rightSite : ι → ℕ)
    (originalCoefficient : ι → ℝ) :
    (∑ i ∈ s, originalCoefficient i *
      (vf915GlobalDecodedPhysicalCharge (leftAge i) (leftSite i) *
        vf915GlobalDecodedPhysicalCharge (rightAge i) (rightSite i))) =
    ∑ i ∈ s, originalCoefficient i *
      (vf915GlobalMu (leftSite i) * vf915GlobalMu (rightSite i) +
        vf915GlobalMu (leftSite i) *
          vf915GlobalPhysicalRemainder (rightAge i) (rightSite i) +
        vf915GlobalPhysicalRemainder (leftAge i) (leftSite i) *
          vf915GlobalMu (rightSite i) +
        vf915GlobalPhysicalRemainder (leftAge i) (leftSite i) *
          vf915GlobalPhysicalRemainder (rightAge i) (rightSite i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [vf915GlobalDecoded_eq_mu_add_remainder,
      vf915GlobalDecoded_eq_mu_add_remainder]
  ring

/-! ## DIRECT actual production returned-pair source, with masks and clips -/

/-- The actual production #915 active mask, carrying the globally decoded
physical charge at each active original odd seat. Zero off the true carrier. -/
def vf915DecodedActivePhysicalSite (R n : ℕ) : ℝ :=
  if n ∈ vfMidOneBlockActivePhysicalCarrier R then
    vf915GlobalDecodedPhysicalCharge R n else 0

theorem vf915DecodedActivePhysicalSite_eq_original (R n : ℕ) :
    vf915DecodedActivePhysicalSite R n =
      vfMidOneBlockActivePhysicalSite R n := by
  simp [vf915DecodedActivePhysicalSite, vfMidOneBlockActivePhysicalSite,
        vf915GlobalDecodedPhysicalCharge_eq_original]

/-- Keep the exact original production mask on EACH of the two Mobius channels. -/
def vf915ActiveMu (R n : ℕ) : ℝ :=
  if n ∈ vfMidOneBlockActivePhysicalCarrier R then vf915GlobalMu n else 0

def vf915ActiveCorrection (R n : ℕ) : ℝ :=
  if n ∈ vfMidOneBlockActivePhysicalCarrier R then
    vf915GlobalPhysicalRemainder R n else 0

theorem vf915DecodedActivePhysicalSite_eq_mu_add_correction (R n : ℕ) :
    vf915DecodedActivePhysicalSite R n =
      vf915ActiveMu R n + vf915ActiveCorrection R n := by
  unfold vf915DecodedActivePhysicalSite vf915ActiveMu
    vf915ActiveCorrection
  split_ifs with h
  · exact vf915GlobalDecoded_eq_mu_add_remainder R n
  · simp

/-- ACTUAL #913/#915 returned physical source:
    - true clipped p-free left site a;
    - true p-admitted cofactor c, actual physical child p*c;
    - no altered original coefficient;
    - no assumed substitute family.

This is the exact #913 kernel theorem spliced with the global all-depth Mobius
decoder, preserving the same individual site masks. -/
theorem vf915ActualReturnedPairWeight_eq_decodedPhysical
    {R p a c : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (haClip : a ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig)
    (hcAdm : c ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig) :
    vfMidActiveReturnedPairWeight R p sig (a, c) =
      vf915DecodedActivePhysicalSite R a *
        vf915DecodedActivePhysicalSite R (p * c) := by
  rw [vfMidActiveReturnedPairWeight_eq_physical hR hp haClip hcAdm]
  simp only [vf915DecodedActivePhysicalSite_eq_original]

/-- FULL four-channel Gram on one ACTUAL returned child occurrence.
Positive, negative, mixed, and correction-square channels all survive with
the TRUE parent and child masks; a Mobius-only term is not the VF source. -/
theorem vf915ActualReturnedPairWeight_eq_fourChannels
    {R p a c : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (haClip : a ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig)
    (hcAdm : c ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig) :
    vfMidActiveReturnedPairWeight R p sig (a, c) =
      vf915ActiveMu R a * vf915ActiveMu R (p * c) +
        vf915ActiveMu R a * vf915ActiveCorrection R (p * c) +
        vf915ActiveCorrection R a * vf915ActiveMu R (p * c) +
        vf915ActiveCorrection R a *
          vf915ActiveCorrection R (p * c) := by
  rw [vf915ActualReturnedPairWeight_eq_decodedPhysical
    hR hp haClip hcAdm,
    vf915DecodedActivePhysicalSite_eq_mu_add_correction,
    vf915DecodedActivePhysicalSite_eq_mu_add_correction]
  ring

/-- The entire ORIGINAL current first-owner clipped/admitted Fubini carrier
obeys the four-channel identity. The index is the literal returned pair;
no generic occurrence assignment or owner-history injection is hypothesized.
-/
theorem vf915ActualReturnedPairCarrier_sum_eq_fourChannels
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    (∑ ac ∈ vfMidActiveReturnedPairCarrier R p sig,
      vfMidActiveReturnedPairWeight R p sig ac) =
      ∑ ac ∈ vfMidActiveReturnedPairCarrier R p sig,
        (vf915ActiveMu R ac.1 * vf915ActiveMu R (p * ac.2) +
          vf915ActiveMu R ac.1 * vf915ActiveCorrection R (p * ac.2) +
          vf915ActiveCorrection R ac.1 * vf915ActiveMu R (p * ac.2) +
          vf915ActiveCorrection R ac.1 *
            vf915ActiveCorrection R (p * ac.2)) := by
  apply Finset.sum_congr rfl
  intro ac hac
  rcases Finset.mem_product.mp hac with ⟨ha, hc⟩
  exact vf915ActualReturnedPairWeight_eq_fourChannels hR hp ha hc

/-- The actual #915 physical global residual and the ACTUAL three
clipped/returned boundary sectors sum to the decoder-based original Co/Div.
Neither the G_R anchor nor the physical masks are replaced. -/
theorem vf915GlobalDecoded_originalResidualAndBoundary
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidActiveGlobalResidualExcess R +
      vfMidActiveThreeBoundaryExcess R =
      2 * ((∑ n ∈ vfMidOddCandidateSeats R,
        vf915GlobalDecodedPhysicalCharge R n) -
        vfMidActualPrimeEndpointDefect R) ^ 2 -
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vf915GlobalDecodedPhysicalCharge R n|) ^ 2 := by
  calc
    vfMidActiveGlobalResidualExcess R +
        vfMidActiveThreeBoundaryExcess R =
      vfMidFirstBadAnchoredCoDivExcess R :=
        (vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess
          hR).symm
    _ = _ := vf915GlobalDecoded_originalAnchoredExcess R

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
#print axioms RHLean.Analysis.vf915GlobalNegativeComposite_freshPrime_normalForm
#print axioms RHLean.Analysis.vf915GlobalDecoded_fullKeyWeightedOwnerWeld
#print axioms RHLean.Analysis.vf915GlobalDecoded_fullyLabelledPairGramWeld
#print axioms RHLean.Analysis.vf915GlobalDecoded_originalAnchoredExcess
#print axioms RHLean.Analysis.vf915ActualReturnedPairCarrier_sum_eq_fourChannels
#print axioms RHLean.Analysis.vf915GlobalDecoded_originalResidualAndBoundary
