import Mathlib
import RHLean.Proof.ComplexVerticalLineGreenKubo

/-!
# Zero-target partial-moment form of the physical Green--Kubo covariance

For the RH physical event field the natural target is zero: `0` means that a
physical child has no endpoint birth/death event.  This file records the exact
NNS-style four-sector decomposition

  CLPM_0 + CUPM_0 - DLPM_0 - DUPM_0 = x*y

for arbitrary real event values, sums it over the physical Green--Kubo pair
carrier, and then uses the already-compiled fresh-prime sign reversal

  event(p*c) = -event(c)

on a prime-stable child to show that adjoining a fresh prime swaps co-partial
and divergent sectors exactly.

No mean centering, norm, absolute-value estimate, independence hypothesis, RH
hypothesis, or Mertens bound is introduced.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Zero-target upper/lower parts -/

/-- Positive-side partial moment about target zero. -/
def zeroTargetUpperPart (x : ℝ) : ℝ := (|x| + x) / 2

/-- Negative-side partial moment magnitude about target zero. -/
def zeroTargetLowerPart (x : ℝ) : ℝ := (|x| - x) / 2

theorem zeroTargetUpperPart_sub_lowerPart (x : ℝ) :
    zeroTargetUpperPart x - zeroTargetLowerPart x = x := by
  unfold zeroTargetUpperPart zeroTargetLowerPart
  ring

@[simp] theorem zeroTargetUpperPart_neg (x : ℝ) :
    zeroTargetUpperPart (-x) = zeroTargetLowerPart x := by
  unfold zeroTargetUpperPart zeroTargetLowerPart
  rw [abs_neg]
  ring

@[simp] theorem zeroTargetLowerPart_neg (x : ℝ) :
    zeroTargetLowerPart (-x) = zeroTargetUpperPart x := by
  unfold zeroTargetUpperPart zeroTargetLowerPart
  rw [abs_neg]
  ring

/-! ## Four NNS-style zero-target pair sectors -/

/-- Co-upper partial product at target zero. -/
def zeroTargetCUPM (x y : ℝ) : ℝ :=
  zeroTargetUpperPart x * zeroTargetUpperPart y

/-- Co-lower partial product at target zero. -/
def zeroTargetCLPM (x y : ℝ) : ℝ :=
  zeroTargetLowerPart x * zeroTargetLowerPart y

/-- Divergent lower/upper partial product at target zero. -/
def zeroTargetDLPM (x y : ℝ) : ℝ :=
  zeroTargetLowerPart x * zeroTargetUpperPart y

/-- Divergent upper/lower partial product at target zero. -/
def zeroTargetDUPM (x y : ℝ) : ℝ :=
  zeroTargetUpperPart x * zeroTargetLowerPart y

/-- **Zero-target partial-moment reassembly.**  The four partial products
reconstruct the raw signed cross product, not mean-centered statistical
covariance. -/
theorem zeroTargetPartialMoment_reassembly (x y : ℝ) :
    zeroTargetCLPM x y + zeroTargetCUPM x y -
        zeroTargetDLPM x y - zeroTargetDUPM x y = x * y := by
  unfold zeroTargetCLPM zeroTargetCUPM zeroTargetDLPM zeroTargetDUPM
  unfold zeroTargetUpperPart zeroTargetLowerPart
  ring

/-- Same-sign pair mass. -/
def zeroTargetCoPartialPair (x y : ℝ) : ℝ :=
  zeroTargetCLPM x y + zeroTargetCUPM x y

/-- Opposite-sign pair mass. -/
def zeroTargetDivergentPair (x y : ℝ) : ℝ :=
  zeroTargetDLPM x y + zeroTargetDUPM x y

theorem zeroTargetCoPartial_sub_divergent_eq_mul (x y : ℝ) :
    zeroTargetCoPartialPair x y - zeroTargetDivergentPair x y = x * y := by
  unfold zeroTargetCoPartialPair zeroTargetDivergentPair
  linear_combination zeroTargetPartialMoment_reassembly x y

/-! ## Fresh-prime sign reversal swaps the four sectors -/

@[simp] theorem zeroTargetCUPM_neg_left (x y : ℝ) :
    zeroTargetCUPM (-x) y = zeroTargetDLPM x y := by
  simp [zeroTargetCUPM, zeroTargetDLPM]

@[simp] theorem zeroTargetCLPM_neg_left (x y : ℝ) :
    zeroTargetCLPM (-x) y = zeroTargetDUPM x y := by
  simp [zeroTargetCLPM, zeroTargetDUPM]

@[simp] theorem zeroTargetDLPM_neg_left (x y : ℝ) :
    zeroTargetDLPM (-x) y = zeroTargetCUPM x y := by
  simp [zeroTargetDLPM, zeroTargetCUPM]

@[simp] theorem zeroTargetDUPM_neg_left (x y : ℝ) :
    zeroTargetDUPM (-x) y = zeroTargetCLPM x y := by
  simp [zeroTargetDUPM, zeroTargetCLPM]

@[simp] theorem zeroTargetCoPartialPair_neg_left (x y : ℝ) :
    zeroTargetCoPartialPair (-x) y = zeroTargetDivergentPair x y := by
  simp [zeroTargetCoPartialPair, zeroTargetDivergentPair]

@[simp] theorem zeroTargetDivergentPair_neg_left (x y : ℝ) :
    zeroTargetDivergentPair (-x) y = zeroTargetCoPartialPair x y := by
  simp [zeroTargetCoPartialPair, zeroTargetDivergentPair]

@[simp] theorem zeroTargetCoPartialPair_neg_both (x y : ℝ) :
    zeroTargetCoPartialPair (-x) (-y) = zeroTargetCoPartialPair x y := by
  simp [zeroTargetCoPartialPair, zeroTargetDivergentPair,
    zeroTargetCUPM, zeroTargetCLPM]

@[simp] theorem zeroTargetDivergentPair_neg_both (x y : ℝ) :
    zeroTargetDivergentPair (-x) (-y) = zeroTargetDivergentPair x y := by
  simp [zeroTargetDivergentPair, zeroTargetDLPM, zeroTargetDUPM]

/-! ## Exact Green--Kubo cross-covariance in zero-target currency -/

/-- Total co-partial pair mass over the same positive-lag pair carrier used by
`signedBlockCrossCovariance`. -/
def zeroTargetCoPartialCross (B : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K,
    ∑ i ∈ Finset.range j, zeroTargetCoPartialPair (B i) (B j)

/-- Total divergent pair mass over that carrier. -/
def zeroTargetDivergentCross (B : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K,
    ∑ i ∈ Finset.range j, zeroTargetDivergentPair (B i) (B j)

/-- **The block cross-covariance is exactly co-partial minus divergent mass at
target zero.**  This is the deterministic pair-sum version of
`CLPM + CUPM - DLPM - DUPM`. -/
theorem signedBlockCrossCovariance_eq_zeroTargetCoPartial_sub_divergent
    (B : ℕ → ℝ) (K : ℕ) :
    signedBlockCrossCovariance B K =
      zeroTargetCoPartialCross B K - zeroTargetDivergentCross B K := by
  rw [signedBlockCrossCovariance_eq_doubleSum]
  unfold zeroTargetCoPartialCross zeroTargetDivergentCross
  calc
    (∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j, B i * B j) =
        ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j,
          (zeroTargetCoPartialPair (B i) (B j) -
            zeroTargetDivergentPair (B i) (B j)) := by
              apply Finset.sum_congr rfl
              intro j _hj
              apply Finset.sum_congr rfl
              intro i _hi
              exact (zeroTargetCoPartial_sub_divergent_eq_mul (B i) (B j)).symm
    _ = ∑ j ∈ Finset.range K,
          ((∑ i ∈ Finset.range j, zeroTargetCoPartialPair (B i) (B j)) -
            ∑ i ∈ Finset.range j, zeroTargetDivergentPair (B i) (B j)) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [Finset.sum_sub_distrib]
    _ = (∑ j ∈ Finset.range K,
            ∑ i ∈ Finset.range j, zeroTargetCoPartialPair (B i) (B j)) -
          ∑ j ∈ Finset.range K,
            ∑ i ∈ Finset.range j, zeroTargetDivergentPair (B i) (B j) := by
              rw [Finset.sum_sub_distrib]

/-- The actual physical line-run covariance therefore has the NNS zero-target
partial-moment decomposition on its native event carrier. -/
theorem signedVerticalLineRunCovariance_eq_zeroTargetCoPartial_sub_divergent
    (a b : ℕ) :
    signedVerticalLineRunCovariance a b =
      zeroTargetCoPartialCross (signedVerticalLineEventStep a b) ((b + 1) ^ 2) -
        zeroTargetDivergentCross (signedVerticalLineEventStep a b) ((b + 1) ^ 2) := by
  unfold signedVerticalLineRunCovariance
  exact signedBlockCrossCovariance_eq_zeroTargetCoPartial_sub_divergent
    (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-! ## Physical fresh-prime sector exchange -/

/-- On a prime-stable physical child, adjoining a fresh larger prime sends
same-sign zero-target mass to opposite-sign mass against every second event. -/
theorem signedVerticalLine_zeroTargetCoPartial_prime_mul_eq_divergent
    {a b p c n : ℕ}
    (hp : p.Prime) (hc : c < p)
    (hstable : signedVerticalLineEventMask a b (p * c) =
      signedVerticalLineEventMask a b c) :
    zeroTargetCoPartialPair
        (signedVerticalLineEventStep a b (p * c))
        (signedVerticalLineEventStep a b n) =
      zeroTargetDivergentPair
        (signedVerticalLineEventStep a b c)
        (signedVerticalLineEventStep a b n) := by
  rw [signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable hp hc hstable]
  exact zeroTargetCoPartialPair_neg_left _ _

/-- Conversely the divergent sector is sent to the co-partial sector. -/
theorem signedVerticalLine_zeroTargetDivergent_prime_mul_eq_coPartial
    {a b p c n : ℕ}
    (hp : p.Prime) (hc : c < p)
    (hstable : signedVerticalLineEventMask a b (p * c) =
      signedVerticalLineEventMask a b c) :
    zeroTargetDivergentPair
        (signedVerticalLineEventStep a b (p * c))
        (signedVerticalLineEventStep a b n) =
      zeroTargetCoPartialPair
        (signedVerticalLineEventStep a b c)
        (signedVerticalLineEventStep a b n) := by
  rw [signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable hp hc hstable]
  exact zeroTargetDivergentPair_neg_left _ _

/-- If both physical coordinates are prime-stable, the two sign reversals
preserve each zero-target sector. -/
theorem signedVerticalLine_zeroTargetCoPartial_both_prime_mul_eq
    {a b p c d : ℕ}
    (hp : p.Prime) (hc : c < p) (hd : d < p)
    (hcstable : signedVerticalLineEventMask a b (p * c) =
      signedVerticalLineEventMask a b c)
    (hdstable : signedVerticalLineEventMask a b (p * d) =
      signedVerticalLineEventMask a b d) :
    zeroTargetCoPartialPair
        (signedVerticalLineEventStep a b (p * c))
        (signedVerticalLineEventStep a b (p * d)) =
      zeroTargetCoPartialPair
        (signedVerticalLineEventStep a b c)
        (signedVerticalLineEventStep a b d) := by
  rw [signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable hp hc hcstable,
    signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable hp hd hdstable]
  exact zeroTargetCoPartialPair_neg_both _ _

/-- Same statement for the divergent sector. -/
theorem signedVerticalLine_zeroTargetDivergent_both_prime_mul_eq
    {a b p c d : ℕ}
    (hp : p.Prime) (hc : c < p) (hd : d < p)
    (hcstable : signedVerticalLineEventMask a b (p * c) =
      signedVerticalLineEventMask a b c)
    (hdstable : signedVerticalLineEventMask a b (p * d) =
      signedVerticalLineEventMask a b d) :
    zeroTargetDivergentPair
        (signedVerticalLineEventStep a b (p * c))
        (signedVerticalLineEventStep a b (p * d)) =
      zeroTargetDivergentPair
        (signedVerticalLineEventStep a b c)
        (signedVerticalLineEventStep a b d) := by
  rw [signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable hp hc hcstable,
    signedVerticalLineEventStep_prime_mul_eq_neg_of_mask_stable hp hd hdstable]
  exact zeroTargetDivergentPair_neg_both _ _

end RHLean.Proof
