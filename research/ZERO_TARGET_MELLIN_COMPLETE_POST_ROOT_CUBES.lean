import Mathlib
import «research.ZERO_TARGET_MELLIN_PHYSICAL_LCM_STENCIL»

/-!
# Complete post-root Mellin covariance cubes remain nonpositive

The physically clipped Mellin square from the preceding module leaves a
first-order edge in general.  Complete post-root parent families are different:
all three fresh-prime child corners lie inside the endpoint, and their common
LCM is `p * lcm(a,b)`.  Consequently the three non-base indicators are the
same lower-scale super-LCM indicator.

For one complete parent pair the Mellin-weighted zero-target cube is therefore

  -r * (2-r) * excess(a,b) * superLcmIndicator(W/p,a,b).

Summing the complete lower carrier gives the exact identity

  completeMellinCubeMass(W,p,r)
    = -r*(2-r) * fullLcmBoundaryKernel(W/p).

The lower boundary kernel is already compiled as nonnegative.  Hence every
complete post-root family is nonpositive for `0 <= r <= 2`, including every
critical ratio with `r^2 = 1/p` and `0 <= r <= 1`.

Thus positive covariance amplification cannot come from complete fresh-prime
cubes after Mellin interpolation.  It is confined to the incomplete clipped
edge isolated in `ZERO_TARGET_MELLIN_PHYSICAL_LCM_STENCIL`.

No norm, support count, RH assumption, or Mertens magnitude estimate appears.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

private theorem zeroTarget_lcm_prime_mul_left_of_not_dvd
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm (p * a) b = p * Nat.lcm a b := by
  apply Nat.dvd_antisymm
  · apply (Nat.lcm_dvd_iff).2
    constructor
    · exact Nat.mul_dvd_mul_left p (Nat.dvd_lcm_left a b)
    · rcases Nat.dvd_lcm_right a b with ⟨k, hk⟩
      refine ⟨p * k, ?_⟩
      rw [hk]
      ac_rfl
  · have hpTarget : p ∣ Nat.lcm (p * a) b :=
      (show p ∣ p * a from ⟨a, rfl⟩).trans (Nat.dvd_lcm_left (p * a) b)
    have haTarget : a ∣ Nat.lcm (p * a) b :=
      (show a ∣ p * a from ⟨p, by simp [Nat.mul_comm]⟩).trans
        (Nat.dvd_lcm_left (p * a) b)
    have hbTarget : b ∣ Nat.lcm (p * a) b := Nat.dvd_lcm_right (p * a) b
    have hlcmTarget : Nat.lcm a b ∣ Nat.lcm (p * a) b :=
      (Nat.lcm_dvd_iff).2 ⟨haTarget, hbTarget⟩
    have hlcmMul : Nat.lcm a b ∣ a * b := by
      apply (Nat.lcm_dvd_iff).2
      exact ⟨⟨b, rfl⟩, ⟨a, by simp [Nat.mul_comm]⟩⟩
    have hpNotLcm : ¬ p ∣ Nat.lcm a b := by
      intro hpLcm
      have hpMul : p ∣ a * b := hpLcm.trans hlcmMul
      rcases hp.dvd_mul.mp hpMul with hpA | hpB
      · exact hpa hpA
      · exact hpb hpB
    have hcop : Nat.Coprime p (Nat.lcm a b) :=
      hp.coprime_iff_not_dvd.mpr hpNotLcm
    exact hcop.mul_dvd_of_dvd_of_dvd hpTarget hlcmTarget

private theorem zeroTarget_lcm_prime_mul_right_of_not_dvd
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm a (p * b) = p * Nat.lcm a b := by
  calc
    Nat.lcm a (p * b) = Nat.lcm (p * b) a := Nat.lcm_comm _ _
    _ = p * Nat.lcm b a :=
      zeroTarget_lcm_prime_mul_left_of_not_dvd hp hpb hpa
    _ = p * Nat.lcm a b := by rw [Nat.lcm_comm b a]

/-- On a complete lower post-root parent pair the base indicator is zero and
all three child indicators are the same lower-scale LCM-wall indicator. -/
theorem physicalSuperLcmIndicators_postRoot_complete
    {W p a b : ℕ} (hp : p ∈ postRootPrimeFamilySet W)
    (hab : (a, b) ∈ mertensPositivePhysicalPairCarrier (W / p)) :
    physicalSuperLcmIndicator W a b = 0 ∧
    physicalSuperLcmIndicator W (p * a) b =
      superLcmIndicator (W / p) a b ∧
    physicalSuperLcmIndicator W a (p * b) =
      superLcmIndicator (W / p) a b ∧
    physicalSuperLcmIndicator W (p * a) (p * b) =
      superLcmIndicator (W / p) a b := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  rcases mem_mertensPositivePhysicalPairCarrier.mp hab with
    ⟨ha1, haq, hb1, hbq, _hablt⟩
  have hqLt : W / p < p :=
    (Nat.div_lt_iff_lt_mul hpPrime.pos).2 ((Nat.sqrt_lt).1 hpRoot)
  have hpa : ¬ p ∣ a := by
    intro hdiv
    exact (not_le.mpr (haq.trans_lt hqLt)) (Nat.le_of_dvd ha1 hdiv)
  have hpb : ¬ p ∣ b := by
    intro hdiv
    exact (not_le.mpr (hbq.trans_lt hqLt)) (Nat.le_of_dvd hb1 hdiv)
  have hqW : W / p ≤ W := Nat.div_le_self W p
  have haW : a ≤ W := haq.trans hqW
  have hbW : b ≤ W := hbq.trans hqW
  have hpaW : p * a ≤ W := by
    calc
      p * a ≤ p * (W / p) := Nat.mul_le_mul_left p haq
      _ ≤ W := by simpa [Nat.mul_comm] using Nat.div_mul_le_self W p
  have hpbW : p * b ≤ W := by
    calc
      p * b ≤ p * (W / p) := Nat.mul_le_mul_left p hbq
      _ ≤ W := by simpa [Nat.mul_comm] using Nat.div_mul_le_self W p
  have hlcmDvd : Nat.lcm a b ∣ a * b :=
    Nat.lcm_dvd_iff.mpr ⟨⟨b, rfl⟩, ⟨a, by ring⟩⟩
  have hL : Nat.lcm a b ≤ W := by
    calc
      Nat.lcm a b ≤ a * b := Nat.le_of_dvd (Nat.mul_pos ha1 hb1) hlcmDvd
      _ ≤ (W / p) * (W / p) := Nat.mul_le_mul haq hbq
      _ = (W / p) ^ 2 := by ring
      _ ≤ W := postRootPrimeFamily_quotient_sq_le hp
  have hcross : W < p * Nat.lcm a b ↔ W / p < Nat.lcm a b := by
    simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul hpPrime.pos :
        W / p < Nat.lcm a b ↔ W < Nat.lcm a b * p).symm
  have hleft := zeroTarget_lcm_prime_mul_left_of_not_dvd hpPrime hpa hpb
  have hright := zeroTarget_lcm_prime_mul_right_of_not_dvd hpPrime hpa hpb
  have hboth : Nat.lcm (p * a) (p * b) = p * Nat.lcm a b := by
    rw [Nat.lcm_mul_left]
  constructor
  · simp [physicalSuperLcmIndicator, superLcmIndicator, haW, hbW,
      Nat.not_lt.mpr hL]
  constructor
  · unfold physicalSuperLcmIndicator superLcmIndicator
    rw [if_pos ⟨hpaW, hbW⟩, hleft]
    by_cases h : W / p < Nat.lcm a b <;> simp [h, hcross]
  constructor
  · unfold physicalSuperLcmIndicator superLcmIndicator
    rw [if_pos ⟨haW, hpbW⟩, hright]
    by_cases h : W / p < Nat.lcm a b <;> simp [h, hcross]
  · unfold physicalSuperLcmIndicator superLcmIndicator
    rw [if_pos ⟨hpaW, hpbW⟩, hboth]
    by_cases h : W / p < Nat.lcm a b <;> simp [h, hcross]

/-- **Pointwise complete-cube Mellin collapse.** -/
theorem zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_eq_neg_factor_lower
    {W p a b : ℕ} (r : ℝ)
    (hp : p ∈ postRootPrimeFamilySet W)
    (hab : (a, b) ∈ mertensPositivePhysicalPairCarrier (W / p)) :
    zeroTargetMellinPhysicalSuperLcmFourCorner W p r a b =
      -(r * (2 - r)) *
        (postRootZeroTargetPairExcess (a, b) *
          superLcmIndicator (W / p) a b) := by
  rcases physicalSuperLcmIndicators_postRoot_complete hp hab with
    ⟨h00, h10, h01, h11⟩
  unfold zeroTargetMellinPhysicalSuperLcmFourCorner
    physicalSuperLcmMellinStencil
  rw [h00, h10, h01, h11]
  ring

/-- **Aggregate complete-family identity.**  The Mellin-weighted complete
post-root family is exactly a scalar multiple of the nonnegative lower LCM
boundary kernel. -/
theorem sum_zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_eq_neg_factor_lower
    {W p : ℕ} (r : ℝ) (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
      zeroTargetMellinPhysicalSuperLcmFourCorner W p r mn.1 mn.2) =
      -(r * (2 - r)) * fullLcmBoundaryKernel (W / p) := by
  rw [fullLcmBoundaryKernel_eq_sum_superLcmIndicator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mn hmn
  rw [zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_eq_neg_factor_lower
    r hp hmn, postRootZeroTargetPairExcess_eq_weight]

/-- Every complete post-root Mellin family is nonpositive whenever
`0 <= r <= 2`. -/
theorem sum_zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_nonpos
    {W p : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
      zeroTargetMellinPhysicalSuperLcmFourCorner W p r mn.1 mn.2) ≤ 0 := by
  rw [sum_zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_eq_neg_factor_lower
    r hp]
  have hfactor : 0 ≤ r * (2 - r) := mul_nonneg hr0 (sub_nonneg.mpr hr2)
  have hkernel : 0 ≤ fullLcmBoundaryKernel (W / p) :=
    fullLcmBoundaryKernel_nonneg (W / p)
  nlinarith

/-- The same conclusion for owner-dependent Mellin ratios.  Thus after summing
all complete post-root families, no positive covariance can come from the
complete-cube part; only incomplete clipped edges remain. -/
theorem sum_all_zeroTargetMellinCompletePostRootFamilies_nonpos
    (W : ℕ) (r : ℕ → ℝ)
    (hr0 : ∀ p ∈ postRootPrimeFamilySet W, 0 ≤ r p)
    (hr2 : ∀ p ∈ postRootPrimeFamilySet W, r p ≤ 2) :
    (∑ p ∈ postRootPrimeFamilySet W,
      ∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
        zeroTargetMellinPhysicalSuperLcmFourCorner W p (r p) mn.1 mn.2) ≤ 0 := by
  apply Finset.sum_nonpos
  intro p hp
  exact sum_zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_nonpos
    (hr0 p hp) (hr2 p hp) hp

end RHLean.Proof
