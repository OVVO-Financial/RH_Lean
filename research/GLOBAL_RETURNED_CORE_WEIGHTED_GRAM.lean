import Mathlib
import «research.GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE»

/-!
# Global returned-core Gram: first-owner factorization

After putting the reciprocal q² daughters on one Möbius clock, the relevant
zero-frequency amplitude is a scalar-weighted Möbius trajectory.  On a complete
fresh-prime square, *any* scalar site weight has an exact factorization: the
four signed Möbius corners are the parent zero-target excess times the product
of the two one-dimensional owner differences.

For the actual AMP weight, those one-dimensional differences are not assumed to
be a constant Mellin ratio.  They are proved below to be exactly a signed sum of
explicit threshold crossings: reciprocal q² daughter-window crossings minus
the root-tail crossing.  This is the global boundary object that must telescope
before the clipped `79/81` exit is applied.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The complementary-tail indicator in the exact rough-correlation identity. -/
def lowOwnerFarTailWeight (R n : ℕ) : ℝ :=
  if R ≤ n then 1 else 0

/-- Site coefficient of the single real zero-frequency AMP trajectory. -/
def lowOwnerZeroFrequencyMobiusWeight (R n : ℕ) : ℝ :=
  lowOwnerFarTailWeight R n + lowOwnerReciprocalDaughterWeight R n

/-- The actual weighted Möbius site. -/
def lowOwnerZeroFrequencyMobiusSite (R n : ℕ) : ℝ :=
  lowOwnerZeroFrequencyMobiusWeight R n * realMoebiusStep n

/-- The AMP site coefficient is nonnegative. -/
theorem lowOwnerZeroFrequencyMobiusWeight_nonneg (R n : ℕ) :
    0 ≤ lowOwnerZeroFrequencyMobiusWeight R n := by
  unfold lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailWeight
  have hd := lowOwnerReciprocalDaughterWeight_nonneg R n
  split <;> norm_num <;> linarith

/-- Four complete signed fresh-prime corners for an arbitrary scalar site
weight. -/
def weightedMoebiusFreshPrimeFourCornerMass
    (w : ℕ → ℝ) (p a b : ℕ) : ℝ :=
  (w a * realMoebiusStep a) * (w b * realMoebiusStep b) +
  (w (p * a) * realMoebiusStep (p * a)) * (w b * realMoebiusStep b) +
  (w a * realMoebiusStep a) * (w (p * b) * realMoebiusStep (p * b)) +
  (w (p * a) * realMoebiusStep (p * a)) *
    (w (p * b) * realMoebiusStep (p * b))

/-- **Generic complete-owner factorization.**  Fresh-prime Möbius sign reversal
turns the full Gram square into a product of one-dimensional owner differences.
No probabilistic or independence input is present. -/
theorem weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
    (w : ℕ → ℝ) {p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    weightedMoebiusFreshPrimeFourCornerMass w p a b =
      postRootZeroTargetPairExcess (a, b) *
        (w a - w (p * a)) * (w b - w (p * b)) := by
  unfold weightedMoebiusFreshPrimeFourCornerMass
  rw [realMoebiusStep_mul_prime_eq_neg hp hpa,
    realMoebiusStep_mul_prime_eq_neg hp hpb]
  simp only [postRootZeroTargetPairExcess_eq_weight,
    zeroTargetPairExcess_eq_mul]
  ring

/-- Root-tail part of one owner difference. -/
def lowOwnerRootCrossingIndicator (R p n : ℕ) : ℝ :=
  if n < R ∧ R ≤ p * n then 1 else 0

/-- Reciprocal daughter windows crossed by multiplication by the current owner. -/
def lowOwnerDaughterCrossingWeight (R p n : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    if n ≤ rawQ2ChildCutoff R q ∧ rawQ2ChildCutoff R q < p * n then
      1 / (q : ℝ)
    else 0

/-- One reciprocal daughter indicator loses exactly its threshold-crossing mass
when the physical site is multiplied by a positive owner. -/
theorem lowOwnerReciprocalDaughterWeight_sub_mul
    {R p n : ℕ} (hp : 1 ≤ p) :
    lowOwnerReciprocalDaughterWeight R n -
        lowOwnerReciprocalDaughterWeight R (p * n) =
      lowOwnerDaughterCrossingWeight R p n := by
  unfold lowOwnerReciprocalDaughterWeight lowOwnerDaughterCrossingWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  have hnp : n ≤ p * n := by
    calc
      n = 1 * n := by simp
      _ ≤ p * n := Nat.mul_le_mul_right n hp
  by_cases hn : n ≤ rawQ2ChildCutoff R q
  · by_cases hpn : p * n ≤ rawQ2ChildCutoff R q
    · simp [hn, hpn]
    · have hlt : rawQ2ChildCutoff R q < p * n := Nat.lt_of_not_ge hpn
      simp [hn, hpn, hlt]
  · have hpn : ¬ p * n ≤ rawQ2ChildCutoff R q := by
      intro hbad
      exact hn (hnp.trans hbad)
    simp [hn, hpn]

/-- The complementary-tail indicator contributes exactly the *negative* root
crossing when the owner is multiplied in. -/
theorem lowOwnerFarTailWeight_sub_mul
    {R p n : ℕ} (hp : 1 ≤ p) :
    lowOwnerFarTailWeight R n - lowOwnerFarTailWeight R (p * n) =
      -lowOwnerRootCrossingIndicator R p n := by
  unfold lowOwnerFarTailWeight lowOwnerRootCrossingIndicator
  have hnp : n ≤ p * n := by
    calc
      n = 1 * n := by simp
      _ ≤ p * n := Nat.mul_le_mul_right n hp
  by_cases hnR : R ≤ n
  · have hpnR : R ≤ p * n := hnR.trans hnp
    simp [hnR, hpnR]
  · have hnlt : n < R := Nat.lt_of_not_ge hnR
    by_cases hpnR : R ≤ p * n
    · simp [hnR, hnlt, hpnR]
    · simp [hnR, hnlt, hpnR]

/-- **Exact AMP owner difference.**  The common-clock site weight has no hidden
owner term: its one-dimensional fresh-prime difference is precisely daughter
threshold crossings minus the root-tail crossing. -/
theorem lowOwnerZeroFrequencyMobiusWeight_sub_mul
    {R p n : ℕ} (hp : 1 ≤ p) :
    lowOwnerZeroFrequencyMobiusWeight R n -
        lowOwnerZeroFrequencyMobiusWeight R (p * n) =
      lowOwnerDaughterCrossingWeight R p n -
        lowOwnerRootCrossingIndicator R p n := by
  unfold lowOwnerZeroFrequencyMobiusWeight
  rw [lowOwnerFarTailWeight_sub_mul hp,
    lowOwnerReciprocalDaughterWeight_sub_mul hp]
  ring

/-- Specialization of the generic complete-owner Gram factorization to the
actual zero-frequency AMP trajectory. -/
theorem lowOwnerZeroFrequencyFreshPrimeFourCorner_eq_crossingProduct
    {R p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerZeroFrequencyMobiusWeight R) p a b =
      postRootZeroTargetPairExcess (a, b) *
        (lowOwnerDaughterCrossingWeight R p a -
          lowOwnerRootCrossingIndicator R p a) *
        (lowOwnerDaughterCrossingWeight R p b -
          lowOwnerRootCrossingIndicator R p b) := by
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerZeroFrequencyMobiusWeight R) hp hpa hpb,
    lowOwnerZeroFrequencyMobiusWeight_sub_mul hp.one_le,
    lowOwnerZeroFrequencyMobiusWeight_sub_mul hp.one_le]

end RHLean.Proof
