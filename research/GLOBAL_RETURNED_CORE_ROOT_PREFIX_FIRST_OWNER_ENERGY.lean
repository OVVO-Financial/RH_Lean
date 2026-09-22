
import Mathlib
import «research.GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY»
import RHLean.Proof.SquareRootLegalAncestryGramReduction

/-!
# Root prefix in the same first-owner energy currency as the q² prefix

The complementary tail coefficient is one minus the lower-root prefix on the
positive physical clock. Constants disappear under a fresh-prime difference,
so the root part of the actual AMP owner gradient is carried by the signed
root-prefix site Z_R(n) = 1_{n<R} * mu(n).

Its fresh-p difference is exactly the compiled root crossing indicator. Its
total amplitude is M(R-1), which lies inside LowerMertensCriticalEnvelope.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

def lowOwnerRootPrefixWeight (R n : ℕ) : ℝ :=
  if n < R then 1 else 0

def lowOwnerRootPrefixSignedSite (R n : ℕ) : ℝ :=
  lowOwnerRootPrefixWeight R n * realMoebiusStep n

theorem lowOwnerRootPrefixWeight_sub_mul
    {R p n : ℕ} (hp : 1 ≤ p) :
    lowOwnerRootPrefixWeight R n -
        lowOwnerRootPrefixWeight R (p * n) =
      lowOwnerRootCrossingIndicator R p n := by
  unfold lowOwnerRootPrefixWeight lowOwnerRootCrossingIndicator
  have hnp : n ≤ p * n := by
    calc
      n = 1 * n := by simp
      _ ≤ p * n := Nat.mul_le_mul_right n hp
  by_cases hn : n < R
  · by_cases hpn : p * n < R
    · have hnot : ¬ R ≤ p * n := Nat.not_le_of_gt hpn
      simp [hn, hpn, hnot]
    · have hRpn : R ≤ p * n := Nat.le_of_not_gt hpn
      simp [hn, hpn, hRpn]
  · have hRn : R ≤ n := Nat.le_of_not_gt hn
    have hRpn : R ≤ p * n := hRn.trans hnp
    simp [hn, hRpn, Nat.not_lt_of_ge hRpn]

theorem sum_lowOwnerRootPrefixSignedSite_eq_mertensPred
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      lowOwnerRootPrefixSignedSite R n) =
      (mertensSummatoryInt (R - 1) : ℝ) := by
  let X := squareRootEndpoint R
  let g : ℕ → ℝ := fun n => lowOwnerRootPrefixSignedSite R n
  have hRX : R ≤ X := le_squareRootEndpoint_self hR
  have hpredX : R - 1 ≤ X := by omega
  have hremove :
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier R, g n) =
        ∑ n ∈ Finset.Icc 1 X, g n := by
    unfold lowOwnerNonzeroMobiusCarrier
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hmu : realMoebiusStep n ≠ 0
    · simp [hmu, g]
    · have hz : realMoebiusStep n = 0 := not_ne_iff.mp hmu
      simp [hz, g, lowOwnerRootPrefixSignedSite]
  have hsub : Finset.Icc 1 (R - 1) ⊆ Finset.Icc 1 X := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnR⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hnR.trans hpredX⟩
  have hzero :
      ∀ n ∈ Finset.Icc 1 X, n ∉ Finset.Icc 1 (R - 1) → g n = 0 := by
    intro n hnX hnnot
    have hRn : R ≤ n := by
      have hn1 := (Finset.mem_Icc.mp hnX).1
      by_contra hbad
      have hnR : n ≤ R - 1 := by omega
      exact hnnot (Finset.mem_Icc.mpr ⟨hn1, hnR⟩)
    simp [g, lowOwnerRootPrefixSignedSite, lowOwnerRootPrefixWeight,
      Nat.not_lt_of_ge hRn]
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      lowOwnerRootPrefixSignedSite R n) =
        ∑ n ∈ lowOwnerNonzeroMobiusCarrier R, g n := by rfl
    _ = ∑ n ∈ Finset.Icc 1 X, g n := hremove
    _ = ∑ n ∈ Finset.Icc 1 (R - 1), g n :=
      (Finset.sum_subset hsub hzero).symm
    _ = ∑ n ∈ Finset.Icc 1 (R - 1), realMoebiusStep n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnR : n < R := by
        have hnle := (Finset.mem_Icc.mp hn).2
        omega
      simp [g, lowOwnerRootPrefixSignedSite, lowOwnerRootPrefixWeight, hnR]
    _ = (mertensSummatoryInt (R - 1) : ℝ) := by
      rw [mertensSummatoryInt_eq_Icc]
      push_cast
      simp [realMoebiusStep]

theorem lowOwnerRootPrefix_emptyEnergy_eq_mertensPred_sq
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerRevealedPairMassWith R ∅
        (lowOwnerRootPrefixSignedSite R) =
      ((mertensSummatoryInt (R - 1) : ℝ) ^ 2) := by
  rw [lowOwnerRevealedPairMassWith_empty_eq_sum_sq]
  rw [sum_lowOwnerRootPrefixSignedSite_eq_mertensPred hR]

private theorem lowerEnvelope_one_le_rootPrefix
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  have hm0 : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  rw [hm0] at h0
  norm_num at h0
  exact h0

theorem mertensPred_sq_le_four_root_mul_lowerEnvelope
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    ((mertensSummatoryInt (R - 1) : ℝ) ^ 2) ≤
      4 * (R : ℝ) * K := by
  have hpred := hK.2 (R - 1) (by omega)
  have hshift :
      (((mertensSummatoryInt (R - 1) - 1 : ℤ) : ℝ)) =
        (mertensSummatoryInt (R - 1) : ℝ) - 1 := by
    push_cast
    ring
  rw [hshift] at hpred
  have hcast : (((R - 1 + 1 : ℕ) : ℝ)) = (R : ℝ) := by
    have : R - 1 + 1 = R := by omega
    rw [this]
  rw [hcast] at hpred
  have hK1 := lowerEnvelope_one_le_rootPrefix (R := R) (K := K) (by omega) hK
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hRK : 1 ≤ (R : ℝ) * K := by nlinarith
  nlinarith [sq_nonneg ((mertensSummatoryInt (R - 1) : ℝ) - 1)]

theorem sum_lowOwnerRootPrefix_firstOwnerMass_le_four_root_mul_envelope
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerGlobalFirstOwnerPairMassWith R p
        (lowOwnerRootPrefixSignedSite R)) ≤
      4 * (R : ℝ) * K := by
  have hfirst :=
    sum_lowOwnerGlobalFirstOwnerPairMassWith_le_emptyEnergy
      R (lowOwnerRootPrefixSignedSite R)
  rw [lowOwnerRootPrefix_emptyEnergy_eq_mertensPred_sq hR] at hfirst
  exact hfirst.trans
    (mertensPred_sq_le_four_root_mul_lowerEnvelope hR hK)

theorem sum_lowOwnerRootPrefix_cellMass_le_two_root_mul_envelope
    {R : ℕ} {K : ℝ} (hR : 2 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerCellGramWith R p sig
          (lowOwnerRootPrefixSignedSite R)) ≤
      2 * (R : ℝ) * K := by
  have hfour :=
    sum_lowOwnerRootPrefix_firstOwnerMass_le_four_root_mul_envelope hR hK
  have hrewrite :
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerPairMassWith R p
          (lowOwnerRootPrefixSignedSite R)) =
        2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerRootPrefixSignedSite R)) := by
    calc
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerPairMassWith R p
          (lowOwnerRootPrefixSignedSite R)) =
        ∑ p ∈ primesUpTo (squareRootEndpoint R),
          2 * (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerRootPrefixSignedSite R)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
            (mem_primesUpTo.mp hp).1
            (lowOwnerRootPrefixSignedSite R)
      _ = 2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerRootPrefixSignedSite R)) := by
          rw [Finset.mul_sum]
  rw [hrewrite] at hfour
  nlinarith

theorem lowOwnerRootPrefixFourCorner_eq_rootCrossingProduct
    {R p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerRootPrefixWeight R) p a b =
      postRootZeroTargetPairExcess (a, b) *
        lowOwnerRootCrossingIndicator R p a *
        lowOwnerRootCrossingIndicator R p b := by
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerRootPrefixWeight R) hp hpa hpb,
    lowOwnerRootPrefixWeight_sub_mul hp.one_le,
    lowOwnerRootPrefixWeight_sub_mul hp.one_le]

end RHLean.Proof
