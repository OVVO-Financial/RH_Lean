import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_ARBITRARY_SITE_CELLS»
import «research.GLOBAL_RETURNED_CORE_POST755_AMPLITUDE_CLOSURE»
import «research.GLOBAL_RETURNED_CORE_WEIGHTED_GRAM»

/-!
# Reciprocal q² prefix energy in first-owner currency

The genuinely recursive q² coordinate is the single signed prefix site

  S_R(n) = w_R(n) * mu(n),

where

  w_R(n) = sum_{q : n <= Y_q} 1/q.

Its total amplitude is exactly the reciprocal Mertens column
`sum_q M(Y_q)/q`.  Therefore all q=q' and q!=q' covariance terms remain
assembled before the square.

The global least-owner Fubini gives an exact first-separation partition of this
one Gram.  Since the diagonal is nonnegative and the reciprocal-square frame is
at most 1/4, the complete ordered first-owner mass costs at most 1/4 of the
literal q² daughter energy, and the existing oriented raw-parent cell carrier
costs at most 1/8.

Finally, the fresh-p owner difference of the scalar prefix weight is exactly the
daughter crossing field.  Hence its complete p-four-corner is literally the
q² threshold-incidence pair product used by the returned-core descent.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed common-clock reciprocal q² prefix site. -/
def lowOwnerReciprocalPrefixSignedSite
    (R n : ℕ) : ℝ :=
  lowOwnerReciprocalDaughterWeight R n * realMoebiusStep n

/-- Removing zero-Mobius sites from the common clock does not change the
reciprocal prefix amplitude. -/
theorem sum_lowOwnerReciprocalPrefixSignedSite_eq_column
    (R : ℕ) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      lowOwnerReciprocalPrefixSignedSite R n) =
      lowOwnerReciprocalMertensColumnReal R := by
  rw [lowOwnerReciprocalMertensColumnReal_eq_weightedMobiusSum]
  unfold lowOwnerReciprocalPrefixSignedSite lowOwnerNonzeroMobiusCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmu : realMoebiusStep n ≠ 0
  · simp [hmu]
  · have hz : realMoebiusStep n = 0 := not_ne_iff.mp hmu
    simp [hz]

/-- Empty revealed energy is exactly the square of the one reciprocal Mertens
column. -/
theorem lowOwnerReciprocalPrefix_emptyEnergy_eq_column_sq
    (R : ℕ) :
    lowOwnerRevealedPairMassWith R ∅
        (lowOwnerReciprocalPrefixSignedSite R) =
      lowOwnerReciprocalMertensColumnReal R ^ 2 := by
  rw [lowOwnerRevealedPairMassWith_empty_eq_sum_sq]
  rw [sum_lowOwnerReciprocalPrefixSignedSite_eq_column]

/-- **Quarter q² bound on the complete ordered first-owner prefix Gram.** -/
theorem sum_lowOwnerReciprocalPrefix_firstOwnerMass_le_quarter_q2Energy
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerGlobalFirstOwnerPairMassWith R p
        (lowOwnerReciprocalPrefixSignedSite R)) ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have hfirst :=
    sum_lowOwnerGlobalFirstOwnerPairMassWith_le_emptyEnergy
      R (lowOwnerReciprocalPrefixSignedSite R)
  rw [lowOwnerReciprocalPrefix_emptyEnergy_eq_column_sq] at hfirst
  exact hfirst.trans
    (lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R)

/-- **Eighth q² bound on the exact oriented raw-parent cell carrier.** -/
theorem sum_lowOwnerReciprocalPrefix_cellMass_le_eighth_q2Energy
    (R : ℕ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerCellGramWith R p sig
          (lowOwnerReciprocalPrefixSignedSite R)) ≤
      (1 / 8 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have hquarter :=
    sum_lowOwnerReciprocalPrefix_firstOwnerMass_le_quarter_q2Energy R
  have hrewrite :
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerPairMassWith R p
          (lowOwnerReciprocalPrefixSignedSite R)) =
        2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerReciprocalPrefixSignedSite R)) := by
    calc
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerPairMassWith R p
          (lowOwnerReciprocalPrefixSignedSite R)) =
        ∑ p ∈ primesUpTo (squareRootEndpoint R),
          2 * (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerReciprocalPrefixSignedSite R)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
            (mem_primesUpTo.mp hp).1
            (lowOwnerReciprocalPrefixSignedSite R)
      _ = 2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerReciprocalPrefixSignedSite R)) := by
          rw [Finset.mul_sum]
  rw [hrewrite] at hquarter
  nlinarith

/-- The scalar reciprocal prefix weight loses exactly the q² daughter crossing
field along a positive owner edge. -/
theorem lowOwnerReciprocalPrefixWeight_sub_mul
    {R p n : ℕ} (hp : 1 ≤ p) :
    lowOwnerReciprocalDaughterWeight R n -
        lowOwnerReciprocalDaughterWeight R (p * n) =
      lowOwnerDaughterCrossingWeight R p n :=
  lowOwnerReciprocalDaughterWeight_sub_mul hp

/-- **Exact q² four-corner dictionary.**

The complete fresh-p four-corner of the reciprocal prefix site is exactly the
signed q² threshold-incidence pair product. -/
theorem lowOwnerReciprocalPrefixFourCorner_eq_daughterCrossingProduct
    {R p a b : ℕ}
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerReciprocalDaughterWeight R) p a b =
      postRootZeroTargetPairExcess (a, b) *
        lowOwnerDaughterCrossingWeight R p a *
        lowOwnerDaughterCrossingWeight R p b := by
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerReciprocalDaughterWeight R) hp hpa hpb,
    lowOwnerReciprocalDaughterWeight_sub_mul hp.one_le,
    lowOwnerReciprocalDaughterWeight_sub_mul hp.one_le]

end RHLean.Proof
