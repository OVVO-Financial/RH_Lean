import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_SIGNED_DESCENT»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DOUBLE_CORNER_RECIPROCAL»

/-!
# Double-corner Fubini stays inside the signed Dirichlet polarization

The pointwise commuting-incidence identity is

  clippedDiff_p,r(u;y) = chi_p(u;y) - doubleCorner_p,r(u;y).

Integrating against the finite AMP threshold measure gives

  Delta_r g_p(u) = g_p(u) - D_p,r(u),

where `D_p,r` is the signed finite double-corner Fubini.  Substituting this into
the exact signed fresh-prime descent cancels the parent `g_p(u)g_p(v)` term
before any norm:

  W_g(r*u,v) = -mu(u)mu(v) D_p,r(u) g_p(v),

and symmetrically in the second endpoint.

This is the legal treatment of the clipped population.  No standalone clipped
square is introduced, and no `1/9` estimate is applied to `D_p,r` here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Finite signed Fubini of the genuine p/r double-corner boundary. -/
def lowOwnerThresholdDoubleCornerFubini
    (R p r n : ℕ) : ℝ :=
  (∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℝ)) *
      lowOwnerThresholdDoubleCornerBoundary
        p r n (rawQ2ChildCutoff R q)) -
    lowOwnerThresholdDoubleCornerBoundary p r n (R - 1)

/-- **Integrated two-boundary decomposition.**  The next-owner difference is
current p-incidence minus the signed double-corner Fubini. -/
theorem lowOwnerThresholdSecondOwnerDifference_eq_current_sub_doubleCornerFubini
    {R p r n : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime)
    (hpr : p < r) (hn : 0 < n) :
    lowOwnerThresholdSecondOwnerDifference R p r n =
      lowOwnerThresholdOwnerIncidenceWeight R p n -
        lowOwnerThresholdDoubleCornerFubini R p r n := by
  rw [lowOwnerThresholdSecondOwnerDifference_eq_clippedFubini
    hR hp.one_le hr.one_le]
  rw [lowOwnerThresholdOwnerIncidenceWeight_eq_finiteThresholdEval
    hR hp.one_le]
  unfold lowOwnerThresholdDoubleCornerFubini
  have hsum :
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerThresholdClippedDifference
            p r n (rawQ2ChildCutoff R q)) =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerThresholdCrossingIndicator
            p n (rawQ2ChildCutoff R q)) -
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerThresholdDoubleCornerBoundary
            p r n (rawQ2ChildCutoff R q)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [lowOwnerThresholdClippedDifference_eq_current_sub_doubleCorner
      hp hr hpr hn]
    ring
  have hroot := lowOwnerThresholdClippedDifference_eq_current_sub_doubleCorner
    (W := R - 1) hp hr hpr hn
  rw [hsum, hroot]
  ring

/-- **Left signed descent after polarization.**  The parent term cancels
exactly, leaving only the double-corner Fubini.  This is not an estimate. -/
theorem lowOwnerThresholdIncidencePairMass_eq_neg_leftDoubleCornerFubini
    {R p r a b : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hra : r ∣ a) (hrb : ¬ r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    lowOwnerThresholdIncidencePairMass R p (a, b) =
      -postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdDoubleCornerFubini R p r u *
        lowOwnerThresholdOwnerIncidenceWeight R p v := by
  dsimp only
  let u := squarefreePrimeFamilyParent r a
  let v := squarefreePrimeFamilyParent r b
  have hparent := arbitraryFreshPrime_left_parent_data hra hrb
  dsimp only at hparent
  have huPos : 0 < u := squarefreePrimeFamilyParent_pos_public hr ha
  have hdesc := lowOwnerThresholdIncidencePairMass_add_parent_eq_leftDifference
    (R := R) (p := p) hr haSq hbSq ha hb hra hrb
  dsimp only at hdesc
  rw [lowOwnerThresholdSecondOwnerDifference_eq_current_sub_doubleCornerFubini
    hR hp hr hpr huPos] at hdesc
  unfold lowOwnerThresholdIncidencePairMass at hdesc
  linear_combination hdesc

/-- **Right signed descent after polarization.** -/
theorem lowOwnerThresholdIncidencePairMass_eq_neg_rightDoubleCornerFubini
    {R p r a b : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hra : ¬ r ∣ a) (hrb : r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    lowOwnerThresholdIncidencePairMass R p (a, b) =
      -postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdOwnerIncidenceWeight R p u *
        lowOwnerThresholdDoubleCornerFubini R p r v := by
  dsimp only
  let u := squarefreePrimeFamilyParent r a
  let v := squarefreePrimeFamilyParent r b
  have hvPos : 0 < v := squarefreePrimeFamilyParent_pos_public hr hb
  have hdesc := lowOwnerThresholdIncidencePairMass_add_parent_eq_rightDifference
    (R := R) (p := p) hr haSq hbSq ha hb hra hrb
  dsimp only at hdesc
  rw [lowOwnerThresholdSecondOwnerDifference_eq_current_sub_doubleCornerFubini
    hR hp hr hpr hvPos] at hdesc
  unfold lowOwnerThresholdIncidencePairMass at hdesc
  linear_combination hdesc

/-- Orientation-free form for a greatest-owner fresh coordinate.  Exactly one
endpoint carries the owner, and after parent cancellation the child mass is a
single double-corner Fubini residual. -/
theorem descendingGreatestOwner_thresholdIncidence_eq_doubleCornerFubini
    {R p r a b : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet a b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    (lowOwnerThresholdIncidencePairMass R p (a, b) =
      -postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdDoubleCornerFubini R p r u *
        lowOwnerThresholdOwnerIncidenceWeight R p v) ∨
    (lowOwnerThresholdIncidencePairMass R p (a, b) =
      -postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdOwnerIncidenceWeight R p u *
        lowOwnerThresholdDoubleCornerFubini R p r v) := by
  have hxor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor hr ha hb).1 hrFresh
  rcases hxor with hleft | hright
  · exact Or.inl
      (lowOwnerThresholdIncidencePairMass_eq_neg_leftDoubleCornerFubini
        hR hp hr hpr haSq hbSq ha hb hleft.1 hleft.2)
  · exact Or.inr
      (lowOwnerThresholdIncidencePairMass_eq_neg_rightDoubleCornerFubini
        hR hp hr hpr haSq hbSq ha hb hright.2 hright.1)

end RHLean.Proof
