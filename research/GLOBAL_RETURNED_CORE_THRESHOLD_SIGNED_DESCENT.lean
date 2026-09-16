import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_CLIPPED_FUBINI»
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_FRESH_PRIME_DESCENT»

/-!
# Signed fresh-prime descent of the threshold-incidence kernel

The reciprocal normalization must not be applied to the positive compensated
square in isolation: its Euler factors cancel the reciprocal denominators.
The correct operation is to retain the signed owner descent before estimating.

For the current threshold-incidence coordinate

  g_p(n) = F_R(n) - F_R(p*n),

put

  W_g(a,b) = mu(a) mu(b) g_p(a) g_p(b).

If a fresh prime `r` divides exactly one endpoint, stripping `r` reverses the
Mobius pair sign.  Suppose `a = r*u` and `b = v`.  Then, exactly,

  W_g(r*u,v) + W_g(u,v)
    = mu(u)mu(v) * (g_p(u)-g_p(r*u)) * g_p(v).

The parent term cancels before any norm.  The remaining one-coordinate
difference is already the finite clipped Fubini compiled in
`GLOBAL_RETURNED_CORE_THRESHOLD_CLIPPED_FUBINI`: it is a signed sum of literal
r-clipped threshold edges at the q^2 daughter thresholds and at `R-1`.

The symmetric formula holds when r is inserted in the second endpoint.  This is
the exact signed dictionary that was missing between the kernel coordinate and
the clipped-edge geometry.  No Cauchy--Schwarz, spectral tail estimate, or
reciprocal energy contraction is used in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Weighted zero-target pair mass in the current threshold-incidence
coordinate. -/
def lowOwnerThresholdIncidencePairMass
    (R p : ℕ) (mn : ℕ × ℕ) : ℝ :=
  postRootZeroTargetPairExcess mn *
    lowOwnerThresholdOwnerIncidenceWeight R p mn.1 *
    lowOwnerThresholdOwnerIncidenceWeight R p mn.2

/-- On p-free endpoints, this is exactly the product of the actual compensated
AMP signed sites. -/
theorem lowOwnerThresholdIncidencePairMass_eq_compensatedSites
    {R p a b : ℕ} (hp : 1 ≤ p) :
    lowOwnerThresholdIncidencePairMass R p (a, b) =
      ((lowOwnerDaughterCrossingWeight R p a -
          lowOwnerRootCrossingIndicator R p a) * realMoebiusStep a) *
      ((lowOwnerDaughterCrossingWeight R p b -
          lowOwnerRootCrossingIndicator R p b) * realMoebiusStep b) := by
  unfold lowOwnerThresholdIncidencePairMass
  rw [postRootZeroTargetPairExcess_eq_weight,
    lowOwnerThresholdOwnerIncidenceWeight_eq_crossing hp,
    lowOwnerThresholdOwnerIncidenceWeight_eq_crossing hp]
  ring

/-- Left-oriented fresh-prime parent identities. -/
theorem arbitraryFreshPrime_left_parent_data
    {r a b : ℕ} (hra : r ∣ a) (hrb : ¬ r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    a = r * u ∧ b = v := by
  dsimp only
  unfold squarefreePrimeFamilyParent
  rw [if_pos hra, if_neg hrb]
  exact ⟨(Nat.mul_div_cancel' hra).symm, rfl⟩

/-- Right-oriented fresh-prime parent identities. -/
theorem arbitraryFreshPrime_right_parent_data
    {r a b : ℕ} (hra : ¬ r ∣ a) (hrb : r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    a = u ∧ b = r * v := by
  dsimp only
  unfold squarefreePrimeFamilyParent
  rw [if_neg hra, if_pos hrb]
  exact ⟨rfl, (Nat.mul_div_cancel' hrb).symm⟩

/-- **Signed descent, owner inserted in the first endpoint.** -/
theorem lowOwnerThresholdIncidencePairMass_add_parent_eq_leftDifference
    {R p r a b : ℕ}
    (hr : r.Prime) (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hra : r ∣ a) (hrb : ¬ r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    lowOwnerThresholdIncidencePairMass R p (a, b) +
        lowOwnerThresholdIncidencePairMass R p (u, v) =
      postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdSecondOwnerDifference R p r u *
        lowOwnerThresholdOwnerIncidenceWeight R p v := by
  dsimp only
  let u := squarefreePrimeFamilyParent r a
  let v := squarefreePrimeFamilyParent r b
  have hdata := arbitraryFreshPrime_left_parent_data hra hrb
  dsimp only at hdata
  have hsign := arbitraryFreshPrime_pairWeight_eq_neg_parentPairWeight
    hr haSq hbSq ha hb (Or.inl ⟨hra, hrb⟩)
  have hsignUV :
      realMoebiusStep a * realMoebiusStep b =
        -(realMoebiusStep u * realMoebiusStep v) := by
    simpa [u, v] using hsign
  have haEq : a = r * u := by simpa [u, v] using hdata.1
  have hbEq : b = v := by simpa [u, v] using hdata.2
  unfold lowOwnerThresholdIncidencePairMass
  rw [postRootZeroTargetPairExcess_eq_weight,
    postRootZeroTargetPairExcess_eq_weight]
  change
    (realMoebiusStep a * realMoebiusStep b) *
        lowOwnerThresholdOwnerIncidenceWeight R p a *
        lowOwnerThresholdOwnerIncidenceWeight R p b +
      (realMoebiusStep u * realMoebiusStep v) *
        lowOwnerThresholdOwnerIncidenceWeight R p u *
        lowOwnerThresholdOwnerIncidenceWeight R p v = _
  rw [hsignUV, haEq, hbEq]
  unfold lowOwnerThresholdSecondOwnerDifference
  ring

/-- **Signed descent, owner inserted in the second endpoint.** -/
theorem lowOwnerThresholdIncidencePairMass_add_parent_eq_rightDifference
    {R p r a b : ℕ}
    (hr : r.Prime) (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hra : ¬ r ∣ a) (hrb : r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    lowOwnerThresholdIncidencePairMass R p (a, b) +
        lowOwnerThresholdIncidencePairMass R p (u, v) =
      postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdOwnerIncidenceWeight R p u *
        lowOwnerThresholdSecondOwnerDifference R p r v := by
  dsimp only
  let u := squarefreePrimeFamilyParent r a
  let v := squarefreePrimeFamilyParent r b
  have hdata := arbitraryFreshPrime_right_parent_data hra hrb
  dsimp only at hdata
  have hsign := arbitraryFreshPrime_pairWeight_eq_neg_parentPairWeight
    hr haSq hbSq ha hb (Or.inr ⟨hrb, hra⟩)
  have hsignUV :
      realMoebiusStep a * realMoebiusStep b =
        -(realMoebiusStep u * realMoebiusStep v) := by
    simpa [u, v] using hsign
  have haEq : a = u := by simpa [u, v] using hdata.1
  have hbEq : b = r * v := by simpa [u, v] using hdata.2
  unfold lowOwnerThresholdIncidencePairMass
  rw [postRootZeroTargetPairExcess_eq_weight,
    postRootZeroTargetPairExcess_eq_weight]
  change
    (realMoebiusStep a * realMoebiusStep b) *
        lowOwnerThresholdOwnerIncidenceWeight R p a *
        lowOwnerThresholdOwnerIncidenceWeight R p b +
      (realMoebiusStep u * realMoebiusStep v) *
        lowOwnerThresholdOwnerIncidenceWeight R p u *
        lowOwnerThresholdOwnerIncidenceWeight R p v = _
  rw [hsignUV, haEq, hbEq]
  unfold lowOwnerThresholdSecondOwnerDifference
  ring

/-- **Left residual is literally the finite r-clipped threshold Fubini.** -/
theorem lowOwnerThresholdIncidencePairMass_add_parent_eq_leftClippedFubini
    {R p r a b : ℕ}
    (hR : 1 ≤ R) (hp : 1 ≤ p) (hr : r.Prime)
    (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hra : r ∣ a) (hrb : ¬ r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    lowOwnerThresholdIncidencePairMass R p (a, b) +
        lowOwnerThresholdIncidencePairMass R p (u, v) =
      postRootZeroTargetPairExcess (u, v) *
        ((∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℝ)) *
            lowOwnerThresholdClippedDifference
              p r u (rawQ2ChildCutoff R q)) -
          lowOwnerThresholdClippedDifference p r u (R - 1)) *
        lowOwnerThresholdOwnerIncidenceWeight R p v := by
  dsimp only
  rw [lowOwnerThresholdIncidencePairMass_add_parent_eq_leftDifference
    hr haSq hbSq ha hb hra hrb]
  rw [lowOwnerThresholdSecondOwnerDifference_eq_clippedFubini
    hR hp hr.one_le]

/-- **Right residual is literally the finite r-clipped threshold Fubini.** -/
theorem lowOwnerThresholdIncidencePairMass_add_parent_eq_rightClippedFubini
    {R p r a b : ℕ}
    (hR : 1 ≤ R) (hp : 1 ≤ p) (hr : r.Prime)
    (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hra : ¬ r ∣ a) (hrb : r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    lowOwnerThresholdIncidencePairMass R p (a, b) +
        lowOwnerThresholdIncidencePairMass R p (u, v) =
      postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdOwnerIncidenceWeight R p u *
        ((∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℝ)) *
            lowOwnerThresholdClippedDifference
              p r v (rawQ2ChildCutoff R q)) -
          lowOwnerThresholdClippedDifference p r v (R - 1)) := by
  dsimp only
  rw [lowOwnerThresholdIncidencePairMass_add_parent_eq_rightDifference
    hr haSq hbSq ha hb hra hrb]
  rw [lowOwnerThresholdSecondOwnerDifference_eq_clippedFubini
    hR hp hr.one_le]

/-- Orientation-free greatest-owner specialization: one of the preceding two
exact clipped-Fubini descents always applies. -/
theorem descendingGreatestOwner_thresholdIncidence_signedDescent
    {R p r a b : ℕ}
    (hR : 1 ≤ R) (hp : 1 ≤ p) (hr : r.Prime)
    (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet a b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    (lowOwnerThresholdIncidencePairMass R p (a, b) +
        lowOwnerThresholdIncidencePairMass R p (u, v) =
      postRootZeroTargetPairExcess (u, v) *
        ((∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℝ)) *
            lowOwnerThresholdClippedDifference
              p r u (rawQ2ChildCutoff R q)) -
          lowOwnerThresholdClippedDifference p r u (R - 1)) *
        lowOwnerThresholdOwnerIncidenceWeight R p v) ∨
    (lowOwnerThresholdIncidencePairMass R p (a, b) +
        lowOwnerThresholdIncidencePairMass R p (u, v) =
      postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdOwnerIncidenceWeight R p u *
        ((∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℝ)) *
            lowOwnerThresholdClippedDifference
              p r v (rawQ2ChildCutoff R q)) -
          lowOwnerThresholdClippedDifference p r v (R - 1))) := by
  have hxor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor hr ha hb).1 hrFresh
  rcases hxor with hleft | hright
  · exact Or.inl
      (lowOwnerThresholdIncidencePairMass_add_parent_eq_leftClippedFubini
        hR hp hr haSq hbSq ha hb hleft.1 hleft.2)
  · exact Or.inr
      (lowOwnerThresholdIncidencePairMass_add_parent_eq_rightClippedFubini
        hR hp hr haSq hbSq ha hb hright.2 hright.1)

end RHLean.Proof