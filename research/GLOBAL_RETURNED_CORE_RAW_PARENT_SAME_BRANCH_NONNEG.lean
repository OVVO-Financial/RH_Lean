import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_FULL_BRANCH_CURRENCY»
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BRANCH_SQUARES»

/-!
# The full-branch same-branch continuation is favorable

For any finite site set `S`, key map `k`, and real site weight `f`, the equal-key
Cartesian Gram

  sum_{a,b in S, k(a)=k(b)} f(a)f(b)

is exactly

  sum_tau (sum_{a in S, k(a)=tau} f(a))^2,

hence nonnegative.

Apply this twice on the full revealed r-free branch, first to the signed
r-difference of the Dirichlet base coordinate and then to the signed
r-difference of the returned coordinate.  Their sum is exactly the
`lowOwnerFirstOwnerBranchSameBranchMass` subtracted in the full-branch currency
identity.

Therefore the same-branch continuation is globally favorable after the exact
branch reassembly.  No packetwise sign assertion is made; nonnegativity appears
only after the complete equal-signature Gram is summed.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private def equalKeyPairCarrier
    (S : Finset ℕ) (key : ℕ → Finset ℕ) : Finset (ℕ × ℕ) :=
  (S.product S).filter fun mn => key mn.1 = key mn.2

private def equalKeySet
    (S : Finset ℕ) (key : ℕ → Finset ℕ) : Finset (Finset ℕ) :=
  S.image key

private def equalKeyFiber
    (S : Finset ℕ) (key : ℕ → Finset ℕ) (tau : Finset ℕ) : Finset ℕ :=
  S.filter fun n => key n = tau

private theorem equalKeyPairFiber_eq_product
    (S : Finset ℕ) (key : ℕ → Finset ℕ) (tau : Finset ℕ) :
    (equalKeyPairCarrier S key).filter (fun mn => key mn.1 = tau) =
      (equalKeyFiber S key tau).product (equalKeyFiber S key tau) := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hpair, hmTau⟩
    rcases Finset.mem_filter.mp hpair with ⟨hprod, hmnKey⟩
    rcases Finset.mem_product.mp hprod with ⟨hmS, hnS⟩
    have hnTau : key n = tau := by rw [← hmnKey, hmTau]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hmS, hmTau⟩,
        Finset.mem_filter.mpr ⟨hnS, hnTau⟩⟩
  · intro hmn
    rcases Finset.mem_product.mp hmn with ⟨hm, hn⟩
    rcases Finset.mem_filter.mp hm with ⟨hmS, hmTau⟩
    rcases Finset.mem_filter.mp hn with ⟨hnS, hnTau⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hmS, hnS⟩, by rw [hmTau, hnTau]⟩,
        hmTau⟩

private theorem equalKeyFiberAmplitude_sq_eq_pairSum
    (S : Finset ℕ) (key : ℕ → Finset ℕ)
    (f : ℕ → ℝ) (tau : Finset ℕ) :
    (∑ n ∈ equalKeyFiber S key tau, f n) ^ 2 =
      ∑ mn ∈ (equalKeyFiber S key tau).product
          (equalKeyFiber S key tau),
        f mn.1 * f mn.2 := by
  calc
    (∑ n ∈ equalKeyFiber S key tau, f n) ^ 2 =
      (∑ m ∈ equalKeyFiber S key tau, f m) *
        (∑ n ∈ equalKeyFiber S key tau, f n) := by ring
    _ = ∑ m ∈ equalKeyFiber S key tau,
        ∑ n ∈ equalKeyFiber S key tau, f m * f n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]
    _ = _ := by
      symm
      simpa only using
        (Finset.sum_product
          (s := equalKeyFiber S key tau)
          (t := equalKeyFiber S key tau)
          (f := fun mn : ℕ × ℕ => f mn.1 * f mn.2))

/-- **Generic equal-key Gram square identity.** -/
theorem sum_equalKeyPairCarrier_eq_sum_fiberSquares
    (S : Finset ℕ) (key : ℕ → Finset ℕ) (f : ℕ → ℝ) :
    (∑ mn ∈ equalKeyPairCarrier S key, f mn.1 * f mn.2) =
      ∑ tau ∈ equalKeySet S key,
        (∑ n ∈ equalKeyFiber S key tau, f n) ^ 2 := by
  let P := equalKeyPairCarrier S key
  let T := equalKeySet S key
  let F : ℕ × ℕ → ℝ := fun mn => f mn.1 * f mn.2
  have hmaps : ∀ mn ∈ P, key mn.1 ∈ T := by
    intro mn hmn
    have hprod := (Finset.mem_filter.mp hmn).1
    have hmS := (Finset.mem_product.mp hprod).1
    exact Finset.mem_image.mpr ⟨mn.1, hmS, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := P) (t := T) (g := fun mn => key mn.1) hmaps F
  change (∑ mn ∈ P, F mn) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro tau _htau
  have hset := equalKeyPairFiber_eq_product S key tau
  rw [hset]
  symm
  simpa [P, T, F] using equalKeyFiberAmplitude_sq_eq_pairSum S key f tau

/-- Equal-key Gram sums are nonnegative. -/
theorem sum_equalKeyPairCarrier_nonneg
    (S : Finset ℕ) (key : ℕ → Finset ℕ) (f : ℕ → ℝ) :
    0 ≤ ∑ mn ∈ equalKeyPairCarrier S key, f mn.1 * f mn.2 := by
  rw [sum_equalKeyPairCarrier_eq_sum_fiberSquares]
  apply Finset.sum_nonneg
  intro tau _htau
  exact sq_nonneg _

/-- Signed r-difference of the Dirichlet base coordinate. -/
def lowOwnerBranchBaseDifferenceSignedSite
    (R r n : ℕ) : ℝ :=
  realMoebiusStep n *
    lowOwnerDirichletOwnerDifference r (lowOwnerDirichletBaseCoefficient R) n

/-- Signed r-difference of the returned p-coordinate. -/
def lowOwnerBranchReturnedDifferenceSignedSite
    (R p r n : ℕ) : ℝ :=
  realMoebiusStep n *
    lowOwnerDirichletOwnerDifference r
      (lowOwnerDirichletReturnedCoefficient R p) n

/-- Base four-corner on an r-free pair is the product of two signed base
difference sites. -/
theorem lowOwnerFirstOwnerBranchBaseFourCorner_eq_siteProduct
    {R r : ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime)
    (hra : ¬ r ∣ parent.1) (hrb : ¬ r ∣ parent.2) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerDirichletBaseCoefficient R) r parent.1 parent.2 =
      lowOwnerBranchBaseDifferenceSignedSite R r parent.1 *
        lowOwnerBranchBaseDifferenceSignedSite R r parent.2 := by
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
    (lowOwnerDirichletBaseCoefficient R) hr hra hrb]
  rw [postRootZeroTargetPairExcess_eq_weight]
  unfold lowOwnerBranchBaseDifferenceSignedSite
    lowOwnerDirichletOwnerDifference
  ring

/-- Returned four-corner has the analogous site-product form. -/
theorem lowOwnerFirstOwnerBranchReturnedFourCorner_eq_siteProduct
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ parent.1) (hrb : ¬ r ∣ parent.2) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerDirichletReturnedCoefficient R p) r parent.1 parent.2 =
      lowOwnerBranchReturnedDifferenceSignedSite R p r parent.1 *
        lowOwnerBranchReturnedDifferenceSignedSite R p r parent.2 := by
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
    (lowOwnerDirichletReturnedCoefficient R p) hr hra hrb]
  rw [postRootZeroTargetPairExcess_eq_weight]
  unfold lowOwnerBranchReturnedDifferenceSignedSite
    lowOwnerDirichletOwnerDifference
  ring

/-- The branch carrier is exactly the generic equal-key carrier on its r-free
site set. -/
theorem lowOwnerFirstOwnerRawParentBranchCarrier_eq_genericEqualKey
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentBranchCarrier R p sig r =
      equalKeyPairCarrier
        (lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r)
        (lowOwnerRawParentRevealedKey R r) := by
  exact lowOwnerFirstOwnerRawParentBranchCarrier_eq_equalKeyProduct R p sig r

/-- Aggregate base same-branch four-corner is nonnegative. -/
theorem sum_lowOwnerFirstOwnerBranchBaseFourCorner_nonneg
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    0 ≤ ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerDirichletBaseCoefficient R) r parent.1 parent.2 := by
  rw [lowOwnerFirstOwnerRawParentBranchCarrier_eq_genericEqualKey]
  have hgram := sum_equalKeyPairCarrier_nonneg
    (lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r)
    (lowOwnerRawParentRevealedKey R r)
    (lowOwnerBranchBaseDifferenceSignedSite R r)
  refine hgram.trans_eq ?_
  apply Finset.sum_congr rfl
  intro parent hparent
  have hprod := (Finset.mem_filter.mp hparent).1
  rcases Finset.mem_product.mp hprod with ⟨haSite, hbSite⟩
  have hra := (Finset.mem_filter.mp haSite).2
  have hrb := (Finset.mem_filter.mp hbSite).2
  exact (lowOwnerFirstOwnerBranchBaseFourCorner_eq_siteProduct
    (parent := parent) hr hra hrb).symm

/-- Aggregate returned same-branch four-corner is nonnegative. -/
theorem sum_lowOwnerFirstOwnerBranchReturnedFourCorner_nonneg
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    0 ≤ ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerDirichletReturnedCoefficient R p) r parent.1 parent.2 := by
  rw [lowOwnerFirstOwnerRawParentBranchCarrier_eq_genericEqualKey]
  have hgram := sum_equalKeyPairCarrier_nonneg
    (lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r)
    (lowOwnerRawParentRevealedKey R r)
    (lowOwnerBranchReturnedDifferenceSignedSite R p r)
  refine hgram.trans_eq ?_
  apply Finset.sum_congr rfl
  intro parent hparent
  have hprod := (Finset.mem_filter.mp hparent).1
  rcases Finset.mem_product.mp hprod with ⟨haSite, hbSite⟩
  have hra := (Finset.mem_filter.mp haSite).2
  have hrb := (Finset.mem_filter.mp hbSite).2
  exact (lowOwnerFirstOwnerBranchReturnedFourCorner_eq_siteProduct
    (parent := parent) hr hra hrb).symm

/-- **The entire branch same-branch continuation is nonnegative.** -/
theorem lowOwnerFirstOwnerBranchSameBranchMass_nonneg
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    0 ≤ lowOwnerFirstOwnerBranchSameBranchMass R p sig r := by
  unfold lowOwnerFirstOwnerBranchSameBranchMass
    lowOwnerRawParentSameBranchFourCornerMass
  rw [Finset.sum_add_distrib]
  exact add_nonneg
    (sum_lowOwnerFirstOwnerBranchBaseFourCorner_nonneg
      (R := R) (p := p) (r := r) (sig := sig) hr)
    (sum_lowOwnerFirstOwnerBranchReturnedFourCorner_nonneg
      (R := R) (p := p) (r := r) (sig := sig) hr)

/-- **Legal one-sided consequence of the exact full-branch currency.**  The
subtracted same-branch continuation may be discarded only after its complete
Gram nonnegativity has been proved. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_branchEnergy_add_endpointCorrection
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r +
        lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass R p sig r := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_branchEnergy_add_endpointCorrection_sub_sameBranch
    hR hp hr hpr]
  have hsame :=
    lowOwnerFirstOwnerBranchSameBranchMass_nonneg
      (R := R) (p := p) (r := r) (sig := sig) hr
  linarith

end RHLean.Proof
