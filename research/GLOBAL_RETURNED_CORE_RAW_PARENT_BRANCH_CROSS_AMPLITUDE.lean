import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_SAME_BRANCH_NONNEG»

/-!
# Full-branch cross-amplitude factorization before energy

After inert = tail, one descending owner layer is a complete equal-signature
Gram on the r-free branch.  This is the correct place to pass through amplitude
before squaring.

For one revealed signature fibre tau, define the signed r-difference amplitudes
of the Dirichlet base and returned coordinates,

  B_tau = sum mu(n) Delta_r Base(n),
  J_tau = sum mu(n) Delta_r Returned(n).

The incidence amplitude is exactly `B_tau - J_tau`.  Fibrewise polarization is
therefore

  (B_tau-J_tau)^2 - B_tau^2 - J_tau^2 = -2 B_tau J_tau.

Summing the complete fibres gives the exact current polarization.  Only then do
we use the elementary amplitude inequality

  -2 B J <= (1/2) (B-J)^2,

which is equivalent to `(B+J)^2 >= 0`.  Thus the signed branch polarization is
bounded by one half of the *assembled Dirichlet-incidence fibre energy*.
No pairwise Cauchy--Schwarz or owner-count bound appears.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed r-difference of the physical Dirichlet incidence coordinate. -/
def lowOwnerBranchDirichletIncidenceDifferenceSignedSite
    (R p r n : ℕ) : ℝ :=
  realMoebiusStep n *
    lowOwnerDirichletOwnerDifference r
      (lowOwnerPhysicalDirichletIncidenceWeight R p) n

/-- Base difference amplitude on one revealed branch fibre. -/
def lowOwnerFirstOwnerBranchBaseDifferenceAmplitude
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
    lowOwnerBranchBaseDifferenceSignedSite R r n

/-- Returned difference amplitude on one revealed branch fibre. -/
def lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
    lowOwnerBranchReturnedDifferenceSignedSite R p r n

/-- Dirichlet-incidence difference amplitude on one revealed branch fibre. -/
def lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
    lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n

/-- Incidence difference is base difference minus returned difference. -/
theorem lowOwnerBranchDirichletIncidenceDifferenceSignedSite_eq_base_sub_returned
    (R p r n : ℕ) :
    lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n =
      lowOwnerBranchBaseDifferenceSignedSite R r n -
        lowOwnerBranchReturnedDifferenceSignedSite R p r n := by
  unfold lowOwnerBranchDirichletIncidenceDifferenceSignedSite
    lowOwnerBranchBaseDifferenceSignedSite
    lowOwnerBranchReturnedDifferenceSignedSite
    lowOwnerDirichletOwnerDifference
    lowOwnerPhysicalDirichletIncidenceWeight
    lowOwnerDirichletBaseCoefficient
    lowOwnerDirichletReturnedCoefficient
  ring

/-- Fibre incidence amplitude is `B-J`. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_eq_base_sub_returned
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
        R p sig tau r =
      lowOwnerFirstOwnerBranchBaseDifferenceAmplitude R p sig tau r -
        lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude R p sig tau r := by
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
    lowOwnerFirstOwnerBranchBaseDifferenceAmplitude
    lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  exact lowOwnerBranchDirichletIncidenceDifferenceSignedSite_eq_base_sub_returned
    R p r n

/-- Generic branch Gram of an arbitrary one-dimensional site. -/
def lowOwnerFirstOwnerRawParentBranchGram
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
    v parent.1 * v parent.2

/-- Generic amplitude on one branch signature fibre. -/
def lowOwnerFirstOwnerRawParentBranchFiberAmplitude
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
    v n

/-- One branch key fibre of the branch pair carrier is the Cartesian square of
the corresponding site fibre. -/
private theorem lowOwnerFirstOwnerRawParentBranchCarrier_keyFiber_eq_product
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) :
    (lowOwnerFirstOwnerRawParentBranchCarrier R p sig r).filter
        (fun parent => lowOwnerRawParentRevealedKey R r parent.1 = tau) =
      (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r) := by
  rw [lowOwnerFirstOwnerRawParentBranchCarrier_eq_equalKeyProduct]
  ext parent
  rcases parent with ⟨a, b⟩
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨heq, haTau⟩
    rcases Finset.mem_filter.mp heq with ⟨hprod, habKey⟩
    rcases Finset.mem_product.mp hprod with ⟨haS, hbS⟩
    have hbTau : lowOwnerRawParentRevealedKey R r b = tau := by
      rw [← habKey, haTau]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨haS, haTau⟩,
        Finset.mem_filter.mpr ⟨hbS, hbTau⟩⟩
  · intro h
    rcases Finset.mem_product.mp h with ⟨ha, hb⟩
    rcases Finset.mem_filter.mp ha with ⟨haS, haTau⟩
    rcases Finset.mem_filter.mp hb with ⟨hbS, hbTau⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haS, hbS⟩, by rw [haTau, hbTau]⟩,
        haTau⟩

/-- Square of a generic branch fibre amplitude is its Cartesian pair Gram. -/
private theorem lowOwnerFirstOwnerRawParentBranchFiberAmplitude_sq_eq_pairSum
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) (v : ℕ → ℝ) :
    lowOwnerFirstOwnerRawParentBranchFiberAmplitude R p sig tau r v ^ 2 =
      ∑ parent ∈
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
          (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r),
        v parent.1 * v parent.2 := by
  unfold lowOwnerFirstOwnerRawParentBranchFiberAmplitude
  calc
    (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        v n) ^ 2 =
      (∑ a ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        v a) *
      (∑ b ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        v b) := by ring
    _ = ∑ a ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        ∑ b ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
          v a * v b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = _ := by
      symm
      simpa only using
        (Finset.sum_product
          (s := lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r)
          (t := lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r)
          (f := fun parent : ℕ × ℕ => v parent.1 * v parent.2))

/-- Generic branch Gram equals the sum of squared revealed-fibre amplitudes. -/
theorem lowOwnerFirstOwnerRawParentBranchGram_eq_sum_fiberAmplitude_sq
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (v : ℕ → ℝ) :
    lowOwnerFirstOwnerRawParentBranchGram R p sig r v =
      ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        lowOwnerFirstOwnerRawParentBranchFiberAmplitude
          R p sig tau r v ^ 2 := by
  let P := lowOwnerFirstOwnerRawParentBranchCarrier R p sig r
  let T := lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r
  let key : ℕ → Finset ℕ := lowOwnerRawParentRevealedKey R r
  let F : ℕ × ℕ → ℝ := fun parent => v parent.1 * v parent.2
  have hmaps : ∀ parent ∈ P, key parent.1 ∈ T := by
    intro parent hparent
    have hbranch := (Finset.mem_filter.mp hparent).1
    have haBase := (Finset.mem_product.mp hbranch).1
    have haSite : parent.1 ∈
        lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r := by
      have hfree := (Finset.mem_filter.mp hparent).2.2.1
      exact Finset.mem_filter.mpr ⟨haBase, hfree⟩
    exact Finset.mem_image.mpr ⟨parent.1, haSite, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := P) (t := T) (g := fun parent => key parent.1) hmaps F
  unfold lowOwnerFirstOwnerRawParentBranchGram
  change (∑ parent ∈ P, F parent) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro tau _htau
  have hset :=
    lowOwnerFirstOwnerRawParentBranchCarrier_keyFiber_eq_product
      R p sig tau r
  change (∑ parent ∈ P.filter (fun parent => key parent.1 = tau),
    F parent) = _
  rw [show P.filter (fun parent => key parent.1 = tau) =
      (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r) by
      simpa [P, key] using hset]
  symm
  simpa [F] using
    lowOwnerFirstOwnerRawParentBranchFiberAmplitude_sq_eq_pairSum
      R p sig tau r v

/-- Branch Dirichlet-incidence difference energy as an assembled Gram. -/
def lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  lowOwnerFirstOwnerRawParentBranchGram R p sig r
    (lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r)

/-- It is literally the sum of squared incidence fibre amplitudes. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_sum_sq
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy R p sig r =
      ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
          R p sig tau r ^ 2 := by
  rw [lowOwnerFirstOwnerRawParentBranchGram_eq_sum_fiberAmplitude_sq]
  apply Finset.sum_congr rfl
  intro tau _htau
  rfl

/-- Exact full-branch cross-amplitude normal form. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_neg_two_sum_base_mul_returned
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        (-2 * lowOwnerFirstOwnerBranchBaseDifferenceAmplitude
            R p sig tau r *
          lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude
            R p sig tau r) := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_branchNextPolarization
    hp hr hpr]
  let B : ℕ → ℝ := lowOwnerBranchBaseDifferenceSignedSite R r
  let J : ℕ → ℝ := lowOwnerBranchReturnedDifferenceSignedSite R p r
  have hpoint :
      ∀ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent =
          (B parent.1 - J parent.1) * (B parent.2 - J parent.2) -
            B parent.1 * B parent.2 - J parent.1 * J parent.2 := by
    intro parent hparent
    rcases Finset.mem_filter.mp hparent with
      ⟨_hprod, _hsigAbove, hra, hrb⟩
    unfold lowOwnerFirstOwnerRawParentNextPolarizationTerm
      lowOwnerDirichletNextPolarizationScalar B J
    rw [postRootZeroTargetPairExcess_eq_weight]
    unfold lowOwnerBranchBaseDifferenceSignedSite
      lowOwnerBranchReturnedDifferenceSignedSite
      lowOwnerDirichletOwnerDifference
    ring
  calc
    (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      (lowOwnerFirstOwnerRawParentBranchGram R p sig r
          (fun n => B n - J n)) -
        lowOwnerFirstOwnerRawParentBranchGram R p sig r B -
        lowOwnerFirstOwnerRawParentBranchGram R p sig r J := by
      unfold lowOwnerFirstOwnerRawParentBranchGram
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro parent hparent
      exact hpoint parent hparent
    _ =
      (∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        (lowOwnerFirstOwnerRawParentBranchFiberAmplitude
          R p sig tau r (fun n => B n - J n)) ^ 2) -
      (∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        (lowOwnerFirstOwnerRawParentBranchFiberAmplitude
          R p sig tau r B) ^ 2) -
      ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        (lowOwnerFirstOwnerRawParentBranchFiberAmplitude
          R p sig tau r J) ^ 2 := by
      rw [lowOwnerFirstOwnerRawParentBranchGram_eq_sum_fiberAmplitude_sq,
        lowOwnerFirstOwnerRawParentBranchGram_eq_sum_fiberAmplitude_sq,
        lowOwnerFirstOwnerRawParentBranchGram_eq_sum_fiberAmplitude_sq]
    _ = _ := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro tau _htau
      have hBJ :
          lowOwnerFirstOwnerRawParentBranchFiberAmplitude
              R p sig tau r (fun n => B n - J n) =
            lowOwnerFirstOwnerRawParentBranchFiberAmplitude
                R p sig tau r B -
              lowOwnerFirstOwnerRawParentBranchFiberAmplitude
                R p sig tau r J := by
        unfold lowOwnerFirstOwnerRawParentBranchFiberAmplitude
        rw [Finset.sum_sub_distrib]
      rw [hBJ]
      change
        (lowOwnerFirstOwnerBranchBaseDifferenceAmplitude R p sig tau r -
            lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude R p sig tau r) ^ 2 -
          lowOwnerFirstOwnerBranchBaseDifferenceAmplitude R p sig tau r ^ 2 -
          lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude R p sig tau r ^ 2 = _
      ring

/-- Elementary amplitude gate with the sharp universal coefficient 1/2. -/
theorem neg_two_mul_le_half_sub_sq (B J : ℝ) :
    -2 * B * J ≤ (1 / 2 : ℝ) * (B - J) ^ 2 := by
  nlinarith [sq_nonneg (B + J)]

/-- **Amplitude-before-energy gate.**  The complete signed branch polarization
is at most one half of the assembled Dirichlet-incidence fibre energy. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_half_dirichletIncidenceEnergy
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      (1 / 2 : ℝ) *
        lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy R p sig r := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_neg_two_sum_base_mul_returned
    hp hr hpr,
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_sum_sq,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro tau _htau
  rw [lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_eq_base_sub_returned]
  exact neg_two_mul_le_half_sub_sq
    (lowOwnerFirstOwnerBranchBaseDifferenceAmplitude R p sig tau r)
    (lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude R p sig tau r)

end RHLean.Proof
