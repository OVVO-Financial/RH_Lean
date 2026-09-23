import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_SAME_BRANCH_NONNEG»

/-!
# Full-branch cross-amplitude factorization before energy

After inert = tail, one descending owner layer is a complete equal-signature
Gram on the r-free branch.  On one branch parent `(a,b)`, the next-polarization
atom is already purely mixed:

  Pi_r(a,b) = -B(a) J(b) - J(a) B(b),

where `B` and `J` are the signed r-differences of the Dirichlet base and
returned coordinates.  Fibrewise Fubini therefore gives exactly

  sum Pi_r = -2 * sum_tau B_tau J_tau.

Only after that complete signed reassembly do we use

  -2 B J <= (1/2) (B-J)^2,

which follows from `(B+J)^2 >= 0`.  This is the amplitude-before-energy gate;
no pairwise Cauchy--Schwarz or owner-count estimate appears.
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

/-- Fibre incidence amplitude is exactly `B-J`. -/
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

/-- The assembled Dirichlet-incidence fibre energy. -/
def lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
      R p sig tau r ^ 2

@[simp] theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_nonneg
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    0 ≤ lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy R p sig r := by
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
  apply Finset.sum_nonneg
  intro tau _htau
  exact sq_nonneg _

/-- Pointwise next-polarization atom is purely cross-amplitude after the
complete r-four-corner has been formed. -/
theorem lowOwnerFirstOwnerBranchNextPolarizationTerm_eq_crossSites
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (_hparent : parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r) :
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent =
      -(lowOwnerBranchBaseDifferenceSignedSite R r parent.1 *
          lowOwnerBranchReturnedDifferenceSignedSite R p r parent.2) -
        lowOwnerBranchReturnedDifferenceSignedSite R p r parent.1 *
          lowOwnerBranchBaseDifferenceSignedSite R r parent.2 := by
  unfold lowOwnerFirstOwnerRawParentNextPolarizationTerm
    lowOwnerDirichletNextPolarizationScalar
    lowOwnerBranchBaseDifferenceSignedSite
    lowOwnerBranchReturnedDifferenceSignedSite
    lowOwnerDirichletOwnerDifference
    lowOwnerDirichletIncidenceCoefficient
    lowOwnerDirichletBaseCoefficient
    lowOwnerDirichletReturnedCoefficient
  ring

/-- One revealed-signature fibre of the branch pair carrier is the Cartesian
square of its one-dimensional site fibre. -/
private theorem lowOwnerFirstOwnerRawParentBranch_keyFiber_eq_product
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

/-- Cross terms on a Cartesian square factor exactly. -/
private theorem sum_product_cross_factor
    (s : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ ab ∈ s.product s,
      (-(f ab.1 * g ab.2) - g ab.1 * f ab.2)) =
      -2 * (∑ a ∈ s, f a) * (∑ b ∈ s, g b) := by
  have hfg :
      (∑ ab ∈ s.product s, f ab.1 * g ab.2) =
        (∑ a ∈ s, f a) * (∑ b ∈ s, g b) := by
    calc
      (∑ ab ∈ s.product s, f ab.1 * g ab.2) =
          ∑ a ∈ s, ∑ b ∈ s, f a * g b := by
        simpa only using
          (Finset.sum_product
            (s := s) (t := s)
            (f := fun ab : ℕ × ℕ => f ab.1 * g ab.2))
      _ = ∑ a ∈ s, f a * (∑ b ∈ s, g b) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  have hgf :
      (∑ ab ∈ s.product s, g ab.1 * f ab.2) =
        (∑ a ∈ s, g a) * (∑ b ∈ s, f b) := by
    calc
      (∑ ab ∈ s.product s, g ab.1 * f ab.2) =
          ∑ a ∈ s, ∑ b ∈ s, g a * f b := by
        simpa only using
          (Finset.sum_product
            (s := s) (t := s)
            (f := fun ab : ℕ × ℕ => g ab.1 * f ab.2))
      _ = ∑ a ∈ s, g a * (∑ b ∈ s, f b) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hfg, hgf]
  ring

/-- Exact fibrewise Fubini of the branch cross-amplitude. -/
theorem sum_lowOwnerFirstOwnerBranchNextPolarization_eq_neg_two_sum_base_mul_returned
    {R p r : ℕ} {sig : Finset ℕ} :
    (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        (-2 * lowOwnerFirstOwnerBranchBaseDifferenceAmplitude
            R p sig tau r *
          lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude
            R p sig tau r) := by
  let P := lowOwnerFirstOwnerRawParentBranchCarrier R p sig r
  let T := lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r
  let key : ℕ → Finset ℕ := lowOwnerRawParentRevealedKey R r
  let F : ℕ × ℕ → ℝ := fun parent =>
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent
  have hmaps : ∀ parent ∈ P, key parent.1 ∈ T := by
    intro parent hparent
    have hprod := (Finset.mem_filter.mp hparent).1
    have haBase := (Finset.mem_product.mp hprod).1
    have hra := (Finset.mem_filter.mp hparent).2.2.1
    have haSite : parent.1 ∈
        lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r :=
      Finset.mem_filter.mpr ⟨haBase, hra⟩
    exact Finset.mem_image.mpr ⟨parent.1, haSite, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := P) (t := T) (g := fun parent => key parent.1) hmaps F
  change (∑ parent ∈ P, F parent) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro tau _htau
  have hset := lowOwnerFirstOwnerRawParentBranch_keyFiber_eq_product
    R p sig tau r
  change
    (∑ parent ∈ P.filter (fun parent => key parent.1 = tau), F parent) = _
  rw [show P.filter (fun parent => key parent.1 = tau) =
      (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r) by
      simpa [P, key] using hset]
  have hpoint :
      ∀ parent ∈
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
          (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r),
        F parent =
          -(lowOwnerBranchBaseDifferenceSignedSite R r parent.1 *
              lowOwnerBranchReturnedDifferenceSignedSite R p r parent.2) -
            lowOwnerBranchReturnedDifferenceSignedSite R p r parent.1 *
              lowOwnerBranchBaseDifferenceSignedSite R r parent.2 := by
    intro parent hparent
    rcases Finset.mem_product.mp hparent with ⟨ha, hb⟩
    have haBranch := (Finset.mem_filter.mp ha).1
    have hbBranch := (Finset.mem_filter.mp hb).1
    have hkeyA := (Finset.mem_filter.mp ha).2
    have hkeyB := (Finset.mem_filter.mp hb).2
    have hpair : parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨(Finset.mem_filter.mp haBranch).1,
            (Finset.mem_filter.mp hbBranch).1⟩,
          ⟨by
              unfold lowOwnerRawParentRevealedKey at hkeyA hkeyB
              exact hkeyA.trans hkeyB.symm,
            (Finset.mem_filter.mp haBranch).2,
            (Finset.mem_filter.mp hbBranch).2⟩⟩
    exact lowOwnerFirstOwnerBranchNextPolarizationTerm_eq_crossSites hpair
  calc
    (∑ parent ∈
      (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r),
      F parent) =
      ∑ parent ∈
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
          (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r),
        (-(lowOwnerBranchBaseDifferenceSignedSite R r parent.1 *
            lowOwnerBranchReturnedDifferenceSignedSite R p r parent.2) -
          lowOwnerBranchReturnedDifferenceSignedSite R p r parent.1 *
            lowOwnerBranchBaseDifferenceSignedSite R r parent.2) := by
      apply Finset.sum_congr rfl
      intro parent hparent
      exact hpoint parent hparent
    _ = _ := by
      simpa [lowOwnerFirstOwnerBranchBaseDifferenceAmplitude,
        lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude] using
        sum_product_cross_factor
          (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r)
          (lowOwnerBranchBaseDifferenceSignedSite R r)
          (lowOwnerBranchReturnedDifferenceSignedSite R p r)

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
  exact sum_lowOwnerFirstOwnerBranchNextPolarization_eq_neg_two_sum_base_mul_returned

/-- Elementary amplitude gate with the sharp universal coefficient `1/2`. -/
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
    hp hr hpr]
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro tau _htau
  rw [lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_eq_base_sub_returned]
  exact neg_two_mul_le_half_sub_sq
    (lowOwnerFirstOwnerBranchBaseDifferenceAmplitude R p sig tau r)
    (lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude R p sig tau r)


/-! ## Endpoint correction completes the physical incidence square -/

/-- Square of one assembled Dirichlet-incidence fibre amplitude as its literal
ordered pair sum. -/
private theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_sq_eq_pairSum
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
        R p sig tau r ^ 2 =
      ∑ mn ∈
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
          (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r),
        lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r mn.1 *
          lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r mn.2 := by
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
  calc
    (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n) ^ 2 =
      (∑ m ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r m) *
      (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n) := by
          ring
    _ =
      ∑ m ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
          lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r m *
            lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m _hm
          rw [Finset.mul_sum]
    _ = _ := by
      symm
      simpa only using
        (Finset.sum_product
          (s := lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r)
          (t := lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r)
          (f := fun mn : ℕ × ℕ =>
            lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r mn.1 *
              lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r mn.2))

/-- The assembled Dirichlet-incidence fibre energy is exactly the equal-key
Gram on the full revealed r-free branch. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_pairSum
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy R p sig r =
      ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r parent.1 *
          lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r parent.2 := by
  let P := lowOwnerFirstOwnerRawParentBranchCarrier R p sig r
  let T := lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r
  let key : ℕ → Finset ℕ := lowOwnerRawParentRevealedKey R r
  let F : ℕ × ℕ → ℝ := fun parent =>
    lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r parent.1 *
      lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r parent.2
  have hmaps : ∀ parent ∈ P, key parent.1 ∈ T := by
    intro parent hparent
    have hprod := (Finset.mem_filter.mp hparent).1
    have haBase := (Finset.mem_product.mp hprod).1
    have hra := (Finset.mem_filter.mp hparent).2.2.1
    have haSite : parent.1 ∈
        lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r :=
      Finset.mem_filter.mpr ⟨haBase, hra⟩
    exact Finset.mem_image.mpr ⟨parent.1, haSite, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := P) (t := T) (g := fun parent => key parent.1) hmaps F
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
  change (∑ tau ∈ T,
      lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
        R p sig tau r ^ 2) = ∑ parent ∈ P, F parent
  calc
    (∑ tau ∈ T,
      lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
        R p sig tau r ^ 2) =
      ∑ tau ∈ T,
        ∑ parent ∈
          (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
            (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r),
          F parent := by
            apply Finset.sum_congr rfl
            intro tau _htau
            exact
              lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_sq_eq_pairSum
                R p sig tau r
    _ = ∑ tau ∈ T,
        ∑ parent ∈ P.filter (fun parent => key parent.1 = tau), F parent := by
          apply Finset.sum_congr rfl
          intro tau _htau
          have hset :=
            lowOwnerFirstOwnerRawParentBranch_keyFiber_eq_product
              R p sig tau r
          rw [show P.filter (fun parent => key parent.1 = tau) =
              (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
                (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r) by
            simpa [P, key] using hset]
    _ = ∑ parent ∈ P, F parent := hfiber

/-- A physical Dirichlet-incidence four-corner on the full branch is the
product of its two signed one-dimensional incidence differences. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceFourCorner_eq_siteProduct
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime)
    (hparent : parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r) :
    lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent =
      lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r parent.1 *
        lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r parent.2 := by
  rcases Finset.mem_filter.mp hparent with
    ⟨_hprod, _hsigAbove, hra, hrb⟩
  unfold lowOwnerRawParentDirichletIncidenceFourCornerMass
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
    (lowOwnerPhysicalDirichletIncidenceWeight R p) hr hra hrb]
  rw [postRootZeroTargetPairExcess_eq_weight]
  unfold lowOwnerBranchDirichletIncidenceDifferenceSignedSite
    lowOwnerDirichletOwnerDifference
  ring

/-- **Endpoint-energy completion identity.**

The endpoint correction is not an independent error term.  After full
equal-signature reassembly it is exactly the signed cross/square completion
which turns the threshold branch energy into the physical Dirichlet-incidence
energy.  No norm or inequality is used. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_branchThresholdEnergy_add_endpointCorrection
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy R p sig r =
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r +
        lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass R p sig r := by
  rw [lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_pairSum]
  calc
    (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r parent.1 *
        lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r parent.2) =
      ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent := by
          apply Finset.sum_congr rfl
          intro parent hparent
          symm
          exact lowOwnerFirstOwnerBranchDirichletIncidenceFourCorner_eq_siteProduct
            hr hparent
    _ =
      ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        (weightedMoebiusFreshPrimeFourCornerMass
            (lowOwnerThresholdOwnerIncidenceWeight R p)
            r parent.1 parent.2 +
          lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent) := by
            apply Finset.sum_congr rfl
            intro parent hparent
            exact
              lowOwnerFirstOwnerBranchDirichletIncidenceFourCorner_eq_threshold_add_endpointCorrection
                hR hp hr hparent
    _ =
      (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p)
          r parent.1 parent.2) +
      ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent := by
          rw [Finset.sum_add_distrib]
    _ =
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r +
        lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass R p sig r := by
          rw [sum_lowOwnerFirstOwnerBranchThresholdFourCorner_eq_branchThresholdEnergy hr]
          rfl

end RHLean.Proof