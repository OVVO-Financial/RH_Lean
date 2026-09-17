import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_PREFIX_STAR_ENERGY»

/-!
# Revealed-branch threshold energies are literal sums of squares

The prefix-star factorization rewrote one raw threshold-incidence layer as

  BranchEnergy - TailEnergy.

Both terms are equal-signature Gram sums.  This file performs the same finite
fibrewise square realization already used by `GLOBAL_RETURNED_CORE_SIGNATURE_PAIR_ENERGY`:
partition the one-dimensional r-free branch by its revealed-prime signature,
and each pair fibre is exactly the Cartesian square of one signature fibre.

Consequently both branch and tail energies are sums of squared signed
amplitudes and are nonnegative.  Therefore the tail may be discarded in the
one-sided direction *after* the exact signed factorization, with no pair-count
or Cauchy--Schwarz loss.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- r-free sites of one first-owner base cell. -/
def lowOwnerFirstOwnerRawParentBranchSiteCarrier
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerBaseFiber R p sig).filter fun n => ¬ r ∣ n

/-- Sites in that branch whose r-child lies beyond the physical endpoint. -/
def lowOwnerFirstOwnerRawParentTailSiteCarrier
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r).filter fun n =>
    squareRootEndpoint R < r * n

/-- Revealed signature key at the current descending owner. -/
def lowOwnerRawParentRevealedKey
    (R r n : ℕ) : Finset ℕ :=
  lowOwnerRevealedPrimeSignature (lowOwnerRevealedPrimesAbove R r) n

/-- Signature values actually occurring in the r-free branch. -/
def lowOwnerFirstOwnerRawParentBranchSignatureSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  (lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r).image
    (lowOwnerRawParentRevealedKey R r)

/-- Signature values actually occurring in the tail. -/
def lowOwnerFirstOwnerRawParentTailSignatureSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  (lowOwnerFirstOwnerRawParentTailSiteCarrier R p sig r).image
    (lowOwnerRawParentRevealedKey R r)

/-- One revealed-signature fibre of the branch. -/
def lowOwnerFirstOwnerRawParentBranchSignatureFiber
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r).filter fun n =>
    lowOwnerRawParentRevealedKey R r n = tau

/-- One revealed-signature fibre of the tail. -/
def lowOwnerFirstOwnerRawParentTailSignatureFiber
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerRawParentTailSiteCarrier R p sig r).filter fun n =>
    lowOwnerRawParentRevealedKey R r n = tau

/-- Signed threshold amplitude on one revealed branch fibre. -/
def lowOwnerFirstOwnerRawParentBranchThresholdAmplitude
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
    lowOwnerRawParentThresholdSignedSite R p r n

/-- Signed threshold amplitude on one tail fibre. -/
def lowOwnerFirstOwnerRawParentTailThresholdAmplitude
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r,
    lowOwnerRawParentThresholdSignedSite R p r n

/-- The full branch pair carrier is exactly the equal-key square of the r-free
branch site carrier. -/
theorem lowOwnerFirstOwnerRawParentBranchCarrier_eq_equalKeyProduct
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentBranchCarrier R p sig r =
      ((lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r).product
        (lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r)).filter
        (fun mn =>
          lowOwnerRawParentRevealedKey R r mn.1 =
            lowOwnerRawParentRevealedKey R r mn.2) := by
  ext mn
  rcases mn with ⟨m, n⟩
  simp [lowOwnerFirstOwnerRawParentBranchCarrier,
    lowOwnerFirstOwnerRawParentBranchSiteCarrier,
    lowOwnerRawParentRevealedKey, and_assoc, and_left_comm, and_comm]

/-- The tail pair carrier is exactly the equal-key square of tail sites. -/
theorem lowOwnerFirstOwnerRawParentTailCarrier_eq_equalKeyProduct
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentTailCarrier R p sig r =
      ((lowOwnerFirstOwnerRawParentTailSiteCarrier R p sig r).product
        (lowOwnerFirstOwnerRawParentTailSiteCarrier R p sig r)).filter
        (fun mn =>
          lowOwnerRawParentRevealedKey R r mn.1 =
            lowOwnerRawParentRevealedKey R r mn.2) := by
  ext mn
  rcases mn with ⟨m, n⟩
  simp [lowOwnerFirstOwnerRawParentTailCarrier,
    lowOwnerFirstOwnerRawParentBranchCarrier,
    lowOwnerFirstOwnerRawParentTailSiteCarrier,
    lowOwnerFirstOwnerRawParentBranchSiteCarrier,
    lowOwnerRawParentRevealedKey,
    not_or, Nat.not_le, and_assoc, and_left_comm, and_comm]

/-- One key fibre of an equal-key pair carrier is a Cartesian square. -/
private theorem equalKeyPair_filter_eq_fiberProduct
    (S : Finset ℕ) (key : ℕ → Finset ℕ) (tau : Finset ℕ) :
    ((S.product S).filter (fun mn => key mn.1 = key mn.2)).filter
        (fun mn => key mn.1 = tau) =
      (S.filter (fun n => key n = tau)).product
        (S.filter (fun n => key n = tau)) := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨heqPair, hmTau⟩
    rcases Finset.mem_filter.mp heqPair with ⟨hprod, hmnKey⟩
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

/-- Square of one branch-fibre amplitude as its ordered pair sum. -/
theorem lowOwnerFirstOwnerRawParentBranchThresholdAmplitude_sq_eq_pairSum
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentBranchThresholdAmplitude R p sig tau r ^ 2 =
      ∑ mn ∈
        (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r).product
          (lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r),
        lowOwnerRawParentThresholdSignedSite R p r mn.1 *
          lowOwnerRawParentThresholdSignedSite R p r mn.2 := by
  unfold lowOwnerFirstOwnerRawParentBranchThresholdAmplitude
  calc
    (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        lowOwnerRawParentThresholdSignedSite R p r n) ^ 2 =
      (∑ m ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        lowOwnerRawParentThresholdSignedSite R p r m) *
      (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        lowOwnerRawParentThresholdSignedSite R p r n) := by ring
    _ = ∑ m ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
          lowOwnerRawParentThresholdSignedSite R p r m *
            lowOwnerRawParentThresholdSignedSite R p r n := by
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
            lowOwnerRawParentThresholdSignedSite R p r mn.1 *
              lowOwnerRawParentThresholdSignedSite R p r mn.2))

/-- Tail analogue of the fibre-square identity. -/
theorem lowOwnerFirstOwnerRawParentTailThresholdAmplitude_sq_eq_pairSum
    (R p : ℕ) (sig tau : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentTailThresholdAmplitude R p sig tau r ^ 2 =
      ∑ mn ∈
        (lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r).product
          (lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r),
        lowOwnerRawParentThresholdSignedSite R p r mn.1 *
          lowOwnerRawParentThresholdSignedSite R p r mn.2 := by
  unfold lowOwnerFirstOwnerRawParentTailThresholdAmplitude
  calc
    (∑ n ∈ lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r,
        lowOwnerRawParentThresholdSignedSite R p r n) ^ 2 =
      (∑ m ∈ lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r,
        lowOwnerRawParentThresholdSignedSite R p r m) *
      (∑ n ∈ lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r,
        lowOwnerRawParentThresholdSignedSite R p r n) := by ring
    _ = ∑ m ∈ lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r,
        ∑ n ∈ lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r,
          lowOwnerRawParentThresholdSignedSite R p r m *
            lowOwnerRawParentThresholdSignedSite R p r n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]
    _ = _ := by
      symm
      simpa only using
        (Finset.sum_product
          (s := lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r)
          (t := lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r)
          (f := fun mn : ℕ × ℕ =>
            lowOwnerRawParentThresholdSignedSite R p r mn.1 *
              lowOwnerRawParentThresholdSignedSite R p r mn.2))

/-- **Branch quadratic mass is a sum of squares.** -/
theorem lowOwnerFirstOwnerRawParentBranchThresholdEnergy_eq_sum_fiberSquares
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r =
      ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        lowOwnerFirstOwnerRawParentBranchThresholdAmplitude R p sig tau r ^ 2 := by
  let S := lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r
  let T := lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r
  let key : ℕ → Finset ℕ := lowOwnerRawParentRevealedKey R r
  let P := (S.product S).filter (fun mn => key mn.1 = key mn.2)
  let f : ℕ × ℕ → ℝ := fun mn =>
    lowOwnerRawParentThresholdSignedSite R p r mn.1 *
      lowOwnerRawParentThresholdSignedSite R p r mn.2
  have hmaps : ∀ mn ∈ P, key mn.1 ∈ T := by
    intro mn hmn
    have hprod := (Finset.mem_filter.mp hmn).1
    have hmS := (Finset.mem_product.mp hprod).1
    exact Finset.mem_image.mpr ⟨mn.1, hmS, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := P) (t := T) (g := fun mn => key mn.1) hmaps f
  unfold lowOwnerFirstOwnerRawParentBranchThresholdEnergy
  rw [lowOwnerFirstOwnerRawParentBranchCarrier_eq_equalKeyProduct]
  change (∑ mn ∈ P, f mn) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro tau _htau
  have hset := equalKeyPair_filter_eq_fiberProduct S key tau
  rw [hset]
  symm
  simpa [S, T, key, P, f,
    lowOwnerFirstOwnerRawParentBranchSignatureFiber] using
    lowOwnerFirstOwnerRawParentBranchThresholdAmplitude_sq_eq_pairSum
      R p sig tau r

/-- **Tail quadratic mass is a sum of squares.** -/
theorem lowOwnerFirstOwnerRawParentTailThresholdEnergy_eq_sum_fiberSquares
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentTailThresholdEnergy R p sig r =
      ∑ tau ∈ lowOwnerFirstOwnerRawParentTailSignatureSet R p sig r,
        lowOwnerFirstOwnerRawParentTailThresholdAmplitude R p sig tau r ^ 2 := by
  let S := lowOwnerFirstOwnerRawParentTailSiteCarrier R p sig r
  let T := lowOwnerFirstOwnerRawParentTailSignatureSet R p sig r
  let key : ℕ → Finset ℕ := lowOwnerRawParentRevealedKey R r
  let P := (S.product S).filter (fun mn => key mn.1 = key mn.2)
  let f : ℕ × ℕ → ℝ := fun mn =>
    lowOwnerRawParentThresholdSignedSite R p r mn.1 *
      lowOwnerRawParentThresholdSignedSite R p r mn.2
  have hmaps : ∀ mn ∈ P, key mn.1 ∈ T := by
    intro mn hmn
    have hprod := (Finset.mem_filter.mp hmn).1
    have hmS := (Finset.mem_product.mp hprod).1
    exact Finset.mem_image.mpr ⟨mn.1, hmS, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := P) (t := T) (g := fun mn => key mn.1) hmaps f
  unfold lowOwnerFirstOwnerRawParentTailThresholdEnergy
  rw [lowOwnerFirstOwnerRawParentTailCarrier_eq_equalKeyProduct]
  change (∑ mn ∈ P, f mn) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro tau _htau
  have hset := equalKeyPair_filter_eq_fiberProduct S key tau
  rw [hset]
  symm
  simpa [S, T, key, P, f,
    lowOwnerFirstOwnerRawParentTailSignatureFiber] using
    lowOwnerFirstOwnerRawParentTailThresholdAmplitude_sq_eq_pairSum
      R p sig tau r

@[simp] theorem lowOwnerFirstOwnerRawParentBranchThresholdEnergy_nonneg
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    0 ≤ lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r := by
  rw [lowOwnerFirstOwnerRawParentBranchThresholdEnergy_eq_sum_fiberSquares]
  apply Finset.sum_nonneg
  intro tau _htau
  exact sq_nonneg _

@[simp] theorem lowOwnerFirstOwnerRawParentTailThresholdEnergy_nonneg
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    0 ≤ lowOwnerFirstOwnerRawParentTailThresholdEnergy R p sig r := by
  rw [lowOwnerFirstOwnerRawParentTailThresholdEnergy_eq_sum_fiberSquares]
  apply Finset.sum_nonneg
  intro tau _htau
  exact sq_nonneg _

/-- **Legal one-sided threshold bound after signed prefix-star factorization.** -/
theorem lowOwnerFirstOwnerRawParentThresholdIncidenceMass_le_branchThresholdEnergy
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRawParentThresholdIncidenceMass R p sig r ≤
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r := by
  rw [lowOwnerFirstOwnerRawParentThresholdIncidenceMass_eq_branchEnergy_sub_tailEnergy
    hp hr hpr]
  have htail := lowOwnerFirstOwnerRawParentTailThresholdEnergy_nonneg R p sig r
  linarith

end RHLean.Proof
