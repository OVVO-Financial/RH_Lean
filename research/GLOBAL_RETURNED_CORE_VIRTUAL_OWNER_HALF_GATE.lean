import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BRANCH_CROSS_AMPLITUDE»
import «research.GLOBAL_RETURNED_CORE_SIGNED_POLARIZATION_ENDPOINT»
import «research.GLOBAL_RETURNED_CORE_SIGNATURE_FILTRATION»

/-!
# Virtual-owner half-square gate

The post-#754 branch inequality may be evaluated at a prime coordinate strictly
beyond the physical clock.  Such a coordinate is purely virtual:

* no physical site is divisible by it;
* no larger revealed prime occurs on the clock;
* every virtual child lies beyond the Dirichlet endpoint.

Consequently the revealed-signature branch has one effective fibre and its
Dirichlet owner-difference amplitude is exactly the ordinary first-owner cell
incidence amplitude.  The sharp branch inequality therefore improves the legal
whole-cell guardrail from coefficient 1 to coefficient 1/2.

This is still only a parent estimate.  It is not summed independently over
first owners; the exact prime-filtration telescope must be preserved.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem lowOwnerRevealedPrimesAbove_eq_empty_of_endpoint_lt
    {R r : ℕ} (hXr : squareRootEndpoint R < r) :
    lowOwnerRevealedPrimesAbove R r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqUpTo, hrq⟩
  have hqX := (mem_primesUpTo.mp hqUpTo).2
  omega

private theorem lowOwnerFirstOwnerRawParentBranchSiteCarrier_eq_base_of_endpoint_lt
    {R p r : ℕ} {sig : Finset ℕ}
    (hXr : squareRootEndpoint R < r) :
    lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r =
      lowOwnerFirstOwnerBaseFiber R p sig := by
  ext n
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).1
  · intro hn
    refine Finset.mem_filter.mpr ⟨hn, ?_⟩
    intro hrn
    have hnCar := (Finset.mem_filter.mp hn).1
    have hnIcc := (Finset.mem_filter.mp hnCar).1
    have hnPos : 0 < n := by
      have := (Finset.mem_Icc.mp hnIcc).1
      omega
    have hrle : r ≤ n := Nat.le_of_dvd hnPos hrn
    have hnX := (Finset.mem_Icc.mp hnIcc).2
    omega

private theorem lowOwnerRawParentRevealedKey_eq_empty_of_endpoint_lt
    {R r n : ℕ} (hXr : squareRootEndpoint R < r) :
    lowOwnerRawParentRevealedKey R r n = ∅ := by
  unfold lowOwnerRawParentRevealedKey
  rw [lowOwnerRevealedPrimesAbove_eq_empty_of_endpoint_lt hXr]
  simp [lowOwnerRevealedPrimeSignature]

private theorem lowOwnerPhysicalDirichletIncidenceWeight_virtualChild_eq_zero
    {R p r n : ℕ} (hp : p.Prime)
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hXr : squareRootEndpoint R < r) :
    lowOwnerPhysicalDirichletIncidenceWeight R p (r * n) = 0 := by
  have hnIcc := (Finset.mem_filter.mp hn).1
  have hnOne := (Finset.mem_Icc.mp hnIcc).1
  have hnPos : 0 < n := by omega
  have hrPos : 0 < r := by omega
  have hrnPos : 0 < r * n := Nat.mul_pos hrPos hnPos
  have hrle : r ≤ r * n := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left r hnPos
  have hrnX : squareRootEndpoint R < r * n := hXr.trans_le hrle
  have hprn : r * n ≤ p * (r * n) := Nat.le_mul_of_pos_left (r * n) hp.pos
  have hprnX : squareRootEndpoint R < p * (r * n) := hrnX.trans_le hprn
  unfold lowOwnerPhysicalDirichletIncidenceWeight
  rw [lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hrnX,
    lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hprnX]
  ring

private theorem lowOwnerBranchDirichletIncidenceDifferenceSignedSite_eq_incidenceSite_of_virtual
    {R p r n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hn : n ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hXr : squareRootEndpoint R < r) :
    lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n =
      lowOwnerFirstOwnerDirichletIncidenceSite R p n := by
  have hnCar := (Finset.mem_filter.mp hn).1
  have hzero :=
    lowOwnerPhysicalDirichletIncidenceWeight_virtualChild_eq_zero
      hp hnCar hXr
  unfold lowOwnerBranchDirichletIncidenceDifferenceSignedSite
    lowOwnerDirichletOwnerDifference
    lowOwnerFirstOwnerDirichletIncidenceSite
  rw [hzero]
  ring

private theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_cell_sq_of_virtual
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hXr : squareRootEndpoint R < r) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy R p sig r =
      lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2 := by
  have hbranch :
      lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r =
        lowOwnerFirstOwnerBaseFiber R p sig :=
    lowOwnerFirstOwnerRawParentBranchSiteCarrier_eq_base_of_endpoint_lt hXr
  have habove :
      lowOwnerRevealedPrimesAbove R r = ∅ :=
    lowOwnerRevealedPrimesAbove_eq_empty_of_endpoint_lt hXr
  have hkey :
      ∀ n, lowOwnerRawParentRevealedKey R r n = ∅ := by
    intro n
    exact lowOwnerRawParentRevealedKey_eq_empty_of_endpoint_lt hXr
  by_cases hempty : lowOwnerFirstOwnerBaseFiber R p sig = ∅
  · simp [lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy,
      lowOwnerFirstOwnerDirichletIncidenceAmplitude,
      lowOwnerFirstOwnerRawParentBranchSignatureSet,
      hbranch, hempty]
  · have hne : (lowOwnerFirstOwnerBaseFiber R p sig).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hsigset :
        lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r = {∅} := by
      unfold lowOwnerFirstOwnerRawParentBranchSignatureSet
      rw [hbranch]
      ext tau
      constructor
      · intro htau
        rcases Finset.mem_image.mp htau with ⟨n, _hn, hntau⟩
        rw [hkey n] at hntau
        simpa using hntau.symm
      · intro htau
        have htau0 : tau = ∅ := by simpa using htau
        subst tau
        rcases hne with ⟨n, hn⟩
        exact Finset.mem_image.mpr ⟨n, hn, hkey n⟩
    have hfiber :
        lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig ∅ r =
          lowOwnerFirstOwnerBaseFiber R p sig := by
      unfold lowOwnerFirstOwnerRawParentBranchSignatureFiber
      rw [hbranch]
      ext n
      simp [hkey n]
    unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
    rw [hsigset]
    simp only [Finset.sum_singleton]
    unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
      lowOwnerFirstOwnerDirichletIncidenceAmplitude
    rw [hfiber]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    exact
      lowOwnerBranchDirichletIncidenceDifferenceSignedSite_eq_incidenceSite_of_virtual
        hp hn hXr

/-- **Virtual-owner sharpening of the complete first-owner cell guardrail.** -/
theorem lowOwnerFirstOwnerSignedCellTelescope_le_half_dirichletIncidence_sq
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig ≤
      (1 / 2 : ℝ) * lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2 := by
  obtain ⟨r, hlarge, hr⟩ :=
    Nat.exists_infinite_primes
      (max (squareRootEndpoint R + 1) (p + 1))
  have hXr : squareRootEndpoint R < r := by
    have h := (le_max_left (squareRootEndpoint R + 1) (p + 1)).trans hlarge
    omega
  have hpr : p < r := by
    have h := (le_max_right (squareRootEndpoint R + 1) (p + 1)).trans hlarge
    omega
  have habove :
      lowOwnerRevealedPrimesAbove R r = ∅ :=
    lowOwnerRevealedPrimesAbove_eq_empty_of_endpoint_lt hXr
  have hgate :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_half_dirichletIncidenceEnergy
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
  rw [habove,
    lowOwnerFirstOwnerRevealedPolarizationEnergy_empty_eq_signedCellTelescope hp,
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_cell_sq_of_virtual
      hp hXr] at hgate
  exact hgate

/-- Same sharpening in the literal lower-signature cell coordinate. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_le_half_signatureCell_sq
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig ≤
      (1 / 2 : ℝ) * lowOwnerFirstOwnerSignatureCellAmplitude R p sig ^ 2 := by
  rw [← lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_signatureCellAmplitude hp]
  exact lowOwnerFirstOwnerSignedCellTelescope_le_half_dirichletIncidence_sq hp

end RHLean.Proof
