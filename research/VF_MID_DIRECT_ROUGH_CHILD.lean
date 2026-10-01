import Mathlib
import RHLean.Arithmetic.SignedBuchstabRecursion
import «research.VF_MID_DIRECT_OWNER_DESCENT»

/-!
# Direct rough-child form of the VF-mid discrepancy

This file remains entirely on the direct

  D_R = pi(R^2) - VF_mid(R^2)

architecture.

After the least-prime owner p is stripped from a composite square-band site
n = p*m, the child m is rough below p: every prime factor of m is at least p.

Thus each owner fibre is exactly a finite rough-child interval.  This is the
Buchstab coordinate of the actual band discrepancy P_R - V_R, not a surrogate
PNT/Mertens problem.

If such a rough child m is still composite and q = minFac(m), then

  p <= q
  and
  p*q^2 < (R+1)^2.

So a second descent lives on an explicit hyperbolic region strictly below the
original square boundary.
-/

noncomputable section

open scoped BigOperators
open RHLean.Arithmetic

namespace RHLean.Analysis

/-- A least-prime owner leaves a child with no prime factor below the owner. -/
theorem vfMidSquareBandCompositeOwner_child_roughAbove
    {R p n : ℕ}
    (hn : n ∈ vfMidSquareBandCompositeOwner R p) :
    RoughAbove (p - 1) (n / p) := by
  intro q hq
  have hqData := Nat.mem_primeFactors.mp hq
  have hqPrime : q.Prime := hqData.1
  have hqDvdChild : q ∣ n / p := hqData.2.1
  have hmul := vfMidSquareBandCompositeOwner_mul_div hn
  have hqDvdN : q ∣ n := by
    rw [← hmul]
    exact dvd_mul_of_dvd_right hqDvdChild p
  have hle := Nat.minFac_le_of_dvd hqPrime.two_le hqDvdN
  have howner := (Finset.mem_filter.mp hn).2
  rw [howner] at hle
  omega

/-- If p is prime and m is rough above p-1, then p is the least prime factor
of p*m. -/
theorem minFac_prime_mul_eq_of_roughAbove_pred
    {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hrough : RoughAbove (p - 1) m) :
    (p * m).minFac = p := by
  have hprod2 : 2 ≤ p * m := by
    exact le_trans hp.two_le (Nat.le_mul_of_pos_right p (by omega))
  have hprod1 : p * m ≠ 1 := by omega
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p m)
  · have hqPrime : (p * m).minFac.Prime := Nat.minFac_prime hprod1
    have hqDvd : (p * m).minFac ∣ p * m := Nat.minFac_dvd (p * m)
    rcases hqPrime.dvd_mul.mp hqDvd with hqp | hqm
    · have heq :
          (p * m).minFac = p :=
        (Nat.prime_dvd_prime_iff_eq hqPrime hp).mp hqp
      omega
    · have hm0 : m ≠ 0 := by omega
      have hmem : (p * m).minFac ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqPrime, hqm, hm0⟩
      have hgt := hrough _ hmem
      omega

/-- The exact rough-child carrier for one least-prime owner p. -/
def vfMidSquareBandOwnerRoughChildren (R p : ℕ) : Finset ℕ :=
  (Finset.Icc p (R ^ 2 - 1)).filter fun m =>
    R ^ 2 < p * m ∧
      p * m < (R + 1) ^ 2 ∧
      RoughAbove (p - 1) m

/-- Every stripped owner child lies in the explicit rough-child carrier. -/
theorem vfMidSquareBandCompositeOwnerChildren_subset_rough
    {R p : ℕ} (hR : 3 ≤ R)
    (hp : p ∈ vfMidSquareBandOwnerPrimes R) :
    vfMidSquareBandCompositeOwnerChildren R p ⊆
      vfMidSquareBandOwnerRoughChildren R p := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
  have hpData := mem_vfMidSquareBandOwnerPrimes.mp hp
  have hchildLow :=
    vfMidSquareBandCompositeOwner_le_child (by omega : 2 ≤ R) hn
  have hchildHigh :=
    vfMidSquareBandCompositeOwner_child_lt_square hR hn
  have hmul := vfMidSquareBandCompositeOwner_mul_div hn
  have hcomp : n ∈ vfMidSquareBandComposites R :=
    (Finset.mem_filter.mp hn).1
  have hsite : n ∈ vfMidSquareBandSites R :=
    (Finset.mem_filter.mp hcomp).1
  have hband : R ^ 2 < n ∧ n < (R + 1) ^ 2 := by
    simpa [vfMidSquareBandSites] using hsite
  have hrough := vfMidSquareBandCompositeOwner_child_roughAbove hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hchildLow, ?_⟩, ?_⟩
  · omega
  · rw [hmul]
    exact ⟨hband.1, hband.2, hrough⟩

/-- Conversely every explicit rough child reconstructs a unique composite site
owned by p. -/
theorem vfMidSquareBandOwnerRoughChildren_subset_children
    {R p : ℕ} (hR : 3 ≤ R)
    (hp : p ∈ vfMidSquareBandOwnerPrimes R) :
    vfMidSquareBandOwnerRoughChildren R p ⊆
      vfMidSquareBandCompositeOwnerChildren R p := by
  intro m hm
  have hpData := mem_vfMidSquareBandOwnerPrimes.mp hp
  have hpPrime := hpData.1
  rcases Finset.mem_filter.mp hm with ⟨hmIcc, hdata⟩
  rcases Finset.mem_Icc.mp hmIcc with ⟨hpm, _hmTop⟩
  rcases hdata with ⟨hlo, hhi, hrough⟩
  have hm1 : 1 ≤ m := by
    exact hpPrime.two_le.trans hpm
  have hnSite : p * m ∈ vfMidSquareBandSites R := by
    simp [vfMidSquareBandSites, hlo, hhi]
  have hnNotPrime : ¬ (p * m).Prime := by
    intro hnPrime
    have hpdvd : p ∣ p * m := dvd_mul_right p m
    rcases (Nat.dvd_prime hnPrime).mp hpdvd with hp1 | hpeq
    · exact hpPrime.ne_one hp1
    · have hmEq : m = 1 := by
        apply Nat.eq_of_mul_eq_mul_left hpPrime.pos
        simpa using hpeq.symm
      omega
  have hnComp : p * m ∈ vfMidSquareBandComposites R :=
    Finset.mem_filter.mpr ⟨hnSite, hnNotPrime⟩
  have hmin :=
    minFac_prime_mul_eq_of_roughAbove_pred hpPrime hm1 hrough
  have hnOwner : p * m ∈ vfMidSquareBandCompositeOwner R p :=
    Finset.mem_filter.mpr ⟨hnComp, hmin⟩
  unfold vfMidSquareBandCompositeOwnerChildren
  apply Finset.mem_image.mpr
  refine ⟨p * m, hnOwner, ?_⟩
  exact Nat.mul_div_cancel_left m hpPrime.pos

/-- **Exact rough-child identification.**  One least-prime owner fibre is
literally one finite rough-child interval. -/
theorem vfMidSquareBandCompositeOwnerChildren_eq_rough
    {R p : ℕ} (hR : 3 ≤ R)
    (hp : p ∈ vfMidSquareBandOwnerPrimes R) :
    vfMidSquareBandCompositeOwnerChildren R p =
      vfMidSquareBandOwnerRoughChildren R p :=
  Finset.Subset.antisymm
    (vfMidSquareBandCompositeOwnerChildren_subset_rough hR hp)
    (vfMidSquareBandOwnerRoughChildren_subset_children hR hp)

/-- Direct band discrepancy with every composite owner fibre replaced by its
exact rough-child interval. -/
theorem vfMidSquareBandError_eq_roughOwnerChildren
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidSquareBandError R =
      2 * (R : ℝ) - vfMidBandMass R -
        ∑ p ∈ vfMidSquareBandOwnerPrimes R,
          ((vfMidSquareBandOwnerRoughChildren R p).card : ℝ) := by
  rw [vfMidSquareBandError_eq_ownerChildren R (by omega)]
  apply congrArg
    (fun x : ℝ => 2 * (R : ℝ) - vfMidBandMass R - x)
  apply Finset.sum_congr rfl
  intro p hp
  rw [vfMidSquareBandCompositeOwnerChildren_eq_rough hR hp]

/-- A composite rough child has a second least-prime owner at least as large as
its first owner. -/
theorem vfMidSquareBandOwnerRoughChild_le_minFac
    {R p m : ℕ}
    (hm : m ∈ vfMidSquareBandOwnerRoughChildren R p)
    (hmComp : ¬ m.Prime) :
    p ≤ m.minFac := by
  rcases Finset.mem_filter.mp hm with ⟨hmIcc, hdata⟩
  have hm1 : 1 ≤ m := by
    exact (Finset.mem_Icc.mp hmIcc).1.trans' (by omega : 1 ≤ p)
  have hm0 : 0 < m := by omega
  have hminPrime : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hminDvd : m.minFac ∣ m := Nat.minFac_dvd m
  have hmem : m.minFac ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hminPrime, hminDvd, by omega⟩
  have hgt := hdata.2.2 _ hmem
  omega

/-- **Second-owner hyperbolic compression.**

If a rough child remains composite, q=minFac(m) satisfies p<=q and the exact
physical constraint p*q^2 < (R+1)^2. -/
theorem vfMidSquareBandOwnerRoughChild_secondOwner_geometry
    {R p m : ℕ}
    (hm : m ∈ vfMidSquareBandOwnerRoughChildren R p)
    (hmComp : ¬ m.Prime) :
    p ≤ m.minFac ∧ p * (m.minFac ^ 2) < (R + 1) ^ 2 := by
  have hpq :=
    vfMidSquareBandOwnerRoughChild_le_minFac hm hmComp
  rcases Finset.mem_filter.mp hm with ⟨hmIcc, hdata⟩
  have hmpos : 0 < m := by
    have hpm := (Finset.mem_Icc.mp hmIcc).1
    omega
  have hsq : m.minFac ^ 2 ≤ m :=
    Nat.minFac_sq_le_self hmpos hmComp
  have hmul :
      p * (m.minFac ^ 2) ≤ p * m :=
    Nat.mul_le_mul_left p hsq
  exact ⟨hpq, hmul.trans_lt hdata.2.1⟩

/-- The exact D_(R+1)=D_R+e_R recurrence in rough-child coordinates. -/
theorem vfMidSquareEndpointError_succ_eq_roughOwnerChildren
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidSquareEndpointError (R + 1) =
      vfMidSquareEndpointError R +
        (2 * (R : ℝ) - vfMidBandMass R -
          ∑ p ∈ vfMidSquareBandOwnerPrimes R,
            ((vfMidSquareBandOwnerRoughChildren R p).card : ℝ)) := by
  rw [vfMidSquareEndpointError_succ R (by omega),
    vfMidSquareBandError_eq_roughOwnerChildren R hR]

end RHLean.Analysis
