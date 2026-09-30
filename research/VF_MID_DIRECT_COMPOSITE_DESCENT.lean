import Mathlib
import RHLean.Analysis.NativePNTErrorMass
import «research.VF_MID_SQUARE_BAND_COMPOSITE_BRIDGE»

/-!
# Direct composite descent for the VF-mid square-band error

This file stays on the direct VF-mid proof graph.

Two exact coordinates are exposed:

1. the psi band increment is literally the finite site sum
     sum_{R^2 < n <= (R+1)^2} (Lambda(n) - 1);
2. every composite interior site has a unique least-prime owner p <= R.
   Stripping that owner sends the site to a strictly smaller reciprocal child.
   Once p^3 reaches the upper square, that child is forced to be prime.

No asymptotic prime-distribution estimate is used here.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Integer sites carrying the exact psi increment of one complete square band. -/
def vfMidDirectPsiIntegerBand (R : ℕ) : Finset ℕ :=
  Finset.Ioc (R ^ 2) ((R + 1) ^ 2)

/-- Centered psi increment of one square band, defined here directly from
the native Chebyshev error so this file has no dependency on the experimental
Selberg branch. -/
def vfMidCompositePsiBandError (R : ℕ) : ℝ :=
  nativePNTError ((R + 1) ^ 2) - nativePNTError (R ^ 2)

/-- Exact finite interval form of the psi increment. -/
theorem vfMidDirectPsiBandMass_eq_siteSum (R : ℕ) :
    nativePsi ((R + 1) ^ 2) - nativePsi (R ^ 2) =
      ∑ n ∈ vfMidDirectPsiIntegerBand R, Λ n := by
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  have hsub :
      Finset.Icc 1 (R ^ 2) ⊆ Finset.Icc 1 ((R + 1) ^ 2) := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnR⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hnR.trans hsq⟩
  have hset :
      Finset.Icc 1 ((R + 1) ^ 2) \ Finset.Icc 1 (R ^ 2) =
        vfMidDirectPsiIntegerBand R := by
    ext n
    simp [vfMidDirectPsiIntegerBand]
    omega
  unfold nativePsi
  rw [← Finset.sum_sdiff hsub, hset]
  ring

/-- **Exact site law.**  The centered psi mass in one square band is the sum
of the elementary local defects Lambda(n)-1 over its 2R+1 integer sites. -/
theorem vfMidCompositePsiBandError_eq_siteDefects (R : ℕ) :
    vfMidCompositePsiBandError R =
      ∑ n ∈ vfMidDirectPsiIntegerBand R, (Λ n - 1) := by
  unfold vfMidCompositePsiBandError nativePNTError
  have hpsi := vfMidDirectPsiBandMass_eq_siteSum R
  have hcard :
      (vfMidDirectPsiIntegerBand R).card = 2 * R + 1 := by
    unfold vfMidDirectPsiIntegerBand
    rw [Finset.card_Ioc]
    omega
  have hones :
      (∑ _n ∈ vfMidDirectPsiIntegerBand R, (1 : ℝ)) =
        2 * (R : ℝ) + 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    push_cast
    ring
  rw [Finset.sum_sub_distrib, hones]
  push_cast at hpsi ⊢
  nlinarith

/-- Composite sites owned by a fixed least prime factor. -/
def vfMidSquareBandCompositeOwner (R p : ℕ) : Finset ℕ :=
  (vfMidSquareBandComposites R).filter (fun n => n.minFac = p)

/-- Membership in an owner fibre exposes the literal least-prime identity. -/
theorem vfMidSquareBandCompositeOwner_mem
    {R p n : ℕ} (hn : n ∈ vfMidSquareBandCompositeOwner R p) :
    n ∈ vfMidSquareBandComposites R ∧ n.minFac = p := by
  exact Finset.mem_filter.mp hn

/-- Every owner of a square-band composite is itself prime and lies at or below
the square root scale R. -/
theorem vfMidSquareBandCompositeOwner_prime_le_root
    {R p n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareBandCompositeOwner R p) :
    p.Prime ∧ p ≤ R := by
  rcases vfMidSquareBandCompositeOwner_mem hn with ⟨hnComp, hmin⟩
  rcases Finset.mem_filter.mp hnComp with ⟨hnBand, hnNotPrime⟩
  rcases Finset.mem_Ioo.mp hnBand with ⟨hnLow, hnHigh⟩
  have hnpos : 0 < n := by omega
  have hn1 : n ≠ 1 := by omega
  have hpPrime : p.Prime := by
    simpa [hmin] using Nat.minFac_prime hn1
  have hpSq : p ^ 2 ≤ n := by
    simpa [hmin] using Nat.minFac_sq_le_self hnpos hnNotPrime
  have hpR : p ≤ R := by
    by_contra hnot
    have hRp : R + 1 ≤ p := by omega
    have hsq : (R + 1) ^ 2 ≤ p ^ 2 :=
      Nat.pow_le_pow_left hRp 2
    omega
  exact ⟨hpPrime, hpR⟩

/-- Stripping the least-prime owner reconstructs the composite exactly. -/
theorem vfMidSquareBandCompositeOwner_mul_div
    {R p n : ℕ} (hn : n ∈ vfMidSquareBandCompositeOwner R p) :
    p * (n / p) = n := by
  rcases vfMidSquareBandCompositeOwner_mem hn with ⟨_hnComp, hmin⟩
  have hpDvd : p ∣ n := by
    simpa [hmin] using Nat.minFac_dvd n
  exact Nat.mul_div_cancel' hpDvd

/-- The stripped child of any owned composite is at least its owner. -/
theorem vfMidSquareBandCompositeOwner_le_child
    {R p n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareBandCompositeOwner R p) :
    p ≤ n / p := by
  rcases vfMidSquareBandCompositeOwner_mem hn with ⟨hnComp, hmin⟩
  rcases Finset.mem_filter.mp hnComp with ⟨hnBand, hnNotPrime⟩
  have hnpos : 0 < n := by
    rcases Finset.mem_Ioo.mp hnBand with ⟨hnLow, _⟩
    omega
  have h := Nat.minFac_le_div hnpos hnNotPrime
  simpa [hmin] using h

/-- **Strict reciprocal descent.**  Removing any least-prime owner from a
square-band composite sends the child below R^2. -/
theorem vfMidSquareBandCompositeOwner_child_lt_square
    {R p n : ℕ} (hR : 3 ≤ R)
    (hn : n ∈ vfMidSquareBandCompositeOwner R p) :
    n / p < R ^ 2 := by
  rcases vfMidSquareBandCompositeOwner_prime_le_root (hR := hR.trans' (by omega)) hn
    with ⟨hpPrime, _hpR⟩
  rcases vfMidSquareBandCompositeOwner_mem hn with ⟨hnComp, _hmin⟩
  rcases Finset.mem_filter.mp hnComp with ⟨hnBand, _hnNotPrime⟩
  have hnHigh : n < (R + 1) ^ 2 := (Finset.mem_Ioo.mp hnBand).2
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hmul := vfMidSquareBandCompositeOwner_mul_div hn
  have hupper : 2 * (n / p) < (R + 1) ^ 2 := by
    calc
      2 * (n / p) ≤ p * (n / p) := Nat.mul_le_mul_right _ hp2
      _ = n := hmul
      _ < (R + 1) ^ 2 := hnHigh
  nlinarith

/-- **High-owner terminal law.**  If the owner's cube already reaches the
upper square, its stripped child cannot still be composite.  It is forced to
be prime. -/
theorem vfMidSquareBandCompositeOwner_child_prime_of_upperSquare_le_cube
    {R p n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidSquareBandCompositeOwner R p)
    (hcube : (R + 1) ^ 2 ≤ p ^ 3) :
    (n / p).Prime := by
  have hpData := vfMidSquareBandCompositeOwner_prime_le_root hR hn
  have hpPrime := hpData.1
  have hpChild := vfMidSquareBandCompositeOwner_le_child hR hn
  have hmul := vfMidSquareBandCompositeOwner_mul_div hn
  rcases vfMidSquareBandCompositeOwner_mem hn with ⟨hnComp, _hmin⟩
  rcases Finset.mem_filter.mp hnComp with ⟨hnBand, _hnNotPrime⟩
  have hnHigh : n < (R + 1) ^ 2 := (Finset.mem_Ioo.mp hnBand).2
  let q : ℕ := n / p
  have hq2 : 2 ≤ q := hpPrime.two_le.trans hpChild
  by_contra hqPrime
  have hqpos : 0 < q := by omega
  have hsPrime : q.minFac.Prime := Nat.minFac_prime (by omega)
  have hsDvdQ : q.minFac ∣ q := Nat.minFac_dvd q
  have hqDvdN : q ∣ n := by
    refine ⟨p, ?_⟩
    simpa [q, mul_comm] using hmul.symm
  have hsDvdN : q.minFac ∣ n := dvd_trans hsDvdQ hqDvdN
  have hpLeS : p ≤ q.minFac := by
    have h := Nat.minFac_le_of_dvd hsPrime.two_le hsDvdN
    simpa using h
  have hsSq : q.minFac ^ 2 ≤ q :=
    Nat.minFac_sq_le_self hqpos hqPrime
  have hpSq : p ^ 2 ≤ q := by
    exact (Nat.pow_le_pow_left hpLeS 2).trans hsSq
  have hpCubeLe : p ^ 3 ≤ n := by
    calc
      p ^ 3 = p * p ^ 2 := by ring
      _ ≤ p * q := Nat.mul_le_mul_left p hpSq
      _ = n := by simpa [q] using hmul
  omega

end RHLean.Analysis
