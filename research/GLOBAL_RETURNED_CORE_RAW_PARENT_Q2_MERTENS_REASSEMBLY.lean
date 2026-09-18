import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_GLOBAL_AMPLITUDE_REASSEMBLY»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_MERTENS_WALL»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_SIGNATURE_FUBINI»
import «research.GLOBAL_RETURNED_CORE_COMPENSATED_OWNER_BLOCK»

/-!
# Reassemble the raw-parent q² column to the literal Mertens daughter

After #754/#755 the current-owner clipped threshold amplitude is still written
on p-free first-owner cells and revealed r-signature fibres.  This file removes
those bookkeeping labels before any square is taken.

The key observation is a generic finite owner-lens identity.  For any scalar
site function f which vanishes beyond the physical clock, the p-free incidence

  sum_{p ∤ a} mu(a) * (f(a) - f(p*a))

reconstructs the full signed physical sum of f.  The p-divisible half is exactly
the returned p-child half with the fresh-prime Möbius sign reversal.

Specialize f to the r-threshold wall at cutoff y.  The preceding Othello wall
identity says that full signed wall is exactly M(y).  Hence the fully
sig/tau-reassembled #755 daughter amplitude is literally the lower-scale
Mertens amplitude, with no coefficient L2 surrogate and no estimate.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Global admitted p-free carrier: the p-child remains on the common clock. -/
def lowOwnerFirstOwnerGlobalAdmittedPFreeCarrier
    (R p : ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerPFreeCarrier R p).filter fun a =>
    p * a ≤ squareRootEndpoint R

/-- A global admitted p-free parent is an admitted parent in its own lower
signature cell. -/
private theorem globalAdmitted_mem_cellAdmitted
    {R p a : ℕ}
    (ha : a ∈ lowOwnerFirstOwnerGlobalAdmittedPFreeCarrier R p) :
    a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p
      (squarefreeLowerPrimeSignature p a) := by
  rcases Finset.mem_filter.mp ha with ⟨haFree, hpaX⟩
  rcases Finset.mem_filter.mp haFree with ⟨haCar, hpa⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨haCar, ⟨rfl, hpa⟩⟩, hpaX⟩

/-- A global p-divisible site is a child in its own lower-signature cell. -/
private theorem globalPDivisible_mem_childCell
    {R p n : ℕ}
    (hn : n ∈ lowOwnerFirstOwnerPDivisibleCarrier R p) :
    n ∈ lowOwnerFirstOwnerChildFiber R p
      (squarefreeLowerPrimeSignature p n) := by
  rcases Finset.mem_filter.mp hn with ⟨hnCar, hpn⟩
  exact Finset.mem_filter.mpr ⟨hnCar, ⟨rfl, hpn⟩⟩

/-- Multiplication by p maps a global admitted p-free parent to the global
p-divisible carrier. -/
private theorem globalAdmitted_mul_mem_pDivisible
    {R p a : ℕ} (hp : p.Prime)
    (ha : a ∈ lowOwnerFirstOwnerGlobalAdmittedPFreeCarrier R p) :
    p * a ∈ lowOwnerFirstOwnerPDivisibleCarrier R p := by
  have hcell := globalAdmitted_mem_cellAdmitted ha
  have hchild := lowOwnerFirstOwner_mul_mem_child_of_admitted hp hcell
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hchild).1, (Finset.mem_filter.mp hchild).2.2⟩

/-- Division by p returns every global p-divisible site to the global admitted
p-free carrier. -/
private theorem globalPDivisible_div_mem_admitted
    {R p n : ℕ} (hp : p.Prime)
    (hn : n ∈ lowOwnerFirstOwnerPDivisibleCarrier R p) :
    n / p ∈ lowOwnerFirstOwnerGlobalAdmittedPFreeCarrier R p := by
  have hchild := globalPDivisible_mem_childCell hn
  have hparent := lowOwnerFirstOwner_div_mem_admitted_of_child hp hchild
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hparent).1).1,
        (Finset.mem_filter.mp (Finset.mem_filter.mp hparent).1).2.2⟩,
      (Finset.mem_filter.mp hparent).2⟩

/-- **Generic p-child return for an arbitrary scalar site function.** -/
private theorem sum_pDivisible_realMoebius_mul_eq_neg_admittedParent
    {R p : ℕ} (hp : p.Prime) (f : ℕ → ℝ) :
    (∑ n ∈ lowOwnerFirstOwnerPDivisibleCarrier R p,
      realMoebiusStep n * f n) =
      ∑ a ∈ lowOwnerFirstOwnerGlobalAdmittedPFreeCarrier R p,
        -(realMoebiusStep a * f (p * a)) := by
  refine Finset.sum_bij
    (fun n _hn => n / p)
    (fun n hn => globalPDivisible_div_mem_admitted hp hn)
    ?_ ?_ ?_
  · intro n hn m hm heq
    have hndiv := (Finset.mem_filter.mp hn).2
    have hmdiv := (Finset.mem_filter.mp hm).2
    change n / p = m / p at heq
    calc
      n = p * (n / p) := (Nat.mul_div_cancel' hndiv).symm
      _ = p * (m / p) := by rw [heq]
      _ = m := Nat.mul_div_cancel' hmdiv
  · intro a ha
    refine ⟨p * a, globalAdmitted_mul_mem_pDivisible hp ha, ?_⟩
    change (p * a) / p = a
    simpa [Nat.mul_comm] using Nat.mul_div_left a hp.pos
  · intro n hn
    have hchild := globalPDivisible_mem_childCell hn
    have hbase := lowOwnerFirstOwner_div_mem_base_of_child hp hchild
    have hnot := (Finset.mem_filter.mp hbase).2.2
    have hndiv := (Finset.mem_filter.mp hn).2
    have hcancel : p * (n / p) = n := Nat.mul_div_cancel' hndiv
    calc
      realMoebiusStep n * f n =
          realMoebiusStep (p * (n / p)) * f (p * (n / p)) := by rw [hcancel]
      _ = -(realMoebiusStep (n / p) * f (p * (n / p))) := by
        rw [realMoebiusStep_mul_prime_eq_neg hp hnot]
        ring

/-- A site function vanishing beyond the physical clock may be pulled back
through every p-free parent; clipped p-children contribute zero. -/
private theorem sum_pFree_childEval_eq_admitted
    {R p : ℕ} (f : ℕ → ℝ)
    (hzero : ∀ n, squareRootEndpoint R < n → f n = 0) :
    (∑ a ∈ lowOwnerFirstOwnerPFreeCarrier R p,
      realMoebiusStep a * f (p * a)) =
      ∑ a ∈ lowOwnerFirstOwnerGlobalAdmittedPFreeCarrier R p,
        realMoebiusStep a * f (p * a) := by
  unfold lowOwnerFirstOwnerGlobalAdmittedPFreeCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hadm : p * a ≤ squareRootEndpoint R
  · simp [hadm]
  · have hclip : squareRootEndpoint R < p * a := Nat.lt_of_not_ge hadm
    rw [hzero (p * a) hclip]
    simp [hadm]

/-- **Generic exact owner lens.**  No positivity or norm is used. -/
theorem sum_pFree_realMoebius_ownerDifference_eq_full
    {R p : ℕ} (hp : p.Prime) (f : ℕ → ℝ)
    (hzero : ∀ n, squareRootEndpoint R < n → f n = 0) :
    (∑ a ∈ lowOwnerFirstOwnerPFreeCarrier R p,
      realMoebiusStep a * (f a - f (p * a))) =
      ∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
        realMoebiusStep n * f n := by
  have hchild :=
    sum_pDivisible_realMoebius_mul_eq_neg_admittedParent
      (R := R) hp f
  have hpull := sum_pFree_childEval_eq_admitted
    (R := R) (p := p) f hzero
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerNonzeroMobiusCarrier R)
      (p := fun n => p ∣ n)
      (f := fun n => realMoebiusStep n * f n)
  have hparts :
      (∑ n ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        realMoebiusStep n * f n) +
      (∑ n ∈ lowOwnerFirstOwnerPDivisibleCarrier R p,
        realMoebiusStep n * f n) =
      ∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
        realMoebiusStep n * f n := by
    simpa [lowOwnerFirstOwnerPFreeCarrier,
      lowOwnerFirstOwnerPDivisibleCarrier, add_comm] using hpartition
  calc
    (∑ a ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        realMoebiusStep a * (f a - f (p * a))) =
      (∑ a ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        realMoebiusStep a * f a) -
      (∑ a ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        realMoebiusStep a * f (p * a)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _ha
          ring
    _ =
      (∑ a ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        realMoebiusStep a * f a) -
      (∑ a ∈ lowOwnerFirstOwnerGlobalAdmittedPFreeCarrier R p,
        realMoebiusStep a * f (p * a)) := by rw [hpull]
    _ =
      (∑ a ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        realMoebiusStep a * f a) +
      (∑ n ∈ lowOwnerFirstOwnerPDivisibleCarrier R p,
        realMoebiusStep n * f n) := by
          rw [hchild, Finset.sum_neg_distrib]
          ring
    _ = _ := hparts

/-- Summing first-owner signatures removes the remaining cell label on the
r-free branch. -/
private theorem sum_signature_branchClippedTotal_eq_rFreePFree
    (R p : ℕ) (r y : ℕ) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r y) =
      ∑ n ∈ (lowOwnerFirstOwnerPFreeCarrier R p).filter (fun n => ¬ r ∣ n),
        realMoebiusStep n *
          lowOwnerThresholdClippedDifference p r n y := by
  let S := (lowOwnerFirstOwnerPFreeCarrier R p).filter (fun n => ¬ r ∣ n)
  let T := lowOwnerFirstOwnerSignatureSet R p
  let key : ℕ → Finset ℕ := squarefreeLowerPrimeSignature p
  let f : ℕ → ℝ := fun n =>
    realMoebiusStep n * lowOwnerThresholdClippedDifference p r n y
  have hmaps : ∀ n ∈ S, key n ∈ T := by
    intro n hn
    have hnFree := (Finset.mem_filter.mp hn).1
    have hnCar := (Finset.mem_filter.mp hnFree).1
    exact Finset.mem_image.mpr ⟨n, hnCar, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := key) hmaps f
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r y) =
      ∑ sig ∈ T,
        ∑ n ∈ S with key n = sig, f n := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          unfold lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
          congr 1
          ext n
          simp [S, key, lowOwnerFirstOwnerPFreeCarrier,
            lowOwnerFirstOwnerRawParentBranchSiteCarrier,
            lowOwnerFirstOwnerBaseFiber,
            and_assoc, and_left_comm, and_comm]
    _ = ∑ n ∈ S, f n := hfiber
    _ = _ := rfl

/-- The r-threshold site function used by the owner-lens reassembly. -/
private def rThresholdWallSite (r y n : ℕ) : ℝ :=
  if ¬ r ∣ n then lowOwnerThresholdCrossingIndicator r n y else 0

/-- The threshold wall is Dirichlet-zero beyond its cutoff, hence beyond any
larger physical clock. -/
private theorem rThresholdWallSite_eq_zero_of_cutoff_lt
    {r y n : ℕ} (hyn : y < n) :
    rThresholdWallSite r y n = 0 := by
  unfold rThresholdWallSite lowOwnerThresholdCrossingIndicator
  by_cases hdiv : r ∣ n
  · simp [hdiv]
  · have hnot : ¬ (n ≤ y ∧ y < r * n) := by omega
    simp [hdiv, hnot]

/-- On an r-free p-parent, the generic p-owner difference is exactly the #755
clipped r-threshold difference. -/
private theorem rThresholdWallSite_ownerDifference_eq_clipped
    {p r n y : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hrn : ¬ r ∣ n) :
    rThresholdWallSite r y n -
        rThresholdWallSite r y (p * n) =
      lowOwnerThresholdClippedDifference p r n y := by
  have hrp : ¬ r ∣ p := by
    intro h
    have heq : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
    omega
  have hrpn : ¬ r ∣ p * n := by
    intro h
    rcases hr.dvd_mul.mp h with h | h
    · exact hrp h
    · exact hrn h
  simp [rThresholdWallSite, hrn, hrpn,
    lowOwnerThresholdClippedDifference]

/-- If the parent already carries r, both sides of the r-threshold p-incidence
vanish. -/
private theorem rThresholdWallSite_ownerDifference_eq_zero_of_dvd
    {p r n y : ℕ} (hrn : r ∣ n) :
    rThresholdWallSite r y n -
        rThresholdWallSite r y (p * n) = 0 := by
  have hrpn : r ∣ p * n := dvd_mul_of_dvd_right hrn p
  simp [rThresholdWallSite, hrn, hrpn]

/-- The sig-summed #755 clipped column is the generic p-incidence of the
r-threshold wall on the whole p-free carrier. -/
private theorem sum_signature_branchClippedTotal_eq_ownerLens
    {R p r y : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r y) =
      ∑ n ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        realMoebiusStep n *
          (rThresholdWallSite r y n -
            rThresholdWallSite r y (p * n)) := by
  rw [sum_signature_branchClippedTotal_eq_rFreePFree]
  unfold lowOwnerFirstOwnerPFreeCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hnCar
  by_cases hrfree : ¬ r ∣ n
  · rw [rThresholdWallSite_ownerDifference_eq_clipped hp hr hpr hrfree]
    simp [hrfree]
  · have hrdvd : r ∣ n := not_not.mp hrfree
    rw [rThresholdWallSite_ownerDifference_eq_zero_of_dvd hrdvd]
    simp [hrfree]

/-- Removing the nonzero-Möbius filter and extending only to the threshold does
not change the r-wall sum. -/
private theorem sum_nonzeroCarrier_rThresholdWall_eq_prefix
    {R r y : ℕ} (hy : y ≤ squareRootEndpoint R) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      realMoebiusStep n * rThresholdWallSite r y n) =
      ∑ n ∈ Finset.Icc 1 y,
        if ¬ r ∣ n then
          realMoebiusStep n *
            lowOwnerThresholdCrossingIndicator r n y
        else 0 := by
  let X := squareRootEndpoint R
  let g : ℕ → ℝ := fun n =>
    if ¬ r ∣ n then
      realMoebiusStep n * lowOwnerThresholdCrossingIndicator r n y
    else 0
  have hremove :
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
        realMoebiusStep n * rThresholdWallSite r y n) =
        ∑ n ∈ Finset.Icc 1 X, g n := by
    unfold lowOwnerNonzeroMobiusCarrier
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hmu : realMoebiusStep n ≠ 0
    · simp [hmu, g, rThresholdWallSite]
    · have hz : realMoebiusStep n = 0 := not_ne_iff.mp hmu
      simp [hz, g]
  have hsub : Finset.Icc 1 y ⊆ Finset.Icc 1 X := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hny⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hny.trans hy⟩
  have hzero :
      ∀ n ∈ Finset.Icc 1 X, n ∉ Finset.Icc 1 y → g n = 0 := by
    intro n hnX hny
    have hyn : y < n := by
      have hn1 := (Finset.mem_Icc.mp hnX).1
      by_contra hnot
      apply hny
      exact Finset.mem_Icc.mpr ⟨hn1, Nat.le_of_not_gt hnot⟩
    unfold g lowOwnerThresholdCrossingIndicator
    by_cases hdiv : r ∣ n
    · simp [hdiv]
    · have hnot : ¬ (n ≤ y ∧ y < r * n) := by omega
      simp [hdiv, hnot]
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      realMoebiusStep n * rThresholdWallSite r y n) =
        ∑ n ∈ Finset.Icc 1 X, g n := hremove
    _ = ∑ n ∈ Finset.Icc 1 y, g n :=
      (Finset.sum_subset hsub hzero).symm
    _ = _ := by rfl

/-- **Fully reassembled #755 daughter = literal lower-scale Mertens amplitude.**

All lower-signature and revealed-signature labels have disappeared before the
equality is stated. -/
theorem sum_signature_branchClippedDifferenceTotalAmplitude_eq_mertens
    {R p r y : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hy : y ≤ squareRootEndpoint R) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r y) =
      (mertensSummatoryInt y : ℝ) := by
  rw [sum_signature_branchClippedTotal_eq_ownerLens hp hr hpr]
  have hzero :
      ∀ n, squareRootEndpoint R < n →
        rThresholdWallSite r y n = 0 := by
    intro n hXn
    exact rThresholdWallSite_eq_zero_of_cutoff_lt (lt_of_le_of_lt hy hXn)
  rw [sum_pFree_realMoebius_ownerDifference_eq_full hp
    (rThresholdWallSite r y) hzero]
  rw [sum_nonzeroCarrier_rThresholdWall_eq_prefix hy]
  exact sum_pFree_thresholdCrossing_eq_mertens hr

/-- q² specialization: every fully reassembled daughter column in #755 is the
actual recursive Mertens daughter at rawQ2ChildCutoff. -/
theorem sum_signature_branchQ2ClippedDifferenceTotalAmplitude_eq_mertensDaughter
    {R p r q : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r (rawQ2ChildCutoff R q)) =
      (mertensSummatoryInt (rawQ2ChildCutoff R q) : ℝ) := by
  apply sum_signature_branchClippedDifferenceTotalAmplitude_eq_mertens
    hp hr hpr
  unfold rawQ2ChildCutoff
  exact Nat.div_le_self _ _

end RHLean.Proof
