import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Analysis.CanonicalHighSectorBridge
import RHLean.Proof.CanonicalGapPrefixGram

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryEnergyBridge

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapPrefixGram

/-!
# Canonical ancestry energy interface

This module is the exact interface between the finite canonical ancestry flow and
its protected square-prefix energy target. It contains only finite algebraic
identities. No analytic estimate is asserted.
-/

/-! ## Exact protected-sequence realization -/

/-- Admissible source products are squarefree. -/
theorem sourceProduct_squarefree_of_admissible {B : ℕ} {s : SourceIndex B}
    (hs : SourceAdmissible s) : Squarefree (sourceProduct s) := by
  rcases hs with ⟨hq, _hcpos, hsq, hcop, _hdom⟩
  exact (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hsq⟩

/-- Admissible source products are strictly larger than one. -/
theorem one_lt_sourceProduct_of_admissible {B : ℕ} {s : SourceIndex B}
    (hs : SourceAdmissible s) : 1 < sourceProduct s := by
  rcases hs with ⟨hq, hcpos, _hsq, _hcop, _hdom⟩
  unfold sourceProduct
  nlinarith [hq.two_le]

/-- The native square-root clock cutoff is exactly the complete-square endpoint. -/
theorem sourceClock_le_iff_sourceProduct_le_endpoint
    {B x : ℕ} (s : SourceIndex B) :
    sourceClock B s ≤ x ↔
      sourceProduct s ≤ RHLean.Analysis.squarePrefixEndpoint x := by
  unfold sourceClock
  constructor
  · intro hclock
    have hsqrt : Nat.sqrt (sourceProduct s) < x + 1 := by omega
    have hlt : sourceProduct s < (x + 1) ^ 2 :=
      (Nat.sqrt_lt').1 hsqrt
    rw [← RHLean.Analysis.squarePrefixEndpoint_add_one x] at hlt
    omega
  · intro hprod
    have hlt :
        sourceProduct s < RHLean.Analysis.squarePrefixEndpoint x + 1 :=
      Nat.lt_succ_of_le hprod
    rw [RHLean.Analysis.squarePrefixEndpoint_add_one x] at hlt
    have hsqrt : Nat.sqrt (sourceProduct s) < x + 1 :=
      (Nat.sqrt_lt').2 hlt
    omega

/-- Active admissible sources under a square-prefix clock. -/
noncomputable def activeSourceSet (B x : ℕ) : Finset (SourceIndex B) := by
  classical
  exact Finset.univ.filter fun s =>
    SourceAdmissible s ∧ sourceClock B s ≤ x

/-- Squarefree integers larger than one under the same clock. -/
noncomputable def activeSquarefreeIntegerSet (x : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
      fun m => 2 ≤ m ∧ Squarefree m

/-- The source prefix is the sum over active admissible source indices. -/
theorem sourcePrefix_eq_activeSource_sum (B x : ℕ) :
    sourcePrefix B x = ∑ s ∈ activeSourceSet B x, sourceWeight s := by
  classical
  rw [sourcePrefix_eq_sum]
  unfold activeSourceSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hadm : SourceAdmissible s <;>
    simp [sourceClock, sourceWeight, hadm]

/-- Exact finite reindexing from native source indices to squarefree integers. -/
theorem sourcePrefix_eq_squarefreeInteger_sum
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourcePrefix B x =
      ∑ m ∈ activeSquarefreeIntegerSet x, (μ m : ℤ) := by
  classical
  rw [sourcePrefix_eq_activeSource_sum]
  refine Finset.sum_bij (fun s _hs => sourceProduct s) ?_ ?_ ?_ ?_
  · intro s hs
    have hsdata : SourceAdmissible s ∧ sourceClock B s ≤ x := by
      simpa [activeSourceSet] using hs
    have hprodle :=
      (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).1 hsdata.2
    have hprodgt := one_lt_sourceProduct_of_admissible hsdata.1
    simp only [activeSquarefreeIntegerSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hprodle, hprodgt,
      sourceProduct_squarefree_of_admissible hsdata.1⟩
  · intro s₁ hs₁ s₂ hs₂ heq
    have hs₁data : SourceAdmissible s₁ ∧ sourceClock B s₁ ≤ x := by
      simpa [activeSourceSet] using hs₁
    have hs₂data : SourceAdmissible s₂ ∧ sourceClock B s₂ ≤ x := by
      simpa [activeSourceSet] using hs₂
    exact sourceProduct_injective_on_admissible hs₁data.1 hs₂data.1 heq
  · intro m hm
    have hmdata :
        m < RHLean.Analysis.squarePrefixEndpoint x + 1 ∧
          2 ≤ m ∧ Squarefree m := by
      simpa [activeSquarefreeIntegerSet] using hm
    have hmgt : 1 < m := hmdata.2.1
    have hmend : m ≤ RHLean.Analysis.squarePrefixEndpoint x :=
      Nat.lt_succ_iff.mp hmdata.1
    have hmB : m ≤ B := hmend.trans hB
    let s := canonicalSourceIndex B m hmdata.2.2 hmgt hmB
    refine ⟨s, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ s, ?_⟩
      refine ⟨canonicalSourceIndex_admissible hmdata.2.2 hmgt hmB, ?_⟩
      apply (sourceClock_le_iff_sourceProduct_le_endpoint (x := x) s).2
      rw [canonicalSourceIndex_product hmdata.2.2 hmgt hmB]
      exact hmend
    · exact canonicalSourceIndex_product hmdata.2.2 hmgt hmB
  · intro s hs
    have hsdata : SourceAdmissible s ∧ sourceClock B s ≤ x := by
      simpa [activeSourceSet] using hs
    exact sourceWeight_of_admissible s hsdata.1

/-- Filtering to squarefree terms does not change the Möbius tail beginning at
`m=2`. -/
theorem activeSquarefreeInteger_sum_eq_Ico_sum (x : ℕ) :
    (∑ m ∈ activeSquarefreeIntegerSet x, (μ m : ℤ)) =
      ∑ m ∈ Finset.Ico 2 (RHLean.Analysis.squarePrefixEndpoint x + 1),
        (μ m : ℤ) := by
  classical
  unfold activeSquarefreeIntegerSet
  rw [Finset.sum_filter]
  have hterm : ∀ m : ℕ,
      (if 2 ≤ m ∧ Squarefree m then (μ m : ℤ) else 0) =
        if 2 ≤ m then (μ m : ℤ) else 0 := by
    intro m
    by_cases hm2 : 2 ≤ m
    · by_cases hsq : Squarefree m
      · simp [hm2, hsq]
      · simp [hm2, hsq,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    · simp [hm2]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp [and_comm]

/-- Exact integer-valued realization, including the exceptional clock `x=0`. -/
theorem sourcePrefix_add_indicator_eq_mertens_sum
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourcePrefix B x + indicator (1 ≤ x) =
      ∑ m ∈ Finset.range (RHLean.Analysis.squarePrefixEndpoint x + 1),
        (μ m : ℤ) := by
  rw [sourcePrefix_eq_squarefreeInteger_sum hB,
    activeSquarefreeInteger_sum_eq_Ico_sum]
  by_cases hx : x = 0
  · subst x
    simp [RHLean.Analysis.squarePrefixEndpoint, indicator]
  · have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx
    have htwo : 2 ≤ x + 1 := by omega
    have hend : 2 ≤ RHLean.Analysis.squarePrefixEndpoint x + 1 := by
      rw [RHLean.Analysis.squarePrefixEndpoint_add_one]
      exact le_trans (by norm_num : 2 ≤ 2 ^ 2)
        (Nat.pow_le_pow_left htwo 2)
    rw [← Finset.sum_range_add_sum_Ico
      (f := fun m : ℕ => (μ m : ℤ)) hend]
    have hsmall :
        (∑ m ∈ Finset.range 2, (μ m : ℤ)) = 1 := by
      simp [Finset.sum_range_succ]
    rw [hsmall]
    simp [indicator, hx1, add_comm]

/-- Exact complex realization with the endpoint correction expressed explicitly. -/
theorem sourcePrefix_add_indicator_eq_squarePrefixMertens
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    ((sourcePrefix B x + indicator (1 ≤ x) : ℤ) : ℂ) =
      RHLean.Analysis.squarePrefixMertens x := by
  rw [sourcePrefix_add_indicator_eq_mertens_sum hB]
  unfold RHLean.Analysis.squarePrefixMertens RHLean.Analysis.mertensSummatory
  push_cast
  rfl

/-- For every nonzero square-prefix clock, the sole omitted source is `m=1`. -/
theorem sourcePrefix_add_one_eq_squarePrefixMertens
    {B x : ℕ}
    (hx : 1 ≤ x)
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    ((sourcePrefix B x : ℤ) : ℂ) + 1 =
      RHLean.Analysis.squarePrefixMertens x := by
  have h := sourcePrefix_add_indicator_eq_squarePrefixMertens hB
  simpa [indicator, hx, Int.cast_add] using h

end CanonicalGapAncestryEnergyBridge

end RHLean.Proof
