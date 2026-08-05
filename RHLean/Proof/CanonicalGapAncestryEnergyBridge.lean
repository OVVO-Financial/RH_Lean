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
  unfold sourceClock RHLean.Analysis.squarePrefixEndpoint
  constructor
  · intro hclock
    have hlt := Nat.lt_succ_sqrt' (sourceProduct s)
    have hsquare :
        (Nat.sqrt (sourceProduct s) + 1) ^ 2 ≤ (x + 1) ^ 2 :=
      Nat.pow_le_pow_left (Nat.succ_le_succ hclock) 2
    omega
  · intro hprod
    have hlt : sourceProduct s < (x + 1) ^ 2 := by omega
    exact Nat.lt_succ_iff.mp ((Nat.sqrt_lt').2 hlt)

/-- Active admissible sources under a square-prefix clock. -/
def activeSourceSet (B x : ℕ) : Finset (SourceIndex B) :=
  Finset.univ.filter fun s => SourceAdmissible s ∧ sourceClock B s ≤ x

/-- Squarefree integers larger than one under the same clock. -/
def activeSquarefreeIntegerSet (x : ℕ) : Finset ℕ :=
  (Finset.range (RHLean.Analysis.squarePrefixEndpoint x + 1)).filter
    fun m => 2 ≤ m ∧ Squarefree m

/-- The source prefix is the sum over active admissible source indices. -/
theorem sourcePrefix_eq_activeSource_sum (B x : ℕ) :
    sourcePrefix B x = ∑ s ∈ activeSourceSet B x, sourceWeight s := by
  classical
  rw [sourcePrefix_eq_sum]
  unfold activeSourceSet
  rw [Finset.sum_filter]
  simp_rw [sourceWeight]
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hadm : SourceAdmissible s <;>
    by_cases hclock : Nat.sqrt (sourceProduct s) ≤ x <;>
      simp [sourceClock, hadm, hclock]

/-- Exact finite reindexing from native source indices to squarefree integers. -/
theorem sourcePrefix_eq_squarefreeInteger_sum
    {B x : ℕ}
    (hB : RHLean.Analysis.squarePrefixEndpoint x ≤ B) :
    sourcePrefix B x =
      ∑ m ∈ activeSquarefreeIntegerSet x, (μ m : ℤ) := by
  classical
  rw [sourcePrefix_eq_activeSource_sum]
  unfold activeSourceSet activeSquarefreeIntegerSet
  refine Finset.sum_bij (fun s _hs => sourceProduct s) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    refine ⟨?_, ?_, sourceProduct_squarefree_of_admissible hs.1⟩
    · rw [Finset.mem_range]
      have hclock :=
        (sourceClock_le_iff_sourceProduct_le_endpoint s).1 hs.2
      omega
    · omega
  · intro s₁ hs₁ s₂ hs₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs₁ hs₂
    exact sourceProduct_injective_on_admissible hs₁.1 hs₂.1 heq
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    rcases hm with ⟨hmend, hm2, hsq⟩
    have hmgt : 1 < m := by omega
    have hmB : m ≤ B := by
      apply le_trans _ hB
      omega
    let s := canonicalSourceIndex B m hsq hmgt hmB
    refine ⟨s, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨canonicalSourceIndex_admissible hsq hmgt hmB, ?_⟩
      apply (sourceClock_le_iff_sourceProduct_le_endpoint s).2
      rw [canonicalSourceIndex_product hsq hmgt hmB]
      omega
    · exact canonicalSourceIndex_product hsq hmgt hmB
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact sourceWeight_of_admissible s hs.1

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
  simp

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
    have hend : 2 ≤ RHLean.Analysis.squarePrefixEndpoint x + 1 := by
      unfold RHLean.Analysis.squarePrefixEndpoint
      nlinarith
    rw [← Finset.sum_range_add_sum_Ico
      (f := fun m : ℕ => (μ m : ℤ)) hend]
    simp [indicator, hx1, ArithmeticFunction.moebius_apply_one]

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
