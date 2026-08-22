import Mathlib

open scoped BigOperators

namespace RHLean.Arithmetic

/-- Alternating parity sign attached to a Boolean-cube vertex. -/
def booleanCubeSign {α : Type*} (t : Finset α) : ℤ :=
  (-1 : ℤ) ^ t.card

/-- Alternating signed mass of the complete Boolean cube on `s`. -/
def booleanCubeAlternatingSum {α : Type*} (s : Finset α) : ℤ :=
  ∑ t ∈ s.powerset, booleanCubeSign t

/-- The zero-dimensional Boolean cube has signed mass one. -/
theorem booleanCubeAlternatingSum_empty {α : Type*} :
    booleanCubeAlternatingSum (∅ : Finset α) = 1 := by
  simp [booleanCubeAlternatingSum, booleanCubeSign]

/-- Adding a new cube coordinate negates the contribution of every old vertex. -/
theorem booleanCube_inserted_half_eq_neg
    {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∉ s) :
    (∑ t ∈ s.powerset, booleanCubeSign (insert a t)) =
      -∑ t ∈ s.powerset, booleanCubeSign t := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hat : a ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht ha
  simp [booleanCubeSign, Finset.card_insert_of_notMem, hat, pow_succ]

/-- Every positive-dimensional complete Boolean cube has exact alternating cancellation. -/
theorem booleanCubeAlternatingSum_eq_zero
    {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    booleanCubeAlternatingSum s = 0 := by
  rcases hs with ⟨a, ha⟩
  have hdecomp : s = insert a (s.erase a) := by
    exact (Finset.insert_erase ha).symm
  rw [hdecomp]
  unfold booleanCubeAlternatingSum
  rw [Finset.sum_powerset_insert (Finset.notMem_erase a s)]
  rw [booleanCube_inserted_half_eq_neg (Finset.notMem_erase a s)]
  simp

/-- Complete-cube cancellation written directly as a parity sum. -/
theorem sum_neg_one_pow_card_powerset_eq_zero
    {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    (∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card) = 0 := by
  exact booleanCubeAlternatingSum_eq_zero hs

/-! ## Rough-prime completed convolution -/

/-- Every prime factor of `m` lies at or above the pivot `p`. -/
def PrimeFactorsAtLeast (p m : ℕ) : Prop :=
  ∀ q ∈ m.primeFactors, p ≤ q

/-- The support left after complete cancellation: every prime factor is the
pivot itself. For positive `m` and prime `p`, this is exactly the `p`-power
channel. -/
def PrimeFactorsOnly (p m : ℕ) : Prop :=
  ∀ q ∈ m.primeFactors, q = p

/-- Prime coordinates strictly above the pivot. -/
def primeFactorsAbove (p m : ℕ) : Finset ℕ :=
  m.primeFactors.filter fun q => p < q

/-- Finite Boolean-face incarnation of
`1_{rough >= p} * (mu * 1_{rough > p})`.

Once factors below `p` are excluded, choosing a squarefree Möbius divisor
supported strictly above `p` is exactly choosing a subface of
`primeFactorsAbove p m`; its Möbius sign is the Boolean parity sign. -/
def roughGECompletedMobiusConvolution (p m : ℕ) : ℤ :=
  if PrimeFactorsAtLeast p m then
    booleanCubeAlternatingSum (primeFactorsAbove p m)
  else
    0

/-- **Completed rough-prime convolution leaves only the pivot-power channel.**
This is the exact finite form of

`1_{rough >= p} * (mu · 1_{rough > p}) = 1_{p-powers}`.

Any prime coordinate strictly above `p` creates a positive-dimensional Boolean
cube and cancels by inclusion-exclusion. If a factor lies below `p`, the
rough-`>= p` side vanishes. Thus mass `1` survives exactly when every prime
factor is `p`. -/
theorem roughGE_convolution_roughGT_moebius_eq_primePowers
    (p m : ℕ) :
    roughGECompletedMobiusConvolution p m =
      if PrimeFactorsOnly p m then 1 else 0 := by
  classical
  by_cases hOnly : PrimeFactorsOnly p m
  · have hAtLeast : PrimeFactorsAtLeast p m := by
      intro q hq
      rw [hOnly q hq]
    have hEmpty : primeFactorsAbove p m = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro q hq
      rw [primeFactorsAbove, Finset.mem_filter] at hq
      have hEq := hOnly q hq.1
      omega
    rw [roughGECompletedMobiusConvolution, if_pos hAtLeast,
      if_pos hOnly, hEmpty]
    exact booleanCubeAlternatingSum_empty
  · by_cases hAtLeast : PrimeFactorsAtLeast p m
    · have hNonempty : (primeFactorsAbove p m).Nonempty := by
        by_contra hnot
        apply hOnly
        intro q hq
        have hpq := hAtLeast q hq
        have hnotlt : ¬ p < q := by
          intro hpq'
          apply hnot
          refine ⟨q, ?_⟩
          exact Finset.mem_filter.mpr ⟨hq, hpq'⟩
        omega
      rw [roughGECompletedMobiusConvolution, if_pos hAtLeast, if_neg hOnly]
      exact booleanCubeAlternatingSum_eq_zero hNonempty
    · simp [roughGECompletedMobiusConvolution, hAtLeast, hOnly]

end RHLean.Arithmetic