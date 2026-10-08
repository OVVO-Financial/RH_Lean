import Mathlib

/-!
# #915 rigorous two-owner clipped-path audit

This is deliberately a **path-level exact identity**, not a new RH hypothesis
or the missing first-bad signed payment. It separates two phenomena:

* Complete two-prime terminal insertion and terminal filtering commute.
  Pure positive multiplication cannot exit and re-enter a common upper clock.
* A squarefree prime **toggle** may insert one prime and strip another; the
  intermediate path can then exit and re-enter. For commuting toggles, the
  order difference equals the signed flux on the EXCLUSIVE intermediate
  physical-status sets. The original terminal weight is never changed.

The historic/current occurrence-level Fubini required to turn this geometric
flux into #915 Co/Div payment is *not* supplied by these universal identities.
-/

noncomputable section

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Keep an exact terminal signed weight only when both the intermediate and
terminal states, as well as the initial state, are on the physical clock. -/
def vfMid915ClippedTwoStep {α : Type*}
    (physical : α → Prop) (weight : α → ℝ)
    (p q : α → α) (x : α) : ℝ :=
  if physical x ∧ physical (p x) ∧ physical (q (p x)) then
    weight (q (p x))
  else 0

/-- First order survives while the reversed order clips at its intermediate
state. This is an actual *oriented, occurrence-tagged* path contribution. -/
def vfMid915FirstOnlyExitReturn {α : Type*}
    (physical : α → Prop) (weight : α → ℝ)
    (p q : α → α) (x : α) : ℝ :=
  if physical x ∧ physical (q (p x)) ∧
       physical (p x) ∧ ¬ physical (q x) then
    weight (q (p x))
  else 0

/-- Reverse order survives while first order clips. -/
def vfMid915ReverseOnlyExitReturn {α : Type*}
    (physical : α → Prop) (weight : α → ℝ)
    (p q : α → α) (x : α) : ℝ :=
  if physical x ∧ physical (q (p x)) ∧
       physical (q x) ∧ ¬ physical (p x) then
    weight (q (p x))
  else 0

/-- **EXACT signed clipped-path commutator.** The full two-step terminal
state is shared. Its order defect is supported only where exactly ONE
intermediate path remains on the clock. No norm, weight replacement, or
fictitious historical parent is introduced. -/
theorem vfMid915ClippedTwoStep_sub_reverse_eq_exitReturn
    {α : Type*} (physical : α → Prop) (weight : α → ℝ)
    (p q : α → α)
    (hcomm : ∀ x, p (q x) = q (p x)) (x : α) :
    vfMid915ClippedTwoStep physical weight p q x -
      vfMid915ClippedTwoStep physical weight q p x =
    vfMid915FirstOnlyExitReturn physical weight p q x -
      vfMid915ReverseOnlyExitReturn physical weight p q x := by
  by_cases hx : physical x <;>
  by_cases hp : physical (p x) <;>
  by_cases hq : physical (q x) <;>
  by_cases hlast : physical (q (p x)) <;>
    simp [vfMid915ClippedTwoStep, vfMid915FirstOnlyExitReturn,
      vfMid915ReverseOnlyExitReturn, hx, hp, hq, hlast, hcomm x]

/-- Signed Fubini over any FINITE set of ORIGINAL occurrences. This theorem
does not assume those occurrences are the actual VF historical/current carrier. -/
theorem vfMid915ClippedTwoStep_sum_order_flux
    {α : Type*} [DecidableEq α]
    (occ : Finset α) (physical : α → Prop)
    (weight : α → ℝ) (p q : α → α)
    (hcomm : ∀ x, p (q x) = q (p x)) :
    (∑ x ∈ occ, vfMid915ClippedTwoStep physical weight p q x) -
      (∑ x ∈ occ, vfMid915ClippedTwoStep physical weight q p x) =
    (∑ x ∈ occ, vfMid915FirstOnlyExitReturn physical weight p q x) -
      (∑ x ∈ occ, vfMid915ReverseOnlyExitReturn physical weight p q x) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl
    (fun x _ => vfMid915ClippedTwoStep_sub_reverse_eq_exitReturn
      physical weight p q hcomm x)

/-- Pure prime INSERTION with an absorbing clipped state. -/
def vfMid915ClippedInsert (X p n : ℕ) : ℕ :=
  if p * n ≤ X then p * n else 0

/-- A product below the clock forces every positive-prime insertion prefix
below the clock. Consequently there is NO insertion-only order leakage. -/
theorem vfMid915ClippedInsert_twoStep_eq_final
    (X p q n : ℕ) (hq : 1 ≤ q) :
    vfMid915ClippedInsert X q (vfMid915ClippedInsert X p n) =
      if (p * q) * n ≤ X then (p * q) * n else 0 := by
  by_cases hp : p * n ≤ X
  · simp only [vfMid915ClippedInsert, if_pos hp]
    rw [show q * (p * n) = (p * q) * n by ring]
  · have hnot : ¬ (p * q) * n ≤ X := by
      intro h
      have hmul : p * n ≤ q * (p * n) := by
        simpa using
          (Nat.mul_le_mul_right (p * n) hq)
      have hnormal : q * (p * n) = (p * q) * n := by
        ring
      omega
    simp [vfMid915ClippedInsert, hp, hnot]

theorem vfMid915ClippedInsert_comm
    (X p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    vfMid915ClippedInsert X q (vfMid915ClippedInsert X p n) =
      vfMid915ClippedInsert X p (vfMid915ClippedInsert X q n) := by
  rw [vfMid915ClippedInsert_twoStep_eq_final X p q n hq,
      vfMid915ClippedInsert_twoStep_eq_final X q p n hp]
  simp only [Nat.mul_comm p q]

/-- Replacement of one odd low prime by a DIFFERENT odd low prime moves a
site out of its ENTIRE open adjacent-square interval. This does not prevent
the replacement from linking an earlier historical site to the current one. -/
theorem vfMid915TwoOddOwnerReplacement_exits_current_square
    {R n p q k : ℕ}
    (hnlo : R ^ 2 < n) (hnhi : n < (R + 1) ^ 2)
    (hqR : q ≤ R) (hn : n = q * k)
    (hgap : p + 2 ≤ q ∨ q + 2 ≤ p) :
    p * k ≤ R ^ 2 ∨ (R + 1) ^ 2 ≤ p * k := by
  have hk : R < k := by
    by_contra h
    have hkR : k ≤ R := Nat.le_of_not_gt h
    have hprod : q * k ≤ R * R := Nat.mul_le_mul hqR hkR
    nlinarith
  have hsquare : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  rcases hgap with hleft | hright
  · have hprod := Nat.mul_le_mul_right k hleft
    have hsubs : p * k + 2 * k ≤ n := by
      nlinarith
    left
    omega
  · have hprod := Nat.mul_le_mul_right k hright
    have hsubs : n + 2 * k ≤ p * k := by
      nlinarith
    right
    omega

/-- Generic finite Boolean curvature identity for one POSITIVE log-response
atom. At an actual divisor d, take u=log(d/m), lp=log(p), lq=log(q),
and bp,bq equal to the two divisibility indicators of d/m. The full response
summation and the clipped VF-weight transport remain separate tasks. -/
theorem vfMid915BooleanMixedResponse_eq_three_nonnegative_atoms
    (u lp lq : ℝ) (bp bq : Bool) :
    u -
      (if bp then u - lp else 0) -
      (if bq then u - lq else 0) +
      (if bp && bq then u - lp - lq else 0) =
    (if !bp && !bq then u else 0) +
      (if bp && !bq then lp else 0) +
      (if !bp && bq then lq else 0) := by
  cases bp <;> cases bq <;> simp

theorem vfMid915BooleanMixedResponse_nonneg
    (u lp lq : ℝ) (bp bq : Bool)
    (hu : 0 ≤ u) (hp : 0 ≤ lp) (hq : 0 ≤ lq) :
    0 ≤ u -
      (if bp then u - lp else 0) -
      (if bq then u - lq else 0) +
      (if bp && bq then u - lp - lq else 0) := by
  rw [vfMid915BooleanMixedResponse_eq_three_nonnegative_atoms]
  cases bp <;> cases bq <;> simp_all

/-- A genuine geometric exit-and-return example on the clock X=80:
39 --adjoin 5--> 195 (clipped) --strip 3--> 65,
but 39 --strip 3--> 13 --adjoin 5--> 65. The FINAL 65 is in the
active square block (64,81); the proof does NOT claim 39 or 13
is an available negative Co/Div parent on #915's compressed anchor. -/
def vfMid915PrimeToggle (p n : ℕ) : ℕ :=
  if p ∣ n then n / p else p * n

example :
    vfMid915ClippedTwoStep
      (fun n : ℕ => n ≤ 80)
      (fun n : ℕ => if 64 < n ∧ n < 81 then (1 : ℝ) else 0)
      (vfMid915PrimeToggle 5) (vfMid915PrimeToggle 3) 39 = 0 := by
  norm_num [vfMid915ClippedTwoStep, vfMid915PrimeToggle]

example :
    vfMid915ClippedTwoStep
      (fun n : ℕ => n ≤ 80)
      (fun n : ℕ => if 64 < n ∧ n < 81 then (1 : ℝ) else 0)
      (vfMid915PrimeToggle 3) (vfMid915PrimeToggle 5) 39 = 1 := by
  norm_num [vfMid915ClippedTwoStep, vfMid915PrimeToggle]

end RHLean.Analysis
