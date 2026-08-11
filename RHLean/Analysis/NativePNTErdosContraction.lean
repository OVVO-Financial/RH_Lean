import Mathlib

/-!
# The generic Erdos cubic contraction

The elementary Selberg--Erdos proof of PNT eventually produces a sequence of
nonnegative linear error envelopes with the deterministic update

`alpha_(n+1) = alpha_n - C * alpha_n^3`, `C > 0`.

This module proves, independently of all number theory, that such an envelope
must tend to zero.  The prime-specific part of the proof therefore only has to
construct the successive envelopes from the finite Selberg recurrence.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace RHLean.Analysis

/-- A nonnegative cubic-improvement envelope has no positive limiting fixed
point: its only possible limit is zero. -/
theorem tendsto_zero_of_cubic_recurrence
    (a : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hrec : ∀ n, a (n + 1) = a n - C * (a n) ^ 3) :
    Tendsto a atTop (𝓝 0) := by
  have hstep : ∀ n, a (n + 1) ≤ a n := by
    intro n
    rw [hrec]
    have hcube : 0 ≤ (a n) ^ 3 := pow_nonneg (hnonneg n) 3
    nlinarith
  have hanti : Antitone a := antitone_nat_of_succ_le hstep
  have hbdd : BddBelow (Set.range a) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hnonneg n
  let L : ℝ := ⨅ n, a n
  have hconv : Tendsto a atTop (𝓝 L) := by
    dsimp [L]
    exact tendsto_atTop_ciInf hanti hbdd
  have hshiftIndex : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine ⟨b, ?_⟩
    intro n hn
    omega
  have hshift : Tendsto (fun n : ℕ => a (n + 1)) atTop (𝓝 L) :=
    hconv.comp hshiftIndex
  have hpoly :
      Tendsto (fun n : ℕ => a n - C * (a n) ^ 3) atTop
        (𝓝 (L - C * L ^ 3)) := by
    exact hconv.sub (tendsto_const_nhds.mul (hconv.pow 3))
  have hshift' :
      Tendsto (fun n : ℕ => a (n + 1)) atTop
        (𝓝 (L - C * L ^ 3)) := by
    simpa only [hrec] using hpoly
  have hfixed : L = L - C * L ^ 3 :=
    tendsto_nhds_unique hshift hshift'
  have hzero : C * L ^ 3 = 0 := by linarith
  have hcube : L ^ 3 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hC)
  have hL : L = 0 := by
    exact (pow_eq_zero hcube)
  simpa [hL] using hconv

end RHLean.Analysis
