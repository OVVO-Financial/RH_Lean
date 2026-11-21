import Mathlib
import RHLean.Analysis.AlpogeNativeSharpASKBalance
import RHLean.Proof.FinitePartialMoments

/-!
# Complete physical ASK - MAIN top-excess: exact averaged signed identity

The pointwise identity was proved in AlpogeNativeSharpASKBalance:
  physical ASK - MAIN = complete De.

This file takes exactly the same physical host, actual prime powers,
inertia cosets, all widths and all lifted nodes, and forms the ORIGINAL
averaged topExcess. It proves this is the averaged real part of the
whole De WITHOUT bounding its characters independently.

The upper partial moment of the COMPLETE De is a valid unconditional
one-sided budget. The small-global-excess estimate required for RH is
NOT inferred or assumed.
-/

noncomputable section
namespace RHLean.Analysis

/-- Full original ASK-MAIN averaged over the actual u,t,j source.
No termwise absolute value is taken. -/
def alpogePhysicalCompleteTopExcess
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) *
    ∑ u : H, ∑ t ∈ TT, ∑ j : Fin m,
      (alpogeNativeFullKernelASK inertia frob N (a t) t (w u j) -
        alpogeNativeMAIN ell (a t) (w u j)).re

/-- Complete signed De averaged on EXACTLY the same nodes, with the
true per-node width and the full prime-power/Frobenius data. -/
def alpogePhysicalCompleteDeAverage
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) *
    ∑ u : H, ∑ t ∈ TT, ∑ j : Fin m,
      (alpogeNativeDe inertia frob ell (a t) t (w u j)).re

/-- Unconditionally complete physical ASK-MAIN identity for the WHOLE
top-excess family, not merely one character or an unramified subband. -/
theorem alpogePhysicalCompleteTopExcess_eq_DeAverage
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hN : ∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ)) :
    alpogePhysicalCompleteTopExcess inertia frob ell N TT a w =
      alpogePhysicalCompleteDeAverage inertia frob ell N TT a w := by
  unfold alpogePhysicalCompleteTopExcess alpogePhysicalCompleteDeAverage
  congr 1
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro j _hj
  exact congrArg Complex.re
    (alpogeNativeFullASK_sub_MAIN_eq_De inertia frob ell N
      (a t) t (w u j) (ha t ht) (hw u j) (hN u j t ht))

/-- NNS upper partial mass of the *one complete signed source*, rather
than a triangle of separate principal and character channels. -/
def alpogePhysicalCompleteDePositiveBudget
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) *
    ∑ u : H, ∑ t ∈ TT, ∑ j : Fin m,
      max (alpogeNativeDe inertia frob ell (a t) t (w u j)).re 0

/-- Exact complete ASK-MAIN source has an unconditional one-sided
UPM1 majorant, paying the positive mass of each FULL De response.
This is NOT a power-saving estimate on the positive budget. -/
theorem alpogePhysicalCompleteTopExcess_le_positiveBudget
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hN : ∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ)) :
    alpogePhysicalCompleteTopExcess inertia frob ell N TT a w ≤
      alpogePhysicalCompleteDePositiveBudget
        inertia frob ell N TT a w := by
  rw [alpogePhysicalCompleteTopExcess_eq_DeAverage
    inertia frob ell N TT a w ha hw hN]
  unfold alpogePhysicalCompleteDeAverage
    alpogePhysicalCompleteDePositiveBudget
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro u _hu
    apply Finset.sum_le_sum
    intro t _ht
    apply Finset.sum_le_sum
    intro j _hj
    exact le_max_left _ _
  · positivity

end RHLean.Analysis
