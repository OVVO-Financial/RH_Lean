import RHLean.Analysis.AlpogeNativeThickFreezing
import RHLean.Analysis.AlpogeNativeCostNormalization

/-!
# Normalized complete-character inequality with the freezing bill paid

The theorem below contains the complete native physical source, its literal
signed thin return and the explicit excluded-character charge. The divisor
comes from subgroup orthogonality, and the movement cost is proved from the
actual prime-power kernel and the native Chebyshev estimate.

This is a finite quantitative source comparison. It does not bound the
remaining signed geometric quantity, and does not identify its variable-height
character signal with the scalar square-clock Gz endpoint.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis

/-- Complete source comparison under the earned normalization. The only
positive width bill is explicit; every thin and excluded-character term is
retained. No source upper bound appears among the hypotheses. -/
theorem alpogeNativeCompleteCharacterSource_normalized_le
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A0 : AddSubgroup H)
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT T2 : Finset H)
    (hTT : TT.Nonempty) (hT2ne : T2.Nonempty) (hm : 0 < m)
    (hT2 : ∀ s ∈ T2, s ∈ A0) (a : H → ℝ) (b h X : ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (Kp : Finset (AddChar (AlpogeNativeE0 × H) ℂ))
    (hKp : Kp ⊆ alpogeNativeProjectionChars A0)
    (hb : 0 < b) (hh : 0 ≤ h) (ha : ∀ t ∈ TT, 0 < a t)
    (hX : ∀ t ∈ TT, a t / b ≤ X)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hthick : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
      b ≤ w u j ρ ∧ w u j ρ ≤ b + h)
    (hN : ∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ))
    (hNb : ∀ t ∈ TT, a t / b ≤ (N : ℝ)) :
    alpogeNativeRetainedSignal (alpogeNativeFrobInertiaGPsi inertia frob ell) Kp TT a b ≤
      (alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w -
        alpogeNativeProjectionThinAverage A0 (alpogeNativeFrobInertiaGPsi inertia frob ell)
          TT T2 a w) / alpogeNativeProjectionDivisor TT T2 m b +
      alpogeNativeExcludedCharacterMass A0 (alpogeNativeFrobInertiaGPsi inertia frob ell)
        Kp TT a b +
      4 * h * (Real.log 4 + 2) * X / (b * alpogeNativeProjectionDensity T2) := by
  have hQ := alpogeNativeProjectionDivisor_pos TT T2 hTT hT2ne m hm b hb
  have hpaid := alpogeNativeRetained_freezing_paid A0 inertia frob ell N
    TT T2 hTT hT2 a b h w Kp hKp hb hh ha hw hthick hN hNb
  have hcost := alpogeNativeFreezing_normalized_cost_le TT T2 hTT hT2ne
    m hm a b h X hb hh (fun t ht => (ha t ht).le) hX
  have hraw :
      alpogeNativeRetainedSignal (alpogeNativeFrobInertiaGPsi inertia frob ell) Kp TT a b -
        alpogeNativeExcludedCharacterMass A0 (alpogeNativeFrobInertiaGPsi inertia frob ell)
          Kp TT a b ≤
      ((alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w -
        alpogeNativeProjectionThinAverage A0 (alpogeNativeFrobInertiaGPsi inertia frob ell)
          TT T2 a w) +
        2 * h * m * ∑ t ∈ TT, nativePsi ⌊a t / b⌋₊) /
          alpogeNativeProjectionDivisor TT T2 m b := by
    apply (le_div_iff₀ hQ).2
    nlinarith [hpaid]
  rw [add_div] at hraw
  linarith

end RHLean.Analysis
