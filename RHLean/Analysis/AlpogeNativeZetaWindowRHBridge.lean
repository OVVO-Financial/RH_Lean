import RHLean.Analysis.AlpogeNativeWindowLandau
import RHLean.Analysis.AlpogeNativeZetaWindowWitness

/-!
# End-to-end native window-witness reduction to the Riemann Hypothesis

This module composes the native zeta-only character-balance / window-witness
consumer (`AlpogeNativeZetaWindowWitness`) with the native one-sided window
Landau theorem (`AlpogeNativeWindowLandau`).

## Scope and honest status

This is a **conditional reduction**, not an unconditional proof of RH:
- No `AlpogeNativeZetaWindowWitness` is constructed here, and joint
  satisfiability of the ten fields is not proved.
- Because the native `ASK - MAIN = De` identity holds for arbitrary `inertia`,
  `frob`, and `ell`, degenerate host data (e.g. `inertia = ⊤`, `ell = 0`)
  makes the `excluded` field trivial and turns `top` into a direct bound on
  `alpogeNativeGzArithmetic`.
- On a genuine physical CM host, Field 10 (`top`) is the open geometric
  estimate supplied in Alpöge's proof by the automorphic theta-lift engine,
  Field 9 (`excluded`) requires root-scale control of up to three surviving
  nonprincipal characters, and Field 6 (`thin`) requires a prime number theorem
  with remainder for every host character.
-/

noncomputable section

namespace RHLean.Analysis

/-- Supplying native zeta window witnesses on arbitrarily large windows
`[Y, Y^(1 + δ)]` rules out every zero of `riemannZeta` strictly to the right
of the critical line `Re(s) > 1 / 2`. -/
theorem riemannZeta_ne_zero_of_zetaWindowWitnesses {δ C ε₁ : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hε₁ : 0 < ε₁)
    (h : AlpogeNativeZetaWindowWitnessesOnWindows δ C ε₁)
    {s : ℂ} (hs : (1 : ℝ) / 2 < s.re) :
    riemannZeta s ≠ 0 := by
  by_cases hge : (1 : ℝ) ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hge
  · have hs1 : s.re < 1 := lt_of_not_ge hge
    set η : ℝ := (s.re - (1 : ℝ) / 2) / 2 with hηd
    have hη : 0 < η := by dsimp [η]; linarith
    have hθ0 : 0 < (1 : ℝ) / 2 + η := by linarith
    have hθ1 : (1 : ℝ) / 2 + η < 1 := by dsimp [η]; linarith
    have hθs : (1 : ℝ) / 2 + η < s.re := by dsimp [η]; linarith
    obtain ⟨K, hK⟩ := alpogeNativeGz_windows_of_witnesses hC hε₁ h η hη
    exact riemannZeta_ne_zero_of_Gz_window hθ0 hθ1 hδ hK s hθs

/-- Supplying native zeta window witnesses on arbitrarily large windows
`[Y, Y^(1 + δ)]` implies Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_zetaWindowWitnesses {δ C ε₁ : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hε₁ : 0 < ε₁)
    (h : AlpogeNativeZetaWindowWitnessesOnWindows δ C ε₁) :
    RiemannHypothesis :=
  riemannHypothesis_of_Gz_windows hδ (alpogeNativeGz_windows_of_witnesses hC hε₁ h)

end RHLean.Analysis
