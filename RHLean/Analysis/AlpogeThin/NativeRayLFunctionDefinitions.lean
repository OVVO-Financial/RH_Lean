import RHLean.Analysis.AlpogeThin.NativeRayLFam

/-!
# Character coefficients and Mellin continuation of the native ray family

The analytic definitions and estimates are reconstructed over the existing
native LFam arithmetic record. On LFam.ofRayData every coefficient remains
its original actual ray-ideal coefficient; no analytic bound is an input.

Source guide: Levent Alpöge's archive, inspected pin
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean`.
No source compiled artifact or terminal RH theorem is imported.
The archive states no license; attribution assigns none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Finset MeasureTheory

namespace RHLean.Analysis.AlpogeThin.NativeRay.LFam

variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

def aChi (n : ℕ) : ℂ := ∑ g, χ g * (𝓕.a g n : ℂ)

def lamChi (n : ℕ) : ℂ := ∑ g, χ g * (𝓕.lam g n : ℂ)

open Classical in

def res : ℂ := if χ = 1 then ((𝓕.κ * Fintype.card 𝓕.G : ℝ) : ℂ) else 0

def mel (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), ((∑ n ∈ Icc 1 ⌊x⌋₊, 𝓕.aChi χ n) - 𝓕.res χ * x) * (x : ℂ) ^ (-s - 1)

open Classical in

def F (s : ℂ) : ℂ := if χ = 1 then 𝓕.res χ * s + (s - 1) * s * 𝓕.mel χ s else s * 𝓕.mel χ s

def psi (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, 𝓕.lamChi χ n

def ell (t : ℝ) : ℝ := Real.log (𝓕.B * (|t| + 2))

def ExcZ (c : ℝ) (Z : Finset ℝ) : Prop :=
  Z.card ≤ 1 ∧ (∀ β ∈ Z, 1 - c / 𝓕.ell 0 ≤ β ∧ β < 1 ∧ 𝓕.F χ β = 0 ∧ deriv (𝓕.F χ) β ≠ 0) ∧
    ∀ s : ℂ, 1 - c / 𝓕.ell s.im ≤ s.re → 𝓕.F χ s = 0 → ∃ β ∈ Z, s = (β : ℂ)

theorem two_lt_ell (t : ℝ) : 2 < 𝓕.ell t := by
  have hB := 𝓕.B_ge
  have ht := abs_nonneg t
  have h8 : (8 : ℝ) ≤ 𝓕.B * (|t| + 2) := by nlinarith
  have h2 := Real.log_two_gt_d9
  have e : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_le_log (by norm_num) h8
  unfold ell
  linarith

theorem half_lt_re_of_region {c : ℝ} (hc : c ≤ 1) {s : ℂ} (hs : 1 - c / 𝓕.ell s.im ≤ s.re) : 1 / 2 < s.re := by
  have h := 𝓕.two_lt_ell s.im
  have : c / 𝓕.ell s.im < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  linarith

end RHLean.Analysis.AlpogeThin.NativeRay.LFam

end
