import Mathlib
import RHLean.Analysis.NativePNTMertens
import «research.EULER_SELF_DUAL_ENDPOINT_GATE_20261027»
import «research.EULER_HYBRID_TRIANGULAR_GRAM_20261027»

/-!
# Asymmetric two-cutoff Euler floor identity and its signed Gram transport

All coefficients are the genuine integer Mobius function.  At X = R^2 - 1,
the a-coordinate stops at N = R - 1 and the b-coordinate stops at
B = N - floor(sqrt R).  The omitted b-strip differs from a unit Mobius
column only by a short corner.  The corner is bounded *unconditionally*
by 2R, using no historical envelope or conjectural cancellation.

The surviving rectangle is also expressed in the ALREADY certified
signed historical Gram coordinates D_R + 2 B_R; the mixed cross term is
not bounded or assigned an independent power saving.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

def eulerAsymCutoff (R : ℕ) : ℕ :=
  R - 1 - Nat.sqrt R

/-- The original, genuinely asymmetric, signed Mobius floor rectangle. -/
def eulerAsymBilinear (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (eulerAsymCutoff R),
    (((μ b : ℤ) : ℂ)) *
      ∑ a ∈ Finset.Icc 1 (R - 1),
        (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b

/-- Original omitted b-strip, before the corner or Gram is rewritten. -/
def eulerAsymOmittedStrip (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Ioc (eulerAsymCutoff R) (R - 1),
    (((μ b : ℤ) : ℂ)) *
      ∑ a ∈ Finset.Icc 1 (R - 1),
        (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b

/-- The literal high-a/high-b corner, in historical Mertens coordinates. -/
def eulerAsymCorner (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Ioc (eulerAsymCutoff R) (R - 1),
    (((μ b : ℤ) : ℂ)) *
      (mertensSummatory (squareRootEndpoint R / b) -
        mertensSummatory (R - 1))

private theorem eulerAsym_Ioc_zero_eq_Icc (n : ℕ) :
    Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

private theorem eulerAsym_sqrt_geometry (R : ℕ) (hR : 2 ≤ R) :
    Nat.sqrt R < R ∧
    2 * Nat.sqrt R ≤ R ∧
    Nat.sqrt R * Nat.sqrt R ≤ R := by
  let H := Nat.sqrt R
  have hs : H * H ≤ R := by
    simpa only [H, pow_two] using Nat.sqrt_le' R
  have hlt : H < R := by
    by_contra h
    have hRH : R ≤ H := Nat.le_of_not_gt h
    have hprod : R * R ≤ H * H := Nat.mul_le_mul hRH hRH
    nlinarith
  have htwice : 2 * H ≤ R := by
    by_cases hsmall : H ≤ 1
    · omega
    · have htwo : 2 ≤ H := by omega
      have hprod : 2 * H ≤ H * H := Nat.mul_le_mul_right H htwo
      omega
  exact ⟨hlt, htwice, hs⟩

/-- Genuine quotient support and a sharp O(sqrt R) excess beyond the root.
The strict <2R bound also makes every post-root floor weight equal to one. -/
private theorem eulerAsym_quotient_geometry
    (R b : ℕ) (hR : 2 ≤ R)
    (hb : eulerAsymCutoff R < b) (hbN : b ≤ R - 1) :
    R ≤ squareRootEndpoint R / b ∧
    squareRootEndpoint R / b < 2 * R ∧
    squareRootEndpoint R / b ≤ R + Nat.sqrt R + 1 := by
  let H := Nat.sqrt R
  let X := squareRootEndpoint R
  obtain ⟨hHlt, hHtwo, hHsq⟩ := eulerAsym_sqrt_geometry R hR
  have hXsq : X + 1 = R * R := by
    dsimp [X, squareRootEndpoint]
    rw [Nat.sub_add_cancel (by nlinarith : 1 ≤ R ^ 2)]
    ring
  have hbpos : 0 < b := by omega
  have hBH : R ≤ b + H := by
    dsimp [eulerAsymCutoff, H] at hb
    omega
  have htwob : R ≤ 2 * b := by
    change 2 * H ≤ R at hHtwo
    omega
  have hRb : R * b ≤ X := by
    have hm := Nat.mul_le_mul_left R hbN
    nlinarith
  have hlow : R ≤ X / b :=
    (Nat.le_div_iff_mul_le hbpos).2 hRb
  have hXtwo : X < (2 * R) * b := by
    have hm := Nat.mul_le_mul_left R htwob
    nlinarith
  have hhigh : X / b < 2 * R :=
    (Nat.div_lt_iff_lt_mul hbpos).2 (by nlinarith)
  have hXshort : X < (R + H + 2) * b := by
    have hm := Nat.mul_le_mul_left (R + H + 2) hBH
    nlinarith
  have hshort : X / b < R + H + 2 :=
    (Nat.div_lt_iff_lt_mul hbpos).2 (by nlinarith)
  refine ⟨hlow, hhigh, ?_⟩
  change X / b ≤ R + H + 1
  omega

private theorem eulerAsym_floor_reorder (R a b : ℕ) :
    eulerSelfDualFloor R a b =
      (((squareRootEndpoint R / b) / a : ℕ) : ℂ) := by
  unfold eulerSelfDualFloor
  congr 1
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- Exactly one, NOT zero, on every admitted post-root corner site. -/
theorem eulerAsym_corner_floor_one
    (R a b : ℕ) (hR : 2 ≤ R)
    (hb : eulerAsymCutoff R < b) (hbN : b ≤ R - 1)
    (ha : R ≤ a) (haX : a ≤ squareRootEndpoint R / b) :
    eulerSelfDualFloor R a b = 1 := by
  obtain ⟨_, hXtwo, _⟩ :=
    eulerAsym_quotient_geometry R b hR hb hbN
  have hap : 0 < a := by omega
  have hlow : 1 ≤ (squareRootEndpoint R / b) / a :=
    (Nat.le_div_iff_mul_le hap).2 (by simpa using haX)
  have hhigh : (squareRootEndpoint R / b) / a < 2 :=
    (Nat.div_lt_iff_lt_mul hap).2 (by omega)
  have hone : (squareRootEndpoint R / b) / a = 1 := by omega
  rw [eulerAsym_floor_reorder, hone]
  norm_num

private theorem eulerAsym_mobius_interval
    (u v : ℕ) (huv : u ≤ v) :
    (∑ n ∈ Finset.Ioc u v, (((μ n : ℤ) : ℂ))) =
      mertensSummatory v - mertensSummatory u := by
  have hs := Finset.sum_Ioc_consecutive
    (f := fun n : ℕ => (((μ n : ℤ) : ℂ))) (Nat.zero_le u) huv
  rw [eulerAsym_Ioc_zero_eq_Icc u,
      eulerAsym_Ioc_zero_eq_Icc v,
      ← mertensSummatory_eq_sum_Icc u,
      ← mertensSummatory_eq_sum_Icc v] at hs
  linear_combination hs

/-- One omitted b-row is the global Mobius floor unit minus the literal
post-root coefficient tail.  No individual floor or divisor correction is
dropped in this identity. -/
theorem eulerAsym_omitted_row
    (R b : ℕ) (hR : 2 ≤ R)
    (hb : eulerAsymCutoff R < b) (hbN : b ≤ R - 1) :
    (∑ a ∈ Finset.Icc 1 (R - 1),
      (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b) =
      1 - (mertensSummatory (squareRootEndpoint R / b) -
        mertensSummatory (R - 1)) := by
  let N := R - 1
  let K := squareRootEndpoint R / b
  have hKbounds := eulerAsym_quotient_geometry R b hR hb hbN
  have hNK : N ≤ K := by dsimp [N, K]; omega
  have hKpos : 1 ≤ K := by dsimp [K]; omega
  have htotalZ := nativeSumMoebiusMulFloor K hKpos
  have htotal :
      (∑ a ∈ Finset.Icc 1 K,
        (((μ a : ℤ) : ℂ)) * (((K / a : ℕ)) : ℂ)) = 1 := by
    exact_mod_cast htotalZ
  let f : ℕ → ℂ := fun a =>
    (((μ a : ℤ) : ℂ)) * (((K / a : ℕ)) : ℂ)
  have hsplit := Finset.sum_Ioc_consecutive
    (f := f) (Nat.zero_le N) hNK
  rw [eulerAsym_Ioc_zero_eq_Icc N,
      eulerAsym_Ioc_zero_eq_Icc K] at hsplit
  have htail :
      (∑ a ∈ Finset.Ioc N K, f a) =
        ∑ a ∈ Finset.Ioc N K, (((μ a : ℤ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro a ha
    have haR : R ≤ a := by
      have haN := (Finset.mem_Ioc.mp ha).1
      dsimp [N] at haN
      omega
    have haK : a ≤ K := (Finset.mem_Ioc.mp ha).2
    have hone : eulerSelfDualFloor R a b = 1 :=
      eulerAsym_corner_floor_one R a b hR hb hbN haR
        (by simpa [K] using haK)
    have hfloor := eulerAsym_floor_reorder R a b
    have hOne : K / a = 1 := by
      have hc : (((K / a : ℕ)) : ℂ) = 1 := by
        simpa [K] using (hfloor.symm.trans hone)
      exact_mod_cast hc
    simp [f, hOne]
  have hfromGlobal :
      (∑ a ∈ Finset.Icc 1 N, f a) +
        (∑ a ∈ Finset.Ioc N K, f a) = 1 := by
    rw [← hsplit]
    simpa [f] using htotal
  rw [htail, eulerAsym_mobius_interval N K hNK] at hfromGlobal
  have hfirst :
      (∑ a ∈ Finset.Icc 1 N, f a) =
        ∑ a ∈ Finset.Icc 1 (R - 1),
          (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b := by
    dsimp [N, f]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [eulerAsym_floor_reorder]
    rfl
  rw [hfirst] at hfromGlobal
  dsimp [N, K] at hfromGlobal
  linear_combination hfromGlobal

/-- The original asymmetric rectangle and the omitted strip partition
the repository's exact symmetric square, without any absolute values. -/
theorem eulerAsym_split_original_square (R : ℕ) :
    eulerAsymBilinear R + eulerAsymOmittedStrip R =
      eulerSelfDualBilinear R := by
  have hB : eulerAsymCutoff R ≤ R - 1 := Nat.sub_le _ _
  have hs := Finset.sum_Ioc_consecutive
    (f := fun b : ℕ => (((μ b : ℤ) : ℂ)) *
      ∑ a ∈ Finset.Icc 1 (R - 1),
        (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b)
    (Nat.zero_le (eulerAsymCutoff R)) hB
  rw [eulerAsym_Ioc_zero_eq_Icc (eulerAsymCutoff R),
      eulerAsym_Ioc_zero_eq_Icc (R - 1)] at hs
  exact hs

/-- The omitted strip is an EXACT historical Mertens increment minus the
small geometric corner.  It is not a dispersion estimate. -/
theorem eulerAsym_omitted_strip_eq_mertens_sub_corner
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAsymOmittedStrip R =
      mertensSummatory (R - 1) -
        mertensSummatory (eulerAsymCutoff R) -
          eulerAsymCorner R := by
  unfold eulerAsymOmittedStrip
  calc
    _ = ∑ b ∈ Finset.Ioc (eulerAsymCutoff R) (R - 1),
       (((μ b : ℤ) : ℂ)) *
        (1 - (mertensSummatory (squareRootEndpoint R / b) -
          mertensSummatory (R - 1))) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := Finset.mem_Ioc.mp hb
      rw [eulerAsym_omitted_row R b hR hb'.1 hb'.2]
    _ = (∑ b ∈ Finset.Ioc (eulerAsymCutoff R) (R - 1),
       (((μ b : ℤ) : ℂ))) - eulerAsymCorner R := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
      rfl
    _ = _ := by
      rw [eulerAsym_mobius_interval
        (eulerAsymCutoff R) (R - 1) (Nat.sub_le _ _)]
      ring

/-- The EXACT asymmetric two-cutoff inversion identity.  It carries the
future Mertens value with coefficient -1 and does not diminish that term. -/
theorem eulerAsymBilinear_eq_mertens_add_corner
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAsymBilinear R =
      mertensSummatory (R - 1) +
        mertensSummatory (eulerAsymCutoff R) -
        mertensSummatory (squareRootEndpoint R) +
        eulerAsymCorner R := by
  have hsplit := eulerAsym_split_original_square R
  rw [eulerAsym_omitted_strip_eq_mertens_sub_corner R hR,
      eulerSelfDualBilinear_eq_two_mertens_sub_endpoint R hR] at hsplit
  linear_combination hsplit

private theorem eulerAsym_norm_moebius (n : ℕ) :
    ‖(((μ n : ℤ) : ℂ))‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

/-- Explicit unconditional corner bound.  It uses only |mu| <= 1, not RH,
historical envelopes, PNT, prime statistics, or a signed-correlation input. -/
theorem eulerAsymCorner_norm_le_two_R (R : ℕ) (hR : 2 ≤ R) :
    ‖eulerAsymCorner R‖ ≤ 2 * (R : ℝ) := by
  let H := Nat.sqrt R
  let N := R - 1
  let B := eulerAsymCutoff R
  have hfacts := eulerAsym_sqrt_geometry R hR
  have hHlt : H < R := by simpa [H] using hfacts.1
  have hHtwo : 2 * H ≤ R := by simpa [H] using hfacts.2.1
  have hHsq : H * H ≤ R := by simpa [H] using hfacts.2.2
  have hN : B + H = N := by
    dsimp [B, N, eulerAsymCutoff, H]
    omega
  have hcard : (Finset.Ioc B N).card = H := by
    rw [Nat.card_Ioc]
    omega
  have hpoint (b : ℕ) (hb : b ∈ Finset.Ioc B N) :
      ‖(((μ b : ℤ) : ℂ)) *
        (mertensSummatory (squareRootEndpoint R / b) -
          mertensSummatory N)‖ ≤ ((H + 2 : ℕ) : ℝ) := by
    have hb' := Finset.mem_Ioc.mp hb
    have hbLo : eulerAsymCutoff R < b := by simpa [B] using hb'.1
    have hbHi : b ≤ R - 1 := by simpa [N] using hb'.2
    have hgeo := eulerAsym_quotient_geometry R b hR hbLo hbHi
    have hlow : N ≤ squareRootEndpoint R / b := by dsimp [N]; omega
    have hdelta : squareRootEndpoint R / b - N ≤ H + 2 := by
      dsimp [N, H]
      omega
    calc
      ‖(((μ b : ℤ) : ℂ)) *
        (mertensSummatory (squareRootEndpoint R / b) -
          mertensSummatory N)‖ =
        ‖(((μ b : ℤ) : ℂ))‖ *
          ‖mertensSummatory (squareRootEndpoint R / b) -
            mertensSummatory N‖ := norm_mul _ _
      _ ≤ 1 * ‖mertensSummatory (squareRootEndpoint R / b) -
            mertensSummatory N‖ :=
        mul_le_mul_of_nonneg_right (eulerAsym_norm_moebius b) (norm_nonneg _)
      _ = ‖mertensSummatory (squareRootEndpoint R / b) -
            mertensSummatory N‖ := one_mul _
      _ ≤ (((squareRootEndpoint R / b - N : ℕ)) : ℝ) :=
        norm_mertensSummatory_sub_le N (squareRootEndpoint R / b) hlow
      _ ≤ ((H + 2 : ℕ) : ℝ) := by exact_mod_cast hdelta
  have hnat : H * (H + 2) ≤ 2 * R := by nlinarith
  unfold eulerAsymCorner
  change ‖∑ b ∈ Finset.Ioc B N,
      (((μ b : ℤ) : ℂ)) *
        (mertensSummatory (squareRootEndpoint R / b) -
          mertensSummatory N)‖ ≤ _
  calc
    _ ≤ ∑ b ∈ Finset.Ioc B N,
      ‖(((μ b : ℤ) : ℂ)) *
        (mertensSummatory (squareRootEndpoint R / b) -
          mertensSummatory N)‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ Finset.Ioc B N, (((H + 2 : ℕ)) : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (H : ℝ) * ((H + 2 : ℕ) : ℝ) := by
      rw [Finset.sum_const, hcard]
      simp [nsmul_eq_mul, mul_comm]
    _ ≤ 2 * (R : ℝ) := by exact_mod_cast hnat

/-- REUSE of the established signed NNS/Gram diagonal-plus-cross
decomposition, with the original omitted strip preserved literally. -/
theorem eulerAsymBilinear_eq_signedGram_sub_omitted
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAsymBilinear R =
      eulerHybridDiagonal R + 2 * eulerHybridStrictCross R -
        eulerAsymOmittedStrip R := by
  have hs := eulerAsym_split_original_square R
  rw [eulerSelfDualBilinear_eq_diagonal_add_signedStrictCross R hR] at hs
  linear_combination hs

/-- The same signed decomposition after paying the omitted strip with
the literal historical root increment and the O(R) geometric corner.
No bound is inferred for the signed strict cross interaction. -/
theorem eulerAsymBilinear_eq_signedGram_add_corner
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAsymBilinear R =
      eulerHybridDiagonal R + 2 * eulerHybridStrictCross R -
        (mertensSummatory (R - 1) -
          mertensSummatory (eulerAsymCutoff R)) +
        eulerAsymCorner R := by
  rw [eulerAsymBilinear_eq_signedGram_sub_omitted R hR,
    eulerAsym_omitted_strip_eq_mertens_sub_corner R hR]
  ring

#print axioms eulerAsym_corner_floor_one
#print axioms eulerAsym_omitted_row
#print axioms eulerAsymBilinear_eq_mertens_add_corner
#print axioms eulerAsymCorner_norm_le_two_R
#print axioms eulerAsymBilinear_eq_signedGram_add_corner

end RHLean.Proof
