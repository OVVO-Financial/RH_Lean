import Mathlib
import «research.EULER_SELF_DUAL_POINTWISE_20261027»
import «research.EULER_HYBRID_TRIANGULAR_GRAM_20261027»
import RHLean.Analysis.MobiusRenewalTelescope

/-!
# Source-faithful finite Euler convolution and historical floor-bilinear bridge

First, expand the actual two historical Möbius copies and zeta by the
existing complete divisor-antidiagonal Fubini theorem. At the self-dual
endpoint X = R^2-1, both historical factors are fully supported in the
rectangle 1<=a,b<R; all other terms are zero, not bounded.

Second, use the independently certified Newton pointwise coefficient
identity for n<R^2. These two calculations meet at the *literal*
eulerSelfDualBilinear of merged PR #1034.

This supplies no uniform signed estimate for the bilinear form.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Analysis.MertensFiniteExtension
open ArithmeticFunction

private theorem eulerZetaPositive (k : ℕ) (hk : 1 ≤ k) :
    zetaInt k = 1 := by
  have hk0 : k ≠ 0 := by omega
  simp [zetaInt, ArithmeticFunction.zeta_apply_ne hk0]

/-- Sum the actual triple convolution by the original divisor geometry.
This is generic in the historical arithmetic function P and cutoff X. -/
private theorem eulerTripleConvolution_sum_eq_hyperbolaFloor
    (P : ArithmeticFunction ℤ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X,
      (((P * P * zetaInt) n : ℤ) : ℂ)) =
      ∑ b ∈ Finset.Icc 1 X,
        ∑ a ∈ Finset.Icc 1 (X / b),
          (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ)) := by
  classical
  have hzeta (N : ℕ) :
      (∑ k ∈ Finset.Icc 1 N, (((zetaInt k : ℤ) : ℂ))) =
        (N : ℂ) := by
    calc
      _ = ∑ k ∈ Finset.Icc 1 N, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkpos := (Finset.mem_Icc.mp hk).1
        rw [eulerZetaPositive k hkpos]
        norm_num
      _ = ((Finset.Icc 1 N).card : ℂ) := by simp
      _ = (N : ℂ) := by simp [Nat.card_Icc]
  have hfirst :
      (∑ n ∈ Finset.Icc 1 X,
        (((P * P * zetaInt) n : ℤ) : ℂ)) =
      ∑ d ∈ Finset.Icc 1 X,
        (((P * P) d : ℤ) : ℂ) * ((X / d : ℕ) : ℂ) := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 X,
        ∑ p ∈ n.divisorsAntidiagonal,
          (((P * P) p.1 : ℤ) : ℂ) * (((zetaInt p.2 : ℤ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro n _hn
        rw [ArithmeticFunction.mul_apply]
        push_cast
        rfl
      _ = ∑ d ∈ Finset.Icc 1 X,
        ∑ k ∈ Finset.Icc 1 (X / d),
          (((P * P) d : ℤ) : ℂ) * (((zetaInt k : ℤ) : ℂ)) :=
        RHLean.Analysis.sum_Icc_divisorsAntidiagonal_eq_sum_div
          (fun d k => (((P * P) d : ℤ) : ℂ) * (((zetaInt k : ℤ) : ℂ))) X
      _ = ∑ d ∈ Finset.Icc 1 X,
        (((P * P) d : ℤ) : ℂ) * ((X / d : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro d _hd
        rw [← Finset.mul_sum, hzeta]
  calc
    (∑ n ∈ Finset.Icc 1 X,
      (((P * P * zetaInt) n : ℤ) : ℂ)) =
      ∑ d ∈ Finset.Icc 1 X,
        (((P * P) d : ℤ) : ℂ) * ((X / d : ℕ) : ℂ) := hfirst
    _ = ∑ d ∈ Finset.Icc 1 X,
      ∑ p ∈ d.divisorsAntidiagonal,
        (((P p.1 : ℤ) : ℂ)) * (((P p.2 : ℤ) : ℂ)) *
          (((X / (p.1 * p.2) : ℕ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro d _hd
        rw [ArithmeticFunction.mul_apply]
        push_cast
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        have hprod : p.1 * p.2 = d :=
          (Nat.mem_divisorsAntidiagonal.mp hp).1
        rw [hprod]
    _ = ∑ b ∈ Finset.Icc 1 X,
        ∑ a ∈ Finset.Icc 1 (X / b),
          (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ)) :=
      RHLean.Analysis.sum_Icc_divisorsAntidiagonal_eq_sum_div
        (fun b a =>
          (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ))) X

/-- On the exact square endpoint, the full historical rectangle is inside
the hyperbola. This is why no masked boundary survives in the bilinear
convolution-to-floor reindexing. -/
private theorem eulerHistoricalProduct_le_squareEndpoint
    {R a b : ℕ} (hR : 2 ≤ R) (ha : 1 ≤ a) (haR : a < R)
    (_hb : 1 ≤ b) (hbR : b < R) :
    a * b ≤ squareRootEndpoint R := by
  have ha' : a ≤ R - 1 := by omega
  have hb' : b ≤ R - 1 := by omega
  have hRpred : R - 1 + 1 = R := by omega
  have hquad : (R - 1) * (R - 1) + 1 ≤ R ^ 2 := by
    nlinarith
  have hmul : a * b ≤ (R - 1) * (R - 1) :=
    Nat.mul_le_mul ha' hb'
  unfold squareRootEndpoint
  omega

/-- The actual triangular historical bilinear floor sum is the
complete Dirichlet convolution summatory on n<R^2, not a proxy. -/
theorem eulerSelfDualBilinear_eq_convolutionSummatory
    (R : ℕ) (hR : 2 ≤ R) :
    eulerSelfDualBilinear R =
      ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        ((eulerSelfDualConvolutionCoefficient R n : ℤ) : ℂ) := by
  classical
  let X : ℕ := squareRootEndpoint R
  let P : ArithmeticFunction ℤ := eulerSelfDualPrefix R
  have hRX : R - 1 ≤ X := by
    dsimp [X, squareRootEndpoint]
    have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have houter :
      Finset.Icc 1 (R - 1) ⊆ Finset.Icc 1 X := by
    intro b hb
    rcases Finset.mem_Icc.mp hb with ⟨hb1, hbR⟩
    exact Finset.mem_Icc.mpr ⟨hb1, hbR.trans hRX⟩
  have hinner (b : ℕ) (hb : b ∈ Finset.Icc 1 (R - 1)) :
      (∑ a ∈ Finset.Icc 1 (X / b),
        (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
          (((X / (b * a) : ℕ) : ℂ))) =
      ∑ a ∈ Finset.Icc 1 (R - 1),
        (((μ b : ℤ) : ℂ)) * (((μ a : ℤ) : ℂ)) *
          (((X / (b * a) : ℕ) : ℂ)) := by
    have hb1 := (Finset.mem_Icc.mp hb).1
    have hbR : b < R := by have t := (Finset.mem_Icc.mp hb).2; omega
    have hsub :
        Finset.Icc 1 (R - 1) ⊆ Finset.Icc 1 (X / b) := by
      intro a ha
      rcases Finset.mem_Icc.mp ha with ⟨ha1, haR⟩
      have hprod : b * a ≤ X := by
        exact eulerHistoricalProduct_le_squareEndpoint hR hb1 hbR ha1 (by omega)
      have haDiv : a ≤ X / b :=
        (Nat.le_div_iff_mul_le (by omega : 0 < b)).2
          (by simpa [Nat.mul_comm] using hprod)
      exact Finset.mem_Icc.mpr ⟨ha1, haDiv⟩
    have hcut :
        (∑ a ∈ Finset.Icc 1 (X / b),
          (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ))) =
        ∑ a ∈ Finset.Icc 1 (R - 1),
          (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ)) := by
      symm
      apply Finset.sum_subset hsub
      intro a ha hnot
      have ha1 := (Finset.mem_Icc.mp ha).1
      have haNot : ¬ a ≤ R - 1 := by
        intro hal
        exact hnot (Finset.mem_Icc.mpr ⟨ha1, hal⟩)
      simp [P, eulerSelfDualPrefix, mobiusPrefix, haNot]
    rw [hcut]
    apply Finset.sum_congr rfl
    intro a ha
    have haR := (Finset.mem_Icc.mp ha).2
    have hbR' := (Finset.mem_Icc.mp hb).2
    simp [P, eulerSelfDualPrefix, mobiusPrefix, haR, hbR']
  have htruncate :
      (∑ b ∈ Finset.Icc 1 X,
        ∑ a ∈ Finset.Icc 1 (X / b),
          (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ))) =
      ∑ b ∈ Finset.Icc 1 (R - 1),
        ∑ a ∈ Finset.Icc 1 (R - 1),
          (((μ b : ℤ) : ℂ)) * (((μ a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ)) := by
    have hcut :
      (∑ b ∈ Finset.Icc 1 X,
        ∑ a ∈ Finset.Icc 1 (X / b),
          (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ))) =
      ∑ b ∈ Finset.Icc 1 (R - 1),
        ∑ a ∈ Finset.Icc 1 (X / b),
          (((P b : ℤ) : ℂ)) * (((P a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ)) := by
      symm
      apply Finset.sum_subset houter
      intro b hb hnot
      have hb1 := (Finset.mem_Icc.mp hb).1
      have hbNot : ¬ b ≤ R - 1 := by
        intro hbR
        exact hnot (Finset.mem_Icc.mpr ⟨hb1, hbR⟩)
      simp [P, eulerSelfDualPrefix, mobiusPrefix, hbNot]
    rw [hcut]
    apply Finset.sum_congr rfl
    intro b hb
    exact hinner b hb
  have hfubini :=
    eulerTripleConvolution_sum_eq_hyperbolaFloor P X
  have hcoefficient :
      (∑ n ∈ Finset.Icc 1 X,
        ((eulerSelfDualConvolutionCoefficient R n : ℤ) : ℂ)) =
      ∑ b ∈ Finset.Icc 1 (R - 1),
        ∑ a ∈ Finset.Icc 1 (R - 1),
          (((μ b : ℤ) : ℂ)) * (((μ a : ℤ) : ℂ)) *
            (((X / (b * a) : ℕ) : ℂ)) := by
    simpa [P, eulerSelfDualPrefix, eulerSelfDualConvolutionCoefficient] using
      hfubini.trans htruncate
  rw [hcoefficient]
  unfold eulerSelfDualBilinear eulerSelfDualFloor
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [X]
  rw [Nat.mul_comm b a]
  ring

#print axioms eulerSelfDualBilinear_eq_convolutionSummatory

end RHLean.Proof
