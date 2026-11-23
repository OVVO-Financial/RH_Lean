import RHLean.Analysis.AlpogeThin.NativeRayCountTheta
import RHLean.Analysis.AlpogeThin.NativeRayPrimePowerMass
import RHLean.Analysis.AlpogeThin.NativeRayRealCharacter
import RHLean.Analysis.AlpogeThin.NativeRayClassBound
import RHLean.Analysis.AlpogeThin.NativeRayNormOne

/-!
# One actual arithmetic family from the same ray ideal coefficients

The original LFam arithmetic record is constructed on the GIVEN field K,
root r, modulus M and ray datum D. Every field is paid by the native ideal,
lattice, Gaussian, prime-power, class-number and real-character suppliers.
The coefficients remain exactly aRay and lamRay; no desired analytic bound
or replacement sequence is supplied as an input. The stronger all-time
theta theorem is retained separately from the original degree-ten field.

Source guide: Levent Alpöge's archive, inspected pin
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/`
`LamIdealOfNotPrimePow.lean`, structure LFam, and
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`
`ExistsLFamRay.lean`, arithmetic record construction.
This module includes no analytic F, zero-free region, prime-window theorem
or terminal RH result. The archive states no license; attribution assigns none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open NumberField Finset ArithmeticFunction
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.NativeRay

/-- The original arithmetic LFam fields, without downstream analytic definitions. -/
structure LFam where
  G : Type
  [ag : AddCommGroup G]
  [ft : Fintype G]
  B : ℝ
  κ : ℝ
  a : G → ℕ → ℝ
  lam : G → ℕ → ℝ
  B_ge : 4 ≤ B
  card_le : (Fintype.card G : ℝ) ≤ B
  κ_ge : 1 / B ≤ κ
  κ_le : κ ≤ 4
  a_nonneg : ∀ g n, 0 ≤ a g n
  a_zero : ∀ g, a g 0 = 0
  a_one : a 0 1 = 1
  a_one_ne : ∀ g, g ≠ 0 → a g 1 = 0
  count : ∀ (g : G) (x : ℝ), 1 ≤ x →
    |∑ n ∈ Icc 1 ⌊x⌋₊, a g n - κ * x| ≤ 10 * Real.sqrt x
  theta : ∀ (g : G) (t : ℝ), 0 < t → t ≤ 1 →
    |∑' n : ℕ, a g n * Real.exp (-(t * n)) - κ / t| ≤ B ^ 10 * t
  lam_nonneg : ∀ g n, 0 ≤ lam g n
  lam_le : ∀ n, ∑ g, lam g n ≤ 2 * Λ n
  conv : ∀ g n, a g n * Real.log n =
    ∑ h, ∑ p ∈ n.divisorsAntidiagonal, lam h p.1 * a (g - h) p.2
  sq : ∀ χ : AddChar G ℂ, χ * χ = 1 → ∀ n : ℕ,
    (0 ≤ ∑ p ∈ n.divisorsAntidiagonal,
      (∑ g, a g p.1) * ∑ g, (χ g).re * a g p.2) ∧
    (∑ g, a g n) ≤ ∑ p ∈ (n ^ 2).divisorsAntidiagonal,
      (∑ g, a g p.1) * ∑ g, (χ g).re * a g p.2

attribute [instance] LFam.ag LFam.ft

namespace LFam

variable (K : Type) [Field K] [NumberField K] (d M : ℕ) (r : K)
    (hp : d.Prime) (hd : d % 4 = 3) (hd100 : 100 ≤ d)
    (hr : r ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2)
    (hM : 3 ≤ M) (D : RayData K M)

/-- Every original arithmetic field is proved for the SAME given ray datum. -/
def ofRayData : LFam := by
  let B : ℝ := 4 * (d : ℝ) * (M : ℝ) ^ 2
  let κ : ℝ := 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2)
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hs : (10 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith)
  have hsd0 : 0 < Real.sqrt (d : ℝ) := by linarith
  have hss : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt hd0.le
  have hsd : Real.sqrt (d : ℝ) ≤ d := by nlinarith
  have hdm : 1 ≤ (d : ℝ) * (M : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hd1 hM2
  have hB : 4 ≤ B := by dsimp [B]; nlinarith
  have hB0 : 0 < B := by linarith
  have hκge : 1 / B ≤ κ := by
    dsimp [κ]
    rw [div_le_div_iff₀ hB0 (mul_pos hsd0 (sq_pos_of_pos hM0))]
    have hsM := mul_le_mul_of_nonneg_right hsd (sq_nonneg (M : ℝ))
    have hpi : (1 : ℝ) ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
    have hscale := mul_le_mul_of_nonneg_right hpi
      (mul_nonneg hd0.le (sq_nonneg (M : ℝ)))
    dsimp [B]
    nlinarith
  have hκle : κ ≤ 4 := by
    dsimp [κ]
    rw [div_le_iff₀ (mul_pos hsd0 (sq_pos_of_pos hM0))]
    have hden := le_mul_of_one_le_right (Real.sqrt_nonneg (d : ℝ)) hM2
    nlinarith [Real.pi_le_four]
  have hcoarse : (3 * Real.pi / 8) * d * Real.sqrt d * (M : ℝ) ^ 2 ≤ B ^ 10 := by
    have hcoef : 3 * Real.pi / 8 ≤ (2 : ℝ) := by linarith [Real.pi_le_four]
    have htwo : (2 : ℝ) ≤ 16 * (M : ℝ) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right htwo
      (mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg (M : ℝ)))
    calc (3 * Real.pi / 8) * d * Real.sqrt d * (M : ℝ) ^ 2
        ≤ 2 * d * Real.sqrt d * (M : ℝ) ^ 2 := by gcongr
      _ ≤ 2 * d * d * (M : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsd (by positivity : (0 : ℝ) ≤ 2 * d))
          (sq_nonneg (M : ℝ))
      _ ≤ B ^ 2 := by dsimp [B]; nlinarith
      _ ≤ B ^ 10 := pow_le_pow_right₀ (by linarith : 1 ≤ B) (by norm_num)
  have hc := rayCountTheta K d M r hp hd hd100 hr h2 hM D
  exact {
    G := Additive D.G
    ft := D.fin
    B := B
    κ := κ
    a := fun g n => aRay D g.toMul n
    lam := fun g n => lamRay D g.toMul n
    B_ge := hB
    card_le := card_ray_le hp hd hr h2 (by omega) D
    κ_ge := hκge
    κ_le := hκle
    a_nonneg := fun g n => aRay_nonneg D g.toMul n
    a_zero := fun g => aRay_norm_zero D g.toMul
    a_one := aRay_one_norm_one D
    a_one_ne := fun g hg => aRay_norm_one_of_ne D hg
    count := by
      intro g y hy
      apply ((hc g.toMul).1 y hy).trans
      have hs1 : 1 ≤ Real.sqrt y := Real.le_sqrt_of_sq_le (by simpa using hy)
      have hdiv := div_le_self
        (by positivity : 0 ≤ 4 * Real.sqrt y) hM1
      linarith
    theta := fun g t ht _ => ((hc g.toMul).2 t ht).2.trans
      (mul_le_mul_of_nonneg_right hcoarse ht.le)
    lam_nonneg := fun g n => lamRay_nonneg D g.toMul n
    lam_le := PrimePowerMass.quadratic_ray_mass_le h2 D
    conv := fun g n => aRay_mul_log K M (by omega) D g.toMul n
    sq := fun χ hχ n => RealCharacter.conv_real_addChar D χ hχ n }

@[simp] theorem ofRayData_B :
    (ofRayData K d M r hp hd hd100 hr h2 hM D).B =
      4 * (d : ℝ) * (M : ℝ) ^ 2 := rfl

@[simp] theorem ofRayData_kappa :
    (ofRayData K d M r hp hd hd100 hr h2 hM D).κ =
      2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) := rfl

@[simp] theorem ofRayData_a (g : Additive D.G) (n : ℕ) :
    (ofRayData K d M r hp hd hd100 hr h2 hM D).a g n =
      aRay D g.toMul n := rfl

@[simp] theorem ofRayData_lam (g : Additive D.G) (n : ℕ) :
    (ofRayData K d M r hp hd hd100 hr h2 hM D).lam g n =
      lamRay D g.toMul n := rfl

/-- Keep the sharper all-time estimate on this literal constructed family. -/
theorem ofRayData_sharp_theta (g : Additive D.G) (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      (ofRayData K d M r hp hd hd100 hr h2 hM D).a g n * Real.exp (-(t * n))) ∧
    |∑' n : ℕ,
        (ofRayData K d M r hp hd hd100 hr h2 hM D).a g n * Real.exp (-(t * n)) -
      (ofRayData K d M r hp hd hd100 hr h2 hM D).κ / t| ≤
      (3 * Real.pi / 8) * d * Real.sqrt d * (M : ℝ) ^ 2 * t := by
  exact (rayCountTheta K d M r hp hd hd100 hr h2 hM D g.toMul).2 t ht

/-- The original prime-support consumer follows, in fact, at every norm. -/
theorem ofRayData_normOne (n : ℕ)
    (hn : (ofRayData K d M r hp hd hd100 hr h2 hM D).lam 0 n ≠ 0) :
    Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOne d M n := by
  exact NormOne.isNormOne_of_lamRay_ne_zero hp hd hr h2 D n hn

end LFam

end RHLean.Analysis.AlpogeThin.NativeRay

end
